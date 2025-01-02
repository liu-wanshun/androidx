/*
 * Copyright 2024 The Android Open Source Project
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package androidx.pdf.view

import android.animation.ValueAnimator
import android.content.Context
import android.content.Intent
import android.graphics.Canvas
import android.graphics.Point
import android.graphics.PointF
import android.graphics.Rect
import android.net.Uri
import android.os.Looper
import android.os.Parcelable
import android.util.AttributeSet
import android.util.Range
import android.view.KeyEvent
import android.view.MotionEvent
import android.view.ScaleGestureDetector
import android.view.View
import androidx.annotation.RestrictTo
import androidx.annotation.VisibleForTesting
import androidx.core.os.HandlerCompat
import androidx.core.view.ViewCompat
import androidx.pdf.PdfDocument
import androidx.pdf.util.Accessibility
import androidx.pdf.util.ZoomUtils
import java.util.LinkedList
import java.util.Queue
import java.util.concurrent.Executors
import kotlin.math.abs
import kotlin.math.max
import kotlin.math.round
import kotlin.math.roundToInt
import kotlinx.coroutines.CoroutineScope
import kotlinx.coroutines.CoroutineStart
import kotlinx.coroutines.Job
import kotlinx.coroutines.SupervisorJob
import kotlinx.coroutines.android.asCoroutineDispatcher
import kotlinx.coroutines.asCoroutineDispatcher
import kotlinx.coroutines.cancelChildren
import kotlinx.coroutines.launch

/**
 * A [View] for presenting PDF content, represented by [PdfDocument].
 *
 * This View supports zooming, scrolling, and flinging. Zooming is supported via pinch gesture,
 * quick scale gesture, and double tap to zoom in or snap back to fitting the page width inside its
 * bounds. Zoom can be changed using the [zoom] property, which is notably distinct from
 * [View.getScaleX] / [View.getScaleY]. Scroll position is based on the [View.getScrollX] /
 * [View.getScrollY] properties.
 */
@RestrictTo(RestrictTo.Scope.LIBRARY)
public open class PdfView
@JvmOverloads
constructor(context: Context, attrs: AttributeSet? = null, defStyle: Int = 0) :
    View(context, attrs, defStyle) {
    /** Supply a [PdfDocument] to process the PDF content for rendering */
    public var pdfDocument: PdfDocument? = null
        set(value) {
            checkMainThread()
            value?.let {
                val reset = field != null && field?.uri != value.uri
                field = it
                if (reset) reset()
                onDocumentSet()
            }
        }

    /** The maximum scaling factor that can be applied to this View using the [zoom] property */
    // TODO(b/376299551) - Make maxZoom configurable via XML attribute
    public var maxZoom: Float = DEFAULT_MAX_ZOOM

    /** The minimum scaling factor that can be applied to this View using the [zoom] property */
    // TODO(b/376299551) - Make minZoom configurable via XML attribute
    public var minZoom: Float = DEFAULT_MIN_ZOOM

    /**
     * The zoom level of this view, as a factor of the content's natural size with when 1 pixel is
     * equal to 1 PDF point. Will always be clamped within ([minZoom], [maxZoom])
     */
    public var zoom: Float = DEFAULT_INIT_ZOOM
        set(value) {
            checkMainThread()
            field = value
            onZoomChanged()
            invalidate()
        }

    /**
     * A set of areas to be highlighted. Each [Highlight] may be a different color. Setting this
     * property overrides any previous highlights, there is no merging behavior of new and previous
     * values.
     */
    public var highlights: List<Highlight> = listOf()
        set(value) {
            checkMainThread()
            val localPageManager =
                pageManager
                    ?: throw IllegalStateException("Can't highlightAreas without PdfDocument")
            localPageManager.setHighlights(value)
        }

    private val visiblePages: Range<Int>
        get() = pageLayoutManager?.visiblePages?.value ?: Range(0, 0)

    /** The first page in the viewport, including partially-visible pages. 0-indexed. */
    public val firstVisiblePage: Int
        get() = visiblePages.lower

    /** The number of pages visible in the viewport, including partially visible pages */
    public val visiblePagesCount: Int
        get() = if (pdfDocument != null) visiblePages.upper - visiblePages.lower + 1 else 0

    /** Listener interface for handling clicks on links in a PDF document. */
    public interface LinkClickListener {
        /**
         * Called when a link in the PDF is clicked.
         *
         * @param uri The URI associated with the link.
         */
        public fun onLinkClicked(uri: Uri)
    }

    /** The listener that is notified when a link in the PDF is clicked. */
    public var linkClickListener: LinkClickListener? = null

    /**
     * The [CoroutineScope] used to make suspending calls to [PdfDocument]. The size of the fixed
     * thread pool is arbitrary and subject to tuning.
     */
    internal val backgroundScope: CoroutineScope =
        CoroutineScope(Executors.newFixedThreadPool(5).asCoroutineDispatcher() + SupervisorJob())

    private var pageLayoutManager: PageLayoutManager? = null
    private var pageManager: PageManager? = null
    private var visiblePagesCollector: Job? = null
    private var dimensionsCollector: Job? = null
    private var invalidationCollector: Job? = null

    private var deferredScrollPage: Int? = null
    private var deferredScrollPosition: PdfPoint? = null

    /** Used to restore saved state */
    private var stateToRestore: PdfViewSavedState? = null
    private var awaitingFirstLayout: Boolean = true
    private var scrollPositionToRestore: PointF? = null
    private var zoomToRestore: Float? = null

    private val gestureHandler = ZoomScrollGestureHandler()
    private val gestureTracker = GestureTracker(context).apply { delegate = gestureHandler }

    private val scroller = RelativeScroller(context)
    /** Whether we are in a fling movement. This is used to detect the end of that movement */
    private var isFling = false

    // To avoid allocations during drawing
    private val visibleAreaRect = Rect()

    @VisibleForTesting internal var accessibilityPageHelper: AccessibilityPageHelper? = null
    @VisibleForTesting
    internal var isTouchExplorationEnabled: Boolean =
        Accessibility.get().isTouchExplorationEnabled(context)
        set(value) {
            field = value
        }

    /**
     * Scrolls to the 0-indexed [pageNum], optionally animating the scroll
     *
     * This View cannot scroll to a page until it knows its dimensions. If [pageNum] is distant from
     * the currently-visible page in a large PDF, there may be some delay while dimensions are being
     * loaded from the PDF.
     */
    @Suppress("UNUSED_PARAMETER")
    public fun scrollToPage(pageNum: Int) {
        checkMainThread()
        val localPageLayoutManager =
            pageLayoutManager
                ?: throw IllegalStateException("Can't scrollToPage without PdfDocument")
        require(pageNum < (pdfDocument?.pageCount ?: Int.MIN_VALUE)) {
            "Page $pageNum not in document"
        }

        if (localPageLayoutManager.reach >= pageNum) {
            gotoPage(pageNum)
        } else {
            localPageLayoutManager.increaseReach(pageNum)
            deferredScrollPage = pageNum
            deferredScrollPosition = null
        }
    }

    /**
     * Scrolls to [position], optionally animating the scroll
     *
     * This View cannot scroll to a page until it knows its dimensions. If [position] is distant
     * from the currently-visible page in a large PDF, there may be some delay while dimensions are
     * being loaded from the PDF.
     */
    @Suppress("UNUSED_PARAMETER")
    public fun scrollToPosition(position: PdfPoint) {
        checkMainThread()
        val localPageLayoutManager =
            pageLayoutManager
                ?: throw IllegalStateException("Can't scrollToPage without PdfDocument")

        if (position.pageNum >= (pdfDocument?.pageCount ?: Int.MIN_VALUE)) {
            return
        }

        if (localPageLayoutManager.reach >= position.pageNum) {
            gotoPoint(position)
        } else {
            localPageLayoutManager.increaseReach(position.pageNum)
            deferredScrollPosition = position
            deferredScrollPage = null
        }
    }

    private fun gotoPage(pageNum: Int) {
        checkMainThread()
        val localPageLayoutManager =
            pageLayoutManager
                ?: throw IllegalStateException("Can't scrollToPage without PdfDocument")
        check(pageNum <= localPageLayoutManager.reach) { "Can't gotoPage that's not laid out" }

        val pageRect =
            localPageLayoutManager.getPageLocation(pageNum, getVisibleAreaInContentCoords())
        // Zoom should match the width of the page
        val zoom =
            ZoomUtils.calculateZoomToFit(
                viewportWidth.toFloat(),
                viewportHeight.toFloat(),
                pageRect.width().toFloat(),
                1f
            )
        val x = round((pageRect.left + pageRect.width() / 2f) * zoom - (viewportWidth / 2f))
        val y = round((pageRect.top + pageRect.height() / 2f) * zoom - (viewportHeight / 2f))

        // Set zoom to fit the width of the page, then scroll to the center of the page
        this.zoom = zoom
        scrollTo(x.toInt(), y.toInt())
    }

    private fun gotoPoint(position: PdfPoint) {
        checkMainThread()
        val localPageLayoutManager =
            pageLayoutManager
                ?: throw IllegalStateException("Can't scrollToPage without PdfDocument")
        check(position.pageNum <= localPageLayoutManager.reach) {
            "Can't gotoPoint on page that's not laid out"
        }

        val pageRect =
            localPageLayoutManager.getPageLocation(
                position.pageNum,
                getVisibleAreaInContentCoords()
            )
        // Zoom should match the width of the page
        val zoom =
            ZoomUtils.calculateZoomToFit(
                viewportWidth.toFloat(),
                viewportHeight.toFloat(),
                pageRect.width().toFloat(),
                1f
            )

        val x = round((pageRect.left + pageRect.width() / 2f) * zoom - (viewportWidth / 2f))
        val y = round((pageRect.top + position.pagePoint.y) * zoom - (viewportHeight / 2f))

        // Set zoom to fit the width of the page, then scroll to the requested point on the page
        this.zoom = zoom
        scrollTo(x.toInt(), y.toInt())
    }

    override fun dispatchHoverEvent(event: MotionEvent): Boolean {
        return accessibilityPageHelper?.dispatchHoverEvent(event) == true ||
            super.dispatchHoverEvent(event)
    }

    override fun dispatchKeyEvent(event: KeyEvent): Boolean {
        return accessibilityPageHelper?.dispatchKeyEvent(event) == true ||
            super.dispatchKeyEvent(event)
    }

    override fun onFocusChanged(gainFocus: Boolean, direction: Int, previouslyFocusedRect: Rect?) {
        super.onFocusChanged(gainFocus, direction, previouslyFocusedRect)
        accessibilityPageHelper?.onFocusChanged(gainFocus, direction, previouslyFocusedRect)
    }

    override fun onDraw(canvas: Canvas) {
        super.onDraw(canvas)
        val localPaginationManager = pageLayoutManager ?: return
        canvas.save()
        canvas.scale(zoom, zoom)
        for (i in visiblePages.lower..visiblePages.upper) {
            pageManager?.drawPage(
                i,
                canvas,
                localPaginationManager.getPageLocation(i, getVisibleAreaInContentCoords())
            )
        }
        canvas.restore()
    }

    override fun onTouchEvent(event: MotionEvent?): Boolean {
        val handled = event?.let { gestureTracker.feed(it) } ?: false
        return handled || super.onTouchEvent(event)
    }

    override fun onSizeChanged(w: Int, h: Int, oldw: Int, oldh: Int) {
        super.onSizeChanged(w, h, oldw, oldh)
        pageLayoutManager?.onViewportChanged(scrollY, height, zoom)
        accessibilityPageHelper?.invalidateRoot()
    }

    override fun onScrollChanged(l: Int, t: Int, oldl: Int, oldt: Int) {
        super.onScrollChanged(l, t, oldl, oldt)
        pageLayoutManager?.onViewportChanged(scrollY, height, zoom)
        accessibilityPageHelper?.invalidateRoot()
    }

    override fun onLayout(changed: Boolean, left: Int, top: Int, right: Int, bottom: Int) {
        super.onLayout(changed, left, top, right, bottom)
        val localScrollPositionToRestore = scrollPositionToRestore
        if (awaitingFirstLayout && localScrollPositionToRestore != null) {
            scrollToRestoredPosition(localScrollPositionToRestore, zoomToRestore ?: zoom)
        }
        awaitingFirstLayout = false
    }

    override fun onAttachedToWindow() {
        super.onAttachedToWindow()
        stopCollectingData()
        awaitingFirstLayout = true
    }

    override fun onWindowVisibilityChanged(visibility: Int) {
        super.onWindowVisibilityChanged(visibility)
        if (visibility == VISIBLE) startCollectingData() else stopCollectingData()
    }

    override fun onDetachedFromWindow() {
        super.onDetachedFromWindow()
        stopCollectingData()
        awaitingFirstLayout = true
        pageManager?.onDetached()
    }

    override fun onSaveInstanceState(): Parcelable? {
        val superState = super.onSaveInstanceState()
        val state = PdfViewSavedState(superState)
        state.contentCenterX = scrollX.toFloat() + width / 2
        state.contentCenterY = scrollY.toFloat() + height / 2
        state.zoom = zoom
        state.documentUri = pdfDocument?.uri
        state.paginationModel = pageLayoutManager?.paginationModel
        return state
    }

    override fun onRestoreInstanceState(state: Parcelable?) {
        if (state !is PdfViewSavedState) {
            super.onRestoreInstanceState(state)
            return
        }
        super.onRestoreInstanceState(state.superState)
        stateToRestore = state
        if (pdfDocument != null) {
            maybeRestoreState()
        }
    }

    override fun computeScroll() {
        // Cause OverScroller to compute the new position
        if (scroller.computeScrollOffset()) {
            scroller.apply(this)
            postInvalidateOnAnimation()
        } else if (isFling) {
            isFling = false
            // Once the fling has ended, prompt the page manager to start fetching data for pages
            // that we don't fetch during a fling
            pageManager?.maybeUpdatePageState(visiblePages, zoom, isFling)
        }
    }

    override fun scrollBy(x: Int, y: Int) {
        // This is precisely the implementation of View.scrollBy; this is defensive in case the
        // View implementation changes given we assume all scrolling flows through scrollTo
        scrollTo(scrollX + x, scrollY + y)
    }

    override fun scrollTo(x: Int, y: Int) {
        val cappedX = x.coerceIn(0..computeHorizontalScrollRange())
        val cappedY = y.coerceIn(minVerticalScrollPosition..computeVerticalScrollRange())
        super.scrollTo(cappedX, cappedY)
    }

    override fun computeHorizontalScrollRange(): Int {
        // Note we provide scroll = 0 here, as we shouldn't consider the current scroll position
        // to compute the maximum scroll position. Scroll position is absolute, not relative
        val contentWidthPx = toViewCoord(contentWidth.toFloat(), zoom, scroll = 0)
        return if (contentWidthPx < width) 0 else (contentWidthPx - width).roundToInt()
    }

    private val minVerticalScrollPosition: Int
        get() {
            // Note we provide scroll = 0 here, as we shouldn't consider the current scroll position
            // to compute the maximum scroll position. Scroll position is absolute, not relative
            val contentHeightPx = toViewCoord(contentHeight.toFloat(), zoom, scroll = 0)
            return if (contentHeightPx < height) {
                // Center vertically
                -(height - contentHeightPx).roundToInt() / 2
            } else {
                0
            }
        }

    override fun computeVerticalScrollRange(): Int {
        // Note we provide scroll = 0 here, as we shouldn't consider the current scroll position
        // to compute the maximum scroll position. Scroll position is absolute, not relative
        val contentHeightPx = toViewCoord(contentHeight.toFloat(), zoom, scroll = 0)
        return if (contentHeightPx < height) {
            // Center vertically
            -(height - contentHeightPx).roundToInt() / 2
        } else {
            (contentHeightPx - height).roundToInt()
        }
    }

    /**
     * Returns true if we are able to restore a previous state from savedInstanceState
     *
     * We are not be able to restore our previous state if it pertains to a different document, or
     * if it is missing critical data like page layout information.
     */
    private fun maybeRestoreState(): Boolean {
        val localStateToRestore = stateToRestore ?: return false
        val localPdfDocument = pdfDocument ?: return false
        if (
            localPdfDocument.uri != localStateToRestore.documentUri ||
                !localStateToRestore.hasEnoughStateToRestore
        ) {
            stateToRestore = null
            return false
        }
        pageLayoutManager =
            PageLayoutManager(
                    localPdfDocument,
                    backgroundScope,
                    DEFAULT_PAGE_PREFETCH_RADIUS,
                    paginationModel = localStateToRestore.paginationModel!!
                )
                .apply { onViewportChanged(scrollY, height, zoom) }
        val positionToRestore =
            PointF(localStateToRestore.contentCenterX, localStateToRestore.contentCenterY)
        if (awaitingFirstLayout) {
            scrollPositionToRestore = positionToRestore
            zoomToRestore = localStateToRestore.zoom
        } else {
            scrollToRestoredPosition(positionToRestore, localStateToRestore.zoom)
        }
        setAccessibility()

        stateToRestore = null
        return true
    }

    private fun scrollToRestoredPosition(position: PointF, zoom: Float) {
        this.zoom = zoom
        scrollTo(round(position.x - width / 2f).toInt(), round(position.y - height / 2f).toInt())
        scrollPositionToRestore = null
        zoomToRestore = null
    }

    private fun startCollectingData() {
        val mainScope =
            CoroutineScope(HandlerCompat.createAsync(handler.looper).asCoroutineDispatcher())
        pageLayoutManager?.let { manager ->
            // Don't let two copies of this run concurrently
            val dimensionsToJoin = dimensionsCollector?.apply { cancel() }
            dimensionsCollector =
                mainScope.launch(start = CoroutineStart.UNDISPATCHED) {
                    manager.dimensions.collect {
                        // Prevent 2 copies from running concurrently
                        dimensionsToJoin?.join()
                        onPageDimensionsReceived(it.first, it.second)
                    }
                }
            // Don't let two copies of this run concurrently
            val visiblePagesToJoin = visiblePagesCollector?.apply { cancel() }
            visiblePagesCollector =
                mainScope.launch(start = CoroutineStart.UNDISPATCHED) {
                    manager.visiblePages.collect {
                        // Prevent 2 copies from running concurrently
                        visiblePagesToJoin?.join()
                        onVisiblePagesChanged()
                    }
                }
        }
        pageManager?.let { manager ->
            val invalidationToJoin = invalidationCollector?.apply { cancel() }
            invalidationCollector =
                mainScope.launch(start = CoroutineStart.UNDISPATCHED) {
                    // Prevent 2 copies from running concurrently
                    invalidationToJoin?.join()
                    launch { manager.invalidationSignalFlow.collect { invalidate() } }
                    launch {
                        manager.pageTextReadyFlow.collect { pageNum ->
                            accessibilityPageHelper?.onPageTextReady(pageNum)
                        }
                    }
                }
        }
    }

    private fun stopCollectingData() {
        dimensionsCollector?.cancel()
        visiblePagesCollector?.cancel()
        invalidationCollector?.cancel()
    }

    /** Start using the [PdfDocument] to present PDF content */
    // Display.width and height are deprecated in favor of WindowMetrics, but in this case we
    // actually want to use the size of the display and not the size of the window.
    @Suppress("deprecation")
    private fun onDocumentSet() {
        val localPdfDocument = pdfDocument ?: return
        /* We use the maximum pixel dimension of the display as the maximum pixel dimension for any
        single Bitmap we render, i.e. the threshold for tiled rendering. This is an arbitrary,
        but reasonable threshold to use that does not depend on volatile state like the current
        screen orientation or the current size of our application's Window. */
        val maxBitmapDimensionPx = max(context.display.width, context.display.height)

        pageManager =
            PageManager(
                localPdfDocument,
                backgroundScope,
                DEFAULT_PAGE_PREFETCH_RADIUS,
                Point(maxBitmapDimensionPx, maxBitmapDimensionPx),
                isTouchExplorationEnabled
            )
        // We'll either create our layout manager from restored state, or instantiate a new one
        if (!maybeRestoreState()) {
            pageLayoutManager =
                PageLayoutManager(localPdfDocument, backgroundScope, DEFAULT_PAGE_PREFETCH_RADIUS)
                    .apply { onViewportChanged(scrollY, height, zoom) }
            setAccessibility()
        }
        // If not, we'll start doing this when we _are_ attached to a visible window
        if (isAttachedToVisibleWindow) {
            startCollectingData()
        }
    }

    private val View.isAttachedToVisibleWindow
        get() = isAttachedToWindow && windowVisibility == VISIBLE

    /**
     * Compute what content is visible from the current position of this View. Generally invoked on
     * position or size changes.
     */
    private fun onZoomChanged() {
        pageLayoutManager?.onViewportChanged(scrollY, height, zoom)
        // Don't fetch new Bitmaps while the user is actively zooming, to avoid jank and rendering
        // churn
        if (!gestureTracker.matches(GestureTracker.Gesture.ZOOM)) {
            pageManager?.maybeUpdatePageState(visiblePages, zoom, isFling)
        }
        accessibilityPageHelper?.invalidateRoot()
    }

    /**
     * Invoked by gesture handlers to let this view know that its position has stabilized, i.e. it's
     * not actively changing due to user input
     */
    internal fun onStableZoom() {
        pageManager?.maybeUpdatePageState(visiblePages, zoom, isFling)
    }

    private fun reset() {
        // Stop any in progress fling when we open a new document
        scroller.forceFinished(true)
        scrollTo(0, 0)
        zoom = DEFAULT_INIT_ZOOM
        pageManager = null
        pageLayoutManager = null
        backgroundScope.coroutineContext.cancelChildren()
        stopCollectingData()
    }

    /** React to a change in visible pages (load new pages and clean up old ones) */
    private fun onVisiblePagesChanged() {
        pageManager?.maybeUpdatePageState(visiblePages, zoom, isFling)
    }

    /** React to a page's dimensions being made available */
    private fun onPageDimensionsReceived(pageNum: Int, size: Point) {
        pageManager?.onPageSizeReceived(
            pageNum,
            size,
            visiblePages.contains(pageNum),
            zoom,
            isFling
        )
        // Learning the dimensions of a page can change our understanding of the content that's in
        // the viewport
        pageLayoutManager?.onViewportChanged(scrollY, height, zoom)

        // We use scrollY to center content smaller than the viewport. This triggers the initial
        // centering if it's needed. It doesn't override any restored state because we're scrolling
        // to the current scroll position.
        if (pageNum == 0) {
            scrollTo(scrollX, scrollY)
        }

        val localDeferredPosition = deferredScrollPosition
        val localDeferredPage = deferredScrollPage
        if (localDeferredPosition != null && localDeferredPosition.pageNum <= pageNum) {
            gotoPoint(localDeferredPosition)
            deferredScrollPosition = null
        } else if (localDeferredPage != null && localDeferredPage <= pageNum) {
            gotoPage(pageNum)
            deferredScrollPage = null
        }
    }

    /** Set the zoom, using the given point as a pivot point to zoom in or out of */
    internal fun zoomTo(zoom: Float, pivotX: Float, pivotY: Float) {
        // TODO(b/376299551) - Restore to developer-configured initial zoom value once that API is
        // implemented
        val newZoom = if (Float.NaN.equals(zoom)) DEFAULT_INIT_ZOOM else zoom
        val deltaX = scrollDeltaNeededForZoomChange(this.zoom, newZoom, pivotX, scrollX)
        val deltaY = scrollDeltaNeededForZoomChange(this.zoom, newZoom, pivotY, scrollY)

        this.zoom = newZoom
        scrollBy(deltaX, deltaY)
    }

    private fun scrollDeltaNeededForZoomChange(
        oldZoom: Float,
        newZoom: Float,
        pivot: Float,
        scroll: Int,
    ): Int {
        // Find where the given pivot point would move to when we change the zoom, and return the
        // delta.
        val contentPivot = toContentCoord(pivot, oldZoom, scroll)
        val movedZoomViewPivot: Float = toViewCoord(contentPivot, newZoom, scroll)
        return (movedZoomViewPivot - pivot).toInt()
    }

    /**
     * Computes the part of the content visible within the outer part of this view (including this
     * view's padding) in co-ordinates of the content.
     */
    internal fun getVisibleAreaInContentCoords(): Rect {
        visibleAreaRect.set(
            toContentX(-paddingLeft.toFloat()).toInt(),
            toContentY(-paddingTop.toFloat()).toInt(),
            toContentX(viewportWidth.toFloat() + paddingRight).toInt(),
            toContentY(viewportHeight.toFloat() + paddingBottom).toInt(),
        )
        return visibleAreaRect
    }

    /**
     * Initializes and sets the accessibility delegate for the PdfView.
     *
     * This method creates an instance of [AccessibilityPageHelper] if both [.pageLayoutManager] and
     * [.pageManager] are initialized, and sets it as the accessibility delegate for the view using
     * [ViewCompat.setAccessibilityDelegate].
     */
    private fun setAccessibility() {
        if (pageLayoutManager != null && pageManager != null) {
            accessibilityPageHelper =
                AccessibilityPageHelper(this, pageLayoutManager!!, pageManager!!)
            ViewCompat.setAccessibilityDelegate(this, accessibilityPageHelper)
        }
    }

    /** The height of the viewport, minus padding */
    private val viewportHeight: Int
        get() = bottom - top - paddingBottom - paddingTop

    /** The width of the viewport, minus padding */
    private val viewportWidth: Int
        get() = right - left - paddingRight - paddingLeft

    /** Converts an X coordinate in View space to an X coordinate in content space */
    internal fun toContentX(viewX: Float): Float {
        return toContentCoord(viewX, zoom, scrollX)
    }

    /** Converts a Y coordinate in View space to a Y coordinate in content space */
    internal fun toContentY(viewY: Float): Float {
        return toContentCoord(viewY, zoom, scrollY)
    }

    internal fun toViewCoord(contentCoord: Float, zoom: Float, scroll: Int): Float {
        return (contentCoord * zoom) - scroll
    }

    /**
     * Converts a one-dimensional coordinate in View space to a one-dimensional coordinate in
     * content space
     */
    private fun toContentCoord(viewCoord: Float, zoom: Float, scroll: Int): Float {
        return (viewCoord + scroll) / zoom
    }

    private val contentWidth: Int
        get() = pageLayoutManager?.paginationModel?.maxWidth ?: 0

    private val contentHeight: Int
        get() = pageLayoutManager?.paginationModel?.totalEstimatedHeight ?: 0

    /** Adjusts the position of [PdfView] in response to gestures detected by [GestureTracker] */
    private inner class ZoomScrollGestureHandler : GestureTracker.GestureHandler() {

        /**
         * The multiplier to convert from a scale gesture's delta span, in pixels, to scale factor.
         *
         * [ScaleGestureDetector] returns scale factors proportional to the ratio of `currentSpan /
         * prevSpan`. This is problematic because it results in scale factors that are very large
         * for small pixel spans, which is particularly problematic for quickScale gestures, where
         * the span pixel values can be small, but the ratio can yield very large scale factors.
         *
         * Instead, we use this to ensure that pinching or quick scale dragging a certain number of
         * pixels always corresponds to a certain change in zoom. The equation that we've found to
         * work well is a delta span of the larger screen dimension should result in a zoom change
         * of 2x.
         */
        private val linearScaleSpanMultiplier: Float =
            2f / maxOf(resources.displayMetrics.heightPixels, resources.displayMetrics.widthPixels)
        /** The maximum scroll distance used to determine if the direction is vertical. */
        private val maxScrollWindow =
            (resources.displayMetrics.density * MAX_SCROLL_WINDOW_DP).toInt()

        /** The smallest scroll distance that can switch mode to "free scrolling". */
        private val minScrollToSwitch =
            (resources.displayMetrics.density * MIN_SCROLL_TO_SWITCH_DP).toInt()

        /** Remember recent scroll events so we can examine the general direction. */
        private val scrollQueue: Queue<PointF> = LinkedList()

        /** Are we correcting vertical scroll for the current gesture? */
        private var straightenCurrentVerticalScroll = true

        private var totalX = 0f
        private var totalY = 0f

        private val totalScrollLength
            // No need for accuracy of correct hypotenuse calculation
            get() = abs(totalX) + abs(totalY)

        override fun onGestureStart() {
            // Stop any in-progress fling when a new gesture begins
            scroller.forceFinished(true)
        }

        override fun onScroll(
            e1: MotionEvent?,
            e2: MotionEvent,
            distanceX: Float,
            distanceY: Float,
        ): Boolean {
            var dx = Math.round(distanceX)
            val dy = Math.round(distanceY)

            if (straightenCurrentVerticalScroll) {
                // Remember a window of recent scroll events.
                scrollQueue.offer(PointF(distanceX, distanceY))
                totalX += distanceX
                totalY += distanceY

                // Only consider scroll direction for a certain window of scroll events.
                while (totalScrollLength > maxScrollWindow && scrollQueue.size > 1) {
                    // Remove the oldest scroll event - it is too far away to determine scroll
                    // direction.
                    val oldest = scrollQueue.poll()
                    oldest?.let {
                        totalY -= oldest.y
                        totalX -= oldest.x
                    }
                }

                if (
                    totalScrollLength > minScrollToSwitch &&
                        abs((totalY / totalX).toDouble()) < SCROLL_CORRECTION_RATIO
                ) {
                    straightenCurrentVerticalScroll = false
                } else {
                    // Ignore the horizontal component of the scroll.
                    dx = 0
                }
            }

            scrollBy(dx, dy)
            return true
        }

        override fun onFling(
            e1: MotionEvent?,
            e2: MotionEvent,
            velocityX: Float,
            velocityY: Float
        ): Boolean {
            // Assume a fling in a roughly vertical direction was meant to be exactly vertical.
            val myVelocityX =
                if (velocityY / velocityX > SCROLL_CORRECTION_RATIO) {
                    0
                } else {
                    velocityX
                }

            isFling = true
            scroller.fling(
                scrollX,
                scrollY,
                -myVelocityX.toInt(),
                -velocityY.toInt(),
                /* minX= */ minVerticalScrollPosition,
                computeHorizontalScrollRange(),
                minVerticalScrollPosition,
                computeVerticalScrollRange(),
            )

            postInvalidateOnAnimation() // Triggers computeScroll()
            return true
        }

        override fun onDoubleTap(e: MotionEvent): Boolean {

            val currentZoom = zoom

            val newZoom =
                ZoomUtils.calculateZoomForDoubleTap(
                    viewportWidth,
                    viewportHeight,
                    contentWidth,
                    currentZoom,
                    minZoom,
                    maxZoom,
                )
            if (newZoom == 0f) {
                // viewport not initialized yet maybe?
                return false
            }

            ValueAnimator.ofFloat(0f, 1f).apply {
                duration = 200 // Slightly shorter duration for snappier feel
                addUpdateListener { animator ->
                    val animatedValue = animator.animatedValue as Float
                    val value = currentZoom + (newZoom - currentZoom) * animatedValue
                    zoomTo(value, e.x, e.y)
                }
                start()
            }

            return true
        }

        override fun onScale(detector: ScaleGestureDetector): Boolean {
            val rawScaleFactor = detector.scaleFactor
            val deltaSpan = abs(detector.currentSpan - detector.previousSpan)
            val scaleDelta = deltaSpan * linearScaleSpanMultiplier
            val linearScaleFactor = if (rawScaleFactor >= 1f) 1f + scaleDelta else 1f - scaleDelta
            val newZoom = (zoom * linearScaleFactor).coerceIn(minZoom, maxZoom)

            zoomTo(newZoom, detector.focusX, detector.focusY)
            return true
        }

        override fun onGestureEnd(gesture: GestureTracker.Gesture?) {
            if (gesture == GestureTracker.Gesture.ZOOM) onStableZoom()
            totalX = 0f
            totalY = 0f
            straightenCurrentVerticalScroll = true
            scrollQueue.clear()
        }

        override fun onSingleTapConfirmed(e: MotionEvent): Boolean {
            val contentX = toContentX(e.x)
            val contentY = toContentY(e.y)

            val pageLayoutManager = pageLayoutManager ?: return super.onSingleTapConfirmed(e)
            val pageNum =
                pageLayoutManager.getPageNumberAt(
                    PointF(contentX, contentY),
                    getVisibleAreaInContentCoords()
                )
            if (pageNum == INVALID_ID) return super.onSingleTapConfirmed(e)

            val pdfCoordinates =
                pageLayoutManager.getPageCoordinatesRelativeToTappedPage(
                    pageNum,
                    getVisibleAreaInContentCoords(),
                    PointF(contentX, contentY)
                )

            pageManager?.getLinkAtTapPoint(PdfPoint(pageNum, pdfCoordinates))?.let { links ->
                if (handleGotoLinks(links, pdfCoordinates)) return true
                if (handleExternalLinks(links, pdfCoordinates)) return true
            }
            return super.onSingleTapConfirmed(e)
        }

        private fun handleGotoLinks(
            links: PdfDocument.PdfPageLinks,
            pdfCoordinates: PointF
        ): Boolean {
            links.gotoLinks.forEach { gotoLink ->
                if (gotoLink.bounds.any { it.contains(pdfCoordinates.x, pdfCoordinates.y) }) {
                    val destination =
                        PdfPoint(
                            pageNum = gotoLink.destination.pageNumber,
                            pagePoint =
                                PointF(
                                    gotoLink.destination.xCoordinate,
                                    gotoLink.destination.yCoordinate
                                )
                        )
                    scrollToPosition(destination)
                    return true
                }
            }
            return false
        }

        private fun handleExternalLinks(
            links: PdfDocument.PdfPageLinks,
            pdfCoordinates: PointF
        ): Boolean {
            links.externalLinks.forEach { externalLink ->
                if (externalLink.bounds.any { it.contains(pdfCoordinates.x, pdfCoordinates.y) }) {
                    var uri = externalLink.uri
                    linkClickListener?.onLinkClicked(uri)
                        ?: run {
                            val intent = Intent(Intent.ACTION_VIEW, uri)
                            context.startActivity(intent)
                        }
                    return true
                }
            }
            return false
        }
    }

    public companion object {
        public const val DEFAULT_INIT_ZOOM: Float = 1.0f
        public const val DEFAULT_MAX_ZOOM: Float = 25.0f
        public const val DEFAULT_MIN_ZOOM: Float = 0.5f

        /** The ratio of vertical to horizontal scroll that is assumed to be vertical only */
        private const val SCROLL_CORRECTION_RATIO = 1.5f
        /** The maximum scroll distance used to determine if the direction is vertical */
        private const val MAX_SCROLL_WINDOW_DP = 70
        /** The smallest scroll distance that can switch mode to "free scrolling" */
        private const val MIN_SCROLL_TO_SWITCH_DP = 30

        private const val DEFAULT_PAGE_PREFETCH_RADIUS: Int = 2
        private const val INVALID_ID = -1

        private fun checkMainThread() {
            check(Looper.myLooper() == Looper.getMainLooper()) {
                "Property must be set on the main thread"
            }
        }
    }
}

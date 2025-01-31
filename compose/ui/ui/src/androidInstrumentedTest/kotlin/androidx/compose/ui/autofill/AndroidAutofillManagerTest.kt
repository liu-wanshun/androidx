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

package androidx.compose.ui.autofill

import android.os.Build
import androidx.annotation.RequiresApi
import androidx.compose.foundation.clickable
import androidx.compose.foundation.layout.Box
import androidx.compose.foundation.layout.size
import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.setValue
import androidx.compose.ui.ComposeUiFlags
import androidx.compose.ui.ExperimentalComposeUiApi
import androidx.compose.ui.Modifier
import androidx.compose.ui.draw.alpha
import androidx.compose.ui.platform.LocalAutofillManager
import androidx.compose.ui.platform.testTag
import androidx.compose.ui.semantics.contentDataType
import androidx.compose.ui.semantics.contentDescription
import androidx.compose.ui.semantics.contentType
import androidx.compose.ui.semantics.editableText
import androidx.compose.ui.semantics.focused
import androidx.compose.ui.semantics.onAutofillText
import androidx.compose.ui.semantics.semantics
import androidx.compose.ui.test.TestActivity
import androidx.compose.ui.test.junit4.createAndroidComposeRule
import androidx.compose.ui.test.onNodeWithTag
import androidx.compose.ui.test.performClick
import androidx.compose.ui.text.AnnotatedString
import androidx.compose.ui.unit.dp
import androidx.test.ext.junit.runners.AndroidJUnit4
import androidx.test.filters.SdkSuppress
import androidx.test.filters.SmallTest
import androidx.test.platform.app.InstrumentationRegistry
import kotlin.test.Ignore
import org.junit.After
import org.junit.Before
import org.junit.Rule
import org.junit.Test
import org.junit.runner.RunWith
import org.mockito.kotlin.any
import org.mockito.kotlin.mock
import org.mockito.kotlin.never
import org.mockito.kotlin.times
import org.mockito.kotlin.verify
import org.mockito.kotlin.verifyNoMoreInteractions

@SdkSuppress(minSdkVersion = 26)
@RequiresApi(Build.VERSION_CODES.O)
@RunWith(AndroidJUnit4::class)
class AndroidAutofillManagerTest {
    @get:Rule val rule = createAndroidComposeRule<TestActivity>()

    private val height = 200.dp
    private val width = 200.dp

    @OptIn(ExperimentalComposeUiApi::class)
    private val previousFlagValue = ComposeUiFlags.isSemanticAutofillEnabled

    @Before
    fun enableAutofill() {
        @OptIn(ExperimentalComposeUiApi::class)
        ComposeUiFlags.isSemanticAutofillEnabled = true
    }

    @After
    fun teardown() {
        val instrumentation = InstrumentationRegistry.getInstrumentation()
        val activity = rule.activity
        while (!activity.isDestroyed) {
            instrumentation.runOnMainSync {
                if (!activity.isDestroyed) {
                    activity.finish()
                }
            }
        }
        @OptIn(ExperimentalComposeUiApi::class)
        ComposeUiFlags.isSemanticAutofillEnabled = previousFlagValue
    }

    @Test
    @SmallTest
    @SdkSuppress(minSdkVersion = 26)
    fun autofillManager_empty() {
        val am: PlatformAutofillManager = mock()
        rule.setContent {
            (LocalAutofillManager.current as AndroidAutofillManager).platformAutofillManager = am
            Box(Modifier.semantics { contentType = ContentType.Username }.size(height, width))
        }

        rule.runOnIdle { verifyNoMoreInteractions(am) }
    }

    @Test
    @SmallTest
    fun autofillManager_doNotCallCommit_nodesAppeared() {
        val am: PlatformAutofillManager = mock()
        var isVisible by mutableStateOf(false)

        rule.setContent {
            (LocalAutofillManager.current as AndroidAutofillManager).platformAutofillManager = am
            if (isVisible) {
                Box(Modifier.semantics { contentType = ContentType.Username }.size(height, width))
            }
        }

        rule.runOnIdle { isVisible = true }

        // `commit` should not be called when an autofillable component appears onscreen.
        rule.runOnIdle { verify(am, times(0)).commit() }
    }

    @Test
    @SmallTest
    fun autofillManager_doNotCallCommit_autofillTagsAdded() {
        val am: PlatformAutofillManager = mock()
        var isRelatedToAutofill by mutableStateOf(false)

        rule.setContent {
            (LocalAutofillManager.current as AndroidAutofillManager).platformAutofillManager = am
            Box(
                modifier =
                    if (isRelatedToAutofill)
                        Modifier.semantics {
                                contentType = ContentType.Username
                                contentDataType = ContentDataType.Text
                            }
                            .size(height, width)
                    else Modifier.size(height, width)
            )
        }

        rule.runOnIdle { isRelatedToAutofill = true }

        // `commit` should not be called a component becomes relevant to autofill.
        rule.runOnIdle { verify(am, times(0)).commit() }
    }

    @Test
    @SmallTest
    fun autofillManager_callCommit_nodesDisappeared() {
        val am: PlatformAutofillManager = mock()
        var revealFirstUsername by mutableStateOf(true)

        rule.setContent {
            (LocalAutofillManager.current as AndroidAutofillManager).platformAutofillManager = am
            if (revealFirstUsername) {
                Box(Modifier.semantics { contentType = ContentType.Username }.size(height, width))
            }
        }

        rule.runOnIdle { revealFirstUsername = false }

        // `commit` should be called when an autofillable component leaves the screen.
        rule.runOnIdle { verify(am, times(1)).commit() }
    }

    @Test
    @SmallTest
    fun autofillManager_callCommit_nodesDisappearedAndAppeared() {
        val am: PlatformAutofillManager = mock()
        var revealFirstUsername by mutableStateOf(true)
        var revealSecondUsername by mutableStateOf(false)

        rule.setContent {
            (LocalAutofillManager.current as AndroidAutofillManager).platformAutofillManager = am
            if (revealFirstUsername) {
                Box(Modifier.semantics { contentType = ContentType.Username }.size(height, width))
            }
            if (revealSecondUsername) {
                Box(Modifier.semantics { contentType = ContentType.Username }.size(height, width))
            }
        }

        rule.runOnIdle { revealFirstUsername = false }
        rule.runOnIdle { revealSecondUsername = true }

        // `commit` should be called when an autofillable component leaves onscreen, even when
        // another, different autofillable component is added.
        rule.runOnIdle { verify(am, times(1)).commit() }
    }

    @Test
    @SmallTest
    fun autofillManager_doNotCallCommit_nonAutofillRelatedNodesAddedAndDisappear() {
        val am: PlatformAutofillManager = mock()
        var isVisible by mutableStateOf(true)
        var semanticsExist by mutableStateOf(false)

        rule.setContent {
            (LocalAutofillManager.current as AndroidAutofillManager).platformAutofillManager = am
            if (isVisible) {
                Box(
                    modifier =
                        Modifier.then(
                            if (semanticsExist)
                                Modifier.semantics { contentDescription = "contentDescription" }
                            else Modifier.size(height, width)
                        )
                )
            }
        }

        rule.runOnIdle { semanticsExist = true }
        rule.runOnIdle { isVisible = false }

        // Adding in semantics not related to autofill should not trigger commit
        rule.runOnIdle { verify(am, never()).commit() }
    }

    @Test
    @SmallTest
    fun autofillManager_callCommit_nodesBecomeAutofillRelatedAndDisappear() {
        val am: PlatformAutofillManager = mock()
        var isVisible by mutableStateOf(true)
        var isRelatedToAutofill by mutableStateOf(false)

        rule.setContent {
            (LocalAutofillManager.current as AndroidAutofillManager).platformAutofillManager = am
            if (isVisible) {
                Box(
                    modifier =
                        if (isRelatedToAutofill)
                            Modifier.semantics {
                                    contentType = ContentType.Username
                                    contentDataType = ContentDataType.Text
                                }
                                .size(height, width)
                        else Modifier.size(height, width)
                )
            }
        }

        rule.runOnIdle { isRelatedToAutofill = true }
        rule.runOnIdle { isVisible = false }

        // `commit` should be called when component becomes autofillable, then leaves the screen.
        rule.runOnIdle { verify(am, times(1)).commit() }
    }

    @Test
    @SmallTest
    @SdkSuppress(minSdkVersion = 26)
    fun autofillManager_notifyValueChanged() {
        val am: PlatformAutofillManager = mock()
        var changeText by mutableStateOf(false)

        rule.setContent {
            (LocalAutofillManager.current as AndroidAutofillManager).platformAutofillManager = am
            Box(
                Modifier.semantics {
                        contentType = ContentType.Username
                        contentDataType = ContentDataType.Text
                        editableText = AnnotatedString(if (changeText) "1234" else "****")
                    }
                    .size(height, width)
            )
        }

        rule.runOnIdle { changeText = true }

        rule.runOnIdle { verify(am).notifyValueChanged(any(), any(), any()) }
    }

    @SmallTest
    @SdkSuppress(minSdkVersion = 26)
    fun autofillManager_notifyValueChanged_fromEmpty() {
        val am: PlatformAutofillManager = mock()
        var changeText by mutableStateOf(false)

        rule.setContent {
            (LocalAutofillManager.current as AndroidAutofillManager).platformAutofillManager = am
            Box(
                Modifier.semantics {
                        contentType = ContentType.Username
                        contentDataType = ContentDataType.Text
                        editableText = AnnotatedString(if (changeText) "1234" else "")
                    }
                    .size(height, width)
            )
        }

        rule.runOnIdle { changeText = true }

        rule.runOnIdle { verify(am).notifyValueChanged(any(), any(), any()) }
    }

    @SmallTest
    @SdkSuppress(minSdkVersion = 26)
    fun autofillManager_notifyValueChanged_toEmpty() {
        val am: PlatformAutofillManager = mock()
        var changeText by mutableStateOf(false)

        rule.setContent {
            (LocalAutofillManager.current as AndroidAutofillManager).platformAutofillManager = am
            Box(
                Modifier.semantics {
                        contentType = ContentType.Username
                        contentDataType = ContentDataType.Text
                        editableText = AnnotatedString(if (changeText) "" else "1234")
                    }
                    .size(height, width)
            )
        }

        rule.runOnIdle { changeText = true }

        rule.runOnIdle { verify(am).notifyValueChanged(any(), any(), any()) }
    }

    @Test
    @SmallTest
    @SdkSuppress(minSdkVersion = 26)
    fun autofillManager_notifyValueChanged_editableTextAdded() {
        val am: PlatformAutofillManager = mock()
        var hasEditableText by mutableStateOf(false)

        rule.setContent {
            (LocalAutofillManager.current as AndroidAutofillManager).platformAutofillManager = am
            Box(
                Modifier.semantics {
                        contentType = ContentType.Username
                        contentDataType = ContentDataType.Text
                        if (hasEditableText) editableText = AnnotatedString("1234")
                    }
                    .size(height, width)
            )
        }

        rule.runOnIdle { hasEditableText = true }

        // TODO: This does not send notifyValueChanged, but will we could add a test to verify that
        //  it sends notifyVisibilityChanged after aosp/3391719 lands.
        rule.runOnIdle { verify(am, never()).notifyValueChanged(any(), any(), any()) }
    }

    @Test
    @SmallTest
    @SdkSuppress(minSdkVersion = 26)
    fun autofillManager_notifyValueChanged_editableTextRemoved() {
        val am: PlatformAutofillManager = mock()
        var hasEditableText by mutableStateOf(true)

        rule.setContent {
            (LocalAutofillManager.current as AndroidAutofillManager).platformAutofillManager = am
            Box(
                Modifier.semantics {
                        contentType = ContentType.Username
                        contentDataType = ContentDataType.Text
                        if (hasEditableText) editableText = AnnotatedString("1234")
                    }
                    .size(height, width)
            )
        }

        rule.runOnIdle { hasEditableText = false }

        // TODO: This does not send notifyValueChanged, but will we could add a test to verify that
        //  it sends notifyVisibilityChanged after aosp/3391719 lands.
        rule.runOnIdle { verify(am, never()).notifyValueChanged(any(), any(), any()) }
    }

    @Test
    @SmallTest
    @SdkSuppress(minSdkVersion = 26)
    fun autofillManager_notifyValueChanged_addedEmptyEditableText() {
        val am: PlatformAutofillManager = mock()
        var hasEditableText by mutableStateOf(false)

        rule.setContent {
            (LocalAutofillManager.current as AndroidAutofillManager).platformAutofillManager = am
            Box(
                Modifier.semantics {
                        contentType = ContentType.Username
                        contentDataType = ContentDataType.Text
                        if (hasEditableText) editableText = AnnotatedString("")
                    }
                    .size(height, width)
            )
        }

        rule.runOnIdle { hasEditableText = true }

        // TODO: This does not send notifyValueChanged, but will we could add a test to verify that
        //  it sends notifyVisibilityChanged after aosp/3391719 lands.
        rule.runOnIdle { verify(am, never()).notifyValueChanged(any(), any(), any()) }
    }

    @Test
    @SmallTest
    @SdkSuppress(minSdkVersion = 26)
    fun autofillManager_notifyValueChanged_removedEmptyEditableText() {
        val am: PlatformAutofillManager = mock()
        var hasEditableText by mutableStateOf(true)

        rule.setContent {
            (LocalAutofillManager.current as AndroidAutofillManager).platformAutofillManager = am
            Box(
                Modifier.semantics {
                        contentType = ContentType.Username
                        contentDataType = ContentDataType.Text
                        if (hasEditableText) editableText = AnnotatedString("")
                    }
                    .size(height, width)
            )
        }

        rule.runOnIdle { hasEditableText = false }

        // TODO: This does not send notifyValueChanged, but will we could add a test to verify that
        //  it sends notifyVisibilityChanged after aosp/3391719 lands.
        rule.runOnIdle { verify(am, never()).notifyValueChanged(any(), any(), any()) }
    }

    @Test
    @SmallTest
    @SdkSuppress(minSdkVersion = 26)
    fun autofillManager_notifyViewEntered_previousFocusFalse() {
        val am: PlatformAutofillManager = mock()
        var hasFocus by mutableStateOf(false)

        rule.setContent {
            (LocalAutofillManager.current as AndroidAutofillManager).platformAutofillManager = am
            Box(
                Modifier.semantics {
                        contentType = ContentType.Username
                        contentDataType = ContentDataType.Text
                        focused = hasFocus
                        onAutofillText { true }
                    }
                    .size(height, width)
            )
        }

        rule.runOnIdle { hasFocus = true }

        rule.runOnIdle { verify(am).notifyViewEntered(any(), any(), any()) }
    }

    @Test
    @SmallTest
    @SdkSuppress(minSdkVersion = 26)
    fun autofillManager_notAutofillable_notifyViewEntered_previousFocusFalse() {
        val am: PlatformAutofillManager = mock()
        var hasFocus by mutableStateOf(false)

        rule.setContent {
            (LocalAutofillManager.current as AndroidAutofillManager).platformAutofillManager = am
            Box(
                Modifier.semantics {
                        contentType = ContentType.Username
                        contentDataType = ContentDataType.Text
                        focused = hasFocus
                    }
                    .size(height, width)
            )
        }

        rule.runOnIdle { hasFocus = true }

        rule.runOnIdle { verifyNoMoreInteractions(am) }
    }

    @Test
    @SmallTest
    @SdkSuppress(minSdkVersion = 26)
    fun autofillManager_notifyViewEntered_previousFocusNull() {
        val am: PlatformAutofillManager = mock()
        var hasFocus by mutableStateOf(false)

        rule.setContent {
            (LocalAutofillManager.current as AndroidAutofillManager).platformAutofillManager = am
            Box(
                modifier =
                    if (hasFocus)
                        Modifier.semantics {
                                contentType = ContentType.Username
                                contentDataType = ContentDataType.Text
                                focused = hasFocus
                                onAutofillText { true }
                            }
                            .size(height, width)
                    else plainVisibleModifier("usernameTag")
            )
        }

        rule.runOnIdle { hasFocus = true }

        rule.runOnIdle { verify(am).notifyViewEntered(any(), any(), any()) }
    }

    @Test
    @SmallTest
    @SdkSuppress(minSdkVersion = 26)
    fun autofillManager_notifyViewEntered_itemNotAutofillable() {
        val am: PlatformAutofillManager = mock()
        var hasFocus by mutableStateOf(false)

        rule.setContent {
            (LocalAutofillManager.current as AndroidAutofillManager).platformAutofillManager = am
            Box(
                modifier =
                    if (hasFocus)
                        Modifier.semantics {
                                contentType = ContentType.Username
                                contentDataType = ContentDataType.Text
                                focused = hasFocus
                            }
                            .size(height, width)
                    else plainVisibleModifier("usernameTag")
            )
        }

        rule.runOnIdle { hasFocus = true }

        rule.runOnIdle { verifyNoMoreInteractions(am) }
    }

    @Test
    @SmallTest
    @SdkSuppress(minSdkVersion = 26)
    fun autofillManager_notifyViewExited_previousFocusTrue() {
        val am: PlatformAutofillManager = mock()
        var hasFocus by mutableStateOf(true)

        rule.setContent {
            (LocalAutofillManager.current as AndroidAutofillManager).platformAutofillManager = am
            Box(
                Modifier.semantics {
                        contentType = ContentType.Username
                        contentDataType = ContentDataType.Text
                        focused = hasFocus
                        onAutofillText { true }
                    }
                    .size(height, width)
            )
        }

        rule.runOnIdle { hasFocus = false }

        rule.runOnIdle { verify(am).notifyViewExited(any(), any()) }
    }

    @Test
    @SmallTest
    @SdkSuppress(minSdkVersion = 26)
    fun autofillManager_notifyViewExited_previouslyFocusedItemNotAutofillable() {
        val am: PlatformAutofillManager = mock()
        var hasFocus by mutableStateOf(true)

        rule.setContent {
            (LocalAutofillManager.current as AndroidAutofillManager).platformAutofillManager = am
            Box(
                Modifier.semantics {
                        contentType = ContentType.Username
                        contentDataType = ContentDataType.Text
                        focused = hasFocus
                    }
                    .size(height, width)
            )
        }

        rule.runOnIdle { hasFocus = false }

        rule.runOnIdle { verifyNoMoreInteractions(am) }
    }

    @Ignore // TODO(b/383198004): Add support for notifyVisibilityChanged.
    @Test
    @SmallTest
    @SdkSuppress(minSdkVersion = 27)
    fun autofillManager_notifyVisibilityChanged_disappeared() {
        val am: PlatformAutofillManager = mock()
        val usernameTag = "usernameTag"
        var isVisible by mutableStateOf(true)

        rule.setContent {
            (LocalAutofillManager.current as AndroidAutofillManager).platformAutofillManager = am
            Box(
                modifier =
                    if (isVisible) plainVisibleModifier(usernameTag)
                    else invisibleModifier(usernameTag)
            )
        }

        rule.runOnIdle { isVisible = false }

        rule.runOnIdle { verify(am).notifyViewVisibilityChanged(any(), any(), any()) }
    }

    @Ignore // TODO(b/383198004): Add support for notifyVisibilityChanged.
    @Test
    @SmallTest
    @SdkSuppress(minSdkVersion = 27)
    fun autofillManager_notifyVisibilityChanged_appeared() {
        val am: PlatformAutofillManager = mock()
        val usernameTag = "username_tag"
        var isVisible by mutableStateOf(false)

        rule.setContent {
            (LocalAutofillManager.current as AndroidAutofillManager).platformAutofillManager = am
            Box(
                modifier =
                    if (isVisible) plainVisibleModifier(usernameTag)
                    else invisibleModifier(usernameTag)
            )
        }

        rule.runOnIdle { isVisible = true }

        rule.runOnIdle { verify(am).notifyViewVisibilityChanged(any(), any(), any()) }
    }

    @Test
    @SmallTest
    @SdkSuppress(minSdkVersion = 26)
    fun autofillManager_notifyCommit() {
        val am: PlatformAutofillManager = mock()
        val forwardTag = "forward_button_tag"
        var autofillManager: AutofillManager?

        rule.setContent {
            (LocalAutofillManager.current as AndroidAutofillManager).platformAutofillManager = am
            autofillManager = LocalAutofillManager.current
            Box(
                modifier =
                    Modifier.clickable { autofillManager?.commit() }
                        .size(height, width)
                        .testTag(forwardTag)
            )
        }

        rule.onNodeWithTag(forwardTag).performClick()

        rule.runOnIdle { verify(am).commit() }
    }

    @Test
    @SmallTest
    @SdkSuppress(minSdkVersion = 26)
    fun autofillManager_notifyCancel() {
        val am: PlatformAutofillManager = mock()
        val backTag = "back_button_tag"
        var autofillManager: AutofillManager?

        rule.setContent {
            autofillManager = LocalAutofillManager.current
            (autofillManager as AndroidAutofillManager).platformAutofillManager = am
            Box(
                modifier =
                    Modifier.clickable { autofillManager?.cancel() }
                        .size(height, width)
                        .testTag(backTag)
            )
        }
        rule.onNodeWithTag(backTag).performClick()

        rule.runOnIdle { verify(am).cancel() }
    }

    @Test
    @SmallTest
    @SdkSuppress(minSdkVersion = 26)
    fun autofillManager_requestAutofillAfterFocus() {
        val am: PlatformAutofillManager = mock()
        val contextMenuTag = "menu_tag"
        var autofillManager: AutofillManager?
        var hasFocus by mutableStateOf(false)

        rule.setContent {
            autofillManager = LocalAutofillManager.current
            (autofillManager as AndroidAutofillManager).platformAutofillManager = am
            Box(
                modifier =
                    if (hasFocus)
                        Modifier.semantics {
                                contentType = ContentType.Username
                                contentDataType = ContentDataType.Text
                                focused = hasFocus
                                onAutofillText { true }
                            }
                            .clickable { autofillManager?.requestAutofillForActiveElement() }
                            .size(height, width)
                            .testTag(contextMenuTag)
                    else plainVisibleModifier(contextMenuTag)
            )
        }

        // `requestAutofill` is always called after an element is focused
        rule.runOnIdle { hasFocus = true }
        rule.runOnIdle { verify(am).notifyViewEntered(any(), any(), any()) }

        // then `requestAutofill` is called on that same previously focused element
        rule.onNodeWithTag(contextMenuTag).performClick()
        rule.runOnIdle { verify(am).requestAutofill(any(), any(), any()) }
    }

    @Test
    @SmallTest
    @SdkSuppress(minSdkVersion = 26)
    fun autofillManager_notAutofillable_doesNotrequestAutofillAfterFocus() {
        val am: PlatformAutofillManager = mock()
        val contextMenuTag = "menu_tag"
        var autofillManager: AutofillManager?
        var hasFocus by mutableStateOf(false)

        rule.setContent {
            autofillManager = LocalAutofillManager.current
            (autofillManager as AndroidAutofillManager).platformAutofillManager = am
            Box(
                modifier =
                    if (hasFocus)
                        Modifier.semantics {
                                contentType = ContentType.Username
                                contentDataType = ContentDataType.Text
                                focused = hasFocus
                            }
                            .clickable { autofillManager?.requestAutofillForActiveElement() }
                            .size(height, width)
                            .testTag(contextMenuTag)
                    else plainVisibleModifier(contextMenuTag)
            )
        }

        // `requestAutofill` is always called after an element is focused
        rule.runOnIdle { hasFocus = true }
        rule.runOnIdle { verifyNoMoreInteractions(am) }
    }

    // ============================================================================================
    // Helper functions
    // ============================================================================================

    private fun plainVisibleModifier(testTag: String): Modifier {
        return Modifier.semantics {
                contentType = ContentType.Username
                contentDataType = ContentDataType.Text
            }
            .size(width, height)
            .testTag(testTag)
    }

    private fun invisibleModifier(testTag: String): Modifier {
        return Modifier.alpha(0f) // this will make the component invisible
            .semantics {
                contentType = ContentType.Username
                contentDataType = ContentDataType.Text
            }
            .size(width, height)
            .testTag(testTag)
    }
}

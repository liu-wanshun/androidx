/*
 * Copyright (C) 2017 The Android Open Source Project
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *       http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package androidx.core.graphics

import android.graphics.Bitmap
import android.graphics.ColorSpace
import android.graphics.Point
import android.graphics.PointF
import androidx.test.filters.SdkSuppress
import androidx.test.filters.SmallTest
import org.junit.Assert.assertEquals
import org.junit.Assert.assertFalse
import org.junit.Assert.assertTrue
import org.junit.Test

@SmallTest
class BitmapTest {
    @Test
    fun create() {
        val bitmap = createBitmap(7, 9)
        assertEquals(7, bitmap.width)
        assertEquals(9, bitmap.height)
        assertEquals(Bitmap.Config.ARGB_8888, bitmap.config)
    }

    @Test
    fun createWithConfig() {
        val bitmap = createBitmap(7, 9, config = Bitmap.Config.RGB_565)
        assertEquals(Bitmap.Config.RGB_565, bitmap.config)
    }

    @SdkSuppress(minSdkVersion = 26)
    @Test
    fun createWithColorSpace() {
        val colorSpace = ColorSpace.get(ColorSpace.Named.ADOBE_RGB)
        val bitmap = createBitmap(7, 9, colorSpace = colorSpace)
        assertEquals(colorSpace, bitmap.colorSpace)
    }

    @Test
    fun scale() {
        val b = createBitmap(7, 9).scale(3, 5)
        assertEquals(3, b.width)
        assertEquals(5, b.height)
    }

    @Test
    fun applyCanvas() {
        val p = createBitmap(2, 2).applyCanvas { drawColor(0x40302010) }.getPixel(1, 1)

        assertEquals(0x40302010, p)
    }

    @Test
    fun getPixel() {
        val b = createBitmap(2, 2).applyCanvas { drawColor(0x40302010) }
        assertEquals(0x40302010, b[1, 1])
    }

    @Test
    fun setPixel() {
        val b = createBitmap(2, 2)
        b[1, 1] = 0x40302010
        assertEquals(0x40302010, b[1, 1])
    }

    @Test
    fun pointInBitmap() {
        val b = createBitmap(5, 5)
        assertTrue(Point(0, 0) in b)
        assertTrue(Point(2, 2) in b)
        assertFalse(Point(-1, -1) in b)
        assertFalse(Point(5, 5) in b)

        assertTrue(PointF(0.0f, 0.0f) in b)
        assertTrue(PointF(2.0f, 2.0f) in b)
        assertFalse(PointF(-1.0f, -1.0f) in b)
        assertFalse(PointF(5.0f, 5.0f) in b)
    }
}

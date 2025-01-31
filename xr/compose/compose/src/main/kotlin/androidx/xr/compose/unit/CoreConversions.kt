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

package androidx.xr.compose.unit

import androidx.compose.ui.unit.Density
import androidx.xr.scenecore.Dimensions

/**
 * Converts this [IntVolumeSize] to a [Dimensions] object in meters, taking into account [density].
 *
 * @return a [Dimensions] object representing the volume size in meters.
 */
internal fun IntVolumeSize.toDimensionsInMeters(density: Density): Dimensions =
    Dimensions(
        Meter.fromPixel(width.toFloat(), density).value,
        Meter.fromPixel(height.toFloat(), density).value,
        Meter.fromPixel(depth.toFloat(), density).value,
    )

/**
 * Creates an [IntVolumeSize] from a [Dimensions] object in meters.
 *
 * The dimensions in meters are rounded to the nearest pixel value.
 *
 * @param density The pixel density of the display.
 * @return an [IntVolumeSize] object representing the same volume size in pixels.
 */
internal fun Dimensions.toIntVolumeSize(density: Density): IntVolumeSize =
    IntVolumeSize(
        Meter(this.width).roundToPx(density),
        Meter(this.height).roundToPx(density),
        Meter(this.depth).roundToPx(density),
    )

/**
 * Converts this [DpVolumeSize] to a [Dimensions] object in meters.
 *
 * @return a [Dimensions] object representing the volume size in meters
 */
internal fun DpVolumeSize.toDimensionsInMeters(): Dimensions =
    Dimensions(width.toMeter().value, height.toMeter().value, depth.toMeter().value)

/**
 * Creates a [DpVolumeSize] from a [Dimensions] object in meters.
 *
 * @return a [DpVolumeSize] object representing the same volume size in Dp.
 */
internal fun Dimensions.toDpVolumeSize(): DpVolumeSize =
    DpVolumeSize(Meter(width).toDp(), Meter(height).toDp(), Meter(depth).toDp())

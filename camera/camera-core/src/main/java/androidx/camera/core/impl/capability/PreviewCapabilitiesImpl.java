/*
 * Copyright 2023 The Android Open Source Project
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

package androidx.camera.core.impl.capability;

import androidx.annotation.RestrictTo;
import androidx.camera.core.CameraInfo;
import androidx.camera.core.Preview;
import androidx.camera.core.PreviewCapabilities;
import androidx.camera.core.impl.CameraInfoInternal;

import org.jspecify.annotations.NonNull;

/**
 * Implementation of {@link PreviewCapabilities}. It delegates to {@link CameraInfoInternal} to
 * retrieve {@link Preview} related capabilities.
 */
@RestrictTo(RestrictTo.Scope.LIBRARY_GROUP)
public class PreviewCapabilitiesImpl implements PreviewCapabilities {

    private boolean mIsStabilizationSupported;

    PreviewCapabilitiesImpl(@NonNull CameraInfoInternal cameraInfoInternal) {
        mIsStabilizationSupported = cameraInfoInternal.isPreviewStabilizationSupported();
    }

    /**
     * Gets {@link PreviewCapabilities} by the {@link CameraInfo}.
     */
    public static @NonNull PreviewCapabilities from(@NonNull CameraInfo cameraInfo) {
        return new PreviewCapabilitiesImpl((CameraInfoInternal) cameraInfo);
    }

    @Override
    public boolean isStabilizationSupported() {
        return mIsStabilizationSupported;
    }
}

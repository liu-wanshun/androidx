/*
 * Copyright 2021 The Android Open Source Project
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

package androidx.camera.camera2.internal.compat.workaround;

import androidx.camera.camera2.internal.compat.quirk.UseTorchAsFlashQuirk;
import androidx.camera.core.impl.Quirks;

import org.jspecify.annotations.NonNull;

/**
 * Workaround to use torch as flash.
 *
 * @see UseTorchAsFlashQuirk
 */
public class UseTorchAsFlash {

    private final boolean mHasUseTorchAsFlashQuirk;

    public UseTorchAsFlash(@NonNull Quirks quirks) {
        mHasUseTorchAsFlashQuirk = quirks.contains(UseTorchAsFlashQuirk.class);
    }

    /** Returns if torch should be used as flash. */
    public boolean shouldUseTorchAsFlash() {
        return mHasUseTorchAsFlashQuirk;
    }
}

/*
 * Copyright 2019 The Android Open Source Project
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

package androidx.swiperefreshlayout.widget;

import android.content.Context;

import androidx.recyclerview.widget.RecyclerView;

import org.jspecify.annotations.NonNull;

public class RequestDisallowInterceptRecordingRecyclerView extends RecyclerView {

    public boolean mRequestDisallowInterceptTrueCalled;
    public boolean mRequestDisallowInterceptFalseCalled;

    public RequestDisallowInterceptRecordingRecyclerView(@NonNull Context context) {
        super(context);
    }

    @Override
    public void requestDisallowInterceptTouchEvent(boolean disallowIntercept) {
        super.requestDisallowInterceptTouchEvent(disallowIntercept);
        if (disallowIntercept) {
            mRequestDisallowInterceptTrueCalled = true;
        } else {
            mRequestDisallowInterceptFalseCalled = true;
        }
    }
}

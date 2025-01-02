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

package androidx.wear.tiles.samples.tile

import android.content.Context
import androidx.wear.protolayout.DimensionBuilders.expand
import androidx.wear.protolayout.DimensionBuilders.weight
import androidx.wear.protolayout.LayoutElementBuilders
import androidx.wear.protolayout.LayoutElementBuilders.Box
import androidx.wear.protolayout.ModifiersBuilders.Background
import androidx.wear.protolayout.ModifiersBuilders.Modifiers
import androidx.wear.protolayout.ResourceBuilders
import androidx.wear.protolayout.ResourceBuilders.AndroidImageResourceByResId
import androidx.wear.protolayout.ResourceBuilders.ImageResource
import androidx.wear.protolayout.TimelineBuilders
import androidx.wear.protolayout.material3.CardColors
import androidx.wear.protolayout.material3.CardDefaults.filledTonalCardColors
import androidx.wear.protolayout.material3.CardDefaults.filledVariantCardColors
import androidx.wear.protolayout.material3.DataCardStyle.Companion.extraLargeDataCardStyle
import androidx.wear.protolayout.material3.DataCardStyle.Companion.smallCompactDataCardStyle
import androidx.wear.protolayout.material3.MaterialScope
import androidx.wear.protolayout.material3.appCard
import androidx.wear.protolayout.material3.avatarImage
import androidx.wear.protolayout.material3.buttonGroup
import androidx.wear.protolayout.material3.graphicDataCard
import androidx.wear.protolayout.material3.iconDataCard
import androidx.wear.protolayout.material3.materialScope
import androidx.wear.protolayout.material3.primaryLayout
import androidx.wear.protolayout.material3.text
import androidx.wear.protolayout.material3.textDataCard
import androidx.wear.protolayout.material3.textEdgeButton
import androidx.wear.protolayout.modifiers.LayoutModifier
import androidx.wear.protolayout.modifiers.contentDescription
import androidx.wear.protolayout.types.layoutString
import androidx.wear.tiles.RequestBuilders
import androidx.wear.tiles.TileBuilders
import androidx.wear.tiles.TileService
import androidx.wear.tiles.samples.R
import com.google.common.util.concurrent.Futures
import com.google.common.util.concurrent.ListenableFuture

private const val RESOURCES_VERSION = "0"

/** Base playground tile service for testing out features. */
class PlaygroundTileService : TileService() {
    override fun onTileResourcesRequest(
        requestParams: RequestBuilders.ResourcesRequest
    ): ListenableFuture<ResourceBuilders.Resources> = resources()

    override fun onTileRequest(
        requestParams: RequestBuilders.TileRequest
    ): ListenableFuture<TileBuilders.Tile> = tile(requestParams, this)
}

private fun resources() =
    Futures.immediateFuture(
        ResourceBuilders.Resources.Builder()
            .addIdToImageMapping(
                "id",
                ImageResource.Builder()
                    .setAndroidResourceByResId(
                        AndroidImageResourceByResId.Builder()
                            .setResourceId(R.drawable.avatar)
                            .build()
                    )
                    .build()
            )
            .setVersion(RESOURCES_VERSION)
            .build()
    )

private fun tile(
    requestParams: RequestBuilders.TileRequest,
    context: Context,
): ListenableFuture<TileBuilders.Tile> =
    Futures.immediateFuture(
        TileBuilders.Tile.Builder()
            .setResourcesVersion(RESOURCES_VERSION)
            .setTileTimeline(
                TimelineBuilders.Timeline.fromLayoutElement(tileLayout(requestParams, context))
            )
            .build()
    )

private fun tileLayout(
    requestParams: RequestBuilders.TileRequest,
    context: Context,
): LayoutElementBuilders.LayoutElement =
    materialScope(context = context, deviceConfiguration = requestParams.deviceConfiguration) {
        primaryLayout(
            mainSlot = { graphicDataCardSample() },
            bottomSlot = {
                textEdgeButton(
                    onClick = EMPTY_LOAD_CLICKABLE,
                    modifier = LayoutModifier.contentDescription("EdgeButton"),
                ) {
                    text("Edge".layoutString)
                }
            }
        )
    }

private fun MaterialScope.appCardSample() =
    appCard(
        onClick = EMPTY_LOAD_CLICKABLE,
        modifier = LayoutModifier.contentDescription("Sample Card"),
        colors =
            CardColors(
                background = colorScheme.tertiary,
                title = colorScheme.onTertiary,
                content = colorScheme.onTertiary,
                time = colorScheme.onTertiary
            ),
        title = {
            text(
                "Title Card!".layoutString,
                maxLines = 1,
            )
        },
        content = {
            text(
                "Content of this Card!".layoutString,
                maxLines = 1,
            )
        },
        label = {
            text(
                "Hello and welcome Tiles in AndroidX!".layoutString,
            )
        },
        avatar = { avatarImage("id") },
        time = {
            text(
                "NOW".layoutString,
            )
        }
    )

private fun MaterialScope.graphicDataCardSample() =
    graphicDataCard(
        onClick = EMPTY_LOAD_CLICKABLE,
        modifier = LayoutModifier.contentDescription("Graphic Data Card"),
        height = expand(),
        horizontalAlignment = LayoutElementBuilders.HORIZONTAL_ALIGN_END,
        title = {
            text(
                "1,234!".layoutString,
            )
        },
        content = {
            text(
                "steps".layoutString,
            )
        },
        graphic = {
            Box.Builder()
                .setWidth(expand())
                .setHeight(expand())
                .setModifiers(
                    Modifiers.Builder()
                        .setBackground(
                            Background.Builder()
                                .setCorner(shapes.full)
                                .setColor(colorScheme.background.prop)
                                .build()
                        )
                        .build()
                )
                .build()
        }
    )

private fun MaterialScope.dataCards() = buttonGroup {
    buttonGroupItem {
        textDataCard(
            onClick = EMPTY_LOAD_CLICKABLE,
            modifier = LayoutModifier.contentDescription("Data Card with icon"),
            width = weight(1f),
            height = expand(),
            colors = filledTonalCardColors(),
            style = extraLargeDataCardStyle(),
            title = { this.text("1km".layoutString) },
            secondaryText = { this.text("id".layoutString) },
            content = { this.text("Run".layoutString) },
        )
    }
    buttonGroupItem {
        iconDataCard(
            onClick = EMPTY_LOAD_CLICKABLE,
            modifier =
                LayoutModifier.contentDescription(
                    "Compact Data Card without icon or secondary label"
                ),
            width = weight(2f),
            height = expand(),
            colors = filledVariantCardColors(),
            style = smallCompactDataCardStyle(),
            title = { this.text("1".layoutString) },
            content = { this.text("PM".layoutString) },
        )
    }
}

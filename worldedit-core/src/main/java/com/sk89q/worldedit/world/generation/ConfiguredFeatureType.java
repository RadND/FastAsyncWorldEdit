/*
 * WorldEdit, a Minecraft world manipulation toolkit
 * Copyright (C) sk89q <http://www.sk89q.com>
 * Copyright (C) WorldEdit team and contributors
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program.  If not, see <https://www.gnu.org/licenses/>.
 */

package com.sk89q.worldedit.world.generation;

import com.sk89q.worldedit.EditSession;
import com.sk89q.worldedit.math.BlockVector3;
import com.sk89q.worldedit.registry.Keyed;
import com.sk89q.worldedit.registry.NamespacedRegistry;

public record ConfiguredFeatureType(String id) implements Keyed {

    public static final NamespacedRegistry<ConfiguredFeatureType> REGISTRY = new NamespacedRegistry<>("configured feature type");

    @Override
    public String toString() {
        return this.id;
    }

    //FAWE start

    /**
     * Place this feature into an {@link EditSession}
     *
     * @param extent   EditSession to place into
     * @param position position to use for placement
     * @return true if successful
     */
    public boolean place(EditSession extent, BlockVector3 position) {
        return extent.getWorld().generateFeature(this, extent, position);
    }
    //FAWE end
}
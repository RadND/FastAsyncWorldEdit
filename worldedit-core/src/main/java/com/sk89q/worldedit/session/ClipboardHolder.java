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

package com.sk89q.worldedit.session;

import com.sk89q.worldedit.extent.Extent;
import com.sk89q.worldedit.extent.clipboard.Clipboard;
import com.sk89q.worldedit.math.transform.Identity;
import com.sk89q.worldedit.math.transform.Transform;

import java.io.Closeable;
import java.io.Flushable;
import java.io.IOException;
import java.util.Collections;
import java.util.List;

import static com.google.common.base.Preconditions.checkNotNull;

/**
 * Holds the clipboard and the current transform on the clipboard.
 */
//FAWE start - closeable and flushable
public class ClipboardHolder implements Closeable, Flushable {

    private Clipboard clipboard;
    private Transform transform = new Identity();

    /**
     * Create a new instance with the given clipboard.
     *
     * @param clipboard the clipboard
     */
    public ClipboardHolder(Clipboard clipboard) {
        checkNotNull(clipboard);
        this.clipboard = clipboard;
    }

    /**
     * Get the clipboard.
     *
     * <p>
     * If there is a transformation applied, the returned clipboard will
     * not contain its effect.
     * </p>
     *
     * @return the clipboard
     * @deprecated FAWE supports multiple loaded schematics {@link #getClipboards()}
     */
    @Deprecated
    public Clipboard getClipboard() {
        return clipboard;
    }

    //FAWE start

    /**
     * Gets all currently held clipboards.
     *
     * @return all clipboards being held.
     */
    public List<Clipboard> getClipboards() {
        return Collections.singletonList(getClipboard());
    }

    public boolean contains(Clipboard clipboard) {
        return this.clipboard == clipboard;
    }

    /**
     * Gets all end ClipboardHolders<br/>
     * - Usually this will return itself.<br/>
     * - If this is a multi clipboard, it will return the children
     *
     * @return a List of end ClipboardHolders
     */
    public List<ClipboardHolder> getHolders() {
        return Collections.singletonList(this);
    }
    //FAWE end

    /**
     * Set the transform.
     *
     * @param transform the transform
     */
    public void setTransform(Transform transform) {
        checkNotNull(transform);
        this.transform = transform;
    }

    /**
     * Get the transform.
     *
     * @return the transform
     */
    public Transform getTransform() {
        return transform;
    }

    /**
     * Create a builder for an operation to paste this clipboard.
     *
     * @return a builder
     */
    public PasteBuilder createPaste(Extent targetExtent) {
        return new PasteBuilder(this, targetExtent);
    }

    @Override
    public void close() {
        if (clipboard != null) {
            clipboard.close();
        }
        clipboard = null;
    }

    @Override
    public void flush() throws IOException {
        if (clipboard != null) {
            clipboard.flush();
        }
    }

}

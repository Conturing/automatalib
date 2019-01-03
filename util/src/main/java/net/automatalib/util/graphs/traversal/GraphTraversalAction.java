/* Copyright (C) 2013-2019 TU Dortmund
 * This file is part of AutomataLib, http://www.automatalib.net/.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
package net.automatalib.util.graphs.traversal;

/**
 * The type of a {@link GraphTraversalAction} to be performed.
 *
 * @author Malte Isberner
 */
public enum GraphTraversalAction {

    IGNORE,
    /**
     * Explore the respective node (in this case, the user data is regarded).
     */
    EXPLORE,
    /**
     * Abort the exploration of the current node.
     */
    ABORT_NODE,
    /**
     * Abort the traversal of the whole graph.
     */
    ABORT_TRAVERSAL
}

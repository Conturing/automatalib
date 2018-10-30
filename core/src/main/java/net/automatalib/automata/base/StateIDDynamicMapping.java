/* Copyright (C) 2013-2018 TU Dortmund
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
package net.automatalib.automata.base;

import net.automatalib.automata.Automaton;
import net.automatalib.commons.smartcollections.ResizingArrayStorage;
import net.automatalib.commons.util.mappings.MutableMapping;
import net.automatalib.commons.util.nid.IDChangeListener;
import net.automatalib.commons.util.nid.NumericID;

public class StateIDDynamicMapping<S extends NumericID, V> implements MutableMapping<S, V>, IDChangeListener<S> {

    private final Automaton<S, ?, ?> automaton;
    private final ResizingArrayStorage<V> storage;

    public StateIDDynamicMapping(Automaton<S, ?, ?> automaton) {
        this.automaton = automaton;
        this.storage = new ResizingArrayStorage<>(Object.class, automaton.size());
    }

    @Override
    public V get(S elem) {
        int id = elem.getId();
        if (id >= 0 && id < storage.array.length) {
            return storage.array[id];
        }
        return null;
    }

    @Override
    public void idChanged(S obj, int newId, int oldId) {
        V oldValue = null;
        if (oldId > 0 && oldId < storage.array.length) {
            oldValue = storage.array[oldId];
            storage.array[oldId] = null;
        }
        if (newId >= storage.array.length) {
            storage.ensureCapacity(automaton.size());
        }
        storage.array[newId] = oldValue;
    }

    @Override
    public V put(S key, V value) {
        int id = key.getId();
        if (id >= storage.array.length) {
            storage.ensureCapacity(automaton.size());
        }
        V old = storage.array[id];
        storage.array[id] = value;
        return old;
    }

}

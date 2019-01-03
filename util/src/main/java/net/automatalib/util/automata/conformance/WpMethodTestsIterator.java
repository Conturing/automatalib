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
package net.automatalib.util.automata.conformance;

import java.util.Collection;
import java.util.Collections;
import java.util.Iterator;
import java.util.List;
import java.util.Set;

import javax.annotation.ParametersAreNonnullByDefault;

import com.google.common.collect.Iterators;
import com.google.common.collect.Sets;
import net.automatalib.automata.UniversalDeterministicAutomaton;
import net.automatalib.commons.util.collections.AbstractThreeLevelIterator;
import net.automatalib.commons.util.collections.CollectionsUtil;
import net.automatalib.commons.util.collections.DelegatingIterator;
import net.automatalib.commons.util.collections.ReusableIterator;
import net.automatalib.commons.util.mappings.MutableMapping;
import net.automatalib.util.automata.Automata;
import net.automatalib.util.automata.cover.Covers;
import net.automatalib.util.automata.equivalence.CharacterizingSets;
import net.automatalib.words.Word;
import net.automatalib.words.WordBuilder;

/**
 * Iterator that returns test words generated by the partial W Method.
 * <p>
 * See "Test selection based on finite state models" by S. Fujiwara et al.
 *
 * @param <I>
 *         input symbol type
 *
 * @author frohme
 */
@ParametersAreNonnullByDefault
public class WpMethodTestsIterator<I> extends DelegatingIterator<Word<I>> {

    public WpMethodTestsIterator(UniversalDeterministicAutomaton<?, I, ?, ?, ?> automaton,
                                 Collection<? extends I> alphabet,
                                 int maxDepth) {
        super(buildIterators(automaton, alphabet, maxDepth));
    }

    private static <I> Iterator<Word<I>> buildIterators(UniversalDeterministicAutomaton<?, I, ?, ?, ?> automaton,
                                                        Collection<? extends I> inputs,
                                                        int maxDepth) {

        final Set<Word<I>> stateCover = Sets.newHashSetWithExpectedSize(automaton.size());
        final Set<Word<I>> transitionCover = Sets.newHashSetWithExpectedSize(automaton.size() * inputs.size());

        Covers.cover(automaton, inputs, stateCover, transitionCover);

        final Iterable<Word<I>> characterizingSet;
        final Iterator<Word<I>> characterizingIter = CharacterizingSets.characterizingSetIterator(automaton, inputs);

        // Special case: List of characterizing suffixes may be empty,
        // but in this case we still need to iterate over the prefixes!
        if (!characterizingIter.hasNext()) {
            characterizingSet = Collections.singletonList(Word.epsilon());
        } else {
            characterizingSet = new ReusableIterator<>(characterizingIter);
        }

        // Phase 1: state cover * middle part * global suffixes
        final Iterator<Word<I>> firstIterator =
                new FirstPhaseIterator<>(stateCover, CollectionsUtil.allTuples(inputs, 0, maxDepth), characterizingSet);

        // Phase 2: transitions (not in state cover) * middle part * local suffixes
        transitionCover.removeAll(stateCover);
        final Iterator<Word<I>> secondIterator = new SecondPhaseIterator<>(automaton,
                                                                           inputs,
                                                                           transitionCover,
                                                                           CollectionsUtil.allTuples(inputs,
                                                                                                     0,
                                                                                                     maxDepth));

        return Iterators.concat(firstIterator, secondIterator);
    }

    private static class FirstPhaseIterator<I> extends AbstractThreeLevelIterator<List<I>, Word<I>, Word<I>, Word<I>> {

        private final Iterable<Word<I>> prefixes;
        private final Iterable<Word<I>> suffixes;

        private final WordBuilder<I> wordBuilder = new WordBuilder<>();

        FirstPhaseIterator(Iterable<Word<I>> prefixes, Iterable<List<I>> middleParts, Iterable<Word<I>> suffixes) {
            super(middleParts.iterator());

            this.prefixes = prefixes;
            this.suffixes = suffixes;
        }

        @Override
        protected Iterator<Word<I>> l2Iterator(List<I> l1Object) {
            return prefixes.iterator();
        }

        @Override
        protected Iterator<Word<I>> l3Iterator(List<I> l1Object, Word<I> l2Object) {
            return suffixes.iterator();
        }

        @Override
        protected Word<I> combine(List<I> middle, Word<I> prefix, Word<I> suffix) {
            wordBuilder.ensureAdditionalCapacity(prefix.size() + middle.size() + suffix.size());
            Word<I> word = wordBuilder.append(prefix).append(middle).append(suffix).toWord();
            wordBuilder.clear();
            return word;
        }
    }

    private static class SecondPhaseIterator<S, I>
            extends AbstractThreeLevelIterator<List<I>, Word<I>, Word<I>, Word<I>> {

        private final UniversalDeterministicAutomaton<S, I, ?, ?, ?> automaton;
        private final Collection<? extends I> inputs;

        private final MutableMapping<S, List<Word<I>>> localSuffixSets;
        private final Iterable<Word<I>> prefixes;

        private final WordBuilder<I> wordBuilder = new WordBuilder<>();

        SecondPhaseIterator(UniversalDeterministicAutomaton<S, I, ?, ?, ?> automaton,
                            Collection<? extends I> inputs,
                            Iterable<Word<I>> prefixes,
                            Iterable<List<I>> middleParts) {
            super(middleParts.iterator());

            this.automaton = automaton;
            this.inputs = inputs;
            this.localSuffixSets = automaton.createStaticStateMapping();
            this.prefixes = prefixes;
        }

        @Override
        protected Iterator<Word<I>> l2Iterator(List<I> l1Object) {
            return prefixes.iterator();
        }

        @Override
        protected Iterator<Word<I>> l3Iterator(List<I> middle, Word<I> prefix) {

            final S tmp = automaton.getState(prefix);
            final S state = automaton.getSuccessor(tmp, middle);

            List<Word<I>> localSuffixes = localSuffixSets.get(state);

            if (localSuffixes == null) {
                localSuffixes = Automata.stateCharacterizingSet(automaton, inputs, state);
                if (localSuffixes.isEmpty()) {
                    localSuffixes = Collections.singletonList(Word.epsilon());
                }
                localSuffixSets.put(state, localSuffixes);
            }

            return localSuffixes.iterator();
        }

        @Override
        protected Word<I> combine(List<I> middle, Word<I> prefix, Word<I> suffix) {
            wordBuilder.ensureAdditionalCapacity(prefix.size() + middle.size() + suffix.size());
            Word<I> word = wordBuilder.append(prefix).append(middle).append(suffix).toWord();
            wordBuilder.clear();
            return word;
        }
    }
}

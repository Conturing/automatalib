/* Copyright (C) 2013-2021 TU Dortmund
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
package net.automatalib.util.ts.modal;

import java.util.Collection;
import java.util.Comparator;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Stream;

import net.automatalib.automata.AutomatonCreator;
import net.automatalib.automata.MutableAutomaton;
import net.automatalib.automata.UniversalFiniteAlphabetAutomaton;
import net.automatalib.commons.util.Pair;
import net.automatalib.ts.TransitionPredicate;
import net.automatalib.ts.modal.CompactMC;
import net.automatalib.ts.modal.CompactMTS;
import net.automatalib.ts.modal.ModalContract;
import net.automatalib.ts.modal.ModalTransitionSystem;
import net.automatalib.ts.modal.transition.ModalContractEdgeProperty;
import net.automatalib.ts.modal.transition.ModalContractEdgePropertyImpl;
import net.automatalib.ts.modal.transition.ModalEdgeProperty;
import net.automatalib.ts.modal.transition.ModalEdgePropertyImpl;
import net.automatalib.util.automata.predicates.TransitionPredicates;
import net.automatalib.util.fixpoint.Closures;

public final class Subgraphs {

    private Subgraphs() {
        // prevent instantiation
    }

    public enum SubgraphType {
        DISREGARD_UNKNOWN_LABELS {
            @Override
            <S, I, T> TransitionPredicate<S, I, T> getTransitionPredicate(Collection<I> inputs) {
                return TransitionPredicates.alwaysFalse();
            }
        },
        HIDE_UNKNOWN_LABELS {
            @Override
            <S, I, T> TransitionPredicate<S, I, T> getTransitionPredicate(Collection<I> inputs) {
                return TransitionPredicates.inputNotIn(inputs);
            }

        };

        abstract <S, I, T> TransitionPredicate<S, I, T> getTransitionPredicate(Collection<I> inputs);
    }

    public static <TP1, TP2> Optional<TP2> propertyFunction(Comparator<TP1> cmp, Function<TP1, TP2> tpMapper, Stream<TP1> properties) {
        //Comparator<ModalEdgeProperty> cmp = Comparator.comparingInt(o -> (o.isMust() ? 1 : 0));
        return properties.max(cmp).map(tpMapper);
    }

    /**
     * Returns the subgraph of ts with labels from inputs.
     * <p>
     * Creates a new instance of creator and copies ts into it. All symbols not in inputs are handled according to
     * strategy.
     */
    public static <A extends UniversalFiniteAlphabetAutomaton<S1, I, T1, ?, TP1>, B extends MutableAutomaton<S2, I, ?, ?, TP2>, S1, I, TP1, S2, T1, TP2> Pair<Map<Set<S1>, S2>, B> subgraphView(
            SubgraphType type,
            A ts,
            Collection<I> remainingInputs,
            AutomatonCreator<B, I> creator,
            Function<? super Collection<? super T1>, ? extends TP2> tpMapping) {

        return Closures.closure(ts,
                                remainingInputs,
                                creator,
                                Closures.toClosureOperator(ts,
                                                           ts.getInputAlphabet(),
                                                           type.getTransitionPredicate(remainingInputs)),
                                TransitionPredicates.inputIn(remainingInputs),
                                tpMapping);
    }

    public static <A extends ModalTransitionSystem<S1, I, T1, TP1>, S1, I, T1, TP1 extends ModalEdgeProperty> Pair<Map<Set<S1>, Integer>, CompactMTS<I>> subgraphViewMTS(
            SubgraphType type,
            A ts,
            Collection<I> remainingInputs) {

        return subgraphView(type,
                            ts,
                            remainingInputs,
                            new CompactMTS.Creator<>(),
                            trs -> ModalEdgePropertyImpl.from(trs.stream()
                                                                .map(t -> ts.getTransitionProperty((T1) t))
                                                                .max(Comparator.comparingInt(o -> (o.isMust() ? 1 : 0)))
                                                                .get())
                            );
    }

    public static <A extends ModalContract<S1, I, T1, TP1>, S1, I, T1, TP1 extends ModalContractEdgeProperty> Pair<Map<Set<S1>, Integer>, CompactMC<I>> subgraphViewMC(
            SubgraphType type,
            A ts,
            Collection<I> remainingInputs) {

        return subgraphView(type,
                            ts,
                            remainingInputs,
                            new CompactMC.Creator<>(),
                            trs -> new ModalContractEdgePropertyImpl(trs.stream()
                                                                        .map(t -> ts.getTransitionProperty((T1) t))
                                                                        .max(Comparator.comparingInt(o -> (o.isMust() ? 1 << 3 : 0)
                                                                                                          + (o.isRed() ? 1 << 2 : 0)
                                                                                                          + (o.isGreen() ? 1 << 1 : 0)))
                                                                        .get())
                            );
    }
}

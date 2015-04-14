/* Copyright (C) 2015 TU Dortmund
 * This file is part of AutomataLib, http://www.automatalib.net/.
 * 
 * AutomataLib is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License version 3.0 as published by the Free Software Foundation.
 * 
 * AutomataLib is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public
 * License along with AutomataLib; if not, see
 * http://www.gnu.de/documents/lgpl.en.html.
 */
package net.automatalib.commons.util.random;

import java.util.ArrayList;
import java.util.List;
import java.util.Random;
import java.util.function.Supplier;

/**
 * This class implements a {@link Supplier} that randomly delegates to one of several (sub-)suppliers.
 * Each sub-supplier is assigned a weight, which determines the probability of it being chosen
 * upon calls to {@link #get()}.
 * <p>
 * The {@link #add(Object, int)} and {@link #add(Supplier, int)} methods return a reference to {@code this},
 * so calls can be chained.
 * <p>
 * <b>Usage example:</b>
 * <pre>
 * {@code
 * Supplier<String> mySupplier = ...;
 * String str = new WeightedSupplier<String>()
 *  .add("foo", 5)
 *  .add(mySupplier, 10)
 *  .get();
 * }
 * </pre>
 * With a one-third chance, the value {@code "foo"} will be assigned to {@code str}. Otherwise (i.e.,
 * with a two-thirds chance), the result of {@code mySupplier.get()} will be assigned to {@code str}. Note
 * that in the former case, {@code mySupplier.get()} will not even be invoked.
 * 
 * @author Malte Isberner
 *
 * @param <T> the supplied type
 */
public class WeightedSupplier<T> implements Supplier<T> {
	
	private static final class SubSupplier<T> implements Supplier<T> {
		private final int lowIdx;
		private final int highIdx;
		private final Supplier<? extends T> supplier;
		
		public SubSupplier(int lowIdx, int highIdx, Supplier<? extends T> supplier) {
			this.lowIdx = lowIdx;
			this.highIdx = highIdx;
			this.supplier = supplier;
		}
		
		@Override
		public T get() {
			return supplier.get();
		}
	}
	
	
	private final Random random;
	private int totalWeight = 0;
	private final List<SubSupplier<T>> subSuppliers = new ArrayList<>();

	public WeightedSupplier() {
		this(new Random());
	}
	
	public WeightedSupplier(Random random) {
		this.random = random;
	}
	
	/**
	 * Adds an object to be supplied with a given weight.
	 * 
	 * @param obj the object to be supplied
	 * @param weight the weight
	 * @return {@code this}
	 */
	public WeightedSupplier<T> add(T obj, int weight) {
		return add(() -> obj, weight);
	}
	
	/**
	 * Adds a sub-supplier with a given weight.
	 * 
	 * @param supplier the sub-supplier
	 * @param weight the weight
	 * @return {@code this}
	 */
	public WeightedSupplier<T> add(Supplier<? extends T> supplier, int weight) {
		if (weight < 0) {
			return this;
		}
		int low = totalWeight;
		totalWeight += weight;
		SubSupplier<T> ss = new SubSupplier<T>(low, totalWeight, supplier);
		subSuppliers.add(ss);
		return this;
	}

	@Override
	public T get() {
		int val = random.nextInt(totalWeight);
		int l = 0, h = subSuppliers.size();
		while (l < h) {
			int mid = l + (h - l)/2;
			SubSupplier<T> ss = subSuppliers.get(mid);
			if (ss.lowIdx <= val) {
				if (ss.highIdx > val) {
					return ss.get();
				}
				l = mid + 1;
			}
			else {
				h = mid;
			}
		}
		throw new AssertionError();
	}

}

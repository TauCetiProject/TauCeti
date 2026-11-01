/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.GCongr

/-!
# Sums under a weakened triangle inequality

An absolute value satisfies `v (a + b) ≤ c * max (v a) (v b)` with `c = 2`, and with `c = 1` when
it is nonarchimedean. Iterating this inequality bounds a sum of `n` terms of size at most `T` by
`c ^ n * T` (`AbsoluteValue.apply_sum_le_pow_mul`). Unlike the triangle inequality, which gives
`n * T`, the bound specializes to `T` itself in the nonarchimedean case.
-/

public section

open Finset

namespace AbsoluteValue

variable {R S : Type*} [Semiring R] [Semiring S] [LinearOrder S] [IsOrderedRing S]

/-- A sum of `card s` terms of size at most `T` has size at most `c ^ card s * T`, for an
absolute value satisfying `v (a + b) ≤ c * max (v a) (v b)` with `1 ≤ c`. -/
theorem apply_sum_le_pow_mul {v : AbsoluteValue R S} {c : S} (hc : 1 ≤ c)
    (hv : ∀ a b, v (a + b) ≤ c * max (v a) (v b)) {ι : Type*} (s : Finset ι) (f : ι → R)
    {T : S} (hT : 0 ≤ T) (hf : ∀ i ∈ s, v (f i) ≤ T) : v (∑ i ∈ s, f i) ≤ c ^ s.card * T := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hT
  | insert a s ha ih =>
    rw [sum_insert ha, card_insert_of_notMem ha, pow_succ', mul_assoc]
    have hs := ih fun i hi ↦ hf i (mem_insert_of_mem hi)
    have hTs : T ≤ c ^ s.card * T := le_mul_of_one_le_left hT (one_le_pow₀ hc)
    calc v (f a + ∑ i ∈ s, f i) ≤ c * max (v (f a)) (v (∑ i ∈ s, f i)) := hv _ _
      _ ≤ c * (c ^ s.card * T) := by
        have : 0 ≤ c := zero_le_one.trans hc
        gcongr
        exact max_le ((hf a (mem_insert_self a s)).trans hTs) hs

end AbsoluteValue

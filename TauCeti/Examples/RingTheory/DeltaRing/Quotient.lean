/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.RingTheory.DeltaRing.Quotient

/-!
# Checks for `δ`-stable ideals and `δ`-quotients

These examples use `ℤ` with its unique `2`-`δ`-structure, for which `δ 2 = -1`. The ideal `(2)`
is therefore not `δ`-stable, although the `δ`-stabilization of `⊥` lies in it: the minimality
statement `deltaStabilization_le_iff` needs its target to be `δ`-stable. The `δ`-stabilization of
`(2)` contains the unit `-1`, so it is the unit ideal and the universal `δ`-quotient of `ℤ` in
which `2` vanishes is the zero ring.
-/

namespace TauCeti.Examples

open TauCeti.DeltaRing

-- `(2)` is not `δ`-stable in `ℤ`, since `δ 2 = -1`.
example : ¬ IsDeltaStable 2 (Ideal.span {(2 : ℤ)}) := fun h => by
  have := h.delta_mem (Ideal.subset_span rfl)
  rw [delta_int_two, Ideal.mem_span_singleton] at this
  norm_num at this

-- The `δ`-stabilization of `⊥` lies in the ideal `(2)`, which is not `δ`-stable.
example : deltaStabilization 2 (⊥ : Ideal ℤ) ≤ Ideal.span {(2 : ℤ)} := by
  simp

-- The `δ`-stabilization of `(2)` is the unit ideal of `ℤ`.
example : deltaStabilization 2 (Ideal.span {(2 : ℤ)}) = ⊤ := by
  have h := iterate_delta_mem_deltaStabilization (p := 2) (Ideal.mem_span_singleton_self (2 : ℤ)) 1
  rw [Function.iterate_one, delta_int_two] at h
  exact Ideal.eq_top_of_isUnit_mem _ h isUnit_one.neg

-- The universal `δ`-quotient of `ℤ` in which `2` vanishes is the zero ring.
example : Subsingleton (ℤ ⧸ deltaStabilization 2 (Ideal.span {(2 : ℤ)})) := by
  have h := iterate_delta_mem_deltaStabilization (p := 2) (Ideal.mem_span_singleton_self (2 : ℤ)) 1
  rw [Function.iterate_one, delta_int_two] at h
  exact Ideal.Quotient.subsingleton_iff.mpr (Ideal.eq_top_of_isUnit_mem _ h isUnit_one.neg)

end TauCeti.Examples

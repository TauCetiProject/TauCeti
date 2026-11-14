/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Set.Card

/-!
# Cardinalities of level sets of finitely supported functions

On an infinite index type a finitely supported function takes the value `0` infinitely often, so
`Set.ncard` counts its zeros as `0`. A nonnegative function takes a value that is not positive
either never or, for `0`, infinitely often, so `Set.ncard` counts both cases as `0`.

## Main declarations

* `Finsupp.ncard_ofPred_eq_zero_of_infinite`: a finitely supported function on an infinite type
  takes the value `0` infinitely often, so `Set.ncard` counts its zeros as `0`.
* `Finsupp.ncard_ofPred_eq_zero_of_nonneg_of_not_pos`: `Set.ncard` counts every value that is not
  positive as taken `0` times by a nonnegative finitely supported function on an infinite type.
-/

public section

namespace Finsupp

variable {α ι : Type*} [Zero α] [Infinite ι]

/-- A finitely supported function on an infinite type takes the value `0` infinitely often, so
`Set.ncard` counts its zeros as `0`. -/
@[simp]
theorem ncard_ofPred_eq_zero_of_infinite (f : ι →₀ α) : {i | f i = 0}.ncard = 0 :=
  Set.Infinite.ncard <| f.support.finite_toSet.infinite_compl.mono fun i hi ↦ by simpa using hi

/-- A nonnegative finitely supported function on an infinite type takes a value `a` that is not
positive either never or, for `a = 0`, infinitely often, so `Set.ncard` counts it as taken `0`
times. -/
theorem ncard_ofPred_eq_zero_of_nonneg_of_not_pos [PartialOrder α] {f : ι →₀ α}
    (hf : ∀ i, 0 ≤ f i) {a : α} (ha : ¬ 0 < a) : {i | f i = a}.ncard = 0 := by
  rcases eq_or_ne a 0 with rfl | ha0
  · exact ncard_ofPred_eq_zero_of_infinite f
  · have : {i | f i = a} = ∅ := Set.eq_empty_of_forall_notMem fun i (hi : f i = a) ↦
      ha <| (hi ▸ hf i).lt_of_ne' ha0
    rw [this, Set.ncard_empty]

end Finsupp

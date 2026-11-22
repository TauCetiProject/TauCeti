/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Alternating.Basic

/-!
# Coefficient extraction for alternating maps

Putting a linear combination `∑ j ∈ s, e j • v j` in place of the `i`-th argument `v i` of an
alternating map, for `i ∈ s`, multiplies its value on `v` by `e i`: every other term of the sum
repeats an argument, so its contribution vanishes. Over a basis, this reads off the `i`-th
coordinate of a vector put in place of the `i`-th basis vector.

## Main results

* `AlternatingMap.map_update_sum_smul`: putting `∑ j ∈ s, e j • v j` in place of `v i`, for
  `i ∈ s`, multiplies the value of an alternating map by `e i`.
-/

public section

namespace AlternatingMap

variable {R M N ι : Type*} [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N]
  [Module R N]

/-- Putting the linear combination `∑ j ∈ s, e j • v j` in place of `v i`, for `i ∈ s`, multiplies
the value of an alternating map by `e i`: every other term repeats an argument. -/
theorem map_update_sum_smul [DecidableEq ι] (f : M [⋀^ι]→ₗ[R] N) (v : ι → M) {s : Finset ι}
    {i : ι} (hi : i ∈ s) (e : ι → R) :
    f (Function.update v i (∑ j ∈ s, e j • v j)) = e i • f v := by
  rw [f.map_update_sum, Finset.sum_eq_single_of_mem i hi fun j _ hji ↦ by
    rw [f.map_update_smul, f.map_update_self _ hji.symm, smul_zero], f.map_update_smul,
    Function.update_eq_self]

end AlternatingMap

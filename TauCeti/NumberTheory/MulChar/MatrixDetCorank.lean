/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.NumberTheory.MulChar.Basic

import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Corank `q`-Pochhammer indicator for square matrices

For a square matrix `A : Matrix n n K` over a field `K`, the corank `Fintype.card n - A.rank` is
strictly positive if and only if `A` is not a unit (`TauCeti.corank_pos_iff_not_isUnit`).
Consequently, for any commutative ring `R` and `q : R`, the product
`∏ l ∈ Finset.range (Fintype.card n - A.rank), (1 - q ^ l)` equals `1` when `IsUnit A`
(`TauCeti.prod_range_corank_one_sub_pow_eq_one_of_isUnit`) and vanishes when `¬IsUnit A` via its
`l = 0` factor `1 - 1 = 0` (`TauCeti.prod_range_corank_one_sub_pow_eq_zero_of_not_isUnit`),
matching the trivial multiplicative character `(1 : MulChar K R) A.det`
(`TauCeti.prod_range_corank_one_sub_pow_eq_mulChar_one`).

## Main results

* `TauCeti.corank_pos_iff_not_isUnit`: `0 < Fintype.card n - A.rank ↔ ¬IsUnit A`.
* `TauCeti.prod_range_corank_one_sub_pow_eq_one_of_isUnit`: the corank product is `1` for units.
* `TauCeti.prod_range_corank_one_sub_pow_eq_zero_of_not_isUnit`: the corank product is `0` for
  non-units.
* `TauCeti.prod_range_corank_one_sub_pow_eq_mulChar_one`:
  `∏ l ∈ Finset.range (Fintype.card n - A.rank), (1 - q ^ l) = (1 : MulChar K R) A.det`.

## Provenance

Adapted from `grh-lean` (`https://github.com/lsernau/grh-lean`, commit
`72fead102f663d5c7a407964a13dc0cf9d977207`), `src/New/OneLift/HeckeValues/PeriodAtOne.lean`
(`New.prod_range_corank_one_sub_q_pow`).
-/

public section

namespace TauCeti

variable {n K R : Type*} [Fintype n] [DecidableEq n] [Field K] [CommRing R]

/-- The corank `Fintype.card n - A.rank` of a square matrix `A` over a field is positive if and
only if `A` is not a unit. -/
theorem corank_pos_iff_not_isUnit (A : Matrix n n K) :
    0 < Fintype.card n - A.rank ↔ ¬IsUnit A := by
  constructor
  · intro hpos hu
    rw [Matrix.rank_of_isUnit A hu, Nat.sub_self] at hpos
    exact lt_irrefl 0 hpos
  · intro hnu
    have hrk := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
    rw [Module.finrank_pi] at hrk
    have hker : Module.finrank K (LinearMap.ker A.mulVecLin) ≠ 0 := fun hzero ↦
      hnu (Matrix.mulVec_injective_iff_isUnit.mp
        (LinearMap.ker_eq_bot.mp (Submodule.finrank_eq_zero.mp hzero)))
    have htoLin : Matrix.toLin (Pi.basisFun K n) (Pi.basisFun K n) A = A.mulVecLin :=
      LinearMap.ext fun x ↦ by ext i; simp [Matrix.toLin_apply, Pi.single_apply]; rfl
    have hrank : A.rank = Module.finrank K (LinearMap.range A.mulVecLin) := by
      rw [← htoLin]
      exact A.rank_eq_finrank_range_toLin (Pi.basisFun K n) (Pi.basisFun K n)
    omega

/-- For an invertible square matrix `A` over a field and any `q : R`, the corank product is `1`. -/
theorem prod_range_corank_one_sub_pow_eq_one_of_isUnit {A : Matrix n n K} (hA : IsUnit A) (q : R) :
    ∏ l ∈ Finset.range (Fintype.card n - A.rank), (1 - q ^ l) = 1 := by
  simp [Matrix.rank_of_isUnit A hA]

/-- For a non-invertible square matrix `A` over a field and any `q : R`, the corank product
vanishes. -/
theorem prod_range_corank_one_sub_pow_eq_zero_of_not_isUnit {A : Matrix n n K} (hA : ¬IsUnit A)
    (q : R) :
    ∏ l ∈ Finset.range (Fintype.card n - A.rank), (1 - q ^ l) = 0 :=
  Finset.prod_eq_zero (i := 0)
    (Finset.mem_range.mpr ((corank_pos_iff_not_isUnit A).mpr hA)) (by simp)

/-- For a square matrix `A` over a field `K` and any `q` in a commutative ring `R`, the corank
product `∏ l ∈ Finset.range (Fintype.card n - A.rank), (1 - q ^ l)` equals the trivial
multiplicative character `(1 : MulChar K R)` evaluated at `A.det`. -/
theorem prod_range_corank_one_sub_pow_eq_mulChar_one (A : Matrix n n K) (q : R) :
    ∏ l ∈ Finset.range (Fintype.card n - A.rank), (1 - q ^ l) = (1 : MulChar K R) A.det := by
  by_cases hA : IsUnit A
  · rw [prod_range_corank_one_sub_pow_eq_one_of_isUnit hA q,
      MulChar.one_apply ((Matrix.isUnit_iff_isUnit_det A).mp hA)]
  · rw [prod_range_corank_one_sub_pow_eq_zero_of_not_isUnit hA q,
      MulChar.map_nonunit _ (mt (Matrix.isUnit_iff_isUnit_det A).mpr hA)]

end TauCeti

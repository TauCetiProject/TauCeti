/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Mathlib.NumberTheory.Height.Basic

import all Mathlib.NumberTheory.Height.Basic

/-!
# Height bounds for coordinate ratios and from local estimates

The height of a ratio of two coordinates is bounded by the projective height of the tuple.
These bounds control the affine coordinates of a projective point after normalization.
Both multiplicative and logarithmic heights are treated over any field with admissible
absolute values and any finite coordinate type.

A height bound for a tuple `z` in terms of a tuple `x` often comes from estimates at each
absolute value separately: the local factor `⨆ i, v (z i)` is at most a constant times
`(⨆ j, v (x j)) ^ p` at the archimedean absolute values, and at most `(⨆ j, v (x j)) ^ p` at the
nonarchimedean ones. `Height.mulHeight_le_of_forall_iSup_le` multiplies these estimates over all
absolute values. This is how heights of polynomial expressions such as determinants are bounded,
since no bound for the height of a sum in terms of the heights of its terms holds.

## Implementation notes

The nonarchimedean step needs the finiteness of the multiplicative support of the local factors
`⨆ i, v (x i)`, which Mathlib proves by the `private` `fun_prop` lemma
`Height.hasFiniteMulSupport_iSup_nonarchAbsVal` in `Mathlib/NumberTheory/Height/Basic.lean`; it
is reached by `import all`, as in `TauCeti/NumberTheory/Height/LinearForm.lean`.

## References

The ratio bounds are adapted from Ralf Stephan's `ArithmeticHeights/Northcott.lean` in
[`rwst/Subspace-Theorems`](https://github.com/rwst/Subspace-Theorems/blob/e443c2479e19f7665b31d8e94e2317c8ced1ca06/ArithmeticHeights/Northcott.lean),
commit `e443c2479e19f7665b31d8e94e2317c8ced1ca06` (Apache 2.0). The local-to-global bound follows
`DiophantineApproximation/HeightTransport.lean` in the same repository, snapshot
`c26d909dc48cf7fe` (Apache 2.0); see also E. Bombieri and W. Gubler,
*Heights in Diophantine Geometry* (2006), §1.6.
-/

public section

namespace Height

variable {K : Type*} [Field K] [AdmissibleAbsValues K] {ι : Type*} [Finite ι]

/-- The multiplicative height of a ratio of two coordinates is at most the height of the tuple.
The denominator may vanish, with division interpreted as the field's totalized division. -/
lemma mulHeight₁_div_le_mulHeight (x : ι → K) (i j : ι) :
    mulHeight₁ (x i / x j) ≤ mulHeight x := by
  rw [mulHeight₁_div_eq_mulHeight]
  simpa only [Matrix.vecCons, Fin.comp_cons, Matrix.empty_eq] using mulHeight_comp_le ![i, j] x

/-- The logarithmic height of a ratio of two coordinates is at most the height of the tuple. -/
lemma logHeight₁_div_le_logHeight (x : ι → K) (i j : ι) :
    logHeight₁ (x i / x j) ≤ logHeight x := by
  rw [logHeight₁_div_eq_logHeight]
  simpa only [Matrix.vecCons, Fin.comp_cons, Matrix.empty_eq] using logHeight_comp_le ![i, j] x

open AdmissibleAbsValues in
/-- **Local-to-global height bound.** Suppose that at every archimedean absolute value `v` the
local factor `⨆ i, v (z i)` is at most `C * (⨆ j, v (x j)) ^ p`, and at every nonarchimedean one
it is at most `(⨆ j, v (x j)) ^ p`. Then `mulHeight z ≤ C ^ totalWeight K * mulHeight x ^ p`. -/
lemma mulHeight_le_of_forall_iSup_le {ι' : Type*} [Finite ι'] {x : ι → K} (hx : x ≠ 0)
    (z : ι' → K) {C : ℝ} (hC : 1 ≤ C) {p : ℕ}
    (harch : ∀ v ∈ archAbsVal (K := K), ⨆ i, v (z i) ≤ C * (⨆ j, v (x j)) ^ p)
    (hnon : ∀ v ∈ nonarchAbsVal (K := K), ⨆ i, v (z i) ≤ (⨆ j, v (x j)) ^ p) :
    mulHeight z ≤ C ^ totalWeight K * mulHeight x ^ p := by
  rcases eq_or_ne z 0 with rfl | hz
  · rw [mulHeight_zero]
    exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ hC) (one_le_pow₀ (one_le_mulHeight x))
  rw [mulHeight_eq hz, mulHeight_eq hx, mul_pow, ← mul_assoc]
  gcongr
  · exact finprod_nonneg fun v ↦ Real.iSup_nonneg fun _ ↦ AbsoluteValue.nonneg _ _
  · exact mul_nonneg (by positivity) (pow_nonneg (Multiset.prod_map_nonneg fun v _ ↦
      Real.iSup_nonneg fun _ ↦ AbsoluteValue.nonneg _ _) p)
  · -- One factor `C` for each archimedean absolute value, counted with multiplicity.
    rw [← Multiset.prod_map_pow, totalWeight, ← Multiset.prod_replicate, ← Multiset.map_const',
      ← Multiset.prod_map_mul]
    exact Multiset.prod_map_le_prod_map₀ _ _
      (fun v _ ↦ Real.iSup_nonneg_of_nonnegHomClass v _) harch
  · rw [finprod_pow (hasFiniteMulSupport_iSup_nonarchAbsVal hx)]
    exact finprod_le_finprod₀ (hasFiniteMulSupport_iSup_nonarchAbsVal hz)
      (fun v ↦ Real.iSup_nonneg fun _ ↦ AbsoluteValue.nonneg _ _)
      ((hasFiniteMulSupport_iSup_nonarchAbsVal hx).pow p) fun v ↦ hnon v.val v.prop

end Height

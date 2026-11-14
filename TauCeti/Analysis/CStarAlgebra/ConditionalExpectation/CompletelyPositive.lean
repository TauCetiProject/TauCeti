/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
public import TauCeti.Analysis.CStarAlgebra.ConditionalExpectation.Basic
import TauCeti.Analysis.CStarAlgebra.CStarMatrix

/-!
# Complete positivity of C⋆-conditional expectations

Every `CStarConditionalExpectation` `E : A → B` onto a unital inclusion `ι : B →⋆ₐ[ℂ] A` is
completely positive (`CompletelyPositiveMapClass (CStarConditionalExpectation ι) A B`), hence
coerces to `A →CP B` and preserves positivity on `CStarMatrix n n A` for every finite index type
`n`.

Writing a positive matrix `M : CStarMatrix (Fin k) (Fin k) A` as `star R * R` decomposes the
`B`-valued quadratic form of `M.map E` into a sum over rows `l` of the expectation Gram forms
`∑ i, ∑ j, star (x i) * E (star (R l i) * R l j) * x j`, each of which is positive by
`CStarConditionalExpectation.sum_star_mul_map_mul_nonneg`; positivity of `M.map E` then follows
from `CStarMatrix.nonneg_iff_forall_sum_nonneg`.

## References

* V. Paulsen, *Completely Bounded Maps and Operator Algebras*, Theorem 3.4 / Exercise 3.4.
* M. Takesaki, *Theory of Operator Algebras I*, Proposition IV.3.4.
-/

public section

open scoped CStarAlgebra

namespace TauCeti.CStarConditionalExpectation

variable {A B : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B] {ι : B →⋆ₐ[ℂ] A}

instance instCompletelyPositiveMapClass :
    CompletelyPositiveMapClass (CStarConditionalExpectation ι) A B where
  map_cstarMatrix_nonneg' E k M hM := by
    obtain ⟨R, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hM
    refine CStarMatrix.nonneg_iff_forall_sum_nonneg.mpr fun x ↦ ?_
    have hcalc : (∑ i : Fin k, ∑ j : Fin k, star (x i) * (star R * R).map E i j * x j) =
        ∑ l : Fin k, ∑ i : Fin k, ∑ j : Fin k, star (x i) * E (star (R l i) * R l j) * x j := by
      simp_rw [CStarMatrix.map_apply, CStarMatrix.mul_apply, CStarMatrix.star_apply, map_sum,
        Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_congr rfl fun i _ ↦ Finset.sum_comm, Finset.sum_comm]
    rw [hcalc]
    exact Finset.sum_nonneg fun l _ ↦ E.sum_star_mul_map_mul_nonneg Finset.univ (R l) x

/-- Entrywise application of a C⋆-conditional expectation preserves positivity on matrices indexed
by any finite type. -/
theorem map_cstarMatrix_nonneg (E : CStarConditionalExpectation ι) {n : Type*} [Fintype n]
    (M : CStarMatrix n n A) (hM : 0 ≤ M) : 0 ≤ M.map E :=
  CompletelyPositiveMap.map_cstarMatrix_nonneg (E : A →CP B) M hM

end TauCeti.CStarConditionalExpectation

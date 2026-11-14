/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module
public import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
public import TauCeti.Analysis.CStarAlgebra.ConditionalExpectation.Basic
import TauCeti.Analysis.CStarAlgebra.CStarMatrix

/-! # Complete positivity of C⋆-conditional expectations

Every `CStarConditionalExpectation` `E : A → B` onto `ι : B →⋆ₐ[ℂ] A` is completely positive
(`CompletelyPositiveMapClass (CStarConditionalExpectation ι) A B`), hence preserves positivity on
`CStarMatrix n n A` (Paulsen, Theorem 3.4; Takesaki, *Theory of Operator Algebras I*, IV.3.4). -/

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
    rw [show (∑ i : Fin k, ∑ j : Fin k, star (x i) * (star R * R).map E i j * x j) =
        ∑ l : Fin k, ∑ i : Fin k, ∑ j : Fin k, star (x i) * E (star (R l i) * R l j) * x j by
      simp_rw [CStarMatrix.map_apply, CStarMatrix.mul_apply, CStarMatrix.star_apply, map_sum,
        Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_congr rfl fun i _ ↦ Finset.sum_comm, Finset.sum_comm]]
    exact Finset.sum_nonneg fun l _ ↦ E.sum_star_mul_map_mul_nonneg Finset.univ (R l) x

theorem map_cstarMatrix_nonneg (E : CStarConditionalExpectation ι) {n : Type*} [Fintype n]
    (M : CStarMatrix n n A) (hM : 0 ≤ M) : 0 ≤ M.map E :=
  CompletelyPositiveMap.map_cstarMatrix_nonneg (E : A →CP B) M hM

end TauCeti.CStarConditionalExpectation

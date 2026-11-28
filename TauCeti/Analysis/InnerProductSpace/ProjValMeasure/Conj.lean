/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.ProjValMeasure.Integral

/-!
# Unitary conjugation of projection-valued measures

A linear isometric equivalence `U : H ≃ₗᵢ[ℂ] H'` transports a projection-valued measure `P` on `H`
to a projection-valued measure `P.conj U` on `H'`, with projections `U P(B) U*` and diagonal
measures `ξ ↦ P.diag (U.symm ξ)`. Conjugation respects identity, inverses, and composition, and
commutes with the bounded Borel integral:
`(P.conj U).integral f = U.conjStarAlgEquiv (P.integral f)`.
-/

public section

open MeasureTheory
open scoped InnerProductSpace

namespace TauCeti.ProjValMeasure

variable {X : Type*} [MeasurableSpace X]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']

/-- Transport a projection-valued measure along a linear isometric equivalence `U : H ≃ₗᵢ[ℂ] H'`. -/
noncomputable def conj (P : ProjValMeasure X H) (U : H ≃ₗᵢ[ℂ] H') : ProjValMeasure X H' where
  proj B hB := U.conjStarAlgEquiv (P.proj B hB)
  diag ξ := P.diag (U.symm ξ)
  diag_finite ξ := P.diag_finite (U.symm ξ)
  inner_proj B hB ξ := by
    have hinner : ⟪ξ, U (P.proj B hB (U.symm ξ))⟫_ℂ = ⟪U.symm ξ, P.proj B hB (U.symm ξ)⟫_ℂ := by
      simpa only [U.apply_symm_apply] using U.inner_map_map (U.symm ξ) (P.proj B hB (U.symm ξ))
    rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, hinner]
    exact P.inner_proj B hB (U.symm ξ)
  proj_univ := by
    rw [P.proj_univ, ← ContinuousLinearMap.one_def, map_one, ContinuousLinearMap.one_def]
  proj_inter B₁ B₂ hB₁ hB₂ := by
    rw [← map_mul, P.proj_inter]

/-- Evaluating the conjugated PVM on a measurable set conjugates the projection by `U`. -/
@[simp]
theorem conj_proj (P : ProjValMeasure X H) (U : H ≃ₗᵢ[ℂ] H') (B : Set X) (hB : MeasurableSet B) :
    (P.conj U).proj B hB = U.conjStarAlgEquiv (P.proj B hB) := by rfl

/-- Diagonal scalar measures of the conjugated PVM pull back along `U.symm`. -/
@[simp]
theorem conj_diag (P : ProjValMeasure X H) (U : H ≃ₗᵢ[ℂ] H') (ξ : H') :
    (P.conj U).diag ξ = P.diag (U.symm ξ) := by rfl

/-- Conjugation by the identity unitary leaves the PVM unchanged. -/
@[simp]
theorem conj_refl (P : ProjValMeasure X H) :
    P.conj (LinearIsometryEquiv.refl ℂ H) = P := by
  ext B hB
  simp

/-- Conjugating by `U` and then by `U.symm` recovers the original PVM. -/
@[simp]
theorem conj_conj_symm (P : ProjValMeasure X H) (U : H ≃ₗᵢ[ℂ] H') :
    (P.conj U).conj U.symm = P := by
  ext B hB
  simp [← LinearIsometryEquiv.symm_conjStarAlgEquiv]

/-- Conjugating by `U.symm` and then by `U` recovers the original PVM. -/
@[simp]
theorem conj_symm_conj (P : ProjValMeasure X H) (U : H' ≃ₗᵢ[ℂ] H) :
    (P.conj U.symm).conj U = P := by
  simpa using P.conj_conj_symm U.symm

/-- Conjugating by `U` and then by `V` equals conjugating by `U.trans V`. -/
theorem conj_trans {H'' : Type*} [NormedAddCommGroup H''] [InnerProductSpace ℂ H'']
    [CompleteSpace H''] (P : ProjValMeasure X H) (U : H ≃ₗᵢ[ℂ] H') (V : H' ≃ₗᵢ[ℂ] H'') :
    (P.conj U).conj V = P.conj (U.trans V) := by
  ext B hB x
  simp [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply]

/-- Unitary conjugation commutes with bounded Borel integrals against a PVM. -/
theorem integral_conj (P : ProjValMeasure X H) (U : H ≃ₗᵢ[ℂ] H') (f : BoundedBorelFunction X) :
    (P.conj U).integral f = U.conjStarAlgEquiv (P.integral f) := by
  have hcont : Continuous (fun g : BoundedBorelFunction X ↦ U.conjStarAlgEquiv (P.integral g)) := by
    simp only [LinearIsometryEquiv.conjStarAlgEquiv_apply]
    exact continuous_const.clm_comp (P.continuous_integral.clm_comp continuous_const)
  refine congrFun (ProjValMeasure.eq_integral_of_continuous _ hcont fun s ↦ ?_).symm f
  simp only [ProjValMeasure.integral_ofSimpleFunc, map_sum]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [_root_.map_smul, conj_proj]

end TauCeti.ProjValMeasure

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fourier.Hardy.Toeplitz

/-!
# Hankel operators and Toeplitz products

The Hankel operator of a bounded circle symbol is multiplication followed by projection onto
the actual orthogonal complement of boundary Hardy space. Together with the Toeplitz
compression, it gives the orthogonal decomposition of multiplication on Hardy functions.

The identity `toeplitz_comp_sub_toeplitz` expresses the defect of multiplicativity of Toeplitz
compression as a product of Hankel operators. The Fourier characterization `hankel_eq_zero_iff`
then gives exact multiplication when the right symbol is analytic or the left symbol is
coanalytic. This is the algebraic input to compactness of continuous-symbol semicommutators.

The construction uses Mathlib's orthogonal projections and the existing `Lp.multiplicationOperator`.
The conventions and product identity follow Conway, *A Course in Functional Analysis*, second
edition, and E. Park, *Toeplitz operators*.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace TauCeti

private theorem norm_compress_hankel_le (a : Lp ℂ ∞ (AddCircle.haarAddCircle (T := 1))) :
    ‖hardySubmoduleᗮ.orthogonalProjectionOnto ∘L Lp.multiplicationOperator a ∘L
      hardySubmodule.subtypeL‖ ≤ ‖a‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro f
  exact (hardySubmoduleᗮ.norm_orthogonalProjectionOnto_apply_le _).trans
    (Lp.norm_multiplicationOperator_apply_le a f.val)

/-- The Hankel symbol map `H_a = (1 - P) M_a |H²`, with the orthogonal complement of Hardy
space as codomain. -/
def hankel : Lp ℂ ∞ (AddCircle.haarAddCircle (T := 1)) →L[ℂ]
    HardySpace →L[ℂ] ↥hardySubmoduleᗮ :=
  LinearMap.mkContinuous
    { toFun a := hardySubmoduleᗮ.orthogonalProjectionOnto ∘L Lp.multiplicationOperator a ∘L
        hardySubmodule.subtypeL
      map_add' a b := by
        simp only [Lp.multiplicationOperator_add, ContinuousLinearMap.add_comp,
          ContinuousLinearMap.comp_add]
      map_smul' c a := by
        simp only [Lp.multiplicationOperator_smul, ContinuousLinearMap.smul_comp,
          ContinuousLinearMap.comp_smul, RingHom.id_apply] }
    1 fun a ↦ (one_mul ‖a‖).symm ▸ norm_compress_hankel_le a

/-- The Hankel operator projects multiplication onto the negative Fourier modes. -/
theorem hankel_apply (a : Lp ℂ ∞ (AddCircle.haarAddCircle (T := 1))) :
    hankel a = hardySubmoduleᗮ.orthogonalProjectionOnto ∘L
      Lp.multiplicationOperator a ∘L hardySubmodule.subtypeL :=
  (rfl)

/-- The ambient value of a Hankel operator is the complementary Hardy projection. -/
theorem coe_hankel_apply (a : Lp ℂ ∞ (AddCircle.haarAddCircle (T := 1))) (f : HardySpace) :
    (hankel a f : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))) =
      a • (f : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))) -
        hardySubmodule.starProjection
          (a • (f : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1)))) := by
  rw [hankel_apply]
  simp only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
    ← Submodule.starProjection_apply, Submodule.starProjection_orthogonal_val,
    Lp.multiplicationOperator_apply]

/-- Multiplication of a Hardy function splits into its Toeplitz and Hankel parts. -/
theorem coe_toeplitz_add_coe_hankel
    (a : Lp ℂ ∞ (AddCircle.haarAddCircle (T := 1))) (f : HardySpace) :
    (toeplitz a f : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))) +
      (hankel a f : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))) =
        a • (f : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))) := by
  rw [coe_toeplitz_apply, coe_hankel_apply]
  exact add_sub_cancel _ _

/-- Hankel compression does not increase the norm of the symbol. -/
theorem norm_hankel_le (a : Lp ℂ ∞ (AddCircle.haarAddCircle (T := 1))) :
    ‖hankel a‖ ≤ ‖a‖ :=
  norm_compress_hankel_le a

/-- A constant symbol has zero Hankel operator. -/
@[simp]
theorem hankel_const (c : ℂ) :
    hankel (Lp.const ∞ (AddCircle.haarAddCircle (T := 1)) c) = 0 := by
  ext f : 1
  rw [hankel_apply]
  simp only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
    Lp.multiplicationOperator_const, smul_apply,
    ContinuousLinearMap.id_apply, zero_apply]
  exact Submodule.orthogonalProjectionOnto_orthogonal_apply_eq_zero
    (hardySubmodule.smul_mem c f.property)

/-- The adjoint of `H_a` multiplies negative-mode functions by the conjugate symbol and
projects back to Hardy space. -/
theorem adjoint_hankel (a : Lp ℂ ∞ (AddCircle.haarAddCircle (T := 1))) :
    ContinuousLinearMap.adjoint (hankel a) = hardySubmodule.orthogonalProjectionOnto ∘L
      Lp.multiplicationOperator (star a) ∘L hardySubmoduleᗮ.subtypeL := by
  simp only [hankel_apply, ContinuousLinearMap.adjoint_comp,
    Submodule.adjoint_subtypeL, Submodule.adjoint_orthogonalProjectionOnto,
    Lp.adjoint_multiplicationOperator, ContinuousLinearMap.comp_assoc]

/-- **Toeplitz semicommutator identity.** The defect of multiplication is minus the product
of the adjoint Hankel operator of the conjugate left symbol with the right Hankel operator. -/
theorem toeplitz_comp_sub_toeplitz
    (a b : Lp ℂ ∞ (AddCircle.haarAddCircle (T := 1))) :
    toeplitz a ∘L toeplitz b - toeplitz (a • b : Lp ℂ ∞ (AddCircle.haarAddCircle (T := 1))) =
      -(ContinuousLinearMap.adjoint (hankel (star a)) ∘L hankel b) := by
  ext f : 1
  apply Subtype.ext
  have hmul := congrArg (fun M => M (f : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))))
    (Lp.multiplicationOperator_comp_multiplicationOperator (E := ℂ) a b)
  simp only [ContinuousLinearMap.comp_apply, Lp.multiplicationOperator_apply] at hmul
  simp only [ContinuousLinearMap.comp_apply, sub_apply, neg_apply, Submodule.coe_sub,
    Submodule.coe_neg, coe_toeplitz_apply, adjoint_hankel, star_star,
    Submodule.subtypeL_apply, Submodule.coe_orthogonalProjectionOnto_apply,
    Lp.multiplicationOperator_apply, coe_hankel_apply]
  rw [← hmul]
  -- Use the linear multiplier API to distribute the heterogeneous L∞ action on L².
  simp only [← Lp.multiplicationOperator_apply, map_sub]
  abel

/-- A Hankel operator vanishes exactly when its symbol has no negative Fourier coefficients. -/
theorem hankel_eq_zero_iff (a : Lp ℂ ∞ (AddCircle.haarAddCircle (T := 1))) :
    hankel a = 0 ↔ ∀ n : ℤ, n < 0 → fourierCoeff a n = 0 := by
  constructor
  · intro ha n hn
    have hzero := congrArg (fun H => H (hardyBasis 0)) ha
    rw [hankel_apply] at hzero
    simp only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
      Lp.multiplicationOperator_apply, zero_apply,
      Submodule.orthogonalProjectionOnto_eq_zero_iff, Submodule.orthogonal_orthogonal] at hzero
    have := (mem_hardySubmodule_iff _).mp hzero n hn
    simpa only [coe_hardyBasis, Nat.cast_zero, fourierCoeff_smul_fourierBasis, sub_zero]
      using this
  · intro ha
    apply ContinuousLinearMap.ext_on
      (s := Set.range hardyBasis) (by
        rw [dense_iff_closure_eq, ← Submodule.topologicalClosure_coe,
          hardyBasis.dense_span]
        rfl)
    rintro _ ⟨j, rfl⟩
    rw [hankel_apply]
    simp only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
      Lp.multiplicationOperator_apply, zero_apply,
      Submodule.orthogonalProjectionOnto_eq_zero_iff, Submodule.orthogonal_orthogonal]
    apply (mem_hardySubmodule_iff _).mpr
    intro n hn
    rw [coe_hardyBasis, fourierCoeff_smul_fourierBasis]
    exact ha _ (by omega)

/-- Toeplitz multiplication is exact when the right symbol has no negative Fourier modes. -/
theorem toeplitz_comp_of_analytic
    (a b : Lp ℂ ∞ (AddCircle.haarAddCircle (T := 1)))
    (hb : ∀ n : ℤ, n < 0 → fourierCoeff b n = 0) :
    toeplitz a ∘L toeplitz b =
      toeplitz (a • b : Lp ℂ ∞ (AddCircle.haarAddCircle (T := 1))) := by
  have h := toeplitz_comp_sub_toeplitz a b
  rw [(hankel_eq_zero_iff b).mpr hb, ContinuousLinearMap.comp_zero] at h
  ext f : 1
  have hf := congrArg (fun T => T f) h
  simpa only [sub_apply, neg_apply, zero_apply, neg_zero, sub_eq_zero] using hf

/-- Toeplitz multiplication is exact when the conjugate left symbol is analytic, that is,
when the left symbol is coanalytic. -/
theorem toeplitz_comp_of_coanalytic
    (a b : Lp ℂ ∞ (AddCircle.haarAddCircle (T := 1)))
    (ha : ∀ n : ℤ, n < 0 →
      fourierCoeff (star a : Lp ℂ ∞ (AddCircle.haarAddCircle (T := 1))) n = 0) :
    toeplitz a ∘L toeplitz b =
      toeplitz (a • b : Lp ℂ ∞ (AddCircle.haarAddCircle (T := 1))) := by
  have h := toeplitz_comp_sub_toeplitz a b
  rw [(hankel_eq_zero_iff (star a)).mpr ha,
    ContinuousLinearMap.adjoint.map_zero, ContinuousLinearMap.zero_comp] at h
  ext f : 1
  have hf := congrArg (fun T => T f) h
  simpa only [sub_apply, neg_apply, zero_apply, neg_zero, sub_eq_zero] using hf

end TauCeti

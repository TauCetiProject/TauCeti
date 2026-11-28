/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fourier.StationaryPhase.SplitQuadratic
import TauCeti.MeasureTheory.Measure.Lebesgue.Complex

/-! # Quadratic stationary phase on a complex vector space -/

public section

open MeasureTheory
open scoped FourierTransform RealInnerProductSpace

namespace TauCeti

universe u

private noncomputable def splitCoordinates (n : ℕ) :
    (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) ≃L[ℝ] (Fin n → ℂ) :=
  ((EuclideanSpace.equiv (Fin n) ℝ).prodCongr (EuclideanSpace.equiv (Fin n) ℝ)).trans
    ((show ((Fin n → ℝ) × (Fin n → ℝ)) ≃ₗ[ℝ] (Fin n → ℝ × ℝ) from
      { (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin n)).symm.toEquiv with
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }).toContinuousLinearEquiv.trans
      (ContinuousLinearEquiv.piCongrRight fun _ ↦ Complex.equivRealProdCLM.symm))

private theorem splitCoordinates_apply (n : ℕ)
    (p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    splitCoordinates n p i = ⟨p.1 i, p.2 i⟩ := rfl

private theorem measurePreserving_splitCoordinates (n : ℕ) :
    MeasurePreserving (splitCoordinates n) volume volume := by
  have h₁ := (PiLp.volume_preserving_ofLp (Fin n)).prod (PiLp.volume_preserving_ofLp (Fin n))
  have h₂ := (volume_measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin n)).symm
  have h₃ := volume_preserving_pi fun _ : Fin n ↦ Complex.measurePreserving_equivRealProdCLM_symm
  exact h₃.comp (h₂.comp h₁)

private theorem re_neg_I_sum_sq (n : ℕ)
    (p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :
    ((-Complex.I / 2) * ∑ i : Fin n, (⟨p.1 i, p.2 i⟩ : ℂ) ^ 2).re = ⟪p.2, p.1⟫ := by
  rw [Finset.mul_sum]
  change Complex.reAddGroupHom (∑ i : Fin n, _) = _
  rw [map_sum]
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  simp [pow_two, Complex.mul_re, Complex.mul_im]
  ring

/-- The quadratic estimate is uniform under complex coordinate changes with bounded operator
norms in both directions. The real Jacobian multiplies the original integral. -/
theorem exists_norm_integral_sum_sq_sub_le (n : ℕ) (R A : ℝ) :
    ∃ C : ℝ, ∀ (L : (Fin n → ℂ) ≃L[ℂ] (Fin n → ℂ)),
      ‖L.toContinuousLinearMap‖ ≤ A → ‖L.symm.toContinuousLinearMap‖ ≤ A →
      ∀ (V : Type u) [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
        (a : (Fin n → ℂ) → V) (S : ℝ),
        ContDiff ℝ (n + 3 : ℕ) a → tsupport a ⊆ Metric.closedBall 0 R →
        (∀ j ≤ n + 3, ∀ z, ‖iteratedFDeriv ℝ j a z‖ ≤ S) →
        ∀ s : ℝ, s ≠ 0 →
          ‖LinearMap.det (L.toLinearEquiv.toLinearMap.restrictScalars ℝ) •
                (∫ z, Complex.exp (Complex.I *
                  ((((-Complex.I / 2) * ∑ i, (L z i) ^ 2).re / s : ℝ) : ℂ)) • a z) -
            (2 * Real.pi * |s|) ^ n • a 0‖ ≤ C * S * |s| ^ (n + 1) := by
  let J := splitCoordinates n
  let R' := ‖J.symm.toContinuousLinearMap‖ * A * R
  set M := max 1 (A * ‖J.toContinuousLinearMap‖)
  obtain ⟨C, hC⟩ :=
    exists_norm_integral_splitQuadratic_sub_le.{u} (E := EuclideanSpace ℝ (Fin n)) R'
  rw [finrank_euclideanSpace_fin] at hC
  refine ⟨C * M ^ (n + 3) * (2 * Real.pi) ^ (n + 1), ?_⟩
  intro L hL hLinv V _ _ _ a S ha hsupp hS s hs
  let T := J.trans (L.symm.restrictScalars ℝ)
  let F := (L.restrictScalars ℝ).trans J.symm
  let b : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → V := a ∘ T
  have hS₀ : 0 ≤ S := (norm_nonneg _).trans (hS 0 (by omega) 0)
  have hT : ‖T.toContinuousLinearMap‖ ≤ M := by
    refine (ContinuousLinearMap.opNorm_comp_le (L.symm.toContinuousLinearMap.restrictScalars ℝ)
      J.toContinuousLinearMap).trans ?_
    change ‖L.symm.toContinuousLinearMap.restrictScalars ℝ‖ * ‖J.toContinuousLinearMap‖ ≤ M
    rw [ContinuousLinearMap.norm_restrictScalars]
    exact (mul_le_mul_of_nonneg_right hLinv (norm_nonneg _)).trans (le_max_right ..)
  have hbs : tsupport b ⊆ Metric.closedBall 0 R' := by
    refine closure_minimal (fun p hp ↦ ?_) Metric.isClosed_closedBall
    have haz : a (T p) ≠ 0 := hp
    have hz := hsupp (subset_tsupport a haz)
    rw [Metric.mem_closedBall, dist_zero_right] at hz ⊢
    have hid : F (T p) = p := by
      simp [F, T]
    rw [← hid]
    have hF : ‖F.toContinuousLinearMap‖ ≤ ‖J.symm.toContinuousLinearMap‖ * A := by
      refine (ContinuousLinearMap.opNorm_comp_le J.symm.toContinuousLinearMap
        (L.toContinuousLinearMap.restrictScalars ℝ)).trans ?_
      change ‖J.symm.toContinuousLinearMap‖ * ‖L.toContinuousLinearMap.restrictScalars ℝ‖ ≤ _
      rw [ContinuousLinearMap.norm_restrictScalars]
      exact mul_le_mul_of_nonneg_left hL (norm_nonneg _)
    exact (F.toContinuousLinearMap.le_opNorm _).trans
      (mul_le_mul hF hz (norm_nonneg _) ((norm_nonneg _).trans hF))
  have hb : ContDiff ℝ (n + 3 : ℕ) b := ha.comp T.toContinuousLinearMap.contDiff
  have hbS (j : ℕ) (hj : j ≤ n + 3) (p) :
      ‖iteratedFDeriv ℝ j b p‖ ≤ S * M ^ (n + 3) := by
    change ‖iteratedFDeriv ℝ j (a ∘ T.toContinuousLinearMap) p‖ ≤ _
    rw [T.toContinuousLinearMap.iteratedFDeriv_comp_right ha p (by exact_mod_cast hj)]
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact mul_le_mul (hS j hj _) ((pow_le_pow_left₀ (norm_nonneg _) hT j).trans
      (pow_le_pow_right₀ (le_max_left ..) hj)) (by positivity) hS₀
  let σ := -(2 * Real.pi * s)
  have hσ : σ ≠ 0 := neg_ne_zero.mpr (mul_ne_zero (by positivity) hs)
  have hσabs : |σ| = 2 * Real.pi * |s| := by
    rw [abs_neg, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * Real.pi)]
  have heq (p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :
      (𝐞 (-⟪p.2, σ⁻¹ • p.1⟫) : ℂ) =
        Complex.exp (Complex.I * ((((-Complex.I / 2) *
          ∑ i, (J p i) ^ 2).re / s : ℝ) : ℂ)) := by
    rw [Real.fourierChar_apply, real_inner_smul_right]
    have hre : ((-Complex.I / 2) * ∑ i, (J p i) ^ 2).re = ⟪p.2, p.1⟫ := by
      simpa only [J, splitCoordinates_apply] using re_neg_I_sum_sq n p
    rw [hre, mul_comm Complex.I]
    suffices 2 * Real.pi * -(σ⁻¹ * ⟪p.2, p.1⟫) = ⟪p.2, p.1⟫ / s by
      rw [this]
    dsimp [σ]
    field_simp
  let f : (Fin n → ℂ) → V := fun z ↦ Complex.exp (Complex.I *
    ((((-Complex.I / 2) * ∑ i, z i ^ 2).re / s : ℝ) : ℂ)) • a (L.symm z)
  let D := LinearMap.det (L.toLinearEquiv.toLinearMap.restrictScalars ℝ)
  have hD : 0 < D := by
    rw [show D = _ from LinearMap.det_restrictScalars_eq_normSq _]
    rw [← LinearEquiv.coe_det]
    exact Complex.normSq_pos.mpr (LinearEquiv.det L.toLinearEquiv).ne_zero
  have hmap : Measure.map (L : (Fin n → ℂ) → (Fin n → ℂ)) volume =
      ENNReal.ofReal D⁻¹ • volume := by
    have h := Measure.map_linearMap_addHaar_eq_smul_addHaar volume
      (f := L.toLinearEquiv.toLinearMap.restrictScalars ℝ) hD.ne'
    simpa [D, abs_of_pos (inv_pos.mpr hD)] using h
  have hchange : (∫ z, f z) = D • ∫ z, f (L z) := by
    have hi := L.toHomeomorph.toMeasurableEquiv.measurableEmbedding.integral_map (μ := volume) f
    change (∫ z, f z ∂Measure.map (L : (Fin n → ℂ) → (Fin n → ℂ)) volume) =
      ∫ z, f (L z) at hi
    rw [hmap, integral_smul_measure, ENNReal.toReal_ofReal (inv_nonneg.mpr hD.le)] at hi
    rw [← hi, smul_smul, mul_inv_cancel₀ hD.ne', one_smul]
  have hi : (∫ p, 𝐞 (-⟪p.2, σ⁻¹ • p.1⟫) • b p) = ∫ z, f z := by
    have hmp : MeasurePreserving (⇑J.toHomeomorph.toMeasurableEquiv) volume volume :=
      measurePreserving_splitCoordinates n
    rw [← hmp.integral_comp' f]
    refine integral_congr_ae (Filter.Eventually.of_forall fun p ↦ ?_)
    change (𝐞 (-⟪p.2, σ⁻¹ • p.1⟫) : ℂ) • b p = f (J p)
    rw [heq]
    rfl
  have h := hC V b (S * M ^ (n + 3)) hb hbs hbS σ hσ
  rw [hi, hchange, hσabs] at h
  convert h using 1
  · have hzero : b (0, 0) = a 0 := by
      change a (T 0) = a 0
      rw [map_zero]
    simp [f, hzero, D]
  · rw [mul_pow]
    ring

end TauCeti

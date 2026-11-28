/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.Inversion
import TauCeti.Analysis.Fourier.Decay

/-!
# Stationary phase for the split quadratic form

Partial Fourier inversion gives the leading term for the phase `⟪y, x⟫`.
-/

public section

open MeasureTheory Set
open scoped ContDiff FourierTransform Real RealInnerProductSpace

namespace TauCeti

universe u

variable {E : Type*} {V : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℂ V]

private theorem iteratedFDeriv_slice {a : E × E → V} {N j : ℕ} (ha : ContDiff ℝ N a)
    (hj : j ≤ N) (x y : E) :
    iteratedFDeriv ℝ j (fun z ↦ a (x, z)) y =
      (iteratedFDeriv ℝ j a (x, y)).compContinuousLinearMap
        (fun _ ↦ ContinuousLinearMap.inr ℝ E E) := by
  let L := ContinuousLinearMap.inr ℝ E E
  have heq : (fun z ↦ a (x, z)) = (fun q ↦ a ((x, 0) + q)) ∘ L := by
    funext z
    simp [L]
  have htranslate : ContDiff ℝ N (fun q ↦ a ((x, 0) + q)) :=
    ha.comp (contDiff_const.add contDiff_id)
  rw [heq, L.iteratedFDeriv_comp_right htranslate y
    (by exact_mod_cast hj), iteratedFDeriv_comp_add_left]
  simp [L]

private theorem norm_iteratedFDeriv_slice_sub_le {a : E × E → V} {N j : ℕ}
    (ha : ContDiff ℝ (N + 1 : ℕ) a) {S : ℝ}
    (hS : ∀ i ≤ N + 1, ∀ p, ‖iteratedFDeriv ℝ i a p‖ ≤ S) (hj : j ≤ N) (x y : E) :
    ‖iteratedFDeriv ℝ j (fun z ↦ a (x, z) - a (0, z)) y‖ ≤ S * ‖x‖ := by
  have hs (w : E) : ContDiff ℝ j (fun z ↦ a (w, z)) :=
    (ha.of_le (by exact_mod_cast (show j ≤ N + 1 by omega))).comp
      (contDiff_const.prodMk contDiff_id)
  change ‖iteratedFDeriv ℝ j ((fun z ↦ a (x, z)) - (fun z ↦ a (0, z))) y‖ ≤ S * ‖x‖
  rw [iteratedFDeriv_sub_apply (hs x).contDiffAt (hs 0).contDiffAt,
    iteratedFDeriv_slice ha (by omega), iteratedFDeriv_slice ha (by omega)]
  rw [show (iteratedFDeriv ℝ j a (x, y)).compContinuousLinearMap
        (fun _ ↦ ContinuousLinearMap.inr ℝ E E) -
      (iteratedFDeriv ℝ j a (0, y)).compContinuousLinearMap
        (fun _ ↦ ContinuousLinearMap.inr ℝ E E) = ContinuousMultilinearMap.compContinuousLinearMap
      (iteratedFDeriv ℝ j a (x, y) - iteratedFDeriv ℝ j a (0, y))
      (fun _ ↦ ContinuousLinearMap.inr ℝ E E) by
    ext m
    rfl]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have hp : (∏ _i : Fin j, ‖ContinuousLinearMap.inr ℝ E E‖) ≤ 1 := by
    simpa using pow_le_one₀ (norm_nonneg (ContinuousLinearMap.inr ℝ E E))
      (ContinuousLinearMap.norm_inr_le_one ℝ E E) (n := j)
  refine (mul_le_of_le_one_right (norm_nonneg _) hp).trans ?_
  have hd : Differentiable ℝ (iteratedFDeriv ℝ j a) :=
    ha.differentiable_iteratedFDeriv (by exact_mod_cast (show j < N + 1 by omega))
  simpa using Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (s := univ)
    (fun p _ ↦ hd p) (fun p _ ↦ by rw [norm_fderiv_iteratedFDeriv]; exact hS _ (by omega) p)
    convex_univ (mem_univ (0, y)) (mem_univ (x, y))

omit [InnerProductSpace ℝ E] [NormedSpace ℂ V] in
private theorem tsupport_slice_subset {a : E × E → V} {R : ℝ}
    (ha : tsupport a ⊆ Metric.closedBall 0 R) (x : E) :
    tsupport (fun y ↦ a (x, y)) ⊆ Metric.closedBall 0 R := by
  refine closure_minimal ?_ Metric.isClosed_closedBall
  intro y hy
  have h := ha (subset_tsupport a (show (x, y) ∈ Function.support a from hy))
  rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def] at h
  exact Metric.mem_closedBall.mpr (by simpa using (le_max_right ‖x‖ ‖y‖).trans h)

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [NormedSpace ℂ V] in
private theorem integrable_slice {a : E × E → V} {R : ℝ}
    (ha : Continuous a) (hc : tsupport a ⊆ Metric.closedBall 0 R) (x : E) :
    Integrable (fun y ↦ a (x, y)) :=
  (ha.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall 0 R)
      ((subset_tsupport _).trans (tsupport_slice_subset hc x)))

private theorem integrable_fourier_slice_zero {a : E × E → V} {R S : ℝ} {N : ℕ}
    (hN : Module.finrank ℝ E < N) (ha : ContDiff ℝ N a)
    (hc : tsupport a ⊆ Metric.closedBall 0 R)
    (hS : ∀ i ≤ N, ∀ p, ‖iteratedFDeriv ℝ i a p‖ ≤ S) :
    Integrable (𝓕 (fun y ↦ a (0, y))) := by
  let f : E → V := fun y ↦ a (0, y)
  have hf : ContDiff ℝ N f := ha.comp (contDiff_const.prodMk contDiff_id)
  have hfc := tsupport_slice_subset hc 0
  have hfi : Integrable f := integrable_slice ha.continuous hc 0
  have hpow := integrable_one_add_norm (μ := (volume : Measure E))
    (by exact_mod_cast hN : (Module.finrank ℝ E : ℝ) < (N : ℝ))
  refine (hpow.const_mul (2 ^ N * (S * volume.real (Metric.closedBall (0 : E) R)))).mono'
    (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hfi).aestronglyMeasurable (ae_of_all _ fun w ↦ ?_)
  have h := one_add_norm_pow_mul_norm_fourier_le_of_tsupport_subset hf
    (isCompact_closedBall 0 R).measure_ne_top hfc (C := S) (fun j hj y ↦ ?_) w
  · rw [Real.rpow_neg (by positivity), Real.rpow_natCast, ← div_eq_mul_inv]
    exact (le_div_iff₀ (by positivity)).2 (by simpa [mul_comm] using h)
  · rw [iteratedFDeriv_slice ha hj]
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
      (mul_le_of_le_one_right (norm_nonneg (iteratedFDeriv ℝ j a (0, y)))
        (pow_le_one₀ (norm_nonneg _) (ContinuousLinearMap.norm_inr_le_one ℝ E E))).trans (hS j hj _)

private theorem fourier_slice_sub_bound {a : E × E → V} {R S : ℝ} {N : ℕ}
    (ha : ContDiff ℝ (N + 1 : ℕ) a) (hc : tsupport a ⊆ Metric.closedBall 0 R)
    (hS : ∀ i ≤ N + 1, ∀ p, ‖iteratedFDeriv ℝ i a p‖ ≤ S) (x w : E) :
    (1 + ‖w‖) ^ N * ‖𝓕 (fun y ↦ a (x, y)) w - 𝓕 (fun y ↦ a (0, y)) w‖ ≤
      2 ^ N * (S * ‖x‖ * volume.real (Metric.closedBall (0 : E) R)) := by
  let f : E → V := fun y ↦ a (x, y) - a (0, y)
  have hs (u : E) : ContDiff ℝ N (fun z ↦ a (u, z)) :=
    (ha.of_le (by norm_cast; omega)).comp (contDiff_const.prodMk contDiff_id)
  have hfc : tsupport f ⊆ Metric.closedBall 0 R := by
    refine closure_minimal (fun y hy ↦ ?_) Metric.isClosed_closedBall
    by_contra h
    have hz (u : E) : a (u, y) = 0 :=
      image_eq_zero_of_notMem_tsupport (f := fun z ↦ a (u, z))
        (fun hx ↦ h (tsupport_slice_subset hc u hx))
    exact hy (by simp [f, hz])
  have h := one_add_norm_pow_mul_norm_fourier_le_of_tsupport_subset
    (f := f) ((hs x).sub (hs 0)) (isCompact_closedBall 0 R).measure_ne_top hfc
    (fun j hj y ↦ norm_iteratedFDeriv_slice_sub_le ha hS hj x y) w
  have heq : 𝓕 f w = 𝓕 (fun y ↦ a (x, y)) w - 𝓕 (fun y ↦ a (0, y)) w := by
    rw [Real.fourier_eq, Real.fourier_eq, Real.fourier_eq, ← integral_sub]
    · simp [f, smul_sub]
    · exact ((Real.fourierIntegral_convergent_iff' (innerSL ℝ) _).2
        (integrable_slice ha.continuous hc x))
    · exact ((Real.fourierIntegral_convergent_iff' (innerSL ℝ) _).2
        (integrable_slice ha.continuous hc 0))
  exact heq ▸ h

private theorem norm_fourier_slice_scaled_sub_le {a : E × E → V} {R S : ℝ} {d : ℕ}
    (ha : ContDiff ℝ (d + 3 : ℕ) a) (hc : tsupport a ⊆ Metric.closedBall 0 R)
    (hS : ∀ i ≤ d + 3, ∀ p, ‖iteratedFDeriv ℝ i a p‖ ≤ S) (s : ℝ) (w : E) :
    ‖𝓕 (fun y ↦ a (s • w, y)) w - 𝓕 (fun y ↦ a (0, y)) w‖ ≤
      2 ^ (d + 2) * volume.real (Metric.closedBall (0 : E) R) * S * |s| *
        (1 + ‖w‖) ^ (-(d + 1 : ℝ)) := by
  have h := fourier_slice_sub_bound (N := d + 2) ha hc hS (s • w) w
  rw [norm_smul, Real.norm_eq_abs] at h
  have hp : 0 < 1 + ‖w‖ := by positivity
  rw [Real.rpow_neg hp.le, show (d + 1 : ℝ) = ((d + 1 : ℕ) : ℝ) by simp,
    Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ (pow_pos hp _)]
  have hS₀ := (norm_nonneg (iteratedFDeriv ℝ 0 a 0)).trans (hS 0 (by omega) 0)
  set A := ‖𝓕 (fun y ↦ a (s • w, y)) w - 𝓕 (fun y ↦ a (0, y)) w‖
  set K := 2 ^ (d + 2) * volume.real (Metric.closedBall (0 : E) R) * S * |s|
  apply (mul_le_mul_iff_of_pos_right hp).mp
  calc
    _ = (1 + ‖w‖) ^ (d + 2) * A := by rw [show d + 2 = d + 1 + 1 by omega, pow_succ]; ring
    _ ≤ 2 ^ (d + 2) * (S * (|s| * ‖w‖) * volume.real (Metric.closedBall (0 : E) R)) := h
    _ = K * ‖w‖ := by simp only [K]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)

/-- The leading-term stationary-phase estimate for the split pairing. Partial Fourier inversion
uses only `dim E + 3` derivatives of the amplitude and works for Banach-valued amplitudes. -/
theorem exists_norm_integral_splitQuadratic_sub_le (R : ℝ) :
    ∃ C : ℝ, ∀ (V : Type u) [NormedAddCommGroup V] [NormedSpace ℂ V]
      [CompleteSpace V] (a : E × E → V) (S : ℝ),
      ContDiff ℝ (Module.finrank ℝ E + 3 : ℕ) a →
      tsupport a ⊆ Metric.closedBall 0 R →
      (∀ j ≤ Module.finrank ℝ E + 3, ∀ p, ‖iteratedFDeriv ℝ j a p‖ ≤ S) →
      ∀ s : ℝ, s ≠ 0 →
        ‖(∫ p, 𝐞 (-⟪p.2, s⁻¹ • p.1⟫) • a p) -
            |s| ^ Module.finrank ℝ E • a (0, 0)‖ ≤ C * S * |s| ^ (Module.finrank ℝ E + 1) := by
  let d := Module.finrank ℝ E
  let N := d + 2
  let weight (w : E) : ℝ := (1 + ‖w‖) ^ (-(d + 1 : ℝ))
  have hw : Integrable weight := integrable_one_add_norm (by dsimp [d]; linarith)
  let K := 2 ^ N * volume.real (Metric.closedBall (0 : E) R)
  refine ⟨K * ∫ w, weight w, ?_⟩
  intro V _ _ _ a S ha hc hS s hs
  have ha' : ContDiff ℝ N a := ha.of_le (by exact_mod_cast (show N ≤ d + 3 by omega))
  let f (w : E) : V := 𝓕 (fun y ↦ a (0, y)) w
  let g (x : E) : V := 𝓕 (fun y ↦ a (x, y)) (s⁻¹ • x)
  have hfi : Integrable f := integrable_fourier_slice_zero
    (show d < N by omega) ha' hc (fun j hj ↦ hS j (by omega))
  have hf : ∫ w, f w = a (0, 0) := by
    have hfcont : Continuous (fun y ↦ a (0, y)) :=
      ha.continuous.comp (continuous_const.prodMk continuous_id)
    have h := congrFun (hfcont.fourierInv_fourier_eq (integrable_slice ha.continuous hc 0) hfi) 0
    simpa [Real.fourierInv_eq, f] using h
  have hai : Integrable (fun p ↦ 𝐞 (-⟪p.2, s⁻¹ • p.1⟫) • a p) := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact (Real.continuous_fourierChar.comp (by fun_prop)).smul ha.continuous
    · refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall 0 R) ?_
      exact (Function.support_smul_subset_right _ _).trans ((subset_tsupport a).trans hc)
  have hg : Integrable g := by
    simpa only [g, Real.fourier_eq] using hai.integral_prod_left
  have heq (w : E) : g (s • w) = 𝓕 (fun y ↦ a (s • w, y)) w := by
    change 𝓕 (fun y ↦ a (s • w, y)) (s⁻¹ • s • w) = _
    rw [inv_smul_smul₀ hs]
  have hb (w : E) : ‖g (s • w) - f w‖ ≤ K * S * |s| * weight w := by
    rw [heq]
    exact norm_fourier_slice_scaled_sub_le ha hc hS s w
  calc
    _ = |s| ^ d * ‖∫ w, g (s • w) - f w‖ := by
      rw [Measure.volume_eq_prod, integral_prod _ hai]
      change ‖(∫ x, g x) - |s| ^ d • a (0, 0)‖ = _
      rw [← hf, integral_sub (hg.comp_smul hs) hfi, Measure.integral_comp_smul, abs_inv, abs_pow]
      conv_rhs =>
        rw [← Real.norm_of_nonneg (show 0 ≤ |s| ^ d by positivity), ← norm_smul]
      rw [smul_sub, Real.norm_of_nonneg (show 0 ≤ |s| ^ d by positivity),
        smul_smul, mul_inv_cancel₀ (pow_ne_zero _ (abs_ne_zero.mpr hs)), one_smul]
    _ ≤ |s| ^ d * (K * S * |s| * ∫ w, weight w) := by
      gcongr
      refine (norm_integral_le_integral_norm _).trans ?_
      rw [← integral_const_mul]
      exact integral_mono ((hg.comp_smul hs).sub hfi).norm (hw.const_mul _) hb
    _ = _ := by rw [pow_succ]; ring

end TauCeti

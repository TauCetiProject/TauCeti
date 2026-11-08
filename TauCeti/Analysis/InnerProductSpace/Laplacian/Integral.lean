/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
public import TauCeti.Analysis.Calculus.LineDeriv.IntegrationByParts
import TauCeti.Analysis.InnerProductSpace.Laplacian.Cutoff
import TauCeti.Analysis.Sobolev.WeakDeriv.Laplacian
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Integrability and integration of Laplacians

The Laplacian of a compactly supported twice continuously differentiable function has integral
zero. More generally, an integrable `C²` scalar function whose Laplacian is bounded below by an
integrable function has an integrable Laplacian. Dilated cutoffs turn the one-sided
bound into a global mass bound. These statements allow integrated Bochner estimates without
assuming derivative decay at infinity.
-/

public section

namespace TauCeti

open MeasureTheory Filter Metric
open scoped ContDiff Laplacian

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {μ : Measure E} [μ.IsAddHaarMeasure] {f : E → F}

/-- The integral of the Laplacian of a compactly supported `C²` function vanishes. -/
theorem integral_laplacian_eq_zero_of_hasCompactSupport (hf : ContDiff ℝ 2 f)
    (hc : HasCompactSupport f) : ∫ x, Δ f x ∂μ = 0 := by
  let b := stdOrthonormalBasis ℝ E
  have hd := hf.fderiv_right (m := 1) (by norm_num)
  have hi (i) : Integrable
      (fun x ↦ fderiv ℝ (fun y ↦ fderiv ℝ f y (b i)) x (b i)) μ :=
    (((hd.clm_apply contDiff_const).continuous_fderiv one_ne_zero).clm_apply
      continuous_const).integrable_of_hasCompactSupport
        ((hc.fderiv_apply (𝕜 := ℝ) (b i)).fderiv_apply (𝕜 := ℝ) (b i))
  simp_rw [laplacian_eq_sum_fderiv_fderiv_apply b (hd.differentiable one_ne_zero _)]
  rw [integral_finsetSum _ fun i _ ↦ hi i]
  apply Finset.sum_eq_zero
  intro i _
  exact integral_fderiv_apply_eq_zero_of_hasCompactSupport
    (hd.clm_apply contDiff_const) (hc.fderiv_apply (𝕜 := ℝ) (b i)) (b i)

/-- On a ball, the Laplacian of a `C²` function plus an integrable function is integrable. -/
private theorem integrableOn_laplacian_add_ball {f g : E → ℝ} (hf : ContDiff ℝ 2 f)
    (hgi : Integrable g μ) (r : ℝ) : IntegrableOn (fun x ↦ Δ f x + g x) (ball 0 r) μ :=
  ((hf.continuous_laplacian.continuousOn.integrableOn_compact
    (isCompact_closedBall 0 r)).mono_set ball_subset_closedBall).add hgi.integrableOn

/-- The mass of `Δ f + g` on a ball is bounded using a cutoff `χ` that is `1` on the ball and
whose Laplacian is at most `C / R ^ 2`, when `Δ f + g` is nonnegative: both derivatives move to
the cutoff by Green's identity, so no first-derivative integrability is needed. -/
private theorem integral_ball_laplacian_add_le {f g χ : E → ℝ} {C R : ℝ}
    (hf : ContDiff ℝ 2 f) (hfi : Integrable f μ) (hgi : Integrable g μ)
    (hle : ∀ x, -g x ≤ Δ f x) (hC0 : 0 ≤ C) (hR : 1 ≤ R) (hχ : ContDiff ℝ ∞ χ)
    (hχc : HasCompactSupport χ) (hχ1 : ∀ x, ‖x‖ < R → χ =ᶠ[nhds x] fun _ ↦ 1)
    (hΔ : ∀ x, ‖Δ χ x‖ ≤ C / R ^ 2) (hχrange : ∀ x, χ x ∈ Set.Icc (0 : ℝ) 1) :
    ∫ x in ball 0 R, (Δ f x + g x) ∂μ ≤ C * (∫ x, ‖f x‖ ∂μ) + ∫ x, ‖g x‖ ∂μ := by
  let k := fun x ↦ Δ f x + g x
  have hk0 : ∀ x, 0 ≤ k x := fun x ↦ by dsimp [k]; linarith [hle x]
  have hχg : Integrable (fun x ↦ χ x * g x) μ :=
    hgi.bdd_mul hχ.continuous.aestronglyMeasurable (ae_of_all μ fun x ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (hχrange x).1]
      exact (hχrange x).2)
  have hχΔ : Integrable (fun x ↦ χ x * Δ f x) μ :=
    (hχ.continuous.mul hf.continuous_laplacian).integrable_of_hasCompactSupport hχc.mul_right
  have hχk : Integrable (fun x ↦ χ x * k x) μ := by
    simpa only [k, mul_add, Pi.add_def] using hχΔ.add hχg
  have hΔf : Integrable (fun x ↦ Δ χ x * f x) μ :=
    ((hχ.of_le (by simp)).continuous_laplacian.mul hf.continuous)
      |>.integrable_of_hasCompactSupport hχc.laplacian.mul_right
  have hgreen : ∫ x, χ x * Δ f x ∂μ = ∫ x, Δ χ x * f x ∂μ := by
    let φ : TestFunction (⊤ : TopologicalSpace.Opens E) ℝ ⊤ :=
      ⟨χ, hχ.of_le (by simp), hχc, Set.subset_univ _⟩
    exact (hf.contDiffOn.integral_laplacian_smul_eq_integral_smul_laplacian φ).symm
  have hbound (x : E) : Δ χ x * f x ≤ C * ‖f x‖ := by
    calc
      Δ χ x * f x ≤ ‖Δ χ x‖ * ‖f x‖ := by
        simpa only [Real.norm_eq_abs, abs_mul] using le_abs_self (Δ χ x * f x)
      _ ≤ C * ‖f x‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        exact (hΔ x).trans (div_le_self hC0 (one_le_pow₀ hR))
  calc
    ∫ x in ball 0 R, k x ∂μ ≤ ∫ x, χ x * k x ∂μ := by
      rw [← integral_indicator measurableSet_ball]
      apply integral_mono
        ((integrableOn_laplacian_add_ball hf hgi R).integrable_indicator measurableSet_ball) hχk
      intro x
      by_cases hx : x ∈ ball (0 : E) R
      · simp only [Set.indicator_of_mem hx, (hχ1 x (mem_ball_zero_iff.mp hx)).self_of_nhds,
          one_mul]
        exact le_rfl
      · simp only [Set.indicator_of_notMem hx]
        exact mul_nonneg (hχrange x).1 (hk0 x)
    _ = (∫ x, Δ χ x * f x ∂μ) + ∫ x, χ x * g x ∂μ := by
      simp_rw [k, mul_add]
      rw [integral_add hχΔ hχg, hgreen]
    _ ≤ (∫ x, C * ‖f x‖ ∂μ) + ∫ x, ‖g x‖ ∂μ := by
      apply add_le_add (integral_mono hΔf (hfi.norm.const_mul C) hbound)
      apply integral_mono hχg hgi.norm
      intro x
      exact (le_abs_self _).trans (by
        rw [abs_mul, abs_of_nonneg (hχrange x).1]
        exact mul_le_of_le_one_left (abs_nonneg _) (hχrange x).2)
    _ = _ := by rw [integral_const_mul]

/-- An integrable `C²` function with an integrable lower bound on its Laplacian has
an integrable Laplacian. No bounds on its first derivatives at infinity are required. -/
theorem integrable_laplacian_of_integrable_of_le {f g : E → ℝ} (hf : ContDiff ℝ 2 f)
    (hfi : Integrable f μ) (hgi : Integrable g μ)
    (hle : ∀ x, -g x ≤ Δ f x) : Integrable (Δ f) μ := by
  obtain ⟨C, hC⟩ := exists_forall_contDiff_cutoff_ball_norm_laplacian_le (E := E)
  have hC0 : 0 ≤ C := by
    obtain ⟨χ, -, -, -, -, -, hΔ, -⟩ := hC 1 zero_lt_one
    simpa using (norm_nonneg (Δ χ 0)).trans (hΔ 0)
  have hR : Tendsto (fun n : ℕ ↦ (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  -- Bound the mass on expanding balls by the same constant, using nonnegative cutoffs.
  have hki : Integrable (fun x ↦ Δ f x + g x) μ := by
    apply (aecover_ball (μ := μ) (x := (0 : E)) hR).integrable_of_integral_bounded_of_nonneg_ae
        (C * (∫ x, ‖f x‖ ∂μ) + ∫ x, ‖g x‖ ∂μ)
        (fun n ↦ integrableOn_laplacian_add_ball hf hgi (n + 1))
        (ae_of_all μ fun x ↦ by linarith [hle x])
    apply Filter.Eventually.of_forall
    intro n
    obtain ⟨χ, hχ, hχc, hχ1, -, -, hΔ, hχrange⟩ := hC (n + 1) (by positivity)
    exact integral_ball_laplacian_add_le hf hfi hgi hle hC0
      (by simp) hχ hχc hχ1 hΔ hχrange
  simpa only [Pi.sub_def, add_sub_cancel_right] using hki.sub hgi

end TauCeti

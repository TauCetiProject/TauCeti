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

Green's first identity `∫ ⟪∇u, ∇v⟫ = -∫ v Δu` holds for a `C²` function `u` and a compactly
supported `C¹` function `v`, with no condition on `u` at infinity.
-/

public section

namespace TauCeti

open MeasureTheory Filter Metric
open scoped Laplacian Gradient InnerProductSpace

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

/-- **Green's first identity against a compactly supported function.** For a `C²` function `u`
and a compactly supported `C¹` function `v`, `∫ ⟪∇u, ∇v⟫ = -∫ v Δu`. No integrability or decay
of `u` is needed. -/
theorem integral_inner_gradient_eq_neg_integral_mul_laplacian {u v : E → ℝ}
    (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 1 v) (hvc : HasCompactSupport v) :
    ∫ x, ⟪∇ u x, ∇ v x⟫_ℝ ∂μ = -∫ x, v x * Δ u x ∂μ := by
  let b := stdOrthonormalBasis ℝ E
  have hu1 : ContDiff ℝ 1 (fderiv ℝ u) := hu.fderiv_right (by norm_num)
  have hdu (i) : ContDiff ℝ 1 fun y ↦ fderiv ℝ u y (b i) := hu1.clm_apply contDiff_const
  have hinner (x) : ⟪∇ u x, ∇ v x⟫_ℝ = ∑ i, fderiv ℝ u x (b i) * fderiv ℝ v x (b i) := by
    rw [← b.sum_inner_mul_inner (∇ u x) (∇ v x)]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [inner_gradient_left, real_inner_comm (∇ v x), inner_gradient_left]
  have hΔ (x) : Δ u x = ∑ i, fderiv ℝ (fun y ↦ fderiv ℝ u y (b i)) x (b i) :=
    laplacian_eq_sum_fderiv_fderiv_apply b ((hu1.differentiable one_ne_zero) x)
  have hint (i) : Integrable (fun x ↦ v x * fderiv ℝ (fun y ↦ fderiv ℝ u y (b i)) x (b i)) μ :=
    (hv.continuous.mul (((hdu i).continuous_fderiv one_ne_zero).clm_apply
      continuous_const)).integrable_of_hasCompactSupport hvc.mul_right
  have hint' (i) : Integrable (fun x ↦ fderiv ℝ u x (b i) * fderiv ℝ v x (b i)) μ :=
    (((hdu i).continuous.mul ((hv.continuous_fderiv one_ne_zero).clm_apply
      continuous_const)).integrable_of_hasCompactSupport
        (hvc.fderiv_apply (𝕜 := ℝ) (b i)).mul_left)
  -- Integrate by parts in each direction of the orthonormal basis.
  have hdir (i) : ∫ x, fderiv ℝ u x (b i) * fderiv ℝ v x (b i) ∂μ =
      -∫ x, v x * fderiv ℝ (fun y ↦ fderiv ℝ u y (b i)) x (b i) ∂μ := by
    simp_rw [mul_comm (v _)]
    exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      (by simpa only [mul_comm (v _)] using hint i) (hint' i)
      (((hdu i).continuous.mul hv.continuous).integrable_of_hasCompactSupport hvc.mul_left)
      (fun x _ ↦ (hdu i).differentiable one_ne_zero x)
      (fun x _ ↦ hv.differentiable one_ne_zero x)
  simp_rw [hinner, hΔ, Finset.mul_sum]
  rw [integral_finsetSum _ fun i _ ↦ hint' i, integral_finsetSum _ fun i _ ↦ hint i,
    ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ ↦ hdir i

/-- An integrable `C²` function with an integrable lower bound on its Laplacian has
an integrable Laplacian. No bounds on its first derivatives at infinity are required. -/
theorem integrable_laplacian_of_integrable_of_le {f g : E → ℝ} (hf : ContDiff ℝ 2 f)
    (hfi : Integrable f μ) (hgi : Integrable g μ)
    (hle : ∀ x, -g x ≤ Δ f x) : Integrable (Δ f) μ := by
  obtain ⟨C, hC⟩ := exists_forall_contDiff_cutoff_ball_norm_laplacian_le (E := E)
  have hC0 : 0 ≤ C := by
    obtain ⟨χ, -, -, -, -, -, hΔ, -⟩ := hC 1 zero_lt_one
    simpa using (norm_nonneg (Δ χ 0)).trans (hΔ 0)
  let k := fun x ↦ Δ f x + g x
  have hk (r : ℝ) : IntegrableOn k (ball 0 r) μ :=
    ((hf.continuous_laplacian.continuousOn.integrableOn_compact
      (isCompact_closedBall 0 r)).mono_set ball_subset_closedBall).add hgi.integrableOn
  have hk0 : ∀ x, 0 ≤ k x := fun x ↦ by dsimp [k]; linarith [hle x]
  have hR : Tendsto (fun n : ℕ ↦ (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  -- Bound the mass on expanding balls by the same constant, using nonnegative cutoffs.
  have hki : Integrable k μ := by
    apply (aecover_ball (μ := μ) (x := (0 : E)) hR).integrable_of_integral_bounded_of_nonneg_ae
        (C * (∫ x, ‖f x‖ ∂μ) + ∫ x, ‖g x‖ ∂μ)
        (fun n ↦ hk (n + 1)) (ae_of_all μ hk0)
    apply Filter.Eventually.of_forall
    intro n
    obtain ⟨χ, hχ, hχc, hχ1, -, -, hΔ, hχrange⟩ := hC (n + 1) (by positivity)
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
    -- Move both derivatives to the cutoff; no first-derivative integrability is needed.
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
          exact (hΔ x).trans (div_le_self hC0
            (by nlinarith [Nat.cast_nonneg (α := ℝ) n] : 1 ≤ (n + 1 : ℝ) ^ 2))
    calc
      ∫ x in Metric.ball 0 (n + 1), k x ∂μ ≤ ∫ x, χ x * k x ∂μ := by
        rw [← integral_indicator measurableSet_ball]
        apply integral_mono
          ((hk (n + 1)).integrable_indicator measurableSet_ball) hχk
        intro x
        by_cases hx : x ∈ Metric.ball (0 : E) (n + 1)
        · simp only [Set.indicator_of_mem hx,
            (hχ1 x (mem_ball_zero_iff.mp hx)).self_of_nhds, one_mul, le_refl]
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
  simpa only [Pi.sub_def, k, add_sub_cancel_right] using hki.sub hgi

end TauCeti

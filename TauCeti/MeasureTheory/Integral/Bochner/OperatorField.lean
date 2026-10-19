/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas

/-!
# Convergence of integrals of bounded operator fields

Bounded operator fields converging almost everywhere preserve convergence of integrated
pairings with velocities converging in `L¹`. Separating the changes of field and velocity
avoids a pointwise bound on the approximating velocities.
-/

public section

open MeasureTheory Set Filter
open scoped Topology

namespace MeasureTheory

variable {α E F : Type*} [MeasurableSpace α] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {μ : Measure α}

/-- Bounded operator fields converging almost everywhere can be paired with velocities
converging in `L¹`. This gives convergence of the actual Bochner integrals. -/
theorem tendsto_integral_clm_apply_of_integral_norm_sub
    {ωn : ℕ → α → E →L[ℝ] F} {ω : α → E →L[ℝ] F}
    {vn : ℕ → α → E} {v : α → E} {C : ℝ}
    (hωn : ∀ n, AEStronglyMeasurable (ωn n) μ)
    (hω : AEStronglyMeasurable ω μ)
    (hboundn : ∀ n, ∀ᵐ x ∂μ, ‖ωn n x‖ ≤ C) (hbound : ∀ᵐ x ∂μ, ‖ω x‖ ≤ C)
    (hωconv : ∀ᵐ x ∂μ, Tendsto (fun n ↦ ωn n x) atTop (nhds (ω x)))
    (hvn : ∀ n, Integrable (vn n) μ) (hv : Integrable v μ)
    (hvconv : Tendsto (fun n ↦ ∫ x, ‖vn n x - v x‖ ∂μ) atTop (nhds 0)) :
    Tendsto (fun n ↦ ∫ x, ωn n x (vn n x) ∂μ) atTop
      (nhds (∫ x, ω x (v x) ∂μ)) := by
  let e : ℕ → α → F := fun n x ↦ (ωn n x - ω x) (v x)
  let d : ℕ → α → F := fun n x ↦ ωn n x (vn n x - v x)
  have heint (n) : Integrable (e n) μ := by
    apply (ContinuousLinearMap.id ℝ (E →L[ℝ] F)).integrable_of_bilin_of_bdd_left
      (C + C) ((hωn n).sub hω) _ hv
    filter_upwards [hboundn n, hbound] with x hx hy
    exact norm_sub_le _ _ |>.trans (add_le_add hx hy)
  have hdint (n) : Integrable (d n) μ :=
    (ContinuousLinearMap.id ℝ (E →L[ℝ] F)).integrable_of_bilin_of_bdd_left
      C (hωn n) (hboundn n) ((hvn n).sub hv)
  have he : Tendsto (fun n ↦ ∫ x, e n x ∂μ) atTop (nhds 0) := by
    have ht := tendsto_integral_filter_of_dominated_convergence
      (μ := μ) (l := atTop) (F := e) (f := fun _ ↦ (0 : F))
      (fun x ↦ (C + C) * ‖v x‖)
      (Eventually.of_forall fun n ↦ (heint n).1) ?_
      (hv.norm.const_mul (C + C)) ?_
    · simpa only [integral_zero] using ht
    · apply Eventually.of_forall
      intro n
      filter_upwards [hboundn n, hbound] with x hx hy
      exact ((ωn n x - ω x).le_opNorm (v x)).trans
        (mul_le_mul_of_nonneg_right ((norm_sub_le _ _).trans (add_le_add hx hy))
          (norm_nonneg _))
    · filter_upwards [hωconv] with x hx
      have hxzero : Tendsto (fun n ↦ ωn n x - ω x) atTop (nhds 0) := by
        simpa only [sub_self] using hx.sub (tendsto_const_nhds (x := ω x))
      convert ((ContinuousLinearMap.apply ℝ F (v x)).continuous.tendsto 0).comp hxzero using 1
      · ext n
        exact (ContinuousLinearMap.apply_apply (v x) (ωn n x - ω x)).symm
      · simp
  have hd : Tendsto (fun n ↦ ∫ x, d n x ∂μ) atTop (nhds 0) := by
    apply squeeze_zero_norm (fun n ↦ ?_) (by simpa using hvconv.const_mul C)
    calc
      ‖∫ x, d n x ∂μ‖ ≤ ∫ x, C * ‖vn n x - v x‖ ∂μ :=
        norm_integral_le_of_norm_le ((hvn n |>.sub hv).norm.const_mul C) (by
          filter_upwards [hboundn n] with x hx
          exact ((ωn n x).le_opNorm _).trans
            (mul_le_mul_of_nonneg_right hx (norm_nonneg _)))
      _ = C * ∫ x, ‖vn n x - v x‖ ∂μ := integral_const_mul _ _
  have hpair : Integrable (fun x ↦ ω x (v x)) μ :=
    (ContinuousLinearMap.id ℝ (E →L[ℝ] F)).integrable_of_bilin_of_bdd_left C hω hbound hv
  have heq (n) : (∫ x, ωn n x (vn n x) ∂μ) =
      (∫ x, ω x (v x) ∂μ) + (∫ x, e n x ∂μ) + ∫ x, d n x ∂μ := by
    rw [← integral_add hpair (heint n),
      ← integral_add (f := fun x ↦ ω x (v x) + e n x)
        (hpair.add (heint n)) (hdint n)]
    apply integral_congr_ae
    filter_upwards with x
    simp only [e, d, sub_apply, map_sub]
    abel
  simpa only [heq, add_zero] using (tendsto_const_nhds.add he).add hd

/-- Multiplying `L¹`-convergent real functions by a fixed bounded measurable function
preserves convergence of their actual integrals. -/
theorem tendsto_integral_mul_of_integral_abs_sub
    {wn : ℕ → α → ℝ} {w R : α → ℝ} {C : ℝ}
    (hwn : ∀ n, Integrable (wn n) μ) (hw : Integrable w μ)
    (hR : AEStronglyMeasurable R μ) (hbound : ∀ᵐ x ∂μ, |R x| ≤ C)
    (hconv : Tendsto (fun n ↦ ∫ x, |wn n x - w x| ∂μ) atTop (nhds 0)) :
    Tendsto (fun n ↦ ∫ x, wn n x * R x ∂μ) atTop (nhds (∫ x, w x * R x ∂μ)) := by
  let ω : α → ℝ →L[ℝ] ℝ := fun x ↦ R x • ContinuousLinearMap.id ℝ ℝ
  have hω : AEStronglyMeasurable ω μ := hR.smul_const _
  have hb : ∀ᵐ x ∂μ, ‖ω x‖ ≤ C * ‖ContinuousLinearMap.id ℝ ℝ‖ := by
    filter_upwards [hbound] with x hx
    simpa only [ω, norm_smul, Real.norm_eq_abs] using
      mul_le_mul_of_nonneg_right hx (norm_nonneg (ContinuousLinearMap.id ℝ ℝ))
  have ht := tendsto_integral_clm_apply_of_integral_norm_sub
    (fun _ ↦ hω) hω (fun _ ↦ hb) hb
    (Eventually.of_forall fun _ ↦ tendsto_const_nhds) hwn hw
    (by simpa only [Real.norm_eq_abs] using hconv)
  simpa only [ω, smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul, mul_comm] using ht

end MeasureTheory

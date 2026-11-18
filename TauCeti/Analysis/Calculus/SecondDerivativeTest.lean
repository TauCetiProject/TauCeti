/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Topology.Order.LocalExtr

/-!
# The second derivative test

Let `f : E → ℝ` be `C²` at a point `a` of a finite-dimensional real normed space, with
`f'(a) = 0` and second derivative positive definite at `a`: `f''(a)(v, v) > 0` for `v ≠ 0`.
Then `a` is a strict local minimum: `f(a) < f(y)` for every `y ≠ a` close to `a`.

Positive definiteness on the compact unit sphere gives a coercivity constant `c > 0`,
`f''(a)(v, v) ≥ c ‖v‖²`. By continuity of `f''`, `f''(z)(v, v) ≥ (c/2) ‖v‖²` for `z` in a
ball around `a`. Along a segment `t ↦ a + t (y - a)` in this ball, the derivative of
`φ(t) = f(a + t (y - a))` vanishes at `0` and is strictly increasing, so `φ` is strictly
increasing on `[0, 1]`.

## Main results

* `eventually_lt_of_fderiv_eq_zero_of_fderiv_fderiv_pos`: the second derivative test.
-/

public section

open Filter Metric Set Topology
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

private theorem exists_pos_mul_norm_sq_le (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hB : ∀ v, v ≠ 0 → 0 < B v v) : ∃ c > 0, ∀ v, c * ‖v‖ ^ 2 ≤ B v v := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · exact ⟨1, one_pos, fun v ↦ by simp [Subsingleton.elim v 0]⟩
  have hcont : Continuous fun v ↦ B v v := B.continuous₂.comp (continuous_id.prodMk continuous_id)
  obtain ⟨u, hu, hmin⟩ := (isCompact_sphere (0 : E) 1).exists_isMinOn
    (NormedSpace.sphere_nonempty.2 zero_le_one) hcont.continuousOn
  have hu0 : u ≠ 0 := ne_zero_of_mem_sphere one_ne_zero ⟨u, hu⟩
  refine ⟨B u u, hB u hu0, fun v ↦ ?_⟩
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  have hnv : 0 < ‖v‖ := norm_pos_iff.2 hv
  have hw : ‖v‖⁻¹ • v ∈ sphere (0 : E) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnv.ne']
  have h := hmin hw
  simp only [mem_ofPred_eq, map_smul, smul_apply, smul_eq_mul] at h
  calc
    B u u * ‖v‖ ^ 2 ≤ ‖v‖⁻¹ * (‖v‖⁻¹ * B v v) * ‖v‖ ^ 2 := by gcongr
    _ = B v v := by field_simp

/-- **The second derivative test.** Let `f` be `C²` at `a`, with `f'(a) = 0` and `f''(a)`
positive definite. Then `f(a) < f(y)` for all `y ≠ a` close to `a`. -/
theorem eventually_lt_of_fderiv_eq_zero_of_fderiv_fderiv_pos {f : E → ℝ} {a : E}
    (hf : ContDiffAt ℝ 2 f a) (hd : fderiv ℝ f a = 0)
    (hpos : ∀ v, v ≠ 0 → 0 < fderiv ℝ (fderiv ℝ f) a v v) :
    ∀ᶠ y in 𝓝[≠] a, f a < f y := by
  obtain ⟨c, hc, hcoer⟩ := exists_pos_mul_norm_sq_le _ hpos
  have hev : ∀ᶠ z in 𝓝 a, ContDiffAt ℝ 2 f z := hf.eventually (by simp)
  have hcont : ContinuousAt (fderiv ℝ (fderiv ℝ f)) a :=
    ((hf.fderiv_right (m := 1) (by norm_num)).fderiv_right (m := 0) (by norm_num)).continuousAt
  have hlim : Tendsto (fderiv ℝ (fderiv ℝ f)) (𝓝 a)
      (@nhds (E →L[ℝ] E →L[ℝ] ℝ)
        (@UniformSpace.toTopologicalSpace _
          (@PseudoMetricSpace.toUniformSpace _ SeminormedAddGroup.toPseudoMetricSpace))
        (fderiv ℝ (fderiv ℝ f) a)) := by
    exact hcont
  have hclose : ∀ᶠ z in 𝓝 a, ‖fderiv ℝ (fderiv ℝ f) z - fderiv ℝ (fderiv ℝ f) a‖ < c / 2 := by
    have hnorm := (hlim.sub_const (fderiv ℝ (fderiv ℝ f) a)).norm
    have hcenter : ‖fderiv ℝ (fderiv ℝ f) a - fderiv ℝ (fderiv ℝ f) a‖ < c / 2 := by
      rw [sub_self]
      rw [ContinuousLinearMap.opNorm_zero]
      exact half_pos hc
    exact hnorm.eventually (gt_mem_nhds hcenter)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.1 (hev.and hclose)
  filter_upwards [inter_mem_nhdsWithin _ (ball_mem_nhds a hδ)] with y hy
  obtain ⟨hya, hyb⟩ := hy
  set h := y - a
  have hh : h ≠ 0 := sub_ne_zero.2 hya
  have hseg (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : a + t • h ∈ ball a δ := by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht.1]
    calc
      _ ≤ 1 * ‖h‖ := by gcongr; exact ht.2
      _ < δ := by rw [one_mul, ← dist_eq_norm]; exact hyb
  have hγ (t : ℝ) : HasDerivAt (fun s : ℝ ↦ a + s • h) h t := by
    simpa using ((hasDerivAt_id t).smul_const h).const_add a
  have hD1 (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun s ↦ f (a + s • h)) (fderiv ℝ f (a + t • h) h) t := by
    have hz := (hball _ (hseg t ht)).1
    exact ((hz.differentiableAt (by norm_num)).hasFDerivAt).comp_hasDerivAt t (hγ t)
  have hD2 (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun s ↦ fderiv ℝ f (a + s • h) h)
        (fderiv ℝ (fderiv ℝ f) (a + t • h) h h) t := by
    have hz := (hball _ (hseg t ht)).1
    have h1 : HasDerivAt (fun s ↦ fderiv ℝ f (a + s • h)) (fderiv ℝ (fderiv ℝ f) (a + t • h) h)
        t :=
      (((hz.fderiv_right (m := 1) (by norm_num)).differentiableAt
        (by norm_num)).hasFDerivAt).comp_hasDerivAt t (hγ t)
    simpa using h1.clm_apply (hasDerivAt_const t h)
  have hpos2 (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      0 < fderiv ℝ (fderiv ℝ f) (a + t • h) h h := by
    have hz := (hball _ (hseg t ht)).2
    have hdiff := ContinuousLinearMap.le_opNorm₂
      (fderiv ℝ (fderiv ℝ f) (a + t • h) - fderiv ℝ (fderiv ℝ f) a) h h
    simp only [sub_apply] at hdiff
    have hnh : 0 < ‖h‖ := norm_pos_iff.2 hh
    have h1 := hcoer h
    have h2 : ‖fderiv ℝ (fderiv ℝ f) (a + t • h) - fderiv ℝ (fderiv ℝ f) a‖ * ‖h‖ * ‖h‖ ≤
        c / 2 * ‖h‖ ^ 2 := by
      rw [mul_assoc, ← sq]
      exact mul_le_mul_of_nonneg_right hz.le (sq_nonneg _)
    have h3 := neg_abs_le (fderiv ℝ (fderiv ℝ f) (a + t • h) h h - fderiv ℝ (fderiv ℝ f) a h h)
    rw [← Real.norm_eq_abs] at h3
    nlinarith [sq_pos_of_pos hnh]
  have hmono1 : StrictMonoOn (fun s : ℝ ↦ fderiv ℝ f (a + s • h) h) (Icc 0 1) :=
    strictMonoOn_of_deriv_pos (convex_Icc 0 1)
      (fun t ht ↦ (hD2 t ht).continuousAt.continuousWithinAt)
      (fun t ht ↦ by
        rw [interior_Icc] at ht
        rw [(hD2 t (Ioo_subset_Icc_self ht)).deriv]
        exact hpos2 t (Ioo_subset_Icc_self ht))
  have hmono : StrictMonoOn (fun s : ℝ ↦ f (a + s • h)) (Icc 0 1) :=
    strictMonoOn_of_deriv_pos (convex_Icc 0 1)
      (fun t ht ↦ (hD1 t ht).continuousAt.continuousWithinAt)
      (fun t ht ↦ by
        rw [interior_Icc] at ht
        rw [(hD1 t (Ioo_subset_Icc_self ht)).deriv]
        have h0 : fderiv ℝ f (a + (0 : ℝ) • h) h = 0 := by simp [hd]
        rw [← h0]
        exact hmono1 (left_mem_Icc.2 zero_le_one) (Ioo_subset_Icc_self ht) ht.1)
  have h01 := hmono (left_mem_Icc.2 zero_le_one) (right_mem_Icc.2 zero_le_one) zero_lt_one
  simpa [h] using h01

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Harmonic.Poisson
public import Mathlib.Analysis.Complex.Harmonic.MeanValue

/-!
# Harnack's inequality on a planar disk

This file proves the Harnack inequality for real-valued harmonic functions on a disk in the
complex plane.  Mathlib's Poisson integral formula writes the value at an interior point as a
circle average weighted by the Poisson kernel; its sharp upper and lower bounds give the
centered Harnack estimate directly.

The Poisson formula first gives the estimate for a function that is harmonic on an open disk,
continuous on its closure and nonnegative on the boundary circle.  Applying this result on
concentric intermediate disks and passing to the outer radius gives the usual formulation for a
nonnegative harmonic function on an open disk.  The pairwise form on a closed subdisk has the
standard constant `((R + r) / (R - r)) ^ 2`.

The argument is the classical Poisson-kernel proof; see Evans, *Partial Differential Equations*,
Chapter 2, Section 2.2.

## Main declarations

* `InnerProductSpace.HarmonicOnNhd.harnack_inequality_center`: the sharp two-sided comparison
  with the value at the center of a disk.
* `InnerProductSpace.HarmonicOnNhd.harnack_inequality`: any two values on a smaller closed disk
  differ by at most the standard Harnack factor.
* `InnerProductSpace.HarmonicOnNhd.eqOn_zero_of_nonneg_of_eq_zero`: a nonnegative harmonic
  function that vanishes at an interior point vanishes throughout the disk.

Each has a counterpart in the `InnerProductSpace.HarmonicContOnCl` namespace, with suffix
`_of_nonneg_on_sphere`, for a function continuous on the closed disk and nonnegative only on its
boundary circle.
-/

public section

noncomputable section

namespace TauCeti

open Complex Filter InnerProductSpace Metric Real Topology

private lemma le_harnack_factor_mul_of_mul_le {R d a b : ℝ} (hd : 0 ≤ d) (hdR : d < R)
    (h : (R - d) / (R + d) * a ≤ b) :
    a ≤ (R + d) / (R - d) * b := by
  rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)] at h
  rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
  linarith

variable {f : ℂ → ℝ} {c w : ℂ} {R : ℝ}

/-- **The centered Harnack inequality on a planar disk.**

If `f` is harmonic on the open disk of radius `R` about `c`, continuous on its closure and
nonnegative on its boundary circle, then every `w` in the open disk satisfies

`(R - ‖w - c‖) / (R + ‖w - c‖) * f c ≤ f w
  ≤ (R + ‖w - c‖) / (R - ‖w - c‖) * f c`. -/
theorem _root_.InnerProductSpace.HarmonicContOnCl.harnack_inequality_center_of_nonneg_on_sphere
    (hf : HarmonicContOnCl f (ball c R)) (hnonneg : ∀ z ∈ sphere c R, 0 ≤ f z)
    (hw : w ∈ ball c R) :
    (R - ‖w - c‖) / (R + ‖w - c‖) * f c ≤ f w ∧
      f w ≤ (R + ‖w - c‖) / (R - ‖w - c‖) * f c := by
  have hR : |R| = R := abs_of_pos (pos_of_mem_ball hw)
  have hfint : CircleIntegrable f c R :=
    (hf.continuousOn_ball.mono sphere_subset_closedBall).circleIntegrable
      (pos_of_mem_ball hw).le
  have hkint : CircleIntegrable ((re ∘ herglotzRieszKernel c w) • f) c R :=
    hfint.continuousOn_smul <| continuous_re.comp_continuousOn <|
      continuousOn_herglotzRieszKernel_sphere <| by
        simpa [hR] using fun h ↦ (mem_ball.1 hw).ne (mem_sphere.1 h)
  have hmean : circleAverage f c R = f c := by
    rw [← hR] at hf
    exact hf.circleAverage_eq
  rw [← hf.circleAverage_re_herglotzRieszKernel_smul hw, ← hmean, ← smul_eq_mul,
    ← circleAverage_smul, ← smul_eq_mul, ← circleAverage_smul]
  constructor
  · refine circleAverage_mono hfint.const_smul hkint fun z hz ↦ ?_
    rw [hR] at hz
    refine mul_le_mul_of_nonneg_right ?_ (hnonneg z hz)
    simpa [herglotzRieszKernel_def] using le_re_herglotzRieszKernel hz hw
  · refine circleAverage_mono hkint hfint.const_smul fun z hz ↦ ?_
    rw [hR] at hz
    refine mul_le_mul_of_nonneg_right ?_ (hnonneg z hz)
    simpa [herglotzRieszKernel_def] using re_herglotzRieszKernel_le hz hw

/-- A function harmonic on an open planar disk, continuous on its closure and nonnegative on its
boundary circle is nonnegative throughout the open disk. -/
theorem _root_.InnerProductSpace.HarmonicContOnCl.nonneg_of_nonneg_on_sphere
    (hf : HarmonicContOnCl f (ball c R)) (hnonneg : ∀ z ∈ sphere c R, 0 ≤ f z)
    (hw : w ∈ ball c R) :
    0 ≤ f w := by
  have hR : |R| = R := abs_of_pos (pos_of_mem_ball hw)
  have hfc : 0 ≤ f c := by
    rw [← hR] at hf
    rw [← hf.circleAverage_eq]
    exact circleAverage_nonneg_of_nonneg fun z hz ↦ hnonneg z (hR ▸ hz)
  have hd : ‖w - c‖ < R := mem_ball_iff_norm.1 hw
  refine (mul_nonneg ?_ hfc).trans (hf.harnack_inequality_center_of_nonneg_on_sphere hnonneg hw).1
  exact div_nonneg (by linarith) (by linarith [norm_nonneg (w - c)])

/-- **The centered Harnack inequality on an open planar disk.**

If `f` is harmonic and nonnegative throughout the open disk of radius `R` about `c`, then
every `w` in the disk satisfies the sharp two-sided comparison with `f c`

`(R - ‖w - c‖) / (R + ‖w - c‖) * f c ≤ f w
  ≤ (R + ‖w - c‖) / (R - ‖w - c‖) * f c`. -/
theorem _root_.InnerProductSpace.HarmonicOnNhd.harnack_inequality_center
    (hf : HarmonicOnNhd f (ball c R)) (hnonneg : ∀ z ∈ ball c R, 0 ≤ f z) (hw : w ∈ ball c R) :
    (R - ‖w - c‖) / (R + ‖w - c‖) * f c ≤ f w ∧
      f w ≤ (R + ‖w - c‖) / (R - ‖w - c‖) * f c := by
  have hdR : ‖w - c‖ < R := mem_ball_iff_norm.mp hw
  have hR : R + ‖w - c‖ ≠ 0 := by linarith [norm_nonneg (w - c)]
  -- Apply the boundary version on every intermediate disk `ball c ρ`, then let `ρ → R`.
  have hρ : ∀ᶠ ρ in 𝓝[<] R, (ρ - ‖w - c‖) / (ρ + ‖w - c‖) * f c ≤ f w ∧
      f w ≤ (ρ + ‖w - c‖) / (ρ - ‖w - c‖) * f c := by
    filter_upwards [Ioo_mem_nhdsLT hdR] with ρ ⟨hdρ, hρR⟩
    exact (hf.mono (closure_ball_subset_closedBall.trans (closedBall_subset_ball hρR)))
      |>.harmonicContOnCl.harnack_inequality_center_of_nonneg_on_sphere
        (fun z hz ↦ hnonneg z (sphere_subset_ball hρR hz)) (mem_ball_iff_norm.2 hdρ)
  constructor
  · refine le_of_tendsto (Tendsto.mono_left ?_ nhdsWithin_le_nhds) (hρ.mono fun _ ↦ And.left)
    exact ContinuousAt.tendsto (by fun_prop (disch := exact hR))
  · refine ge_of_tendsto (Tendsto.mono_left ?_ nhdsWithin_le_nhds) (hρ.mono fun _ ↦ And.right)
    exact ContinuousAt.tendsto (by fun_prop (disch := exact (sub_pos.2 hdR).ne'))

/-- **Harnack's inequality on a smaller closed disk.**

If `f` is harmonic and nonnegative throughout `ball c R` and `r < R`, then for any
`x, y ∈ closedBall c r`,

`f x ≤ ((R + r) / (R - r)) ^ 2 * f y`. -/
theorem _root_.InnerProductSpace.HarmonicOnNhd.harnack_inequality
    (hf : HarmonicOnNhd f (ball c R)) (hnonneg : ∀ z ∈ ball c R, 0 ≤ f z) {r : ℝ} (hrR : r < R)
    {x y : ℂ} (hx : x ∈ closedBall c r) (hy : y ∈ closedBall c r) :
    f x ≤ ((R + r) / (R - r)) ^ 2 * f y := by
  have hdx : ‖x - c‖ ≤ r := mem_closedBall_iff_norm.1 hx
  have hdy : ‖y - c‖ ≤ r := mem_closedBall_iff_norm.1 hy
  have hr : 0 ≤ r := (norm_nonneg _).trans hdx
  have hfc : 0 ≤ f c := hnonneg c (mem_ball_self (hr.trans_lt hrR))
  have hfy : 0 ≤ f y := hnonneg y (closedBall_subset_ball hrR hy)
  have hK : 0 ≤ (R + r) / (R - r) := div_nonneg (by linarith) (by linarith)
  calc
    f x ≤ (R + ‖x - c‖) / (R - ‖x - c‖) * f c :=
      (hf.harnack_inequality_center hnonneg (closedBall_subset_ball hrR hx)).2
    _ ≤ (R + r) / (R - r) * f c := by gcongr; linarith
    _ ≤ (R + r) / (R - r) * ((R + ‖y - c‖) / (R - ‖y - c‖) * f y) := by
      have := (hf.harnack_inequality_center hnonneg (closedBall_subset_ball hrR hy)).1
      gcongr
      exact le_harnack_factor_mul_of_mul_le (norm_nonneg _) (by linarith) this
    _ ≤ (R + r) / (R - r) * ((R + r) / (R - r) * f y) := by gcongr; linarith
    _ = ((R + r) / (R - r)) ^ 2 * f y := by ring

/-- **Harnack's inequality on a smaller closed disk, from boundary nonnegativity.**

If `f` is harmonic on `ball c R`, continuous on its closure and nonnegative on its boundary
circle, and `r < R`, then for any `x, y ∈ closedBall c r`,

`f x ≤ ((R + r) / (R - r)) ^ 2 * f y`. -/
theorem _root_.InnerProductSpace.HarmonicContOnCl.harnack_inequality_of_nonneg_on_sphere
    (hf : HarmonicContOnCl f (ball c R)) (hnonneg : ∀ z ∈ sphere c R, 0 ≤ f z) {r : ℝ}
    (hrR : r < R) {x y : ℂ} (hx : x ∈ closedBall c r) (hy : y ∈ closedBall c r) :
    f x ≤ ((R + r) / (R - r)) ^ 2 * f y :=
  hf.harmonicOnNhd.harnack_inequality (fun _ hz ↦ hf.nonneg_of_nonneg_on_sphere hnonneg hz) hrR
    hx hy

/-- A nonnegative harmonic function on an open planar disk that vanishes at one point vanishes
throughout the disk.  This is the zero case of Harnack's inequality, and the strong minimum
principle in this setting. -/
theorem _root_.InnerProductSpace.HarmonicOnNhd.eqOn_zero_of_nonneg_of_eq_zero
    (hf : HarmonicOnNhd f (ball c R)) (hnonneg : ∀ z ∈ ball c R, 0 ≤ f z) (hw : w ∈ ball c R)
    (hfw : f w = 0) :
    Set.EqOn f 0 (ball c R) := by
  intro z hz
  obtain ⟨r, hr, hrR⟩ := exists_between (max_lt (mem_ball.1 hz) (mem_ball.1 hw))
  have hzw := hf.harnack_inequality hnonneg hrR (mem_closedBall.2 ((le_max_left _ _).trans hr.le))
    (mem_closedBall.2 ((le_max_right _ _).trans hr.le))
  rw [hfw, mul_zero] at hzw
  exact hzw.antisymm (hnonneg z hz)

/-- If a function is harmonic on an open planar disk, continuous on its closure, nonnegative on
the boundary circle, and vanishes at an interior point, then it vanishes throughout the closed
disk. -/
theorem _root_.InnerProductSpace.HarmonicContOnCl.eqOn_zero_of_nonneg_on_sphere_of_eq_zero
    (hf : HarmonicContOnCl f (ball c R)) (hnonneg : ∀ z ∈ sphere c R, 0 ≤ f z)
    (hw : w ∈ ball c R) (hfw : f w = 0) :
    Set.EqOn f 0 (closedBall c R) :=
  (hf.harmonicOnNhd.eqOn_zero_of_nonneg_of_eq_zero
    (fun _ hz ↦ hf.nonneg_of_nonneg_on_sphere hnonneg hz) hw hfw).of_subset_closure
    hf.continuousOn_ball continuousOn_const ball_subset_closedBall
    (closure_ball c (pos_of_mem_ball hw).ne').ge

end TauCeti

end

end

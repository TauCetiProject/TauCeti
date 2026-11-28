/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giada Franz, The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.LineDeriv.Basic

/-!
# Functions satisfying Euler's identity of degree one

Let `v` map between real normed spaces, be differentiable on a ball `B_r(0)`, and satisfy
Euler's identity of degree one, `v(y) = Dv(y) y`. Along each ray, `t ↦ t⁻¹ • v(ty)` is then
constant on `(0, 1]`, so `v` is positively homogeneous of degree one on the ball, and it is
linear there with slope `Dv(0)`. In particular, if also `Dv(0) = 0`, then `v = 0` on the ball.

For a graph `x_(n+1) = v(x)` through the origin, `v(y) - Dv(y) y` is, up to a positive factor,
the normal component of the position vector; this file therefore shows that a graph which is a
cone near its vertex, smooth at the vertex, is a hyperplane.

Conversely, a function that is positively homogeneous of degree one along the ray through `x`
satisfies Euler's identity `Df(x) x = f(x)` at `x`, by Mathlib's
`HasFDerivAt.apply_self_eq_smul_of_eventuallyEq`.

## Main results

* `TauCeti.eq_fderiv_apply_of_forall_eq_fderiv_apply`: `v(y) = Dv(0) y`.
* `TauCeti.eq_zero_of_forall_eq_fderiv_apply`: the case `Dv(0) = 0`.
* `TauCeti.exists_ne_fderiv_apply_of_iteratedFDeriv_two_ne_zero`: if `D²v(0) ≠ 0`, Euler's
  identity fails somewhere in every ball around `0`.
* `HasFDerivAt.apply_self_eq_of_eventually_homogeneous`: Euler's identity `f' x = f x` for a
  function with `f (t • x) = t • f x` for `t` near `1`.
-/

public section

open Filter Metric Set Topology

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Euler's identity of degree one forces linearity.** If `v` is differentiable on `B_r(0)`,
`v(y) = Dv(y) y` on `B_r(0)`, then `v(y) = Dv(0) y` on `B_r(0)`. -/
theorem eq_fderiv_apply_of_forall_eq_fderiv_apply {v : E → F} {r : ℝ}
    (hv : DifferentiableOn ℝ v (ball 0 r))
    (heuler : ∀ y ∈ ball (0 : E) r, v y = fderiv ℝ v y y) {y : E} (hy : y ∈ ball (0 : E) r) :
    v y = fderiv ℝ v 0 y := by
  have hr : 0 < r := pos_of_mem_ball hy
  have hv0 : v 0 = 0 := by
    simpa using heuler 0 (by simpa using hr : (0 : E) ∈ ball 0 r)
  have hmem (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : t • y ∈ ball (0 : E) r := by
    rw [mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg ht.1]
    exact (mul_le_of_le_one_left (norm_nonneg _) ht.2).trans_lt (mem_ball_zero_iff.1 hy)
  have hg (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun s : ℝ ↦ v (s • y)) (fderiv ℝ v (t • y) y) t := by
    have hd := ((hv _ (hmem t ht)).differentiableAt
      (isOpen_ball.mem_nhds (hmem t ht))).hasFDerivAt
    have := hd.comp_hasDerivAt t ((hasDerivAt_id t).smul_const y)
    simp only [one_smul] at this
    exact this
  set h : ℝ → F := fun t ↦ t⁻¹ • v (t • y)
  have hconst (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) : h t = h 1 := by
    have hcont : ContinuousOn h (Icc t 1) := fun s hs ↦
      ((continuousAt_id.inv₀ (ht.1.trans_le hs.1).ne').smul
        (hg s ⟨ht.1.le.trans hs.1, hs.2⟩).continuousAt).continuousWithinAt
    have hderiv : ∀ s ∈ Ico t 1, HasDerivWithinAt h 0 (Ici s) s := by
      intro s hs
      have hs0 : 0 < s := ht.1.trans_le hs.1
      have hsI : s ∈ Icc (0 : ℝ) 1 := ⟨hs0.le, hs.2.le⟩
      have hd := (hasDerivAt_inv hs0.ne').smul (hg s hsI)
      have he := heuler (s • y) (hmem s hsI)
      refine (hd.congr_deriv ?_).hasDerivWithinAt
      simp only [he, map_smul, smul_smul, ← add_smul]
      convert zero_smul ℝ (fderiv ℝ v (s • y) y) using 2
      field_simp
      ring
    exact (constant_of_has_deriv_right_zero hcont hderiv 1 ⟨ht.2, le_rfl⟩).symm
  have hlim : Tendsto h (𝓝[>] 0) (𝓝 (fderiv ℝ v 0 y)) := by
    have h0 := hg 0 ⟨le_rfl, zero_le_one⟩
    rw [zero_smul] at h0
    simpa only [zero_add, zero_smul, hv0, sub_zero] using h0.tendsto_slope_zero_right
  have hlim' : Tendsto h (𝓝[>] 0) (𝓝 (h 1)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Ioc_mem_nhdsGT zero_lt_one] with t ht
    exact (hconst t ht).symm
  have heq := tendsto_nhds_unique hlim' hlim
  simpa [h] using heq

/-- **A cone through the origin which is flat at the vertex vanishes.** If `v` is differentiable
on `B_r(0)`, `Dv(0) = 0` and `v(y) = Dv(y) y` on `B_r(0)`, then `v = 0` on
`B_r(0)`. -/
theorem eq_zero_of_forall_eq_fderiv_apply {v : E → F} {r : ℝ}
    (hv : DifferentiableOn ℝ v (ball 0 r)) (hdv0 : fderiv ℝ v 0 = 0)
    (heuler : ∀ y ∈ ball (0 : E) r, v y = fderiv ℝ v y y) {y : E} (hy : y ∈ ball (0 : E) r) :
    v y = 0 := by
  rw [eq_fderiv_apply_of_forall_eq_fderiv_apply hv heuler hy, hdv0]
  rfl

/-- **A graph which is curved at the vertex is not a cone.** If `r > 0`, `v` is differentiable on
`B_r(0)` and `D²v(0) ≠ 0`, then `v(y) ≠ Dv(y) y` for some `y ∈ B_r(0)`. -/
theorem exists_ne_fderiv_apply_of_iteratedFDeriv_two_ne_zero {v : E → F} {r : ℝ} (hr : 0 < r)
    (hv : DifferentiableOn ℝ v (ball 0 r))
    (h2 : iteratedFDeriv ℝ 2 v 0 ≠ 0) : ∃ y ∈ ball (0 : E) r, v y ≠ fderiv ℝ v y y := by
  by_contra h
  push Not at h
  refine h2 ?_
  have hev : v =ᶠ[𝓝 0] (fderiv ℝ v 0) := by
    filter_upwards [ball_mem_nhds (0 : E) hr] with y hy
    exact eq_fderiv_apply_of_forall_eq_fderiv_apply hv h hy
  rw [(Filter.EventuallyEq.iteratedFDeriv ℝ hev 2).eq_of_nhds]
  have hlin : fderiv ℝ (fderiv ℝ v 0) = fun _ ↦ fderiv ℝ v 0 :=
    funext fun _ ↦ ContinuousLinearMap.fderiv _
  ext m
  simp [iteratedFDeriv_two_apply, hlin]

/-- **Euler's identity of degree one.** If `f` has derivative `f'` at `x` and
`f (t • x) = t • f x` for `t` near `1`, then `f' x = f x`. -/
theorem _root_.HasFDerivAt.apply_self_eq_of_eventually_homogeneous {𝕜 E' F' : Type*}
    [NontriviallyNormedField 𝕜] [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [NormedAddCommGroup F']
    [NormedSpace 𝕜 F'] {f : E' → F'} {f' : E' →L[𝕜] F'} {x : E'} (hd : HasFDerivAt f f' x)
    (hhom : ∀ᶠ t in 𝓝 (1 : 𝕜), f (t • x) = t • f x) : f' x = f x := by
  simpa using hd.apply_self_eq_smul_of_eventuallyEq (hasDerivAt_id (1 : 𝕜)) hhom

end TauCeti

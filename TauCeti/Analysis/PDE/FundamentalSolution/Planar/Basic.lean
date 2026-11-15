/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions

import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# The planar Newtonian kernel away from its pole

This file introduces the logarithmic kernel for the negative Laplacian on the complex plane,

`G(z) = -(2 * π)⁻¹ * log ‖z‖`,

and establishes its classical pointwise properties away from the pole.  In particular, `G` and
each translate `z ↦ G (z - a)` are harmonic away from their poles.  The distributional identity
`-Δ G = δ₀` is `TauCeti.integral_laplacian_mul_planarNewtonianKernel`, in
`TauCeti.Analysis.PDE.FundamentalSolution.Planar.DistributionalLaplacian`.

Harmonicity follows from Mathlib's `AnalyticAt.harmonicAt_log_norm`: `G ∘ f` is harmonic wherever
`f` is analytic and nonzero.  The remaining results record the smoothness, translation, symmetry,
and scaling API used when the kernel is integrated against a source to form a Newtonian potential.

## Main declarations

* `TauCeti.planarNewtonianKernel`: the logarithmic kernel for `-Δ` on `ℂ`.
* `TauCeti.harmonicAt_planarNewtonianKernel`: harmonicity away from the origin.
* `TauCeti.harmonicAt_planarNewtonianKernel_sub`: harmonicity of a kernel with pole `a`.
* `AnalyticAt.harmonicAt_planarNewtonianKernel`: harmonicity of `G ∘ f` for analytic `f` off the
  zeros of `f`.
* `TauCeti.contDiffAt_planarNewtonianKernel`: smoothness away from the origin.
* `TauCeti.hasFDerivAt_planarNewtonianKernel`, `TauCeti.fderiv_planarNewtonianKernel_sub_apply`:
  the Fréchet derivative and the directional derivative of a kernel with pole `a` (the junk value
  `0` at the pole, where the kernel is not differentiable).
* `TauCeti.laplacian_planarNewtonianKernel`: the pointwise equation `Δ G = 0` (genuine off the pole;
  the value at the pole is a junk value).
* `TauCeti.laplacian_planarNewtonianKernel_sub`: the same for a kernel with pole `a`.
* `TauCeti.tendsto_planarNewtonianKernel_sub_sub_cocompact`: moving the pole changes the kernel
  by a function vanishing at infinity.
-/

public section

noncomputable section

namespace TauCeti

open Filter InnerProductSpace Laplacian Topology

/-- The Newtonian kernel for the negative Laplacian on the plane, represented as `ℂ`.

The value assigned at the pole is immaterial for the pointwise theory in this file.  Lean's
convention `Real.log 0 = 0` makes this a total function; analytically, the kernel has a logarithmic
singularity there. -/
def planarNewtonianKernel (z : ℂ) : ℝ :=
  -(2 * Real.pi)⁻¹ * Real.log ‖z‖

/-- The defining formula for the planar Newtonian kernel. -/
theorem planarNewtonianKernel_def (z : ℂ) :
    planarNewtonianKernel z = -(2 * Real.pi)⁻¹ * Real.log ‖z‖ := by
  rw [planarNewtonianKernel]

@[simp]
theorem planarNewtonianKernel_zero : planarNewtonianKernel 0 = 0 := by
  simp [planarNewtonianKernel]

@[simp]
theorem planarNewtonianKernel_neg (z : ℂ) :
    planarNewtonianKernel (-z) = planarNewtonianKernel z := by
  simp [planarNewtonianKernel]

/-- The planar Newtonian kernel is radial: its value only depends on the norm of its argument. -/
theorem planarNewtonianKernel_eq_of_norm_eq {z w : ℂ} (h : ‖z‖ = ‖w‖) :
    planarNewtonianKernel z = planarNewtonianKernel w := by
  rw [planarNewtonianKernel_def, planarNewtonianKernel_def, h]

/-- The planar Newtonian kernel is invariant under multiplication by a unit complex number. -/
theorem planarNewtonianKernel_unit_mul {u z : ℂ} (hu : ‖u‖ = 1) :
    planarNewtonianKernel (u * z) = planarNewtonianKernel z := by
  simp [planarNewtonianKernel, hu]

/-- For nonzero factors, the planar Newtonian kernel turns products into sums. -/
theorem planarNewtonianKernel_mul {z w : ℂ} (hz : z ≠ 0) (hw : w ≠ 0) :
    planarNewtonianKernel (z * w) = planarNewtonianKernel z + planarNewtonianKernel w := by
  rw [planarNewtonianKernel, planarNewtonianKernel, planarNewtonianKernel, norm_mul,
    Real.log_mul (norm_ne_zero_iff.mpr hz) (norm_ne_zero_iff.mpr hw)]
  ring

/-- The kernel with pole `a` is symmetric in its two spatial arguments. -/
theorem planarNewtonianKernel_sub_comm (z a : ℂ) :
    planarNewtonianKernel (z - a) = planarNewtonianKernel (a - z) := by
  rw [← neg_sub a z, planarNewtonianKernel_neg]

/-- The planar Newtonian kernel composed with an analytic function `f` is harmonic at every
point where `f` does not vanish. -/
theorem _root_.AnalyticAt.harmonicAt_planarNewtonianKernel {f : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f z) (hfz : f z ≠ 0) :
    HarmonicAt (fun w : ℂ ↦ planarNewtonianKernel (f w)) z := by
  have hkernel : (fun w : ℂ ↦ planarNewtonianKernel (f w)) =
      (-(2 * Real.pi)⁻¹ : ℝ) • fun w : ℂ ↦ Real.log ‖f w‖ := by
    ext w
    simp [planarNewtonianKernel_def]
  exact hkernel ▸ (hf.harmonicAt_log_norm hfz).const_smul

/-- The translated kernel `z ↦ G(z - a)` is harmonic at every point other than its pole `a`. -/
theorem harmonicAt_planarNewtonianKernel_sub {z a : ℂ} (hza : z ≠ a) :
    HarmonicAt (fun w : ℂ ↦ planarNewtonianKernel (w - a)) z :=
  (analyticAt_id.sub analyticAt_const).harmonicAt_planarNewtonianKernel (sub_ne_zero.mpr hza)

/-- The logarithmic Newtonian kernel is harmonic at every point away from its pole at `0`. -/
theorem harmonicAt_planarNewtonianKernel {z : ℂ} (hz : z ≠ 0) :
    HarmonicAt planarNewtonianKernel z := by
  simpa only [sub_zero] using
    (harmonicAt_planarNewtonianKernel_sub (z := z) (a := 0) hz)

/-- The planar Newtonian kernel is harmonic on the punctured plane. -/
theorem harmonicOnNhd_planarNewtonianKernel :
    HarmonicOnNhd planarNewtonianKernel ({0}ᶜ : Set ℂ) :=
  fun _ hz ↦ harmonicAt_planarNewtonianKernel (Set.mem_compl_singleton_iff.mp hz)

/-- A planar Newtonian kernel with pole `a` is harmonic on the complement of that pole. -/
theorem harmonicOnNhd_planarNewtonianKernel_sub (a : ℂ) :
    HarmonicOnNhd (fun z : ℂ ↦ planarNewtonianKernel (z - a)) ({a}ᶜ : Set ℂ) :=
  fun _ hz ↦ harmonicAt_planarNewtonianKernel_sub (Set.mem_compl_singleton_iff.mp hz)

/-- Away from its pole, a translated planar Newtonian kernel is `C^n` for every `n`. -/
theorem contDiffAt_planarNewtonianKernel_sub {n : WithTop ℕ∞} {z a : ℂ} (hza : z ≠ a) :
    ContDiffAt ℝ n (fun w : ℂ ↦ planarNewtonianKernel (w - a)) z := by
  have hne : z - a ≠ 0 := sub_ne_zero.mpr hza
  have hnorm : ContDiffAt ℝ n (fun w : ℂ ↦ ‖w - a‖) z :=
    (contDiffAt_id.sub contDiffAt_const).norm ℝ hne
  simp only [planarNewtonianKernel_def]
  exact contDiffAt_const.mul (hnorm.log (norm_ne_zero_iff.mpr hne))

/-- Away from its pole, the planar Newtonian kernel is `C^n` for every `n`. -/
theorem contDiffAt_planarNewtonianKernel {n : WithTop ℕ∞} {z : ℂ} (hz : z ≠ 0) :
    ContDiffAt ℝ n planarNewtonianKernel z := by
  simpa only [sub_zero] using
    (contDiffAt_planarNewtonianKernel_sub (n := n) (z := z) (a := 0) hz)

/-- Away from the origin, the planar Newtonian kernel has derivative
`-(2π)⁻¹ ‖z‖⁻² ⟪z, ·⟫`. -/
theorem hasFDerivAt_planarNewtonianKernel {z : ℂ} (hz : z ≠ 0) :
    HasFDerivAt planarNewtonianKernel
      ((-(2 * Real.pi)⁻¹ * (‖z‖ ^ 2)⁻¹) • innerSL ℝ z) z := by
  have hsq :
      HasFDerivAt (fun w : ℂ ↦ ‖w‖ ^ 2) (2 • innerSL ℝ z) z := by
    simpa only [id_eq, one_apply_eq_self, one_smul, ContinuousLinearMap.comp_id] using
      (hasFDerivAt_id z).norm_sq
  have hlog :
      HasFDerivAt (fun w : ℂ ↦ Real.log (‖w‖ ^ 2))
        ((‖z‖ ^ 2)⁻¹ • (2 • innerSL ℝ z)) z :=
    hsq.log (pow_ne_zero 2 (norm_ne_zero_iff.mpr hz))
  have heq :
      planarNewtonianKernel =
        fun w : ℂ ↦ (-(2 * Real.pi)⁻¹ / 2) * Real.log (‖w‖ ^ 2) := by
    funext w
    rw [planarNewtonianKernel_def, Real.log_pow]
    ring
  have hmap :
      ((-(2 * Real.pi)⁻¹ / 2) • ((‖z‖ ^ 2)⁻¹ • (2 • innerSL ℝ z))) =
        ((-(2 * Real.pi)⁻¹ * (‖z‖ ^ 2)⁻¹) • innerSL ℝ z) := by
    ext v
    simp only [smul_apply, innerSL_apply_apply]
    ring
  rw [heq, ← hmap]
  exact hlog.const_mul (-(2 * Real.pi)⁻¹ / 2)

/-- The planar Newtonian kernel is not differentiable at its pole: it is unbounded there, but
takes the value `0` at the origin. -/
theorem not_differentiableAt_planarNewtonianKernel_zero :
    ¬DifferentiableAt ℝ planarNewtonianKernel 0 := by
  intro h
  have hc : Filter.Tendsto planarNewtonianKernel (𝓝[≠] (0 : ℂ)) (𝓝 0) := by
    simpa using h.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))
  have hlog : Filter.Tendsto (fun z : ℂ ↦ Real.log ‖z‖) (𝓝[≠] 0) Filter.atBot :=
    Real.tendsto_log_nhdsGT_zero.comp tendsto_norm_nhdsNE_zero
  have hatTop : Filter.Tendsto planarNewtonianKernel (𝓝[≠] (0 : ℂ)) Filter.atTop := by
    rw [funext planarNewtonianKernel_def]
    exact hlog.const_mul_atBot_of_neg (by simpa using Real.pi_pos)
  exact not_tendsto_nhds_of_tendsto_atTop hatTop _ hc

/-- The Fréchet derivative of the planar Newtonian kernel as a continuous linear functional.
At the pole, where the kernel is not differentiable, both sides are `0`. -/
theorem fderiv_planarNewtonianKernel (z : ℂ) :
    fderiv ℝ planarNewtonianKernel z =
      (-(2 * Real.pi)⁻¹ * (‖z‖ ^ 2)⁻¹) • innerSL ℝ z := by
  rcases eq_or_ne z 0 with rfl | hz
  · rw [fderiv_zero_of_not_differentiableAt not_differentiableAt_planarNewtonianKernel_zero]
    simp
  · exact (hasFDerivAt_planarNewtonianKernel hz).fderiv

/-- The evaluation of `fderiv` of the planar Newtonian kernel in the direction `v` is the radial
inner product `⟪z, v⟫` scaled by `-(2π ‖z‖²)⁻¹`. Away from the pole this is the directional
derivative; at the pole, where the kernel is not differentiable, `fderiv` takes the default
value `0` and both sides are `0` (it is not an actual directional derivative). -/
theorem fderiv_planarNewtonianKernel_apply (z v : ℂ) :
    fderiv ℝ planarNewtonianKernel z v =
      (-(2 * Real.pi)⁻¹ * (‖z‖ ^ 2)⁻¹) * ⟪z, v⟫_ℝ := by
  rw [fderiv_planarNewtonianKernel]
  simp only [smul_apply, smul_eq_mul, innerSL_apply_apply]

/-- A planar Newtonian kernel with pole at `a` has the translated Fréchet derivative. -/
theorem hasFDerivAt_planarNewtonianKernel_sub {z a : ℂ} (hza : z ≠ a) :
    HasFDerivAt (fun w : ℂ ↦ planarNewtonianKernel (w - a))
      ((-(2 * Real.pi)⁻¹ * (‖z - a‖ ^ 2)⁻¹) • innerSL ℝ (z - a)) z := by
  rw [hasFDerivAt_comp_sub]
  exact hasFDerivAt_planarNewtonianKernel (sub_ne_zero.mpr hza)

/-- The formula for `fderiv` of a planar Newtonian kernel with pole at `a`; at the pole it is the
default value `0`, not an actual derivative. -/
theorem fderiv_planarNewtonianKernel_sub (z a : ℂ) :
    fderiv ℝ (fun w : ℂ ↦ planarNewtonianKernel (w - a)) z =
      (-(2 * Real.pi)⁻¹ * (‖z - a‖ ^ 2)⁻¹) • innerSL ℝ (z - a) := by
  rw [fderiv_comp_sub]
  exact fderiv_planarNewtonianKernel (z - a)

/-- The evaluation of `fderiv` of a planar Newtonian kernel with pole at `a` in the direction `v`.
Away from `a` this is the directional derivative; at the pole `fderiv` takes the default value
`0` and both sides are `0` (it is not an actual directional derivative). -/
theorem fderiv_planarNewtonianKernel_sub_apply (z a v : ℂ) :
    fderiv ℝ (fun w : ℂ ↦ planarNewtonianKernel (w - a)) z v =
      (-(2 * Real.pi)⁻¹ * (‖z - a‖ ^ 2)⁻¹) * ⟪z - a, v⟫_ℝ := by
  rw [fderiv_planarNewtonianKernel_sub]
  simp only [smul_apply, smul_eq_mul, innerSL_apply_apply]

/-- Along the real axis through the pole `a`, the derivative of the translated planar Newtonian
kernel in the direction `1` is `-(2 π t)⁻¹`. -/
private theorem fderiv_planarNewtonianKernel_sub_apply_one {a : ℂ} {t : ℝ} (ht : 0 < t) :
    fderiv ℝ (fun w : ℂ ↦ planarNewtonianKernel (w - a)) (a + t) 1 = -(2 * Real.pi)⁻¹ * t⁻¹ := by
  rw [fderiv_planarNewtonianKernel_sub_apply]
  simp [abs_of_pos ht]
  field_simp

/-- The gradient of the translated planar Newtonian kernel is not differentiable at the pole. -/
private theorem not_differentiableAt_fderiv_planarNewtonianKernel_sub (a : ℂ) :
    ¬ DifferentiableAt ℝ (fderiv ℝ (fun w : ℂ ↦ planarNewtonianKernel (w - a))) a := by
  intro hd
  have hg : ContinuousAt
      (fun s : ℝ ↦ fderiv ℝ (fun w : ℂ ↦ planarNewtonianKernel (w - a)) (a + s) 1) 0 :=
    (ContinuousLinearMap.apply ℝ ℝ (1 : ℂ)).continuous.continuousAt.comp
      (hd.continuousAt.comp_of_eq (by fun_prop : Continuous fun s : ℝ ↦ a + (s : ℂ)).continuousAt
        (by simp))
  have h1 : Tendsto (fun s : ℝ ↦ -(2 * Real.pi)⁻¹ * s⁻¹) (𝓝[>] 0) atBot :=
    tendsto_inv_nhdsGT_zero.const_mul_atTop_of_neg (by simp [Real.pi_pos])
  have h2 : Tendsto
      (fun s : ℝ ↦ fderiv ℝ (fun w : ℂ ↦ planarNewtonianKernel (w - a)) (a + s) 1) (𝓝[>] 0)
      atBot :=
    h1.congr' (by
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact (fderiv_planarNewtonianKernel_sub_apply_one hs).symm)
  exact not_tendsto_nhds_of_tendsto_atBot h2 _ (hg.tendsto.mono_left nhdsWithin_le_nhds)

/-- A translated planar Newtonian kernel solves the homogeneous Laplace equation pointwise. At
the pole the value `0` is the junk value of the non-differentiable kernel. Its nonzero
distributional Laplacian is concentrated at the pole. -/
@[simp]
theorem laplacian_planarNewtonianKernel_sub {z a : ℂ} :
    Δ (fun w : ℂ ↦ planarNewtonianKernel (w - a)) z = 0 := by
  rcases eq_or_ne z a with rfl | hza
  · rw [laplacian_eq_iteratedFDeriv_complexPlane]
    simp [iteratedFDeriv_two_apply, fderiv_zero_of_not_differentiableAt
      (not_differentiableAt_fderiv_planarNewtonianKernel_sub z)]
  · exact (harmonicAt_planarNewtonianKernel_sub hza).2.self_of_nhds

/-- The planar Newtonian kernel solves the homogeneous Laplace equation pointwise. At the pole the
value `0` is the junk value of the non-differentiable kernel. Its nonzero distributional Laplacian
`-δ₀` is concentrated at the pole. -/
@[simp]
theorem laplacian_planarNewtonianKernel {z : ℂ} : Δ planarNewtonianKernel z = 0 := by
  simpa using laplacian_planarNewtonianKernel_sub (z := z) (a := 0)

/-- Moving the pole of the planar Newtonian kernel by at most `R` changes its value at a point `z`
with `2 R ≤ ‖z‖` by at most `π⁻¹ R / ‖z‖`. -/
theorem abs_planarNewtonianKernel_sub_sub_le {z y : ℂ} {R : ℝ} (hy : ‖y‖ ≤ R)
    (hz : 2 * R ≤ ‖z‖) (hz₀ : 0 < ‖z‖) :
    |planarNewtonianKernel (z - y) - planarNewtonianKernel z| ≤ Real.pi⁻¹ * (R / ‖z‖) := by
  have hR : 0 ≤ R := (norm_nonneg y).trans hy
  have hzy : ‖z‖ - R ≤ ‖z - y‖ := by linarith [norm_sub_norm_le z y]
  have hzy' : ‖z - y‖ ≤ ‖z‖ + R := by linarith [norm_sub_le z y]
  have hhalf : ‖z‖ / 2 ≤ ‖z - y‖ := by linarith
  have hpos : 0 < ‖z - y‖ := by linarith
  -- `|log a - log b| ≤ |a - b| / min a b`, here with `|a - b| ≤ R` and `min a b ≥ ‖z‖ / 2`.
  have hlog : |Real.log ‖z - y‖ - Real.log ‖z‖| ≤ 2 * (R / ‖z‖) := by
    have h₁ : Real.log ‖z - y‖ - Real.log ‖z‖ ≤ R / ‖z‖ := by
      rw [← Real.log_div hpos.ne' hz₀.ne']
      refine (Real.log_le_sub_one_of_pos (div_pos hpos hz₀)).trans ?_
      rw [div_sub_one hz₀.ne']
      exact div_le_div_of_nonneg_right (by linarith) hz₀.le
    have h₂ : Real.log ‖z‖ - Real.log ‖z - y‖ ≤ 2 * (R / ‖z‖) := by
      rw [← Real.log_div hz₀.ne' hpos.ne']
      refine (Real.log_le_sub_one_of_pos (div_pos hz₀ hpos)).trans ?_
      rw [div_sub_one hpos.ne']
      calc (‖z‖ - ‖z - y‖) / ‖z - y‖ ≤ R / (‖z‖ / 2) :=
            div_le_div₀ hR (by linarith) (by positivity) hhalf
        _ = 2 * (R / ‖z‖) := by field_simp
    have : 0 ≤ R / ‖z‖ := div_nonneg hR hz₀.le
    rw [abs_le]
    constructor <;> linarith
  rw [planarNewtonianKernel_def, planarNewtonianKernel_def, ← mul_sub, abs_mul, abs_neg,
    abs_inv, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
  calc (2 * Real.pi)⁻¹ * |Real.log ‖z - y‖ - Real.log ‖z‖|
      ≤ (2 * Real.pi)⁻¹ * (2 * (R / ‖z‖)) := by gcongr
    _ = Real.pi⁻¹ * (R / ‖z‖) := by field_simp

/-- Moving the pole of the planar Newtonian kernel changes it by a function vanishing at
infinity: `G(z - y) - G z → 0` as `z → ∞`. -/
theorem tendsto_planarNewtonianKernel_sub_sub_cocompact (y : ℂ) :
    Tendsto (fun z ↦ planarNewtonianKernel (z - y) - planarNewtonianKernel z) (cocompact ℂ)
      (𝓝 0) := by
  set R := max ‖y‖ 1
  have hR : 0 < R := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hlim : Tendsto (fun z : ℂ ↦ Real.pi⁻¹ * (R / ‖z‖)) (cocompact ℂ) (𝓝 0) := by
    have h := (tendsto_inv_atTop_zero.comp (tendsto_norm_cocompact_atTop (E := ℂ))).const_mul R
    simpa [Function.comp_def, div_eq_mul_inv] using h.const_mul Real.pi⁻¹
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [tendsto_norm_cocompact_atTop.eventually_ge_atTop (2 * R)] with z hz
  rw [Real.norm_eq_abs]
  exact abs_planarNewtonianKernel_sub_sub_le (le_max_left _ _) hz (by linarith)
end TauCeti

end

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
* `TauCeti.laplacian_planarNewtonianKernel`: the pointwise equation `Δ G = 0` off the pole.
-/

public section

noncomputable section

namespace TauCeti

open InnerProductSpace Laplacian

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

/-- The planar Newtonian kernel solves the homogeneous Laplace equation pointwise away from its
pole.  Its nonzero distributional Laplacian is concentrated at the omitted pole. -/
@[simp]
theorem laplacian_planarNewtonianKernel {z : ℂ} (hz : z ≠ 0) :
    Δ planarNewtonianKernel z = 0 :=
  (harmonicAt_planarNewtonianKernel hz).2.self_of_nhds

/-- A translated planar Newtonian kernel solves the homogeneous Laplace equation away from its
pole. -/
@[simp]
theorem laplacian_planarNewtonianKernel_sub {z a : ℂ} (hza : z ≠ a) :
    Δ (fun w : ℂ ↦ planarNewtonianKernel (w - a)) z = 0 :=
  (harmonicAt_planarNewtonianKernel_sub hza).2.self_of_nhds

end TauCeti

end

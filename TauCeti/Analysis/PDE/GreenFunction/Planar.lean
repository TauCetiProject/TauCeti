/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.FundamentalSolution.Planar
public import TauCeti.Analysis.Complex.Conformal.PseudoHyperbolic

/-!
# The Green kernel of the planar unit disk

This file constructs the Dirichlet Green kernel of the complex unit disk from the logarithmic
Newtonian kernel.  For a pole `a` in the disk, the reflected logarithmic term has no singularity
in the disk.  Subtracting it from the Newtonian kernel gives a function harmonic away from `a`
and zero on the unit circle.

The kernel is the basic ingredient for representing solutions of the planar Dirichlet problem by
Green potentials.  Its normalization agrees with `planarNewtonianKernel`, hence with the
negative-Laplacian convention used by the fundamental-solution development.

The construction is the standard method-of-images formula; see Evans, *Partial Differential
Equations*, Chapter 2, Section 2.2.

## Main declarations

* `TauCeti.planarGreenKernel`: the Dirichlet Green kernel of the unit disk.
* `TauCeti.planarGreenKernel_def`: its formula in terms of Newtonian kernels.
* `TauCeti.harmonicAt_planarGreenKernel`: harmonicity away from the pole in the disk.
* `TauCeti.planarGreenKernel_eq_zero_of_norm_eq_one`: vanishing on the unit circle.
-/

public section

noncomputable section

namespace TauCeti

open Complex InnerProductSpace Metric

/-- The Dirichlet Green kernel of the complex unit disk, with pole `a`.

For `‖a‖ < 1`, the second term is harmonic throughout the disk.  Thus the first term supplies the
Newtonian singularity at `a`, while the difference vanishes on the unit circle. -/
def planarGreenKernel (a z : ℂ) : ℝ :=
  planarNewtonianKernel (z - a) - planarNewtonianKernel (1 - starRingEnd ℂ a * z)

/-- The defining formula for the planar Green kernel. -/
theorem planarGreenKernel_def (a z : ℂ) :
    planarGreenKernel a z =
      planarNewtonianKernel (z - a) - planarNewtonianKernel (1 - starRingEnd ℂ a * z) := by
  rfl

/-- The reflected logarithmic term in `planarGreenKernel` is harmonic at every point of the
unit disk when the pole lies in the disk. -/
private theorem harmonicAt_planarNewtonianKernel_one_sub_conj_mul {a z : ℂ}
    (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) :
    HarmonicAt (fun w : ℂ ↦ planarNewtonianKernel (1 - starRingEnd ℂ a * w)) z := by
  have hne : 1 - starRingEnd ℂ a * z ≠ 0 :=
    one_sub_conj_mul_ne_zero_of_norm_lt_one hz ha
  have hana : AnalyticAt ℂ (fun w : ℂ ↦ 1 - starRingEnd ℂ a * w) z := by
    fun_prop
  have hlog : HarmonicAt (fun w : ℂ ↦ Real.log ‖1 - starRingEnd ℂ a * w‖) z :=
    hana.harmonicAt_log_norm hne
  have hkernel :
      (fun w : ℂ ↦ planarNewtonianKernel (1 - starRingEnd ℂ a * w)) =
        (-(2 * Real.pi)⁻¹ : ℝ) • fun w : ℂ ↦ Real.log ‖1 - starRingEnd ℂ a * w‖ := by
    funext w
    simp only [planarNewtonianKernel_def, Pi.smul_apply, smul_eq_mul]
  rw [hkernel]
  exact hlog.const_smul

/-- Away from its pole, the planar Green kernel is harmonic inside the unit disk. -/
theorem harmonicAt_planarGreenKernel {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ < 1)
    (hza : z ≠ a) :
    HarmonicAt (planarGreenKernel a) z := by
  have hformula : planarGreenKernel a =
      (fun w : ℂ ↦ planarNewtonianKernel (w - a)) -
        (fun w : ℂ ↦ planarNewtonianKernel (1 - starRingEnd ℂ a * w)) := by
    funext w
    exact planarGreenKernel_def a w
  rw [hformula]
  exact (harmonicAt_planarNewtonianKernel_sub hza).sub
    (harmonicAt_planarNewtonianKernel_one_sub_conj_mul ha hz)

/-- The difference between the planar Green kernel and its Newtonian singular term is harmonic
throughout the unit disk. -/
theorem harmonicAt_planarGreenKernel_sub_newtonianKernel {a z : ℂ}
    (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) :
    HarmonicAt (fun w : ℂ ↦ planarGreenKernel a w - planarNewtonianKernel (w - a)) z := by
  simpa only [planarGreenKernel_def, sub_sub_cancel_left, Pi.neg_def] using
    (harmonicAt_planarNewtonianKernel_one_sub_conj_mul ha hz).neg

/-- Away from its pole, the planar Green kernel is positive inside the unit disk. -/
theorem planarGreenKernel_pos {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ < 1)
    (hza : z ≠ a) : 0 < planarGreenKernel a z := by
  have hnormpos : 0 < ‖z - a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hza)
  have hdenpos : 0 < ‖1 - starRingEnd ℂ a * z‖ :=
    norm_pos_iff.mpr (one_sub_conj_mul_ne_zero_of_norm_lt_one hz ha)
  have hlog : Real.log ‖z - a‖ < Real.log ‖1 - starRingEnd ℂ a * z‖ :=
    Real.strictMonoOn_log hnormpos hdenpos
      (norm_sub_lt_norm_one_sub_conj_mul_of_norm_lt_one hz ha)
  have hc : 0 < (2 * Real.pi)⁻¹ := inv_pos.mpr (mul_pos (by norm_num) Real.pi_pos)
  rw [planarGreenKernel, planarNewtonianKernel_def, planarNewtonianKernel_def]
  nlinarith

/-- The planar Green kernel satisfies the homogeneous Dirichlet boundary condition on the unit
 circle. -/
@[simp] theorem planarGreenKernel_eq_zero_of_norm_eq_one {a z : ℂ} (hz : ‖z‖ = 1) :
    planarGreenKernel a z = 0 := by
  have hmul : z * starRingEnd ℂ z = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]
    norm_num
  have hfactor : z * (1 - starRingEnd ℂ z * a) = z - a := by
    calc
      z * (1 - starRingEnd ℂ z * a) = z - (z * starRingEnd ℂ z) * a := by ring
      _ = z - a := by rw [hmul, one_mul]
  have hnorm : ‖z - a‖ = ‖1 - starRingEnd ℂ a * z‖ := by
    calc
      ‖z - a‖ = ‖z * (1 - starRingEnd ℂ z * a)‖ := by rw [hfactor]
      _ = ‖1 - starRingEnd ℂ z * a‖ := by rw [norm_mul, hz, one_mul]
      _ = ‖starRingEnd ℂ (1 - starRingEnd ℂ z * a)‖ := (Complex.norm_conj _).symm
      _ = ‖1 - starRingEnd ℂ a * z‖ := by simp [mul_comm]
  rw [planarGreenKernel, planarNewtonianKernel_def, planarNewtonianKernel_def,
    hnorm, sub_self]

end TauCeti

end

end

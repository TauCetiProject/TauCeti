/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.GreenFunction.Planar
public import TauCeti.Analysis.InnerProductSpace.Harmonic.Dilation
public import TauCeti.Analysis.Normed.Module.Ball

/-!
# The planar Green kernel on a disk

Translation and dilation carry the Green kernel of the complex unit disk to any disk of
positive radius. The resulting kernel is harmonic away from its pole, positive in the disk,
and zero on its boundary. Its singular part is the scaled planar Newtonian kernel;
the difference is harmonic throughout the disk. These properties allow the kernel to be
used in Green-potential representations on balls with arbitrary center and radius.

The normalization follows the standard method-of-images formula in Evans,
*Partial Differential Equations*, Chapter 2, Section 2.2.
-/

public section

noncomputable section

namespace TauCeti

open InnerProductSpace

/-- The Dirichlet Green kernel of the disk `Metric.ball c R`, obtained from the unit-disk
kernel by the similarity `z ↦ R⁻¹ • (z - c)`. The parameter `R` is intended to be positive. -/
def planarGreenKernelDisk (c : ℂ) (R : ℝ) (a z : ℂ) : ℝ :=
  planarGreenKernel (R⁻¹ • (a - c)) (R⁻¹ • (z - c))

/-- The disk kernel is the unit-disk kernel in normalized coordinates. -/
theorem planarGreenKernelDisk_def (c : ℂ) (R : ℝ) (a z : ℂ) :
    planarGreenKernelDisk c R a z =
      planarGreenKernel (R⁻¹ • (a - c)) (R⁻¹ • (z - c)) := by
  rw [planarGreenKernelDisk]

/-- The disk kernel specializes to the unit-disk kernel. -/
@[simp] theorem planarGreenKernelDisk_zero_one (a z : ℂ) :
    planarGreenKernelDisk 0 1 a z = planarGreenKernel a z := by
  simp [planarGreenKernelDisk]

/-- The Green kernel is harmonic in the disk away from its pole. -/
theorem harmonicAt_planarGreenKernelDisk {c a z : ℂ} {R : ℝ} (hR : 0 < R)
    (ha : ‖a - c‖ < R) (hz : ‖z - c‖ < R) (hza : z ≠ a) :
    HarmonicAt (planarGreenKernelDisk c R a) z := by
  have hRne : R⁻¹ ≠ 0 := inv_ne_zero hR.ne'
  have hnormalized : R⁻¹ • (z - c) ≠ R⁻¹ • (a - c) := by
    intro heq
    have := smul_right_injective ℂ hRne heq
    exact hza (sub_left_inj.mp this)
  have hh := harmonicAt_planarGreenKernel (norm_inv_smul_sub_lt_one hR ha)
    (norm_inv_smul_sub_lt_one hR hz) hnormalized
  have hfun : planarGreenKernelDisk c R a =
      fun w : ℂ ↦ planarGreenKernel (R⁻¹ • (a - c)) (-(R⁻¹ • c) + R⁻¹ • w) := by
    funext w
    simp only [planarGreenKernelDisk_def, smul_sub, neg_add_eq_sub]
  rw [hfun]
  exact (harmonicAt_comp_const_add_smul_iff (x := -(R⁻¹ • c)) hRne).2
    (by simpa only [smul_sub, neg_add_eq_sub] using hh)

/-- The Green kernel vanishes on the boundary circle of its disk. -/
@[simp] theorem planarGreenKernelDisk_eq_zero_of_norm_sub_eq {c a z : ℂ} {R : ℝ}
    (hR : 0 < R) (hz : ‖z - c‖ = R) :
    planarGreenKernelDisk c R a z = 0 := by
  apply planarGreenKernel_eq_zero_of_norm_eq_one
  exact norm_inv_smul_sub_eq_one_of_norm_sub_eq hR hz

/-- The Green kernel is strictly positive inside the disk away from its pole. -/
theorem planarGreenKernelDisk_pos {c a z : ℂ} {R : ℝ} (hR : 0 < R)
    (ha : ‖a - c‖ < R) (hz : ‖z - c‖ < R) (hza : z ≠ a) :
    0 < planarGreenKernelDisk c R a z := by
  have hRne : R⁻¹ ≠ 0 := inv_ne_zero hR.ne'
  have hnormalized : R⁻¹ • (z - c) ≠ R⁻¹ • (a - c) := by
    intro heq
    have := smul_right_injective ℂ hRne heq
    exact hza (sub_left_inj.mp this)
  exact planarGreenKernel_pos (norm_inv_smul_sub_lt_one hR ha)
    (norm_inv_smul_sub_lt_one hR hz) hnormalized

/-- The difference between the disk Green kernel and its scaled Newtonian singularity is
harmonic throughout the disk, including at the pole. The scale matters at the pole because
the totalized logarithmic kernel has the assigned value zero there. -/
theorem harmonicAt_planarGreenKernelDisk_sub_newtonianKernel {c a z : ℂ} {R : ℝ}
    (hR : 0 < R) (ha : ‖a - c‖ < R) (hz : ‖z - c‖ < R) :
    HarmonicAt (fun w : ℂ ↦ planarGreenKernelDisk c R a w -
      planarNewtonianKernel (R⁻¹ • (w - a))) z := by
  have hRne : R⁻¹ ≠ 0 := inv_ne_zero hR.ne'
  have hh := harmonicAt_planarGreenKernel_sub_newtonianKernel
    (norm_inv_smul_sub_lt_one hR ha) (norm_inv_smul_sub_lt_one hR hz)
  have hfun : (fun w : ℂ ↦ planarGreenKernelDisk c R a w -
      planarNewtonianKernel (R⁻¹ • (w - a))) =
      fun w : ℂ ↦ planarGreenKernel (R⁻¹ • (a - c)) (-(R⁻¹ • c) + R⁻¹ • w) -
        planarNewtonianKernel ((-(R⁻¹ • c) + R⁻¹ • w) - R⁻¹ • (a - c)) := by
    funext w
    rw [planarGreenKernelDisk_def]
    simp only [smul_sub, neg_add_eq_sub]
    congr 1
    abel_nf
  rw [hfun]
  exact (harmonicAt_comp_const_add_smul_iff (x := -(R⁻¹ • c)) hRne).2
    (by simpa only [neg_add_eq_sub, ← smul_sub] using hh)

/-- The Green kernel of a positive-radius disk is differentiable at a boundary point when
its pole lies inside the disk. -/
theorem differentiableAt_planarGreenKernelDisk_boundary {c a z : ℂ} {R : ℝ}
    (hR : 0 < R) (ha : ‖a - c‖ < R) (hz : ‖z - c‖ = R) :
    DifferentiableAt ℝ (planarGreenKernelDisk c R a) z := by
  have hz' := norm_inv_smul_sub_eq_one_of_norm_sub_eq hR hz
  have hcoord : DifferentiableAt ℝ (fun w : ℂ => R⁻¹ • (w - c)) z := by
    fun_prop
  -- The disk kernel is opaque here, so use its public equation to rewrite the whole function.
  have hfun : planarGreenKernelDisk c R a =
      fun w : ℂ => planarGreenKernel (R⁻¹ • (a - c)) (R⁻¹ • (w - c)) :=
    funext (planarGreenKernelDisk_def c R a)
  rw [hfun]
  simpa only [Function.comp_def] using
    (differentiableAt_planarGreenKernel_boundary
      (norm_inv_smul_sub_lt_one hR ha) hz').comp z hcoord

end TauCeti

end

end

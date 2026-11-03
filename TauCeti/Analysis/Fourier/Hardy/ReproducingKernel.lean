/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fourier.Hardy.DiskFunction
import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# Reproducing kernels of the boundary Hardy space

Point evaluation of the holomorphic disk function is a bounded linear functional on
`TauCeti.HardySpace`. Its Riesz representative is the Szegő kernel, whose nonnegative
Fourier coefficients are the powers of the conjugate evaluation point. Its disk function is
`z ↦ (1 - conj w * z)⁻¹`. The exact norm of this vector gives the sharp norm of evaluation.

The normalized kernels, Mathlib's `NormedSpace.normalize` of the Szegő kernels, have norm one
and reproduce evaluation multiplied by `√(1 - ‖w‖ ^ 2)`. Points are carried by the open unit
disk, so the constructions require no choices of values at boundary or exterior points.

## References

* J. B. Conway, *A Course in Functional Analysis*, second edition.
* P. L. Duren, *Theory of Hᵖ Spaces*, chapter 1.

The construction uses Mathlib's Riesz equivalence `InnerProductSpace.toDual` and the bounded
evaluation theorem for `HardySpace.diskFunction`.
-/

public section

noncomputable section

open scoped InnerProductSpace

namespace TauCeti.HardySpace

variable (w : Metric.ball (0 : ℂ) 1)

/-- Evaluation of the holomorphic disk function at an interior point, as a bounded linear map. -/
def diskEvaluation : HardySpace →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun x => x.diskFunction w
      map_add' := fun x y => x.diskFunction_add y
        (by simpa only [Metric.mem_ball, dist_zero_right] using w.property)
      map_smul' := fun c x => x.diskFunction_smul c
        (by simpa only [Metric.mem_ball, dist_zero_right] using w.property) }
    (√(1 - ‖(w : ℂ)‖ ^ 2))⁻¹ fun x => by
      simpa only [LinearMap.coe_mk, AddHom.coe_mk, div_eq_mul_inv, mul_comm] using
        x.norm_diskFunction_le (by simpa only [Metric.mem_ball, dist_zero_right] using w.property)

/-- The bounded evaluation map agrees with the disk function. -/
@[simp]
theorem diskEvaluation_apply (x : HardySpace) : diskEvaluation w x = x.diskFunction w :=
  (rfl)

/-- The Szegő reproducing kernel at an interior point, as a boundary Hardy vector. -/
def reproducingKernel : HardySpace :=
  (InnerProductSpace.toDual ℂ HardySpace).symm (diskEvaluation w)

/-- Pairing with the Szegő kernel reproduces the disk function, with the inner product
conjugate linear in its first argument. -/
@[simp↓]
theorem inner_reproducingKernel (x : HardySpace) :
    ⟪reproducingKernel w, x⟫_ℂ = x.diskFunction w := by
  simp [reproducingKernel]

/-- The nonnegative Fourier coordinates of the kernel are the powers of the conjugate point. -/
@[simp]
theorem hardyBasis_repr_reproducingKernel (n : ℕ) :
    hardyBasis.repr (reproducingKernel w) n = (starRingEnd ℂ (w : ℂ)) ^ n := by
  rw [HilbertBasis.repr_apply_apply, ← inner_conj_symm, inner_reproducingKernel,
    diskFunction_hardyBasis, map_pow]

/-- The kernel is characterized uniquely by its reproducing property. -/
theorem eq_reproducingKernel_iff (k : HardySpace) :
    k = reproducingKernel w ↔ ∀ x : HardySpace, ⟪k, x⟫_ℂ = x.diskFunction w := by
  constructor
  · rintro rfl x
    exact inner_reproducingKernel w x
  · intro h
    exact ext_inner_right ℂ fun x => (h x).trans (inner_reproducingKernel w x).symm

/-- The disk function of the Szegő kernel is its usual geometric-series expression. -/
@[simp↓]
theorem diskFunction_reproducingKernel {z : ℂ} (hz : ‖z‖ < 1) :
    (reproducingKernel w).diskFunction z = (1 - starRingEnd ℂ (w : ℂ) * z)⁻¹ := by
  have hw : ‖(w : ℂ)‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using w.property
  have hprod : ‖starRingEnd ℂ (w : ℂ) * z‖ < 1 := by
    rw [norm_mul, Complex.norm_conj]
    nlinarith [norm_nonneg (w : ℂ), norm_nonneg z]
  rw [diskFunction_def]
  simp_rw [← hardyBasis_repr, hardyBasis_repr_reproducingKernel, ← mul_pow]
  exact tsum_geometric_of_norm_lt_one hprod

/-- The squared norm of the Szegő kernel. -/
theorem norm_reproducingKernel_sq :
    ‖reproducingKernel w‖ ^ 2 = (1 - ‖(w : ℂ)‖ ^ 2)⁻¹ := by
  have hw : ‖(w : ℂ)‖ < 1 := by
    simpa only [Metric.mem_ball, dist_zero_right] using w.property
  have hpos : 0 < 1 - ‖(w : ℂ)‖ ^ 2 := by nlinarith [norm_nonneg (w : ℂ)]
  calc
    ‖reproducingKernel w‖ ^ 2 = ‖⟪reproducingKernel w, reproducingKernel w⟫_ℂ‖ :=
      by rw [← inner_self_re_eq_norm, inner_self_eq_norm_sq]
    _ = ‖(1 - starRingEnd ℂ (w : ℂ) * (w : ℂ))⁻¹‖ := by
      rw [inner_reproducingKernel, diskFunction_reproducingKernel w hw]
    _ = (1 - ‖(w : ℂ)‖ ^ 2)⁻¹ := by
      rw [norm_inv, Complex.conj_mul', ← Complex.ofReal_pow, ← Complex.ofReal_one,
        ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]

/-- The norm of the Szegő kernel is the reciprocal square root of the disk defect. -/
theorem norm_reproducingKernel :
    ‖reproducingKernel w‖ = (√(1 - ‖(w : ℂ)‖ ^ 2))⁻¹ := by
  rw [← Real.sqrt_inv, ← norm_reproducingKernel_sq, Real.sqrt_sq (norm_nonneg _)]

/-- Evaluation has sharp norm equal to the norm of its reproducing kernel. -/
theorem norm_diskEvaluation :
    ‖diskEvaluation w‖ = (√(1 - ‖(w : ℂ)‖ ^ 2))⁻¹ := by
  rw [← norm_reproducingKernel]
  exact ((InnerProductSpace.toDual ℂ HardySpace).symm.norm_map (diskEvaluation w)).symm

/-- The Szegő kernel is nonzero. -/
@[simp]
theorem reproducingKernel_ne_zero : reproducingKernel w ≠ 0 := by
  have hw : ‖(w : ℂ)‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using w.property
  have hpos : 0 < 1 - ‖(w : ℂ)‖ ^ 2 := by nlinarith [norm_nonneg (w : ℂ)]
  rw [← norm_pos_iff, norm_reproducingKernel]
  exact inv_pos.mpr (Real.sqrt_pos.mpr hpos)

/-- The unit-norm Szegő kernel `NormedSpace.normalize (reproducingKernel w)` is the kernel
scaled by the positive square root of the disk defect. -/
theorem normalize_reproducingKernel :
    NormedSpace.normalize (reproducingKernel w) =
      (√(1 - ‖(w : ℂ)‖ ^ 2) : ℂ) • reproducingKernel w := by
  rw [NormedSpace.normalize, norm_reproducingKernel, inv_inv]
  exact (Complex.coe_smul ..).symm

/-- Pairing with a normalized kernel is the corresponding scaled evaluation. -/
@[simp↓]
theorem inner_normalize_reproducingKernel (x : HardySpace) :
    ⟪NormedSpace.normalize (reproducingKernel w), x⟫_ℂ =
      (√(1 - ‖(w : ℂ)‖ ^ 2) : ℂ) * x.diskFunction w := by
  rw [normalize_reproducingKernel,
    inner_smul_left (𝕜 := ℂ) (E := HardySpace), inner_reproducingKernel]
  simp only [Complex.conj_ofReal]

/-- Every normalized Szegő kernel has norm one. -/
@[simp↓]
theorem norm_normalize_reproducingKernel :
    ‖NormedSpace.normalize (reproducingKernel w)‖ = 1 :=
  NormedSpace.norm_normalize_eq_one_iff.mpr (reproducingKernel_ne_zero w)

/-- The normalized Szegő kernel has the normalized geometric-series disk function. -/
@[simp↓]
theorem diskFunction_normalize_reproducingKernel {z : ℂ} (hz : ‖z‖ < 1) :
    (NormedSpace.normalize (reproducingKernel w)).diskFunction z =
      (√(1 - ‖(w : ℂ)‖ ^ 2) : ℂ) * (1 - starRingEnd ℂ (w : ℂ) * z)⁻¹ := by
  rw [normalize_reproducingKernel, diskFunction_smul _ _ hz,
    diskFunction_reproducingKernel w hz]

end TauCeti.HardySpace

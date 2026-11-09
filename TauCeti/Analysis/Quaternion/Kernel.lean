/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import TauCeti.Analysis.Quaternion.Fueter
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# The Cauchy–Fueter kernel

The kernel `cauchyFueterKernel q q₀` is `(q - q₀)⁻¹ / ‖q - q₀‖²`, with value zero at
its pole. We use the equivalent expression `‖q - q₀‖⁻⁴ • star (q - q₀)` to compute its
real derivative and prove both Fueter equations away from the pole. Together with
`RightFueterAt.sum_fderiv_mul_leftFueterAt`, these give zero divergence for both ordered
kernel-weighted boundary forms in the Cauchy–Fueter formula.

## References

* I. Frenkel and M. Libine, *Quaternionic analysis, representation theory and physics*,
  Adv. Math. 218 (2008), arXiv:0711.2699v5, §2.2, Proposition 3.
-/

public section

open Quaternion
open scoped RealInnerProductSpace

namespace TauCeti

/-- The Cauchy–Fueter kernel with pole `q₀`, totalized to zero at the pole. -/
noncomputable def cauchyFueterKernel (q q₀ : ℍ) : ℍ :=
  (‖q - q₀‖ ^ 4)⁻¹ • star (q - q₀)

/-- The conjugate-over-fourth-power expression for the kernel, including its value at the pole. -/
theorem cauchyFueterKernel_eq (q q₀ : ℍ) :
    cauchyFueterKernel q q₀ = (‖q - q₀‖ ^ 4)⁻¹ • star (q - q₀) :=
  (rfl)

@[simp]
theorem cauchyFueterKernel_self (q₀ : ℍ) : cauchyFueterKernel q₀ q₀ = 0 := by
  simp [cauchyFueterKernel_eq]

/-- The kernel is the inverse displacement divided by its squared Euclidean norm. -/
theorem cauchyFueterKernel_eq_inv (q q₀ : ℍ) :
    cauchyFueterKernel q q₀ = (‖q - q₀‖ ^ 2)⁻¹ • (q - q₀)⁻¹ := by
  rw [cauchyFueterKernel_eq, Quaternion.inv_def, normSq_eq_norm_mul_self, smul_smul]
  congr 1
  ring

/-- Translating both arguments does not change the kernel. -/
@[simp]
theorem cauchyFueterKernel_add_right (q q₀ a : ℍ) :
    cauchyFueterKernel (q + a) (q₀ + a) = cauchyFueterKernel q q₀ := by
  simp [cauchyFueterKernel_eq]

/-- Quaternion conjugation conjugates the kernel without changing its magnitude. -/
@[simp]
theorem cauchyFueterKernel_star (q q₀ : ℍ) :
    cauchyFueterKernel (star q) (star q₀) = star (cauchyFueterKernel q q₀) := by
  simp [cauchyFueterKernel_eq, ← star_sub]

/-- The kernel has magnitude the inverse cube of the distance from its pole. -/
@[simp]
theorem norm_cauchyFueterKernel (q q₀ : ℍ) :
    ‖cauchyFueterKernel q q₀‖ = (‖q - q₀‖ ^ 3)⁻¹ := by
  rw [cauchyFueterKernel_eq_inv, norm_smul]
  simp
  ring

/-- The kernel times the displacement is the inverse squared distance, `G(r) * r = ‖r‖⁻²`,
including at the pole, where both sides are `0`. -/
theorem _root_.Quaternion.cauchyFueterKernel_mul_sub (q q₀ : ℍ) :
    cauchyFueterKernel q q₀ * (q - q₀) = ((‖q - q₀‖ ^ 2)⁻¹ : ℝ) := by
  rw [cauchyFueterKernel_eq, smul_mul_assoc, Quaternion.star_mul_self, normSq_eq_norm_mul_self,
    ← Quaternion.coe_smul, smul_eq_mul]
  congr 1
  by_cases hr : ‖q - q₀‖ = 0
  · simp [hr]
  · field_simp

/-- Real dilation scales the kernel by the inverse cube, also with the totalized value
at a zero dilation. -/
theorem cauchyFueterKernel_smul (r : ℝ) (q q₀ : ℍ) :
    cauchyFueterKernel (r • q) (r • q₀) = (r ^ 3)⁻¹ • cauchyFueterKernel q q₀ := by
  simp only [cauchyFueterKernel_eq, ← smul_sub, norm_smul, mul_pow, mul_inv_rev,
    Quaternion.star_smul, smul_smul]
  congr 1
  rw [Real.norm_eq_abs, (by decide : Even 4).pow_abs]
  by_cases hr : r = 0
  · simp [hr]
  · field_simp

/-- The kernel is smooth at every point other than its pole. -/
theorem contDiffAt_cauchyFueterKernel {q q₀ : ℍ} (hq : q ≠ q₀) {n : WithTop ℕ∞} :
    ContDiffAt ℝ n (fun x ↦ cauchyFueterKernel x q₀) q := by
  let C : ℍ →L[ℝ] ℍ :=
    ((Quaternion.starAe : ℍ ≃ₐ[ℝ] ℍᵐᵒᵖ).toLinearEquiv.trans
      (MulOpposite.opLinearEquiv ℝ).symm).toContinuousLinearMap
  have hC (x : ℍ) : C x = star x := rfl
  have hr : ContDiffAt ℝ n (fun x : ℍ ↦ x - q₀) q := contDiffAt_id.sub contDiffAt_const
  have hs := ((hr.norm_sq ℝ).pow 2).inv (pow_ne_zero 2 (pow_ne_zero 2
    (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hq))))
  convert hs.fun_smul (C.contDiff.contDiffAt.comp q hr) using 1
  funext x
  simp [cauchyFueterKernel_eq, hC, ← pow_mul]

/-- The kernel is continuous on every set that avoids its pole. -/
theorem continuousOn_cauchyFueterKernel {s : Set ℍ} {q₀ : ℍ} (h : q₀ ∉ s) :
    ContinuousOn (fun q ↦ cauchyFueterKernel q q₀) s := by
  intro q hq
  exact (contDiffAt_cauchyFueterKernel (ne_of_mem_of_not_mem hq h)
    (n := 0)).continuousAt.continuousWithinAt

/-- The real derivative of the kernel, evaluated in an arbitrary tangent direction. -/
theorem fderiv_cauchyFueterKernel_apply {q q₀ : ℍ} (hq : q ≠ q₀) (h : ℍ) :
    fderiv ℝ (fun x ↦ cauchyFueterKernel x q₀) q h =
      (‖q - q₀‖ ^ 4)⁻¹ • star h -
        (4 * ⟪q - q₀, h⟫ / ‖q - q₀‖ ^ 6) • star (q - q₀) := by
  let C : ℍ →L[ℝ] ℍ :=
    ((Quaternion.starAe : ℍ ≃ₐ[ℝ] ℍᵐᵒᵖ).toLinearEquiv.trans
      (MulOpposite.opLinearEquiv ℝ).symm).toContinuousLinearMap
  have hC (x : ℍ) : C x = star x := rfl
  have hr := (hasFDerivAt_id (𝕜 := ℝ) q).sub_const q₀
  have hs := (hasDerivAt_inv (pow_ne_zero 2 (pow_ne_zero 2
    (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hq))))).comp_hasFDerivAt q ((hr.norm_sq).pow 2)
  have hd := hs.fun_smul (C.hasFDerivAt.comp q hr)
  have he := congrArg (fun D : ℍ →L[ℝ] ℍ ↦ D h) hd.fderiv
  simp only [Function.comp_def, hC, ← pow_mul, id_eq] at he
  simp_rw [cauchyFueterKernel_eq]
  rw [he]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smulRight_apply, hC, innerSL_apply_apply, smul_eq_mul,
    smul_smul, sub_eq_add_neg, ← neg_smul, nsmul_eq_mul, Nat.reduceSub, Nat.reduceMul]
  congr 1
  congr 1
  field_simp [norm_ne_zero_iff.mpr (sub_ne_zero.mpr hq)]
  ring

/-- The kernel satisfies the left Fueter equation away from the pole. -/
theorem leftFueterAt_cauchyFueterKernel {q q₀ : ℍ} (hq : q ≠ q₀) :
    LeftFueterAt (fun x ↦ cauchyFueterKernel x q₀) q := by
  apply ((contDiffAt_cauchyFueterKernel hq (n := 1)).differentiableAt
    one_ne_zero).hasFDerivAt.leftFueterAt_iff.mpr
  rw [fueterLeft_apply]
  simp only [fderiv_cauchyFueterKernel_apply hq]
  have hn := normSq_eq_norm_mul_self (q - q₀)
  simp only [normSq_def', re_sub, imI_sub, imJ_sub, imK_sub] at hn
  have hn0 : ‖q - q₀‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hq)
  ext <;> simp [Quaternion.inner_def] <;> field_simp
  <;> nlinarith [hn]

/-- The kernel is left Fueter regular on every set that avoids its pole. -/
theorem leftFueterOn_cauchyFueterKernel {s : Set ℍ} {q₀ : ℍ} (h : q₀ ∉ s) :
    LeftFueterOn (fun q ↦ cauchyFueterKernel q q₀) s :=
  leftFueterOn_iff.mpr fun _ hq ↦
    leftFueterAt_cauchyFueterKernel (ne_of_mem_of_not_mem hq h)

/-- The kernel satisfies the right Fueter equation away from the pole. -/
theorem rightFueterAt_cauchyFueterKernel {q q₀ : ℍ} (hq : q ≠ q₀) :
    RightFueterAt (fun x ↦ cauchyFueterKernel x q₀) q := by
  apply ((contDiffAt_cauchyFueterKernel hq (n := 1)).differentiableAt
    one_ne_zero).hasFDerivAt.rightFueterAt_iff.mpr
  rw [fueterRight_apply]
  simp only [fderiv_cauchyFueterKernel_apply hq]
  have hn := normSq_eq_norm_mul_self (q - q₀)
  simp only [normSq_def', re_sub, imI_sub, imJ_sub, imK_sub] at hn
  have hn0 : ‖q - q₀‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hq)
  ext <;> simp [Quaternion.inner_def] <;> field_simp
  <;> nlinarith [hn]

/-- The kernel is right Fueter regular on every set that avoids its pole. -/
theorem rightFueterOn_cauchyFueterKernel {s : Set ℍ} {q₀ : ℍ} (h : q₀ ∉ s) :
    RightFueterOn (fun q ↦ cauchyFueterKernel q q₀) s :=
  rightFueterOn_iff.mpr fun _ hq ↦
    rightFueterAt_cauchyFueterKernel (ne_of_mem_of_not_mem hq h)

end TauCeti

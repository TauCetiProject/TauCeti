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
import TauCeti.Analysis.Calculus.IteratedFDeriv.CompContinuousLinearEquiv
import TauCeti.Analysis.Calculus.IteratedFDeriv.Homogeneous

/-!
# The Cauchy–Fueter kernel

The kernel `cauchyFueterKernel q q₀` is `(q - q₀)⁻¹ / ‖q - q₀‖²`, with value zero at
its pole. We use the equivalent expression `‖q - q₀‖⁻⁴ • star (q - q₀)` to compute its
real derivative and prove both Fueter equations away from the pole. Together with
`RightFueterAt.sum_fderiv_mul_leftFueterAt`, these give zero divergence for both ordered
kernel-weighted boundary forms in the Cauchy–Fueter formula.

Homogeneity of degree `-3` bounds the `m`-th real derivative by
`C / ‖q - q₀‖^(3 + m)`, with a positive constant depending only on the prescribed
maximum order. Derivatives in the second argument have the same bound and differ
from spatial derivatives by `(-1)^m`. Positive separation gives uniform bounds,
including on closed balls about the pole, for differentiating boundary integrals.
The compact-sphere argument is supplied by
`TauCeti.exists_norm_iteratedFDeriv_le_mul_zpow_of_smul_eq`.

## References

* I. Frenkel and M. Libine, *Quaternionic analysis, representation theory and physics*,
  Adv. Math. 218 (2008), arXiv:0711.2699v5, §2.2, Proposition 3 and Theorem 9
  (the integral formula).
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

/-- The kernel is smooth in its second argument away from the first argument. -/
theorem contDiffAt_cauchyFueterKernel_right {q q₀ : ℍ} (hq : q ≠ q₀)
    {n : WithTop ℕ∞} : ContDiffAt ℝ n (cauchyFueterKernel q) q₀ := by
  -- Eta-expand so the pointwise kernel formula can rewrite the partially applied function.
  change ContDiffAt ℝ n (fun x ↦ cauchyFueterKernel q x) q₀
  simpa [Function.comp_def, cauchyFueterKernel_eq] using
    (contDiffAt_cauchyFueterKernel (sub_ne_zero.mpr hq) (n := n)).comp q₀
      (contDiffAt_const.sub contDiffAt_id)

/-- The kernel is continuous on every set that avoids its pole. -/
theorem continuousOn_cauchyFueterKernel {s : Set ℍ} {q₀ : ℍ} (h : q₀ ∉ s) :
    ContinuousOn (fun q ↦ cauchyFueterKernel q q₀) s := by
  intro q hq
  exact (contDiffAt_cauchyFueterKernel (ne_of_mem_of_not_mem hq h)
    (n := 0)).continuousAt.continuousWithinAt

/-- The kernel is continuous in its second argument on every set avoiding the first argument. -/
theorem continuousOn_cauchyFueterKernel_right {s : Set ℍ} {q : ℍ} (h : q ∉ s) :
    ContinuousOn (cauchyFueterKernel q) s := by
  intro q₀ hq₀
  exact (contDiffAt_cauchyFueterKernel_right (ne_of_mem_of_not_mem hq₀ h).symm
    (n := 0)).continuousAt.continuousWithinAt

/-- The real derivative of the kernel, evaluated in an arbitrary tangent direction. At the pole
the kernel is not differentiable and both sides vanish. -/
theorem fderiv_cauchyFueterKernel_apply {q q₀ : ℍ} (h : ℍ) :
    fderiv ℝ (fun x ↦ cauchyFueterKernel x q₀) q h =
      (‖q - q₀‖ ^ 4)⁻¹ • star h -
        (4 * ⟪q - q₀, h⟫ / ‖q - q₀‖ ^ 6) • star (q - q₀) := by
  by_cases hq : q = q₀
  · -- At the pole the kernel is unbounded, hence not differentiable, and both sides are `0`.
    subst hq
    open Filter Topology in
    have hnd : ¬ DifferentiableAt ℝ (fun x ↦ cauchyFueterKernel x q) q := by
      intro hd
      have h0 : Tendsto (fun x ↦ ‖cauchyFueterKernel x q‖) (𝓝[≠] q) (𝓝 0) := by
        simpa [cauchyFueterKernel_self] using
          hd.continuousAt.norm.tendsto.mono_left nhdsWithin_le_nhds
      have h1 : Tendsto (fun x : ℍ ↦ (‖x - q‖ ^ 3)⁻¹) (𝓝[≠] q) atTop := by
        simpa only [Function.comp_def, Pi.inv_apply, inv_pow] using
          (Filter.tendsto_pow_atTop (by decide : (3 : ℕ) ≠ 0)).comp
            ((tendsto_norm_sub_self_nhdsNE q).inv_tendsto_nhdsGT_zero)
      simp only [norm_cauchyFueterKernel] at h0
      exact not_tendsto_nhds_of_tendsto_atTop h1 0 h0
    simp [fderiv_zero_of_not_differentiableAt hnd]
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
  simp only [fderiv_cauchyFueterKernel_apply]
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
  simp only [fderiv_cauchyFueterKernel_apply]
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

/-- Spatial derivatives of a kernel with arbitrary pole are translates of those
of the kernel with pole zero. This identity also holds at the totalized pole. -/
theorem iteratedFDeriv_cauchyFueterKernel (m : ℕ) (q q₀ : ℍ) :
    iteratedFDeriv ℝ m (fun x ↦ cauchyFueterKernel x q₀) q =
      iteratedFDeriv ℝ m (fun x ↦ cauchyFueterKernel x 0) (q - q₀) := by
  have heq : (fun x ↦ cauchyFueterKernel x q₀) =
      (fun x ↦ cauchyFueterKernel (x - q₀) 0) := by
    funext x
    simp [cauchyFueterKernel_eq]
  rw [heq, iteratedFDeriv_comp_sub (f := fun x ↦ cauchyFueterKernel x 0)]

/-- Differentiation in the second argument contributes one minus sign per derivative.
No differentiability hypothesis is needed for this identity of totalized derivatives. -/
theorem iteratedFDeriv_cauchyFueterKernel_right (m : ℕ) (q q₀ : ℍ) :
    iteratedFDeriv ℝ m (cauchyFueterKernel q) q₀ =
      (-1 : ℝ) ^ m • iteratedFDeriv ℝ m (fun x ↦ cauchyFueterKernel x 0) (q - q₀) := by
  have heq : cauchyFueterKernel q =
      (fun x ↦ cauchyFueterKernel (q + (-1 : ℝ) • x) 0) := by
    funext x
    simp [cauchyFueterKernel_eq, sub_eq_add_neg]
  rw [heq, iteratedFDeriv_comp_const_smul_apply
    (fun x ↦ cauchyFueterKernel (q + x) 0),
    iteratedFDeriv_comp_add_left (f := fun x ↦ cauchyFueterKernel x 0)]
  simp [sub_eq_add_neg]

/-- Uniform bounds through any prescribed finite order for spatial derivatives of
the kernel, with a positive constant independent of the pole and evaluation point. -/
theorem exists_norm_iteratedFDeriv_cauchyFueterKernel_le (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ m ≤ N, ∀ q q₀ : ℍ, q ≠ q₀ →
      ‖iteratedFDeriv ℝ m (fun x ↦ cauchyFueterKernel x q₀) q‖ ≤
        C / ‖q - q₀‖ ^ (3 + m) := by
  have hs : ContDiffOn ℝ N (fun x ↦ cauchyFueterKernel x 0) {0}ᶜ :=
    fun x hx ↦ (contDiffAt_cauchyFueterKernel hx).contDiffWithinAt
  have hh (t : ℝ) (_ht : 0 < t) (x : ℍ) (_hx : x ≠ 0) :
      cauchyFueterKernel (t • x) 0 = t ^ (-3 : ℤ) • cauchyFueterKernel x 0 := by
    simpa [zpow_neg, zpow_ofNat] using cauchyFueterKernel_smul t x 0
  obtain ⟨A, hA⟩ := exists_norm_iteratedFDeriv_le_mul_zpow_of_smul_eq hs hh
  refine ⟨A + 1, by positivity, fun m hm q q₀ hq ↦ ?_⟩
  rw [iteratedFDeriv_cauchyFueterKernel]
  have h := hA m hm (q - q₀) (sub_ne_zero.mpr hq)
  have hexp : (-3 : ℤ) - m = -((3 + m : ℕ) : ℤ) := by omega
  rw [hexp, zpow_neg, zpow_natCast, ← div_eq_mul_inv] at h
  exact h.trans (div_le_div_of_nonneg_right (by simp) (by positivity))

/-- The same pole-independent decay estimate holds for derivatives in the second
argument, as used in the differentiated boundary representation. -/
theorem exists_norm_iteratedFDeriv_cauchyFueterKernel_right_le (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ m ≤ N, ∀ q q₀ : ℍ, q ≠ q₀ →
      ‖iteratedFDeriv ℝ m (cauchyFueterKernel q) q₀‖ ≤
        C / ‖q - q₀‖ ^ (3 + m) := by
  obtain ⟨C, hC, h⟩ := exists_norm_iteratedFDeriv_cauchyFueterKernel_le N
  refine ⟨C, hC, fun m hm q q₀ hq ↦ ?_⟩
  simpa [iteratedFDeriv_cauchyFueterKernel_right, norm_smul,
    iteratedFDeriv_cauchyFueterKernel] using h m hm q q₀ hq

/-- Positive separation bounds derivatives in the second argument, with a constant
depending only on the maximum order, not on the points or separation scale. -/
theorem exists_norm_iteratedFDeriv_cauchyFueterKernel_right_le_of_le_norm_sub (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ m ≤ N, ∀ {q q₀ : ℍ} {δ : ℝ}, 0 < δ → δ ≤ ‖q - q₀‖ →
      ‖iteratedFDeriv ℝ m (cauchyFueterKernel q) q₀‖ ≤ C / δ ^ (3 + m) := by
  obtain ⟨C, hC, h⟩ := exists_norm_iteratedFDeriv_cauchyFueterKernel_right_le N
  refine ⟨C, hC, fun m hm q q₀ δ hδ hsep ↦ ?_⟩
  have hne : q ≠ q₀ := by
    intro heq
    simp [heq] at hsep
    linarith
  exact (h m hm _ _ hne).trans
    (div_le_div_of_nonneg_left hC.le (by positivity) (pow_le_pow_left₀ hδ.le hsep _))

/-- If a point is at distance at least `δ` from a pole, its kernel derivatives in
the second argument have a common bound on every closed ball of radius `r < δ`
about that pole. The positive constant depends only on the maximum order `N`,
providing a common-neighbourhood dominator for boundary integrals. -/
theorem exists_norm_iteratedFDeriv_cauchyFueterKernel_right_le_of_mem_closedBall (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ m ≤ N, ∀ {q q₀ p : ℍ} {δ r : ℝ}, r < δ →
      δ ≤ ‖q - q₀‖ → p ∈ Metric.closedBall q₀ r →
      ‖iteratedFDeriv ℝ m (cauchyFueterKernel q) p‖ ≤ C / (δ - r) ^ (3 + m) := by
  obtain ⟨C, hC, h⟩ :=
    exists_norm_iteratedFDeriv_cauchyFueterKernel_right_le_of_le_norm_sub N
  refine ⟨C, hC, fun m hm q q₀ p δ r hr hsep hp ↦ ?_⟩
  apply h m hm (sub_pos.mpr hr)
  have hdist : ‖p - q₀‖ ≤ r := by
    simpa only [Metric.mem_closedBall, dist_eq_norm] using hp
  have htri := dist_triangle q p q₀
  simp only [dist_eq_norm] at htri
  linarith

end TauCeti

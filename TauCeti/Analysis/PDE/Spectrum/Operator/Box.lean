/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Spectrum.Box
public import TauCeti.Analysis.PDE.Spectrum.Operator.PoincareFriedrichs
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import TauCeti.Analysis.Calculus.FDeriv.Pi.Lp
import TauCeti.Analysis.Calculus.Gradient
import TauCeti.Analysis.SpecialFunctions.Integrals.Trigonometric.Oscillation
import TauCeti.Analysis.Sobolev.LipschitzDomain.Examples.BoxDomain
import TauCeti.Analysis.Sobolev.Poincare.SharpConstant
import TauCeti.Analysis.Sobolev.W1p.VanishingBoundary
import TauCeti.MeasureTheory.Function.Lp.Integral.L2NormSq
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Basic
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Wirtinger

/-!
# The mixed Laplacian on a box with one Dirichlet face

Let `Ω = ∏ⱼ (aⱼ, bⱼ)` be a box in `EuclideanSpace ℝ ι` and let `Γ` be a part of the hyperplane
`xᵢ = aᵢ` whose closure contains the open face `xᵢ = aᵢ` of `Ω`, such as that face itself. This file
computes the bottom of the spectrum of the mixed Laplacian `-Δ_Γ`
(`TauCeti.PDE.mixedOperator` for the identity coefficient), with the Dirichlet condition on `Γ` and
the Neumann condition on the rest of the boundary: it is `k² = (π / (2 (bᵢ - aᵢ)))²`, the first
eigenvalue of `-u''` on the side `(aᵢ, bᵢ)` with `u(aᵢ) = 0` and `u'(bᵢ) = 0`. The other directions
contribute nothing, since the Neumann condition allows functions constant in them.

* **The sharp inequality.** Every `u ∈ H¹_Γ(Ω)` satisfies `k² ‖u‖²_{L²} ≤ ‖∇u‖²_{L²}`. On the
  generators of `H¹_Γ(Ω)`, smooth functions vanishing on the face, this is Wirtinger's inequality
  with one Dirichlet endpoint
  (`AbsolutelyContinuousOnInterval.mul_integral_sq_le_integral_deriv_sq_of_eq_zero_left`) on each
  segment of `Ω` parallel to the `i`-th axis, integrated over the other coordinates
  (`TauCeti.lintegral_le_lintegral_of_forall_lintegral_update_le`) and combined with
  `(∂ᵢφ)² ≤ ‖∇φ‖²`. The inequality is a closed condition, so it passes to `H¹_Γ(Ω)`.
* **The extremal function.** `sin (k (xᵢ - aᵢ))` vanishes on the hyperplane `xᵢ = aᵢ`, so it lies
  in `H¹_Γ(Ω)` (`TauCeti.W1p.mem_w1pVanishingOnSubmodule_of_locallyLipschitz_of_eqOn_zero`), and
  its gradient `k cos (k (xᵢ - aᵢ)) eᵢ` has `‖∇u‖² = k² ‖u‖²`, since `sin²` and `cos²` have the
  same integral over a quarter period
  (`TauCeti.integral_sin_sq_and_integral_cos_sq_quarter_period`).

So `k²` is the best constant in `C ‖u‖² ≤ ‖∇u‖²` on `H¹_Γ(Ω)`, `1 / k = 2 (bᵢ - aᵢ) / π` is the
optimal Poincaré–Friedrichs constant, and `k² = ‖(-Δ_Γ)⁻¹‖⁻¹`. When `Ω` has the Rellich property
this is the least point of the spectrum of `-Δ_Γ`
(`TauCeti.PDE.isLeast_spectrum_mixedOperator_laplacian_of_poincare`). The unit square `(0, 1)²`
has it, being a Lipschitz domain (`TauCeti.W1p.isCompactOperator_valueL_boxDomain_zero_one`), so
its mixed Laplacian with one Dirichlet side has first eigenvalue `π² / 4`.

## Main declarations

* `TauCeti.PDE.mul_norm_value_sq_le_norm_gradient_sq_of_mem_w1pVanishingOnSubmodule_boxDomain`: the
  inequality `k² ‖u‖² ≤ ‖∇u‖²` on `H¹_Γ(Ω)`.
* `TauCeti.PDE.isGreatest_mul_norm_value_sq_le_norm_gradient_sq_boxDomain` and
  `TauCeti.PDE.isLeast_norm_value_le_mul_norm_gradient_boxDomain`: `k²` is the best constant, and
  `2 (bᵢ - aᵢ) / π` the optimal Poincaré–Friedrichs constant.
* `TauCeti.PDE.inv_norm_resolvent_mixedOperator_laplacian_zero_boxDomain`: `‖(-Δ_Γ)⁻¹‖⁻¹ = k²`.
* `TauCeti.PDE.isLeast_spectrum_mixedOperator_laplacian_boxDomain`: under the Rellich property, `k²`
  is the least point of the spectrum of `-Δ_Γ`.
* `TauCeti.PDE.isLeast_spectrum_mixedOperator_laplacian_boxDomain_zero_one`: the first mixed
  eigenvalue of the unit square with one Dirichlet side is `π² / 4`.

## References

* R. Courant, D. Hilbert, *Methods of Mathematical Physics*, Vol. I, Chapter VI, §4 (the
  eigenvalues of rectangles by separation of variables, with mixed boundary conditions).
* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*, §8.4,
  Example 5 (a Dirichlet condition at one endpoint only) and Theorem 9.31 (the eigenbasis of the
  Laplacian).
-/

public section

noncomputable section

open MeasureTheory Set TopologicalSpace
open scoped ENNReal Gradient Real RealInnerProductSpace

namespace TauCeti.PDE

variable {ι : Type*} [Fintype ι] {mu : Measure (EuclideanSpace ℝ ι)}
  [mu.IsAddHaarMeasure] {a b : ι → ℝ} {i : ι}

variable [DecidableEq ι] in
/-- **Wirtinger's inequality on a box, for a `C¹` function vanishing on one face.** If `φ` is `C¹`
and vanishes on the face `xᵢ = aᵢ` of the box `Ω = ∏ⱼ (aⱼ, bⱼ)`, then
`k² ∫_Ω φ² ≤ ∫_Ω ‖∇φ‖²` with `k = π / (2 (bᵢ - aᵢ))`, for every additive Haar measure. On each
segment of `Ω` parallel to the `i`-th axis this is Wirtinger's inequality, since
`(∂ᵢφ)² ≤ ‖∇φ‖²`. -/
private theorem mul_setIntegral_sq_le_setIntegral_norm_gradient_sq (hab : a i < b i)
    {φ : EuclideanSpace ℝ ι → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hφ0 : ∀ x : ι → ℝ, (∀ j ≠ i, x j ∈ Ioo (a j) (b j)) →
      φ (WithLp.toLp 2 (Function.update x i (a i))) = 0) :
    (π / (2 * (b i - a i))) ^ 2 * ∫ x in boxDomain a b, φ x ^ 2 ∂mu ≤
      ∫ x in boxDomain a b, ‖∇ φ x‖ ^ 2 ∂mu := by
  have hgc : Continuous fun x => ‖∇ φ x‖ ^ 2 := by
    simp_rw [norm_gradient_eq_norm_fderiv]
    exact ((hφ.continuous_fderiv one_ne_zero).norm).pow 2
  rw [← integral_const_mul]
  refine setIntegral_boxDomain_le (i := i) (continuous_const.mul (hφ.continuous.pow 2)) hgc
    (fun _ => by positivity) (fun _ => by positivity) fun x hx => ?_
  -- The restriction `h` of `φ` to the line is `C¹`, and `|h'| = |∂ᵢφ| ≤ ‖∇φ‖`.
  set h : ℝ → ℝ := fun t => φ (WithLp.toLp 2 (Function.update x i t))
  have hhc : ContDiff ℝ 1 h := hφ.comp (PiLp.contDiff_toLp.comp (contDiff_update 1 x i))
  have hdle (t : ℝ) : deriv h t ^ 2 ≤ ‖∇ φ (WithLp.toLp 2 (Function.update x i t))‖ ^ 2 := by
    rw [← sq_abs, ← Real.norm_eq_abs, norm_deriv_eq_norm_fderiv,
      PiLp.norm_fderiv_update φ x i t (hφ.differentiable one_ne_zero _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (PiLp.norm_apply_le _ i) 2
  exact (setLIntegral_Ioo_mul_sq_le_deriv_sq_of_eq_zero_left hab hhc (hφ0 x hx)).trans
    (lintegral_mono fun t => ENNReal.ofReal_le_ofReal (hdle t))

variable {Γ : Set (EuclideanSpace ℝ ι)}

/-- **The Poincaré–Friedrichs inequality on a box with a Dirichlet face, in Rayleigh form.** Let
`Ω = ∏ⱼ (aⱼ, bⱼ)` be a box and let the closure of `Γ` contain the open face `xᵢ = aᵢ` of `Ω`. Every
`u ∈ H¹_Γ(Ω)` satisfies `k² ‖u‖²_{L²(Ω)} ≤ ‖∇u‖²_{L²(Ω)}` with `k = π / (2 (bᵢ - aᵢ))`, for every
additive Haar measure. -/
theorem mul_norm_value_sq_le_norm_gradient_sq_of_mem_w1pVanishingOnSubmodule_boxDomain
    (hab : a i < b i)
    (hΓ : ∀ x : EuclideanSpace ℝ ι, x i = a i → (∀ j ≠ i, x j ∈ Ioo (a j) (b j)) → x ∈ closure Γ)
    {u : W1p mu (boxDomain a b) 2} (hu : u ∈ w1pVanishingOnSubmodule mu (boxDomain a b) 2 Γ) :
    (π / (2 * (b i - a i))) ^ 2 * ‖W1p.value u‖ ^ 2 ≤ ‖W1p.gradient u‖ ^ 2 := by
  classical
  -- The inequality is a closed condition, so it suffices to check it on the generators.
  have hclosed : IsClosed {u : W1p mu (boxDomain a b) 2 |
      (π / (2 * (b i - a i))) ^ 2 * ‖W1p.value u‖ ^ 2 ≤ ‖W1p.gradient u‖ ^ 2} := by
    simp only [← W1p.valueL_apply, ← W1p.gradientL_apply]
    exact isClosed_le (continuous_const.mul ((W1p.valueL).continuous.norm.pow 2))
      ((W1p.gradientL).continuous.norm.pow 2)
  refine w1pVanishingOnSubmodule_subset_of_isClosed hclosed (fun φ hφ => ?_) hu
  -- A generator is a test function `φ` vanishing on `closure Γ`, hence on the face.
  have hφ0 (x : ι → ℝ) (hx : ∀ j ≠ i, x j ∈ Ioo (a j) (b j)) :
      φ (WithLp.toLp 2 (Function.update x i (a i))) = 0 := by
    refine image_eq_zero_of_notMem_tsupport (hφ.notMem_of_mem_right (hΓ _ (by simp) ?_))
    intro j hj
    simpa [hj] using hx j hj
  have hgrad : ‖W1p.gradient (W1p.restrictL le_top (W1p.ofTestFunctionₗ mu ⊤ 2 φ) :
      W1p mu (boxDomain a b) 2)‖ ^ 2 = ∫ x in boxDomain a b, ‖∇ φ x‖ ^ 2 ∂mu := by
    rw [← W1p.integral_norm_gradient_sq_eq_norm_gradient_sq]
    exact integral_congr_ae
      ((W1p.gradient_restrictL_ofTestFunctionₗ_ae (p := 2) le_top φ).mono fun x hx => by
        simp only [hx])
  rw [mem_ofPred_eq, L2.norm_sq_eq_integral_sq_of_ae_eq
      (W1p.value_restrictL_ofTestFunctionₗ_ae le_top φ), hgrad]
  exact mul_setIntegral_sq_le_setIntegral_norm_gradient_sq hab (φ.contDiff.of_le (by simp)) hφ0

/-- Integrals over a box of functions of the `i`-th coordinate compare as their integrals over the
`i`-th side do. -/
private theorem setIntegral_comp_apply_le (hab : a i ≤ b i) {F G : ℝ → ℝ} (hF : Continuous F)
    (hG : Continuous G) (hF0 : ∀ t, 0 ≤ F t) (hG0 : ∀ t, 0 ≤ G t)
    (h : ∫ t in a i..b i, F t ≤ ∫ t in a i..b i, G t) :
    ∫ x in boxDomain a b, F (x i) ∂mu ≤ ∫ x in boxDomain a b, G (x i) ∂mu := by
  classical
  have hci : Continuous fun x : EuclideanSpace ℝ ι => x i := PiLp.continuous_apply 2 _ i
  refine setIntegral_boxDomain_le (i := i) (hF.comp hci) (hG.comp hci) (fun _ => hF0 _)
    (fun _ => hG0 _) fun x _ => ?_
  simp only [Function.update_self]
  rw [setLIntegral_Ioo_ofReal_eq_ofReal_intervalIntegral hab (hF.intervalIntegrable _ _)
      fun t _ => hF0 t,
    setLIntegral_Ioo_ofReal_eq_ofReal_intervalIntegral hab (hG.intervalIntegrable _ _)
      fun t _ => hG0 t]
  exact ENNReal.ofReal_le_ofReal h

/-! ### The extremal function -/

/-- The square of `sin (k (xᵢ - aᵢ))`, `k = π / (2 (bᵢ - aᵢ))`, has positive integral over the box
`∏ⱼ (aⱼ, bⱼ)`: it is positive there, since `0 < k (xᵢ - aᵢ) < π / 2`. -/
private theorem setIntegral_boxDomain_sin_sq_pos (hab : ∀ j, a j < b j) :
    0 < ∫ x in boxDomain a b, Real.sin (π / (2 * (b i - a i)) * (x i - a i)) ^ 2 ∂mu := by
  set k := π / (2 * (b i - a i))
  have hk : 0 < k := div_pos Real.pi_pos (by linarith [hab i])
  have hkb : k * (b i - a i) = π / 2 := by
    simp only [k]
    field_simp [(sub_pos.2 (hab i)).ne']
  have hpos (x : EuclideanSpace ℝ ι) (hx : x ∈ (boxDomain a b : Set (EuclideanSpace ℝ ι))) :
      0 < Real.sin (k * (x i - a i)) ^ 2 := by
    have hxi := (mem_boxDomain.1 hx) i
    have hkx : k * (x i - a i) < π := by nlinarith [hxi.2, Real.pi_pos]
    exact pow_pos (Real.sin_pos_of_pos_of_lt_pi (mul_pos hk (by linarith [hxi.1])) hkx) 2
  rw [setIntegral_pos_iff_support_of_nonneg_ae (ae_of_all _ fun x => by positivity)
      (integrableOn_boxDomain (by fun_prop)),
    inter_eq_right.2 fun x hx => (hpos x hx).ne']
  exact (boxDomain a b).isOpen.measure_pos mu (nonempty_boxDomain hab)

/-- **The extremal function.** If `Γ` lies in the hyperplane `xᵢ = aᵢ`, the class of
`sin (k (xᵢ - aᵢ))`, `k = π / (2 (bᵢ - aᵢ))`, lies in `H¹_Γ(Ω)` for the box `Ω = ∏ⱼ (aⱼ, bⱼ)`, is
nonzero, and has `‖∇u‖² = k² ‖u‖²`. -/
private theorem exists_mem_w1pVanishingOnSubmodule_boxDomain_norm_gradient_sq_eq
    (hab : ∀ j, a j < b j) (hΓ : ∀ x ∈ Γ, x i = a i) :
    ∃ u ∈ w1pVanishingOnSubmodule mu (boxDomain a b) 2 Γ, 0 < ‖W1p.value u‖ ^ 2 ∧
      ‖W1p.gradient u‖ ^ 2 = (π / (2 * (b i - a i))) ^ 2 * ‖W1p.value u‖ ^ 2 := by
  classical
  set k := π / (2 * (b i - a i))
  set Ω : Set (EuclideanSpace ℝ ι) := (boxDomain a b : Set (EuclideanSpace ℝ ι))
  set s : EuclideanSpace ℝ ι → ℝ := fun x => Real.sin (k * (x i - a i))
  have hs : ContDiff ℝ 1 s := Real.contDiff_sin.comp
    (contDiff_const.mul ((EuclideanSpace.proj i : EuclideanSpace ℝ ι →L[ℝ] ℝ).contDiff.sub
      contDiff_const))
  obtain ⟨u, hv, hg⟩ := W1p.exists_value_gradient_ae_eq_of_contDiffOn_of_isCompact (mu := mu)
    (Omega := boxDomain a b) (p := 2) isOpen_univ hs.contDiffOn
    (isBounded_boxDomain a b).isCompact_closure subset_closure (subset_univ _)
  -- `s` vanishes on the hyperplane `xᵢ = aᵢ`, which contains `closure Γ`.
  have hmem : u ∈ w1pVanishingOnSubmodule mu (boxDomain a b) 2 Γ := by
    refine W1p.mem_w1pVanishingOnSubmodule_of_locallyLipschitz_of_eqOn_zero
      (by norm_num) (isBounded_boxDomain a b) (hs.locallyLipschitz) (fun x hx => ?_) hv
    simp [s, hΓ x hx]
  -- The two squared norms are integrals of functions of `xᵢ` over the box.
  have hval : ‖W1p.value u‖ ^ 2 = ∫ x in Ω, (fun t => Real.sin (k * (t - a i)) ^ 2) (x i) ∂mu :=
    L2.norm_sq_eq_integral_sq_of_ae_eq hv
  have hgrad : ‖W1p.gradient u‖ ^ 2 =
      ∫ x in Ω, (fun t => (k * Real.cos (k * (t - a i))) ^ 2) (x i) ∂mu := by
    rw [← W1p.integral_norm_gradient_sq_eq_norm_gradient_sq]
    refine integral_congr_ae (hg.mono fun x hx => ?_)
    have hsg : HasGradientAt s _ x :=
      (((hasDerivAt_id' (x i)).sub_const (a i)).const_mul k).sin.hasGradientAt_comp_apply
    simp [hx, hsg.gradient, norm_smul, mul_pow, PiLp.norm_single, mul_comm]
  -- Along the `i`-th side, `∫ cos² = ∫ sin²`.
  obtain ⟨hsin, hcos⟩ := integral_sin_sq_and_integral_cos_sq_quarter_period (hab i)
  have hside : ∫ t in a i..b i, (k * Real.cos (k * (t - a i))) ^ 2 =
      ∫ t in a i..b i, k ^ 2 * Real.sin (k * (t - a i)) ^ 2 := by
    simp_rw [mul_pow]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hcos, hsin]
  have hcs : Continuous fun t => (k * Real.cos (k * (t - a i))) ^ 2 := by fun_prop
  have hss : Continuous fun t => k ^ 2 * Real.sin (k * (t - a i)) ^ 2 := by fun_prop
  refine ⟨u, hmem, ?_, ?_⟩
  · rw [hval]
    exact setIntegral_boxDomain_sin_sq_pos hab
  · rw [hgrad, hval, ← integral_const_mul]
    exact le_antisymm
      (setIntegral_comp_apply_le (hab i).le hcs hss (fun _ => by positivity)
        (fun _ => by positivity) hside.le)
      (setIntegral_comp_apply_le (hab i).le hss hcs (fun _ => by positivity)
        (fun _ => by positivity) hside.ge)

/-! ### The sharp constants -/

/-- **The sharp Poincaré–Friedrichs inequality on a box with a Dirichlet face, Rayleigh form.** Let
`Ω = ∏ⱼ (aⱼ, bⱼ)` be a nonempty box and `Γ` a part of the hyperplane `xᵢ = aᵢ` whose closure
contains the open face `xᵢ = aᵢ` of `Ω`. The best constant `C` with `C ‖u‖²_{L²} ≤ ‖∇u‖²_{L²}` on
`H¹_Γ(Ω)` is `(π / (2 (bᵢ - aᵢ)))²`, attained by `sin (π (xᵢ - aᵢ) / (2 (bᵢ - aᵢ)))`. -/
theorem isGreatest_mul_norm_value_sq_le_norm_gradient_sq_boxDomain (hab : ∀ j, a j < b j)
    (hΓ : ∀ x ∈ Γ, x i = a i)
    (hface : ∀ x : EuclideanSpace ℝ ι, x i = a i → (∀ j ≠ i, x j ∈ Ioo (a j) (b j)) →
      x ∈ closure Γ) :
    IsGreatest {C : ℝ | ∀ u ∈ w1pVanishingOnSubmodule mu (boxDomain a b) 2 Γ,
      C * ‖W1p.value u‖ ^ 2 ≤ ‖W1p.gradient u‖ ^ 2} ((π / (2 * (b i - a i))) ^ 2) := by
  obtain ⟨u, hu, hu0, hgu⟩ := exists_mem_w1pVanishingOnSubmodule_boxDomain_norm_gradient_sq_eq
    (mu := mu) hab hΓ
  exact W1p.isGreatest_mul_norm_value_sq_le_norm_gradient_sq_of_eq (fun v hv =>
    mul_norm_value_sq_le_norm_gradient_sq_of_mem_w1pVanishingOnSubmodule_boxDomain (hab i) hface
      hv) hu hu0 hgu

/-- **The optimal Poincaré–Friedrichs constant of a box with a Dirichlet face.** Under the
hypotheses of `TauCeti.PDE.isGreatest_mul_norm_value_sq_le_norm_gradient_sq_boxDomain`, the least
`C ≥ 0` with `‖u‖_{L²} ≤ C ‖∇u‖_{L²}` on `H¹_Γ(Ω)` is `2 (bᵢ - aᵢ) / π`. -/
theorem isLeast_norm_value_le_mul_norm_gradient_boxDomain (hab : ∀ j, a j < b j)
    (hΓ : ∀ x ∈ Γ, x i = a i)
    (hface : ∀ x : EuclideanSpace ℝ ι, x i = a i → (∀ j ≠ i, x j ∈ Ioo (a j) (b j)) →
      x ∈ closure Γ) :
    IsLeast {C : ℝ | 0 ≤ C ∧ ∀ u ∈ w1pVanishingOnSubmodule mu (boxDomain a b) 2 Γ,
      ‖W1p.value u‖ ≤ C * ‖W1p.gradient u‖} (2 * (b i - a i) / π) := by
  obtain ⟨u, hu, hu0, hgu⟩ := exists_mem_w1pVanishingOnSubmodule_boxDomain_norm_gradient_sq_eq
    (mu := mu) hab hΓ
  rw [← inv_div]
  exact W1p.isLeast_norm_value_le_mul_norm_gradient_of_eq
    (div_pos Real.pi_pos (by linarith [hab i]))
    (fun v hv => mul_norm_value_sq_le_norm_gradient_sq_of_mem_w1pVanishingOnSubmodule_boxDomain
      (hab i) hface hv) hu hu0 hgu

/-! ### The first mixed eigenvalue -/

variable [DecidableEq ι] in
/-- **The norm of the inverse of the mixed Laplacian on a box with a Dirichlet face.** Under the
hypotheses of `TauCeti.PDE.isGreatest_mul_norm_value_sq_le_norm_gradient_sq_boxDomain`, `0` is a
resolvent point of the mixed Laplacian `-Δ_Γ` on `Ω = ∏ⱼ (aⱼ, bⱼ)`, and its resolvent `R(0)`, minus
the inverse of `-Δ_Γ`, has `‖R(0)‖⁻¹ = (π / (2 (bᵢ - aᵢ)))²`. -/
theorem inv_norm_resolvent_mixedOperator_laplacian_zero_boxDomain (hab : ∀ j, a j < b j)
    (hΓ : ∀ x ∈ Γ, x i = a i)
    (hface : ∀ x : EuclideanSpace ℝ ι, x i = a i → (∀ j ≠ i, x j ∈ Ioo (a j) (b j)) →
      x ∈ closure Γ) :
    ‖(mixedOperator (memLp_energyIntegrand_const_zero_zero (mu := mu) (Omega := boxDomain a b)
      (1 : Matrix ι ι ℝ)) Γ).resolvent 0‖⁻¹ = (π / (2 * (b i - a i))) ^ 2 :=
  (isGreatest_inv_norm_resolvent_mixedOperator_laplacian_zero_of_poincare
    (disjoint_boxDomain_of_forall_apply_eq_left hΓ) (nonempty_boxDomain hab)
    (isLeast_norm_value_le_mul_norm_gradient_boxDomain (mu := mu) hab hΓ hface).1.2).unique
    (isGreatest_mul_norm_value_sq_le_norm_gradient_sq_boxDomain hab hΓ hface)

variable [DecidableEq ι] in
/-- **The first mixed eigenvalue of a box with a Dirichlet face.** Under the hypotheses of
`TauCeti.PDE.isGreatest_mul_norm_value_sq_le_norm_gradient_sq_boxDomain`, if the box
`Ω = ∏ⱼ (aⱼ, bⱼ)` has the Rellich property that the value map `H¹(Ω) → L²(Ω)` is compact, the least
point of the spectrum of the mixed Laplacian `-Δ_Γ` is `(π / (2 (bᵢ - aᵢ)))²`. -/
theorem isLeast_spectrum_mixedOperator_laplacian_boxDomain (hab : ∀ j, a j < b j)
    (hΓ : ∀ x ∈ Γ, x i = a i)
    (hface : ∀ x : EuclideanSpace ℝ ι, x i = a i → (∀ j ≠ i, x j ∈ Ioo (a j) (b j)) →
      x ∈ closure Γ)
    (hK : IsCompactOperator (W1p.valueL (mu := mu) (Omega := boxDomain a b) (p := 2))) :
    IsLeast (mixedOperator (memLp_energyIntegrand_const_zero_zero (mu := mu)
      (Omega := boxDomain a b) (1 : Matrix ι ι ℝ)) Γ).spectrum ((π / (2 * (b i - a i))) ^ 2) := by
  rw [← inv_norm_resolvent_mixedOperator_laplacian_zero_boxDomain (mu := mu) hab hΓ hface]
  exact isLeast_spectrum_mixedOperator_laplacian_of_poincare
    (disjoint_boxDomain_of_forall_apply_eq_left hΓ) (nonempty_boxDomain hab)
    (isLeast_norm_value_le_mul_norm_gradient_boxDomain (mu := mu) hab hΓ hface).1.2 hK

/-! ### The unit square -/

/-- **The first mixed eigenvalue of the unit square with one Dirichlet side is `π² / 4`.** Let `Γ`
be a part of the side `xᵢ = 0` of the unit square `(0, 1)²` whose closure contains the open side,
for instance `Γ = {0} × (0, 1)`. The least point of the spectrum of the mixed Laplacian `-Δ_Γ`, with
the Dirichlet condition on `Γ` and the Neumann condition on the rest of the boundary, is `π² / 4`.
-/
theorem isLeast_spectrum_mixedOperator_laplacian_boxDomain_zero_one {i : Fin 2}
    {Γ : Set (EuclideanSpace ℝ (Fin 2))} (hΓ : ∀ x ∈ Γ, x i = 0)
    (hface : ∀ x : EuclideanSpace ℝ (Fin 2), x i = 0 → (∀ j ≠ i, x j ∈ Ioo 0 1) →
      x ∈ closure Γ) :
    IsLeast (mixedOperator (memLp_energyIntegrand_const_zero_zero (mu := volume)
      (Omega := boxDomain (0 : Fin 2 → ℝ) 1) (1 : Matrix (Fin 2) (Fin 2) ℝ)) Γ).spectrum
      (π ^ 2 / 4) := by
  have h := isLeast_spectrum_mixedOperator_laplacian_boxDomain (a := 0) (b := 1)
    (fun _ => zero_lt_one) hΓ hface W1p.isCompactOperator_valueL_boxDomain_zero_one
  convert h using 1
  simp only [Pi.one_apply, Pi.zero_apply, sub_zero, mul_one, div_pow]
  ring

end TauCeti.PDE

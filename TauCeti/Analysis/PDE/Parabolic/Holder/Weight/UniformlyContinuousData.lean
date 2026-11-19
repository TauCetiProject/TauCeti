/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.Holder.UniformlyContinuousData
public import TauCeti.Analysis.PDE.Parabolic.Holder.Weight.Solvability

/-!
# The weighted Cauchy problem with uniformly continuous initial data

On `ℝⁿ = EuclideanSpace ℝ ι` and a time slab `ℝⁿ × [0, T]`, let

`P u = ∂ₜu - aⁱʲ ∂ᵢ∂ⱼu - bⁱ ∂ᵢu - c u`

have coefficients in `C_b^{α,α/2}`, `0 < α < 1`, with `a` uniformly elliptic, and let `w = exp ℓ` be
a positive time-independent weight whose logarithm `ℓ` is `C²` with bounded `α`-Hölder partial
derivatives `∂ᵢℓ` and `∂ᵢ∂ⱼℓ`; `ℓ` itself may be unbounded. This file solves the Cauchy problem
`P u = w f`, `u(·, 0) = w g` for `f ∈ C_b^{α,α/2}` and initial data `g` that are only bounded and
uniformly continuous, so that the initial values `w g` are measured in the weighted uniform norm
`‖u(·, 0) / w‖_∞`.

Writing `u = w V`, the conjugation identity `P (w V) = w P_w V`
(`TauCeti.ParabolicC2HolderSpace.exp_mul_euclideanParabolicOperatorL_eq`) reduces the problem to
the Cauchy problem `P_w V = f`, `V(·, 0) = g` for an operator of the same type, with the same
principal coefficients and the lower-order coefficients `b_w`, `c_w`
(`TauCeti.ParabolicC2HolderSpace.euclideanWeightedFirstOrderCoeff`,
`TauCeti.ParabolicC2HolderSpace.euclideanWeightedZerothOrderCoeff`). Its solution for uniformly
continuous initial data is the extended solution operator
`TauCeti.ParabolicC2HolderSpace.euclideanCauchySolutionBUC`, and the solution of the weighted
problem is

`u(x, t) = exp (ℓ x) V(x, t)`, with `V = euclideanCauchySolutionBUC … a b_w c_w … (f, g)`.

The results below describe `u` through the original operator `P`:

* **Approximation by classical solutions.** If `u'` is a classical solution of `P u' = w f`,
  `u'(·, 0) = w g'` in the weighted class `u' / w ∈ C_b^{2+α,1+α/2}`, with `g'` a bounded
  `C^{2,α}` function uniformly within `δ` of `g`, then
  `|u(x, t) - u'(x, t)| ≤ w(x) exp (‖c_w‖ T) (1 + T) δ`. Since `C_b^{2,α}` is dense in the
  uniformly continuous functions, `u` is the limit in the weighted uniform norm of the classical
  weighted solutions with approximating initial data, and this property determines `u`.
* **Agreement.** For `g ∈ C_b^{2,α}`, `u` satisfies `P u = w f` pointwise on the slab.

Since `u / w = V`, the statements about `u / w` alone are the unweighted results for
`euclideanCauchySolutionBUC` with the coefficients `a`, `b_w`, `c_w`, and are not restated here:
`TauCeti.ParabolicC2HolderSpace.euclideanCauchySolutionBUC_apply_slabMk_zero` gives the initial
values `u(x, 0) = w(x) g(x)`,
`TauCeti.ParabolicC2HolderSpace.tendstoUniformly_euclideanCauchySolutionBUC` gives
`u(·, t) / w → g` uniformly on `ℝⁿ` as `t → 0⁺` (the initial trace in the weighted uniform norm),
and `TauCeti.ParabolicC2HolderSpace.abs_euclideanCauchySolutionBUC_apply_le` with `c := c_w`
gives the maximum principle `|u(x, t)| ≤ w(x) exp (γ t) (M + t K)` when `c_w ≤ γ`, `0 ≤ γ`,
`|f| ≤ K` and `|g| ≤ M`.

## Main declarations

All declarations are in the `TauCeti.ParabolicC2HolderSpace` namespace.

* `abs_sub_le_exp_mul_of_eq_exp_mul_euclideanCauchySolutionBUC`: the comparison with classical
  weighted solutions.
* `derivWithin_sub_eq_exp_mul_of_eq_exp_mul_euclideanCauchySolutionBUC`: the solution satisfies
  `P u = w f` pointwise for initial data in `C_b^{2,α}`.

## References

* A. Friedman, *Partial Differential Equations of Parabolic Type*, Chapter 2 (the substitution
  `u = w v` by a positive weight).
* A. Lunardi, *Linear and nonlinear diffusion problems*, Cortona lecture notes, 2004, Chapter 4
  (solutions with continuous initial data as limits of solutions with smooth data).
-/

public section

namespace TauCeti.ParabolicC2HolderSpace

open Set ParabolicSpaceTime Real BoundedContinuousFunction
open scoped NNReal

variable {α : ℝ≥0} {ι : Type*} [Fintype ι] [DecidableEq ι] {T : ℝ≥0}
  (hα₀ : 0 < α) (hα₁ : α < 1) (hT : (0 : ℝ) < T)
  {a : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ}
  {b : ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ}
  {c : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ}
  (ha : ∃ lam : ℝ, 0 < lam ∧ ∀ p (ξ : EuclideanSpace ℝ ι),
    lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ)
  {dℓ : ι → HolderSpace α (EuclideanSpace ℝ ι) ℝ}
  {d2ℓ : ι → ι → HolderSpace α (EuclideanSpace ℝ ι) ℝ} {ℓ : EuclideanSpace ℝ ι → ℝ}

/-- **Comparison with classical weighted solutions.** Let `w = exp ℓ` be a spatial weight as in
`eq_euclideanInitialDataCLE_symm_iff_exp_mul`, let `f ∈ C_b^{α,α/2}` and let `g` be bounded and
uniformly continuous. Let `u = exp ℓ * V`, where `V` is the extended solution of the conjugated
problem `P_w V = f`, `V(·, 0) = g`. Let `u' = exp ℓ * v` with `v ∈ C_b^{2+α,1+α/2}` be a classical
solution of `P u' = exp ℓ * f`, `u'(·, 0) = exp ℓ * g'`, where `g' ∈ C_b^{2,α}` satisfies
`|g - g'| ≤ δ`. Then `|u(x, t) - u'(x, t)| ≤ exp (ℓ x) exp (‖c_w‖ T) (1 + T) δ`. -/
theorem abs_sub_le_exp_mul_of_eq_exp_mul_euclideanCauchySolutionBUC (hℓ : ContDiff ℝ 2 ℓ)
    (hdℓ : ∀ i x, fderiv ℝ ℓ x (EuclideanSpace.single i 1) = dℓ i x)
    (hd2ℓ : ∀ i j x, fderiv ℝ (fderiv ℝ ℓ) x (EuclideanSpace.single i 1)
      (EuclideanSpace.single j 1) = d2ℓ i j x)
    (f : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
    (g : uniformContinuousSubmodule ℝ (EuclideanSpace ℝ ι) ℝ) {u : EuclideanSpace ℝ ι → ℝ → ℝ}
    (hu : ∀ y (s : Icc (0 : ℝ) T), u y s = exp (ℓ y) *
      euclideanCauchySolutionBUC hα₀ hα₁ hT a (euclideanWeightedFirstOrderCoeff a b dℓ)
        (euclideanWeightedZerothOrderCoeff a b c dℓ d2ℓ) ha (f, g) (slabMk y s))
    (g' : CkHolderSpace 2 α (EuclideanSpace ℝ ι) ℝ) {δ : ℝ}
    (hg' : ∀ x, |(g : EuclideanSpace ℝ ι →ᵇ ℝ) x - g' x| ≤ δ)
    (v : ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ hT) {u' : EuclideanSpace ℝ ι → ℝ → ℝ}
    (hu' : ∀ y (s : Icc (0 : ℝ) T), u' y s = exp (ℓ y) * v (slabMk y s))
    (hP : ∀ (x : EuclideanSpace ℝ ι) (t : Icc (0 : ℝ) T), derivWithin (u' x) (Icc 0 T) t -
      (∑ i, ∑ j, a i j (slabMk x t) * fderiv ℝ (fderiv ℝ fun y ↦ u' y t) x
          (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) +
        ∑ i, b i (slabMk x t) * fderiv ℝ (fun y ↦ u' y t) x (EuclideanSpace.single i 1) +
        c (slabMk x t) * u' x t) = exp (ℓ x) * f (slabMk x t))
    (hinit : ∀ x, u' x 0 = exp (ℓ x) * g' x) (x : EuclideanSpace ℝ ι) (t : Icc (0 : ℝ) T) :
    |u x t - u' x t| ≤ exp (ℓ x) *
      (Real.exp (‖euclideanWeightedZerothOrderCoeff a b c dℓ d2ℓ‖ * T) * (1 + T) * δ) := by
  -- The classical solution `u'` is `exp ℓ` times the classical solution of the conjugated problem.
  have hv := (eq_euclideanInitialDataCLE_symm_iff_exp_mul hα₀ hα₁ hT b c ha hℓ hdℓ hd2ℓ v hu' f
    g').2 ⟨hP, hinit⟩
  rw [hu x t, hu' x t, ← mul_sub, abs_mul, abs_of_pos (exp_pos _), hv]
  exact mul_le_mul_of_nonneg_left
    (abs_euclideanCauchySolutionBUC_apply_sub_le hα₀ hα₁ hT ha f g g' hg' _) (exp_pos _).le

/-- **Agreement with the classical weighted solution.** If the initial datum `g` of
`abs_sub_le_exp_mul_of_eq_exp_mul_euclideanCauchySolutionBUC` is a bounded `C^{2,α}` function `g'`,
then `u = exp ℓ * V` satisfies `P u = exp ℓ * f` pointwise on the slab, with the derivatives of `u`
taken by `derivWithin` and `fderiv`. -/
theorem derivWithin_sub_eq_exp_mul_of_eq_exp_mul_euclideanCauchySolutionBUC (hℓ : ContDiff ℝ 2 ℓ)
    (hdℓ : ∀ i x, fderiv ℝ ℓ x (EuclideanSpace.single i 1) = dℓ i x)
    (hd2ℓ : ∀ i j x, fderiv ℝ (fderiv ℝ ℓ) x (EuclideanSpace.single i 1)
      (EuclideanSpace.single j 1) = d2ℓ i j x)
    (f : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
    (g : uniformContinuousSubmodule ℝ (EuclideanSpace ℝ ι) ℝ) {u : EuclideanSpace ℝ ι → ℝ → ℝ}
    (hu : ∀ y (s : Icc (0 : ℝ) T), u y s = exp (ℓ y) *
      euclideanCauchySolutionBUC hα₀ hα₁ hT a (euclideanWeightedFirstOrderCoeff a b dℓ)
        (euclideanWeightedZerothOrderCoeff a b c dℓ d2ℓ) ha (f, g) (slabMk y s))
    (g' : CkHolderSpace 2 α (EuclideanSpace ℝ ι) ℝ)
    (hg' : ∀ x, (g : EuclideanSpace ℝ ι →ᵇ ℝ) x = g' x)
    (x : EuclideanSpace ℝ ι) (t : Icc (0 : ℝ) T) :
    derivWithin (u x) (Icc 0 T) t -
      (∑ i, ∑ j, a i j (slabMk x t) * fderiv ℝ (fderiv ℝ fun y ↦ u y t) x
          (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) +
        ∑ i, b i (slabMk x t) * fderiv ℝ (fun y ↦ u y t) x (EuclideanSpace.single i 1) +
        c (slabMk x t) * u x t) = exp (ℓ x) * f (slabMk x t) := by
  have hu' (y : EuclideanSpace ℝ ι) (s : Icc (0 : ℝ) T) : u y s = exp (ℓ y) *
      (euclideanInitialDataCLE hα₀ hα₁ hT a (euclideanWeightedFirstOrderCoeff a b dℓ)
        (euclideanWeightedZerothOrderCoeff a b c dℓ d2ℓ) ha).symm (f, g') (slabMk y s) := by
    rw [hu, euclideanCauchySolutionBUC_apply_of_ckHolderSpace hα₀ hα₁ hT ha f g g' hg',
      valueL_apply]
  exact ((eq_euclideanInitialDataCLE_symm_iff_exp_mul hα₀ hα₁ hT b c ha hℓ hdℓ hd2ℓ _ hu' f
    g').1 rfl).1 x t

end TauCeti.ParabolicC2HolderSpace

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import TauCeti.Analysis.Calculus.FDeriv.Prod
import TauCeti.Analysis.Calculus.ParametricIntegral.Basic
import TauCeti.MeasureTheory.Integral.Rectangle

/-!
# Interval integrals along the slices of a map of two variables

For a map `ξ` of two variables `(s, t)`, these are calculus facts about the slices
`t ↦ ξ(s, t)` and their interval integrals in `t`, used for maps on the cylinder that have
period `T` in `t`, together with the splitting of the integral of `‖ξ‖²` over a rectangle
`[a₁, b₁] × [a, b]` off a function of `s` when every slice of the rest integrates to zero.

## Main declarations

* `TauCeti.integral_fderiv_apply_zero_one_eq_zero`: the `t`-derivative of a `C¹` map of period
  `T` in `t` integrates to zero over a period.
* `TauCeti.hasDerivAt_intervalIntegral_inner`: the derivative of `s ↦ ∫ₐᵇ ⟪ξ(s, t), η(s, t)⟫ dt`
  for `C¹` maps `ξ` and `η`, computed under the integral sign.
* `TauCeti.hasDerivAt_intervalIntegral_norm_sq`: the derivative `∫ₐᵇ 2 ⟪ξ, ∂s ξ⟫ dt` of the slice
  energy `s ↦ ∫ₐᵇ ‖ξ(s, t)‖² dt` of a `C¹` map.
* `TauCeti.hasDerivAt_intervalIntegral_two_mul_inner_fderiv`: for a `C²` map, the derivative
  `∫ₐᵇ 2 (⟪ξ, ∂s² ξ⟫ + ‖∂s ξ‖²) dt` of `s ↦ ∫ₐᵇ 2 ⟪ξ, ∂s ξ⟫ dt`, the second derivative of the
  slice energy.
* `TauCeti.setIntegral_norm_add_sq_eq`: over a rectangle `[a₁, b₁] × [a, b]`,
  `∫ ‖m(s) + w‖² = (b - a) ∫ₛ ‖m‖² + ∫ ‖w‖²` when every slice of `w` integrates to zero.
-/

public section

open MeasureTheory Set
open scoped RealInnerProductSpace

namespace TauCeti

/-- The `t`-derivative of a `C¹` map of period `T` in `t` integrates to zero over a period:
`∫₀ᵀ ∂t f(s, t) dt = 0`. -/
theorem integral_fderiv_apply_zero_one_eq_zero {E W : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {f : E × ℝ → W} (hf : ContDiff ℝ 1 f) {T : ℝ} (hper : ∀ s t, f (s, t + T) = f (s, t))
    (s : E) : ∫ t in (0 : ℝ)..T, fderiv ℝ f (s, t) (0, 1) = 0 := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ ↦ hasDerivAt_slice_right (hf.differentiable one_ne_zero (s, t)))
    ((continuous_fderiv_apply_slice_right hf s (0, 1)).intervalIntegrable _ _)]
  simpa using congrArg (· - f (s, 0)) (hper s 0)

/-- **Differentiating an integral of inner products along slices.** For `C¹` maps `ξ` and `η`, the
function `s ↦ ∫ₐᵇ ⟪ξ(s, t), η(s, t)⟫ dt` has derivative
`∫ₐᵇ (⟪∂s ξ(s, t), η(s, t)⟫ + ⟪ξ(s, t), ∂s η(s, t)⟫) dt`. -/
theorem hasDerivAt_intervalIntegral_inner {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] {ξ η : ℝ × ℝ → V} (hξ : ContDiff ℝ 1 ξ) (hη : ContDiff ℝ 1 η)
    (a b s : ℝ) :
    HasDerivAt (fun s ↦ ∫ t in a..b, ⟪ξ (s, t), η (s, t)⟫)
      (∫ t in a..b, (⟪fderiv ℝ ξ (s, t) (1, 0), η (s, t)⟫ +
        ⟪ξ (s, t), fderiv ℝ η (s, t) (1, 0)⟫)) s := by
  have h := (hasDerivAt_intervalIntegral_of_contDiffOn (G := fun z ↦ ⟪ξ z, η z⟫) isOpen_univ
    (hξ.inner ℝ hη).contDiffOn (x₀ := s) (a := a) (b := b) (subset_univ _)).2
  refine h.congr_deriv (intervalIntegral.integral_congr fun t _ ↦ ?_)
  rw [fderiv_inner_apply ℝ (hξ.differentiable one_ne_zero (s, t))
    (hη.differentiable one_ne_zero (s, t)), add_comm]

/-- **The derivative of the slice energy.** For a `C¹` map `ξ`, the slice energy
`s ↦ ∫ₐᵇ ‖ξ(s, t)‖² dt` has derivative `∫ₐᵇ 2 ⟪ξ(s, t), ∂s ξ(s, t)⟫ dt`. -/
theorem hasDerivAt_intervalIntegral_norm_sq {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] {ξ : ℝ × ℝ → V} (hξ : ContDiff ℝ 1 ξ) (a b s : ℝ) :
    HasDerivAt (fun s ↦ ∫ t in a..b, ‖ξ (s, t)‖ ^ 2)
      (∫ t in a..b, 2 * ⟪ξ (s, t), fderiv ℝ ξ (s, t) (1, 0)⟫) s := by
  have h := hasDerivAt_intervalIntegral_inner hξ hξ a b s
  simp only [real_inner_self_eq_norm_sq] at h
  refine h.congr_deriv (intervalIntegral.integral_congr fun t _ ↦ ?_)
  simp only [real_inner_comm (ξ (s, t))]
  ring

/-- **The second derivative of the slice energy.** For a `C²` map `ξ`, the function
`s ↦ ∫ₐᵇ 2 ⟪ξ(s, t), ∂s ξ(s, t)⟫ dt` has derivative
`∫ₐᵇ 2 (⟪ξ(s, t), ∂s² ξ(s, t)⟫ + ‖∂s ξ(s, t)‖²) dt`. -/
theorem hasDerivAt_intervalIntegral_two_mul_inner_fderiv {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] {ξ : ℝ × ℝ → V} (hξ : ContDiff ℝ 2 ξ) (a b s : ℝ) :
    HasDerivAt (fun s ↦ ∫ t in a..b, 2 * ⟪ξ (s, t), fderiv ℝ ξ (s, t) (1, 0)⟫)
      (∫ t in a..b, 2 * (⟪ξ (s, t), fderiv ℝ (fun y ↦ fderiv ℝ ξ y (1, 0)) (s, t) (1, 0)⟫ +
        ‖fderiv ℝ ξ (s, t) (1, 0)‖ ^ 2)) s := by
  have h := (hasDerivAt_intervalIntegral_inner (η := fun y ↦ fderiv ℝ ξ y (1, 0))
    (hξ.of_le (by norm_num)) ((hξ.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const)
    a b s).const_mul 2
  simp only [← intervalIntegral.integral_const_mul] at h
  refine h.congr_deriv (intervalIntegral.integral_congr fun t _ ↦ ?_)
  simp only [real_inner_self_eq_norm_sq]
  ring

/-- **Splitting off a function of the first variable.** If every slice `t ↦ w(s, t)` of the
continuous map `w` into a real inner product space has integral zero over `[a, b]`, then for every
continuous `m`, over the rectangle `[a₁, b₁] × [a, b]` with `a ≤ b`,
`∫ ‖m(s) + w(s, t)‖² = (b - a) ∫ₛ ‖m(s)‖² + ∫ ‖w‖²`. -/
theorem setIntegral_norm_add_sq_eq {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] {m : ℝ → V} {w : ℝ × ℝ → V} {a₁ b₁ a b : ℝ} (hab : a ≤ b)
    (hm : Continuous m) (hw : Continuous w) (hw0 : ∀ s, ∫ t in Icc a b, w (s, t) = 0) :
    ∫ z in Icc a₁ b₁ ×ˢ Icc a b, ‖m z.1 + w z‖ ^ 2 =
      (b - a) * (∫ s in Icc a₁ b₁, ‖m s‖ ^ 2) + ∫ z in Icc a₁ b₁ ×ˢ Icc a b, ‖w z‖ ^ 2 := by
  have hm₁ : Continuous fun z : ℝ × ℝ ↦ m z.1 := hm.comp continuous_fst
  have hM : IntegrableOn (fun z : ℝ × ℝ ↦ ‖m z.1‖ ^ 2) (Icc a₁ b₁ ×ˢ Icc a b) :=
    (hm₁.norm.pow 2).integrableOn_Icc_prod_Icc
  have hC : IntegrableOn (fun z : ℝ × ℝ ↦ 2 * ⟪m z.1, w z⟫) (Icc a₁ b₁ ×ˢ Icc a b) :=
    (continuous_const.mul (hm₁.inner hw)).integrableOn_Icc_prod_Icc
  have hW : IntegrableOn (fun z ↦ ‖w z‖ ^ 2) (Icc a₁ b₁ ×ˢ Icc a b) :=
    (hw.norm.pow 2).integrableOn_Icc_prod_Icc
  have hMC : IntegrableOn (fun z : ℝ × ℝ ↦ ‖m z.1‖ ^ 2 + 2 * ⟪m z.1, w z⟫)
      (Icc a₁ b₁ ×ˢ Icc a b) := hM.add hC
  simp_rw [norm_add_sq_real]
  rw [integral_add hMC hW, integral_add hM hC]
  -- The first term integrates over `[a, b]` in `t`, and the cross term vanishes.
  have h₁ : ∫ z in Icc a₁ b₁ ×ˢ Icc a b, ‖m z.1‖ ^ 2 = (b - a) * ∫ s in Icc a₁ b₁, ‖m s‖ ^ 2 :=
    setIntegral_Icc_prod_comp_fst (fun s ↦ ‖m s‖ ^ 2) hab
  have h₂ : ∫ z in Icc a₁ b₁ ×ˢ Icc a b, 2 * ⟪m z.1, w z⟫ = 0 := by
    rw [Measure.volume_eq_prod, setIntegral_prod _ hC]
    refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun s ↦ ?_)
    have hws : Integrable (fun t ↦ w (s, t)) (volume.restrict (Icc a b)) :=
      (hw.comp (Continuous.prodMk_right s)).integrableOn_Icc
    simp only [Pi.zero_apply]
    rw [integral_const_mul, integral_inner hws, hw0 s, inner_zero_right, mul_zero]
  rw [h₁, h₂, add_zero]

end TauCeti

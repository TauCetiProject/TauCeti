/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Fréchet derivative of quotients into a normed field

This file provides the Fréchet quotient rule (`HasStrictFDerivAt.div`, `HasFDerivWithinAt.div`,
and `HasFDerivAt.div`) for functions taking values in a normed field `𝕜'` over a nontrivially
normed base field `𝕜`.
-/

public section

namespace TauCeti

variable {𝕜 E 𝕜' : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedField 𝕜'] [NormedAlgebra 𝕜 𝕜'] {f g : E → 𝕜'} {f' g' : E →L[𝕜] 𝕜'} {s : Set E} {x : E}

/-- Fréchet quotient rule for `HasStrictFDerivAt`: if `f` and `g` have strict Fréchet derivatives
`f'` and `g'` at `x` and `g x ≠ 0`, then `f / g` has strict Fréchet derivative
`(g x)⁻¹ • (f' - (f x / g x) • g')` at `x`. -/
@[to_fun]
theorem _root_.HasStrictFDerivAt.div (hf : HasStrictFDerivAt f f' x) (hg : HasStrictFDerivAt g g' x)
    (hq : g x ≠ 0) :
    HasStrictFDerivAt (f / g) ((g x)⁻¹ • (f' - (f x / g x) • g')) x := by
  rw [div_eq_mul_inv]
  have hmul := hf.mul ((hasStrictFDerivAt_inv' hq).comp x hg)
  refine hmul.congr_fderiv ?_
  ext v
  simp only [add_apply, smul_apply, neg_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.mulLeftRight_apply, sub_apply, smul_eq_mul]
  field_simp
  ring

/-- Fréchet quotient rule for `HasFDerivWithinAt`: if `f` and `g` have Fréchet derivatives `f'`
and `g'` within `s` at `x` and `g x ≠ 0`, then `f / g` has Fréchet derivative
`(g x)⁻¹ • (f' - (f x / g x) • g')` within `s` at `x`. -/
@[to_fun]
theorem _root_.HasFDerivWithinAt.div (hf : HasFDerivWithinAt f f' s x)
    (hg : HasFDerivWithinAt g g' s x) (hq : g x ≠ 0) :
    HasFDerivWithinAt (f / g) ((g x)⁻¹ • (f' - (f x / g x) • g')) s x := by
  rw [div_eq_mul_inv]
  have hmul := hf.mul ((hasFDerivAt_inv' hq).comp_hasFDerivWithinAt x hg)
  refine hmul.congr_fderiv ?_
  ext v
  simp only [add_apply, smul_apply, neg_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.mulLeftRight_apply, sub_apply, smul_eq_mul, Function.comp_apply]
  field_simp
  ring

/-- Fréchet quotient rule for `HasFDerivAt`: if `f` and `g` have Fréchet derivatives `f'` and `g'`
at `x` and `g x ≠ 0`, then `f / g` has Fréchet derivative
`(g x)⁻¹ • (f' - (f x / g x) • g')` at `x`. -/
@[to_fun]
theorem _root_.HasFDerivAt.div (hf : HasFDerivAt f f' x) (hg : HasFDerivAt g g' x)
    (hq : g x ≠ 0) :
    HasFDerivAt (f / g) ((g x)⁻¹ • (f' - (f x / g x) • g')) x := by
  rw [← hasFDerivWithinAt_univ] at hf hg ⊢
  exact hf.div hg hq

end TauCeti

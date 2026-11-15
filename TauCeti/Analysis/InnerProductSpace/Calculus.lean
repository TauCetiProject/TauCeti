/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Complex derivatives of inner products

The inner product `⟪x, y⟫` of a complex inner product space is conjugate-linear in `x`, so the
inner product `⟪f w, g w⟫` of two holomorphic families is not holomorphic in general. It is
holomorphic when the first family is *antiholomorphic*, that is of the form `w ↦ f (conj w)` with
`f` holomorphic: the two conjugations cancel. This is the form in which inner products of analytic
families of vectors enter Stein's interpolation argument and the three-lines theorem.

## Main results

* `HasDerivAt.inner_comp_conj`: if `f` has derivative `f'` at `conj z` and `g` has derivative `g'`
  at `z`, then `w ↦ ⟪f (conj w), g w⟫` has derivative `⟪f', g z⟫ + ⟪f (conj z), g'⟫` at `z`.
-/

public section

open scoped InnerProductSpace ComplexConjugate

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X]

/-- The inner product of an antiholomorphic and a holomorphic family is holomorphic: if `f` has
complex derivative `f'` at `conj z` and `g` has complex derivative `g'` at `z`, then
`w ↦ ⟪f (conj w), g w⟫` has complex derivative `⟪f', g z⟫ + ⟪f (conj z), g'⟫` at `z`. -/
theorem HasDerivAt.inner_comp_conj {f g : ℂ → X} {f' g' : X} {z : ℂ}
    (hf : HasDerivAt f f' (conj z)) (hg : HasDerivAt g g' z) :
    HasDerivAt (fun w ↦ ⟪f (conj w), g w⟫_ℂ) (⟪f', g z⟫_ℂ + ⟪f (conj z), g'⟫_ℂ) z := by
  -- Over `ℝ`, `w ↦ f (conj w)` is differentiable with derivative `h ↦ conj h • f'`.
  have hf₁ : HasFDerivAt f ((ContinuousLinearMap.toSpanSingleton ℂ f').restrictScalars ℝ)
      (Complex.conjCLE z) := by
    simpa using hf.hasFDerivAt.restrictScalars ℝ
  have hD := (hf₁.comp z Complex.conjCLE.hasFDerivAt).inner ℂ (hg.hasFDerivAt.restrictScalars ℝ)
  refine hasDerivAt_iff_hasFDerivAt.2 (hasFDerivAt_of_restrictScalars ℝ hD ?_)
  ext1 h
  simp [fderivInnerCLM_apply, inner_smul_left, inner_smul_right, mul_add, add_comm]

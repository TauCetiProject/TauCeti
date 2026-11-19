/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Analysis.CStarAlgebra.Module.Defs

/-!
# Inner products of functional-calculus multiples of a vector

Let `x` be a vector of a Hilbert C⋆-module `E` over a possibly nonunital C⋆-algebra `A`, and
suppose that `⟪x, x⟫_A = w(s)` for a self-adjoint `s` and a real function `w` vanishing at `0`.
Then the inner products of the vectors `f(s) • x`, for real functions `f` vanishing at `0`, are
computed by the nonunital continuous functional calculus at `s`:
`⟪f(s) • x, g(s) • x⟫_A = (g w f)(s)`. In particular the defect `f(s) • x - x` has inner square
`(w (1 - f) ^ 2)(s)`, which reduces norm estimates for `f(s) • x - x` to real estimates on the
spectrum of `s`. Typically `s = ⟪x, x⟫_A ^ r` and `w(u) = u ^ (1 / r)`.

## Main declarations

* `CStarModule.inner_cfcₙ_smul_left`: `⟪f(s) • x, x⟫_A = (w f)(s)`.
* `CStarModule.inner_cfcₙ_smul_right`: `⟪x, f(s) • x⟫_A = (f w)(s)`.
* `CStarModule.inner_cfcₙ_smul_cfcₙ_smul`: `⟪f(s) • x, g(s) • x⟫_A = (g w f)(s)`.
* `CStarModule.inner_cfcₙ_smul_sub_self`: `⟪f(s) • x - x, f(s) • x - x⟫_A = (w (1 - f) ^ 2)(s)`.

## References

* Iain Raeburn and Dana P. Williams, *Morita Equivalence and Continuous-Trace C⋆-Algebras*,
  proof of Proposition 2.31.
-/

public section

namespace CStarModule

variable {A E : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A]
  [AddCommGroup E] [Module ℂ E] [SMul A E] [Norm E] [CStarModule A E]
  {x : E} {s : A} {w : ℝ → ℝ}

/-- If `⟪x, x⟫_A = w(s)`, the inner product of `f(s) • x` with `x` is `(w f)(s)`. -/
theorem inner_cfcₙ_smul_left (f : ℝ → ℝ) (hxs : cfcₙ w s = inner A x x)
    (hw : ContinuousOn w (quasispectrum ℝ s) := by cfc_cont_tac)
    (hw0 : w 0 = 0 := by cfc_zero_tac)
    (hf : ContinuousOn f (quasispectrum ℝ s) := by cfc_cont_tac)
    (hf0 : f 0 = 0 := by cfc_zero_tac) :
    inner A (cfcₙ f s • x) x = cfcₙ (fun u ↦ w u * f u) s := by
  rw [inner_op_smul_left, (IsSelfAdjoint.cfcₙ (f := f)).star_eq, cfcₙ_mul w f s, hxs]

/-- If `⟪x, x⟫_A = w(s)`, the inner product of `x` with `f(s) • x` is `(f w)(s)`. -/
theorem inner_cfcₙ_smul_right (f : ℝ → ℝ) (hxs : cfcₙ w s = inner A x x)
    (hw : ContinuousOn w (quasispectrum ℝ s) := by cfc_cont_tac)
    (hw0 : w 0 = 0 := by cfc_zero_tac)
    (hf : ContinuousOn f (quasispectrum ℝ s) := by cfc_cont_tac)
    (hf0 : f 0 = 0 := by cfc_zero_tac) :
    inner A x (cfcₙ f s • x) = cfcₙ (fun u ↦ f u * w u) s := by
  rw [inner_op_smul_right, cfcₙ_mul f w s, hxs]

/-- If `⟪x, x⟫_A = w(s)`, the inner product of `f(s) • x` with `g(s) • x` is `(g w f)(s)`. -/
theorem inner_cfcₙ_smul_cfcₙ_smul (f g : ℝ → ℝ) (hxs : cfcₙ w s = inner A x x)
    (hw : ContinuousOn w (quasispectrum ℝ s) := by cfc_cont_tac)
    (hw0 : w 0 = 0 := by cfc_zero_tac)
    (hf : ContinuousOn f (quasispectrum ℝ s) := by cfc_cont_tac)
    (hf0 : f 0 = 0 := by cfc_zero_tac)
    (hg : ContinuousOn g (quasispectrum ℝ s) := by cfc_cont_tac)
    (hg0 : g 0 = 0 := by cfc_zero_tac) :
    inner A (cfcₙ f s • x) (cfcₙ g s • x) = cfcₙ (fun u ↦ g u * w u * f u) s := by
  rw [inner_op_smul_left, inner_cfcₙ_smul_right g hxs, (IsSelfAdjoint.cfcₙ (f := f)).star_eq,
    cfcₙ_mul (fun u ↦ g u * w u) f s]

/-- If `⟪x, x⟫_A = w(s)`, the defect `f(s) • x - x` has inner square `(w (1 - f) ^ 2)(s)`. -/
theorem inner_cfcₙ_smul_sub_self (f : ℝ → ℝ) (hxs : cfcₙ w s = inner A x x)
    (hw : ContinuousOn w (quasispectrum ℝ s) := by cfc_cont_tac)
    (hw0 : w 0 = 0 := by cfc_zero_tac)
    (hf : ContinuousOn f (quasispectrum ℝ s) := by cfc_cont_tac)
    (hf0 : f 0 = 0 := by cfc_zero_tac) :
    inner A (cfcₙ f s • x - x) (cfcₙ f s • x - x) = cfcₙ (fun u ↦ w u * (1 - f u) ^ 2) s := by
  rw [inner_sub_left, inner_sub_right, inner_sub_right, inner_cfcₙ_smul_cfcₙ_smul f f hxs,
    inner_cfcₙ_smul_left f hxs, inner_cfcₙ_smul_right f hxs, ← hxs]
  -- Fold the three differences of functional calculi into one, then compare pointwise.
  rw [← cfcₙ_sub (hf := ?_) (hf0 := ?_) (hg := ?_) (hg0 := ?_),
    ← cfcₙ_sub (hf := ?_) (hf0 := ?_) (hg := ?_) (hg0 := ?_),
    ← cfcₙ_sub (hf := ?_) (hf0 := ?_) (hg := ?_) (hg0 := ?_)]
  · exact cfcₙ_congr fun u _ ↦ by ring
  all_goals first | fun_prop | simp [hf0, hw0]

end CStarModule

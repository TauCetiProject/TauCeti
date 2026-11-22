/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Derivatives of families with locally constant square

If a family `f` of elements of a normed algebra has locally constant square `f y * f y = c`, then
differentiating the square shows that every derivative of `f` anticommutes with `f`:
`f x * df(x) v + df(x) v * f x = 0` (`TauCeti.mul_fderiv_add_fderiv_mul_eq_zero`). For a family of
almost complex structures, `J(y)² = -1`, this says that `dJ(y) v` anticommutes with `J(y)`, that
is, the derivatives of `J` are tangent to the space of almost complex structures.
-/

public section

open scoped Topology

namespace TauCeti

variable {𝕜 E 𝔸 : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedRing 𝔸] [NormedAlgebra 𝕜 𝔸]

/-- **Derivatives of a family with locally constant square anticommute with it.** If
`f y * f y = c` for all `y` near `x`, then `f x * df(x) v + df(x) v * f x = 0` for every `v`. No
differentiability is needed: where `f` is not differentiable its derivative is zero. -/
theorem mul_fderiv_add_fderiv_mul_eq_zero {f : E → 𝔸} {x : E} {c : 𝔸}
    (h : ∀ᶠ y in 𝓝 x, f y * f y = c) (v : E) :
    f x * fderiv 𝕜 f x v + fderiv 𝕜 f x v * f x = 0 := by
  by_cases hf : DifferentiableAt 𝕜 f x
  · -- The square has derivative `f x • df + df <• f x` by the product rule, and `0` since it is
    -- locally constant.
    have hsq := hf.hasFDerivAt.mul' hf.hasFDerivAt
    have hc : HasFDerivAt (f * f) (0 : E →L[𝕜] 𝔸) x :=
      (hasFDerivAt_const c x).congr_of_eventuallyEq (h.mono fun y hy ↦ hy)
    simpa using congrArg (fun L : E →L[𝕜] 𝔸 ↦ L v) (hsq.unique hc)
  · simp [fderiv_zero_of_not_differentiableAt hf]

end TauCeti

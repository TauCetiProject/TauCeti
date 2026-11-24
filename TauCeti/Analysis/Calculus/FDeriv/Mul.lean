/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Derivatives of families with locally constant square

If a family `f` of elements of a normed algebra has locally constant square `f y * f y = c`, then
differentiating the square shows that every derivative of `f` anticommutes with `f`:
`f x * df(x) v + df(x) v * f x = 0` (`TauCeti.mul_fderiv_add_fderiv_mul_eq_zero`). For a family of
almost complex structures, `J(y)² = -1`, this says that `dJ(y) v` anticommutes with `J(y)`, that
is, the derivatives of `J` are tangent to the space of almost complex structures.

The file also records the chain rule for `Ring.inverse` along a family: where `f x` is a unit,
`y ↦ (f y)⁻¹ʳ` has derivative `v ↦ -(f x)⁻¹ʳ * df(x) v * (f x)⁻¹ʳ`
(`HasFDerivAt.ringInverse`). Mathlib has the derivative of `Ring.inverse` itself and the
differentiability of the composite, but not the composite's derivative.
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

open scoped Ring

/-- **The derivative of the inverse along a family.** If `f` has derivative `f'` at `x` and
`f x` is a unit, then `y ↦ (f y)⁻¹ʳ` has derivative `v ↦ -(f x)⁻¹ʳ * f' v * (f x)⁻¹ʳ` at `x`. -/
theorem HasFDerivAt.ringInverse {𝕜 E 𝔸 : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedRing 𝔸] [NormedAlgebra 𝕜 𝔸]
    [HasSummableGeomSeries 𝔸] {f : E → 𝔸} {f' : E →L[𝕜] 𝔸} {x : E} (hf : HasFDerivAt f f' x)
    (hx : IsUnit (f x)) :
    HasFDerivAt (fun y ↦ (f y)⁻¹ʳ)
      (-(ContinuousLinearMap.mulLeftRight 𝕜 𝔸 (f x)⁻¹ʳ (f x)⁻¹ʳ ∘L f')) x := by
  obtain ⟨u, hu⟩ := hx
  have hinv := hasFDerivAt_ringInverse (𝕜 := 𝕜) u
  rw [hu] at hinv
  simpa [← hu, Ring.inverse_unit, Function.comp_def] using hinv.comp x hf

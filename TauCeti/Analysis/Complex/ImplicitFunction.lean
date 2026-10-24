/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.JointImplicitFunction
public import TauCeti.Analysis.Complex.CauchyIntegralPolydisc

/-!
# The holomorphic implicit function theorem

Let `G (z, v)` be holomorphic near `(z₀, v₀)` on a product of finite-dimensional complex normed
spaces, with invertible partial derivative in `v` at `(z₀, v₀)`. Then there is a holomorphic map
`ψ (z, w)`, defined near `(z₀, G (z₀, v₀))`, with `ψ (z₀, G (z₀, v₀)) = v₀` and
`G (z, ψ (z, w)) = w`, and near `((z₀, v₀), G (z₀, v₀))` the equation `G (z, v) = w` holds exactly
when `v = ψ (z, w)`. For each `z`, `w ↦ ψ (z, w)` is the local inverse of `v ↦ G (z, v)`, and it
depends holomorphically on the parameter `z` and the value `w` jointly.

Holomorphy here is complex differentiability on a neighbourhood, with no smoothness assumption. In
finite dimensions it already gives analyticity
(`DifferentiableOn.analyticAt_of_finiteDimensional`, a consequence of the polydisc Cauchy
formula), and the map `ψ` is then the joint implicit function
`HasStrictFDerivAt.jointImplicitFunctionOfProdDomain` of the analytic equation, which is analytic.

## Main results

* `TauCeti.exists_jointImplicitFunction_of_eventually_differentiableAt`: the **joint holomorphic
  implicit function theorem**.

## References

* R. C. Gunning, H. Rossi, *Analytic Functions of Several Complex Variables*, Prentice-Hall
  (1965), Chapter I (the holomorphic inverse and implicit function theorems).
-/

public section

open Filter
open scoped Topology

namespace TauCeti

variable {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℂ E₁] [FiniteDimensional ℂ E₁]
  {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace ℂ E₂] [FiniteDimensional ℂ E₂]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- **The joint holomorphic implicit function theorem.** Let `G : E₁ × E₂ → F` be complex
differentiable near `u`, with invertible partial derivative `∂₂G(u) : E₂ →L[ℂ] F`. Then there is a
map `ψ : E₁ × F → E₂`, holomorphic (indeed analytic) near `(u.1, G u)`, with `ψ (u.1, G u) = u.2`
and `G (z, ψ (z, w)) = w` near `(u.1, G u)`; moreover, for `(z, v)` near `u` and `w` near `G u`,
`G (z, v) = w` holds exactly when `ψ (z, w) = v`. One choice of `ψ` is
`HasStrictFDerivAt.jointImplicitFunctionOfProdDomain`, and any two maps with these properties
agree near `(u.1, G u)`
(`HasStrictFDerivAt.eventuallyEq_jointImplicitFunctionOfProdDomain_of_continuousAt`). -/
theorem exists_jointImplicitFunction_of_eventually_differentiableAt {G : E₁ × E₂ → F}
    {u : E₁ × E₂} (hG : ∀ᶠ x in 𝓝 u, DifferentiableAt ℂ G x)
    (hinv : (fderiv ℂ G u ∘L .inr ℂ E₁ E₂).IsInvertible) :
    ∃ ψ : E₁ × F → E₂, (∀ᶠ p in 𝓝 (u.1, G u), AnalyticAt ℂ ψ p) ∧ ψ (u.1, G u) = u.2 ∧
      (∀ᶠ p in 𝓝 (u.1, G u), G (p.1, ψ p) = p.2) ∧
      ∀ᶠ q in 𝓝 (u, G u), G q.1 = q.2 ↔ ψ (q.1.1, q.2) = q.1.2 := by
  have := FiniteDimensional.complete ℂ E₁
  have := FiniteDimensional.complete ℂ E₂
  -- `F` is isomorphic to `E₂` through the partial derivative, hence complete
  have : FiniteDimensional ℂ F :=
    let ⟨e, _⟩ := hinv
    LinearEquiv.finiteDimensional e.toLinearEquiv
  have := FiniteDimensional.complete ℂ F
  have hGa : AnalyticAt ℂ G u := DifferentiableOn.analyticAt_of_finiteDimensional
    (s := {x | DifferentiableAt ℂ G x}) (fun _ hx ↦ hx.differentiableWithinAt) hG
  have dfu := hGa.hasStrictFDerivAt
  exact ⟨dfu.jointImplicitFunctionOfProdDomain hinv,
    (dfu.analyticAt_jointImplicitFunctionOfProdDomain hinv hGa).eventually_analyticAt,
    dfu.jointImplicitFunctionOfProdDomain_apply_self hinv,
    dfu.eventually_apply_jointImplicitFunctionOfProdDomain hinv,
    dfu.eventually_apply_eq_iff_jointImplicitFunctionOfProdDomain hinv⟩

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic

import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Scalar second-order linear differential operators

Pointwise linearity of the scalar second-order linear differential operator
`L(w) = w'' + f w' + g w` over any nontrivially normed field
(`TauCeti.secondOrder_operator_add_const_mul`).
-/

public section

open scoped Topology

namespace TauCeti

/-- Pointwise linearity `L(ψ + c' Φ) = L(ψ) + c' L(Φ)` for the second-order linear differential
operator `L(w) = w'' + f w' + g w` under local differentiability assumptions near `z`. -/
theorem secondOrder_operator_add_const_mul {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {f g ψ Φ : 𝕜 → 𝕜} {c' z : 𝕜}
    (hψ₁ : ∀ᶠ w in nhds z, DifferentiableAt 𝕜 ψ w)
    (hΦ₁ : ∀ᶠ w in nhds z, DifferentiableAt 𝕜 Φ w)
    (hψ₂ : DifferentiableAt 𝕜 (deriv ψ) z)
    (hΦ₂ : DifferentiableAt 𝕜 (deriv Φ) z) :
    (deriv (deriv fun w ↦ ψ w + c' * Φ w) z + f z * deriv (fun w ↦ ψ w + c' * Φ w) z +
        g z * (ψ z + c' * Φ z)) =
      (deriv (deriv ψ) z + f z * deriv ψ z + g z * ψ z) +
        c' * (deriv (deriv Φ) z + f z * deriv Φ z + g z * Φ z) := by
  have hd1_ev :
      deriv (fun w ↦ ψ w + c' * Φ w) =ᶠ[nhds z] fun w ↦ deriv ψ w + c' * deriv Φ w := by
    filter_upwards [hψ₁, hΦ₁] with w hwψ hwΦ
    exact ((hwψ.hasDerivAt).add ((hwΦ.hasDerivAt).const_mul c')).deriv
  have hd2 : deriv (deriv fun w ↦ ψ w + c' * Φ w) z =
      deriv (deriv ψ) z + c' * deriv (deriv Φ) z :=
    (((hψ₂.hasDerivAt).add ((hΦ₂.hasDerivAt).const_mul c')).congr_of_eventuallyEq hd1_ev).deriv
  rw [hd1_ev.self_of_nhds, hd2]
  ring

end TauCeti

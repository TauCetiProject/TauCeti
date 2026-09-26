/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.WeilDivisor.AbelJacobi.Basic

/-!
# The Picard scheme and Abel-Jacobi map

This file formalizes the degree-zero Picard group and the Abel-Jacobi map on a curve,
advancing toward Layer F of the Jacobian challenge. It builds directly on Tau Ceti's
divisor order system and abstract Picard group `Pic⁰(X)`, proving that the Abel-Jacobi
map sends the chosen rational basepoint to the zero element in `Pic⁰(X)`.

<!--tauceti-target:v1
  {"focus":"JacobianChallenge",
   "id":"JacobianChallenge.The_Picard_scheme_and_Abel_Jacobi_map"}-->
-/

public section

namespace TauCeti.AlgebraicGeometry.WeilDivisor.OrderSystem

variable {X G : Type*} [AddCommGroup G] (S : OrderSystem X G)

/-- The Abel-Jacobi map on closed points of a curve sending each point `x` to its degree-zero
divisor class `[x] - w(x)[x₀]` in the abstract Picard group `Pic⁰(X)`. -/
noncomputable abbrev abelJacobi (w : X → ℤ) (hdeg : S.IsWeightedDegreeZero w)
    {x₀ : X} (hx₀ : w x₀ = 1) : X → picZero w hdeg :=
  S.weightedAbelJacobiClass w hdeg hx₀

/-- The Abel-Jacobi map sends the basepoint `x₀` to the identity element (zero) in `Pic⁰(X)`. -/
@[simp]
theorem abelJacobi_basepoint (w : X → ℤ) (hdeg : S.IsWeightedDegreeZero w)
    {x₀ : X} (hx₀ : w x₀ = 1) :
    abelJacobi S w hdeg hx₀ x₀ = 0 :=
  S.weightedAbelJacobiClass_base w hdeg hx₀

/-- Two points have the same Abel-Jacobi image if and only if their degree-corrected
point divisors are linearly equivalent. -/
theorem abelJacobi_eq_iff_linearlyEquivalent (w : X → ℤ)
    (hdeg : S.IsWeightedDegreeZero w) {x₀ : X} (hx₀ : w x₀ = 1) (x y : X) :
    abelJacobi S w hdeg hx₀ x = abelJacobi S w hdeg hx₀ y ↔
      S.LinearlyEquivalent (weightedPointBaseDifference w x₀ x)
        (weightedPointBaseDifference w x₀ y) :=
  S.weightedAbelJacobiClass_eq_iff_linearlyEquivalent w hdeg hx₀

end TauCeti.AlgebraicGeometry.WeilDivisor.OrderSystem

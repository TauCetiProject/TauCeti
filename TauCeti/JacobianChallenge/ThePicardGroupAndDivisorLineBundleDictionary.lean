/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.Picard

/-!
# The Picard group and divisor-line-bundle dictionary

This file establishes the divisor-line-bundle dictionary on an integral Noetherian
curve whose codimension-one local rings are discrete valuation rings. It identifies
the divisor class group `Cl(X)` with the Picard group `Additive (LineBundleClass X)`
of isomorphism classes of invertible sheaves (line bundles) via the canonical
isomorphism `classGroupAddEquivLineBundleClass`.

<!--tauceti-target:v1
  {"focus":"JacobianChallenge",
   "id":"JacobianChallenge.The_Picard_group_and_divisor_line_bundle_dictionary"}-->
-/

public section

namespace TauCeti.AlgebraicGeometry.SchemeWeilDivisor

open CategoryTheory

universe u

variable {X : AlgebraicGeometry.Scheme.{u}} [hX : CurveAssumptions X]

/-- The divisor-line-bundle dictionary: the canonical additive isomorphism between the
divisor class group `Cl(X)` and the Picard group `Additive (LineBundleClass X)` of
line-bundle isomorphism classes on a curve. -/
noncomputable abbrev divisorClassGroupEquivPicard :
    (WeilDivisor.OrderSystem.ofScheme X).ClassGroup ≃+
      Additive (LineBundleClass X) :=
  classGroupAddEquivLineBundleClass X

/-- Every line-bundle class on a curve is in the range of the divisor-to-line-bundle
map from the divisor class group. -/
theorem divisor_class_surjective :
    Function.Surjective (classGroupAddEquivLineBundleClass X) :=
  (classGroupAddEquivLineBundleClass X).surjective

/-- Two divisor classes yield isomorphic line bundles if and only if they are equal. -/
theorem divisor_class_injective :
    Function.Injective (classGroupAddEquivLineBundleClass X) :=
  (classGroupAddEquivLineBundleClass X).injective

/-- The kernel of the divisor-to-line-bundle map consists of exactly the zero class
in the divisor class group, which corresponds to principal divisors. -/
theorem divisor_class_eq_zero_iff
    (c : (WeilDivisor.OrderSystem.ofScheme X).ClassGroup) :
    classGroupAddEquivLineBundleClass X c = 0 ↔ c = 0 :=
  (classGroupAddEquivLineBundleClass X).map_eq_zero_iff c

end TauCeti.AlgebraicGeometry.SchemeWeilDivisor

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.PlaneCurve.Genus
public import TauCeti.FieldTheory.FunctionField.PlaneCurve.KleinQuartic

import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# The Klein quartic as a smooth projective curve

Let `k` be a field in which `7 ≠ 0`. The **Klein quartic** `C` is the projective plane curve

`X₀³ X₁ + X₁³ X₂ + X₂³ X₀ = 0`

over `k`, the scheme `TauCeti.AlgebraicGeometry.projectivePlaneCurve` of the homogeneous quartic
`TauCeti.kleinQuartic`, the projective closure of the affine curve `x³ y + y³ + x = 0`. This file
shows that `C` is a smooth projective curve over `k` of genus `3 = (4 - 1)(4 - 2) / 2`:

* `C` is smooth of relative dimension one over `k`, because its equation is nonsingular away from
  characteristic `7` (`TauCeti.forall_exists_aeval_pderiv_kleinQuartic_ne_zero`);
* `C` is an integral proper curve over `k`, because a nonsingular plane equation is irreducible
  (`TauCeti.irreducible_kleinQuartic`);
* `k` is the exact constant field of the function field of `C`, which has genus `3`, and the genus
  `dim_k H¹(C, 𝒪_C)` of the scheme is `3`.

These are the general statements for smooth projective plane curves in
`TauCeti.AlgebraicGeometry.Curves.PlaneCurve.Smooth` and
`TauCeti.AlgebraicGeometry.Curves.PlaneCurve.Genus`, specialized to the Klein quartic. In
characteristic `7` the curve is singular at the point `(1 : 2 : 4)`
(`TauCeti.forall_exists_aeval_pderiv_kleinQuartic_ne_zero_iff`).

## Main results

All in the namespace `TauCeti.AlgebraicGeometry.projectivePlaneCurve`:

* `smoothOfRelativeDimension_kleinQuartic`: the Klein quartic is smooth of relative dimension one.
* `isCurveOver_kleinQuartic`: the Klein quartic is a curve over `k`.
* `isIntegrallyClosedIn_functionField_kleinQuartic`: `k` is the exact constant field of its function
  field.
* `genus_functionField_kleinQuartic`: its function field has genus `3`.
* `genus_kleinQuartic`: **the Klein quartic has genus `3`**, `dim_k H¹(C, 𝒪_C) = 3`.

## References

* F. Klein, *Ueber die Transformation siebenter Ordnung der elliptischen Functionen*, Math. Ann.
  14 (1878), 428–471.
* W. Fulton, *Algebraic Curves*, Sections 5.1 and 8.3.
-/

public section

open AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry.projectivePlaneCurve

variable {k : Type u} [Field k]

/-- **The Klein quartic is smooth away from characteristic `7`**: if `7 ≠ 0` in `k`, the projective
plane curve `X₀³ X₁ + X₁³ X₂ + X₂³ X₀ = 0` is smooth of relative dimension one over `k`. -/
theorem smoothOfRelativeDimension_kleinQuartic (h7 : (7 : k) ≠ 0) :
    SmoothOfRelativeDimension 1
      (projectivePlaneCurve (isHomogeneous_kleinQuartic k) ↘ Spec (.of k)) :=
  smoothOfRelativeDimension _
    (forall_exists_aeval_pderiv_kleinQuartic_ne_zero (AlgebraicClosure k) h7)

/-- If `7 ≠ 0` in `k`, the Klein quartic is an integral proper curve over `k`. -/
theorem isCurveOver_kleinQuartic (h7 : (7 : k) ≠ 0) :
    (projectivePlaneCurve (isHomogeneous_kleinQuartic k)).IsCurveOver k :=
  have : Fact (Irreducible (kleinQuartic k)) := ⟨irreducible_kleinQuartic h7⟩
  isCurveOver _ (forall_exists_aeval_pderiv_kleinQuartic_ne_zero (AlgebraicClosure k) h7)

/-- If `7 ≠ 0` in `k`, then `k` is the exact constant field of the function field of the Klein
quartic. -/
theorem isIntegrallyClosedIn_functionField_kleinQuartic (h7 : (7 : k) ≠ 0) :
    haveI := isCurveOver_kleinQuartic h7
    IsIntegrallyClosedIn k (projectivePlaneCurve (isHomogeneous_kleinQuartic k)).functionField :=
  have : Fact (Irreducible (kleinQuartic k)) := ⟨irreducible_kleinQuartic h7⟩
  isIntegrallyClosedIn_functionField _
    (forall_exists_aeval_pderiv_kleinQuartic_ne_zero (AlgebraicClosure k) h7)

/-- If `7 ≠ 0` in `k`, the function field of the Klein quartic has genus `3`. -/
theorem genus_functionField_kleinQuartic (h7 : (7 : k) ≠ 0) :
    haveI := isCurveOver_kleinQuartic h7
    genus k (projectivePlaneCurve (isHomogeneous_kleinQuartic k)).functionField = 3 :=
  have : Fact (Irreducible (kleinQuartic k)) := ⟨irreducible_kleinQuartic h7⟩
  genus_functionField _ (forall_exists_aeval_pderiv_kleinQuartic_ne_zero (AlgebraicClosure k) h7)

/-- **The Klein quartic has genus three**: if `7 ≠ 0` in `k`, the genus `dim_k H¹(C, 𝒪_C)` of the
Klein quartic `C : X₀³ X₁ + X₁³ X₂ + X₂³ X₀ = 0` is `3 = (4 - 1)(4 - 2) / 2`. -/
theorem genus_kleinQuartic (h7 : (7 : k) ≠ 0) :
    haveI := isCurveOver_kleinQuartic h7
    haveI := isDiscreteValuationRing_stalk (isHomogeneous_kleinQuartic k)
      (forall_exists_aeval_pderiv_kleinQuartic_ne_zero (AlgebraicClosure k) h7)
    haveI := finiteDimensional_cohomology_one_trivial_of_isProper k
      (X := projectivePlaneCurve (isHomogeneous_kleinQuartic k))
      (Scheme.IsCurveOver.topologicalKrullDim_eq_one k)
    (projectivePlaneCurve (isHomogeneous_kleinQuartic k)).genus k = 3 :=
  have : Fact (Irreducible (kleinQuartic k)) := ⟨irreducible_kleinQuartic h7⟩
  genus_eq _ (forall_exists_aeval_pderiv_kleinQuartic_ne_zero (AlgebraicClosure k) h7)

end TauCeti.AlgebraicGeometry.projectivePlaneCurve

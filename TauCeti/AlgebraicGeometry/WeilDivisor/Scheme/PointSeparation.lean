/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Scheme.FunctionField
public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.SerreDuality
public import TauCeti.FieldTheory.FunctionField.Consequences.PointSeparation

/-!
# Abel–Jacobi point separation on curves of positive genus

On a proper regular integral curve of positive genus with exact constant field, linearly
equivalent closed points coincide whenever one has residue degree one. Thus the map
`x ↦ [𝒪_X(x - x₀)]` is injective on rational closed points, for any fixed closed point `x₀`.
The base point need not be rational for point separation; rationality is needed to make
these classes have degree zero.

This is the point-separation part of the Abel–Jacobi embedding theorem. The result concerns
line-bundle classes, and does not construct a scheme morphism or prove an immersion.
It applies over arbitrary exact constant fields, without perfectness assumptions.

At a rational closed point `p`, the space `H⁰(X, 𝒪_X(p))` is one-dimensional in positive
genus, and the inclusion `𝒪_X ⟶ 𝒪_X(p)` induces a bijection on global sections. These
results use `Divisor.dim_ofPoint_eq_one_of_genus_pos` through the scheme/function-field
comparison and supply the cohomological input to tangent separation.

## References

* R. Hartshorne, *Algebraic Geometry*, Chapter IV, Section 1 and Theorem 4.17.
* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., Theorem 1.6.8.
-/

public section

open CategoryTheory Limits AlgebraicGeometry Order
open Module (finrank)

namespace TauCeti.AlgebraicGeometry.SchemeWeilDivisor

universe u

noncomputable section

variable (k : Type u) [Field k] {X : Scheme.{u}} [IsIntegral X] [IsNoetherian X]
  [∀ y : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (y : X))]
  [hX : Fact (∀ y : X, coheight y ≤ 1)] [X.Over (Spec (.of k))] [IsProper (X ↘ Spec (.of k))]
  [FiniteDimensional k (Scheme.Modules.Cohomology (InvertibleSheaf.trivial X).obj 1)]

/-- **Linearly equivalent rational points on a curve of positive genus are equal.** Here
`X` is a proper integral curve over `k` whose codimension-one local rings are discrete valuation
rings, with `k` integrally closed in `k(X)`, and only the point `x` is required to have residue
degree one. -/
theorem eq_of_linearlyEquivalent_ofPoint_of_genus_pos
    (hk : IsIntegrallyClosedIn k X.functionField) (hg : 0 < X.genus k) {x y : CodimensionOnePoint X}
    (hx : (X ↘ Spec (.of k)).residueDegree x = 1)
    (h : (WeilDivisor.OrderSystem.ofScheme X).LinearlyEquivalent (WeilDivisor.ofPoint x)
      (WeilDivisor.ofPoint y)) :
    x = y := by
  have : X.IsSeparated := ⟨by rw [← terminal.comp_from (X ↘ Spec (.of k))]; infer_instance⟩
  have hex : ValuativeCriterion.Existence (X ↘ Spec (.of k)) :=
    (UniversallyClosed.eq_valuativeCriterion ▸
      (inferInstance : UniversallyClosed (X ↘ Spec (.of k)))).1
  have hF := isFunctionField_functionField_of_forall_coheight_le_one_of_coheight_eq_one
    k hX.out x.2
  have hgF : 0 < genus k X.functionField := by
    rwa [← genus_eq_genus_functionField hex hX.out hF hk]
  apply (CodimensionOnePoint.equivPlace hex hX.out).injective
  rw [CodimensionOnePoint.equivPlace_apply, CodimensionOnePoint.equivPlace_apply]
  refine Place.eq_of_linearlyEquivalent_ofPoint_of_genus_pos hF hk hgF
    (by rw [X.toPlace_degree_eq_residueDegree, hx]) ?_
  rw [← equivFunctionFieldDivisor_ofPoint hex hX.out,
    ← equivFunctionFieldDivisor_ofPoint hex hX.out,
    linearlyEquivalent_equivFunctionFieldDivisor_iff hex hX.out hF]
  exact h

/-- On a positive-genus proper regular curve with exact constants, the Abel–Jacobi
line-bundle class separates rational closed points, with any fixed closed base point. -/
theorem injective_toLineBundleClass_pointDifference
    (hk : IsIntegrallyClosedIn k X.functionField) (hg : 0 < X.genus k)
    (x₀ : CodimensionOnePoint X) :
    Function.Injective fun x : {x : CodimensionOnePoint X //
      (X ↘ Spec (.of k)).residueDegree x = 1} ↦
        toLineBundleClass hX.out (WeilDivisor.pointDifference x.1 x₀) := by
  intro x y h
  have hlin := (toLineBundleClass_eq_iff hX.out).mp h
  apply Subtype.ext
  apply eq_of_linearlyEquivalent_ofPoint_of_genus_pos k hk hg x.2
  simpa [WeilDivisor.pointDifference] using
    hlin.add_right (WeilDivisor.OrderSystem.ofScheme X) (WeilDivisor.ofPoint x₀)

variable (hk : IsIntegrallyClosedIn k X.functionField)
  {p : CodimensionOnePoint X} (hp : (X ↘ Spec (.of k)).residueDegree p = 1)

include hk hp

/-- On a positive-genus proper regular curve with exact constants, allowing a simple pole
at a rational closed point still gives only a one-dimensional space of global sections. -/
theorem finrank_cohomology_zero_sheaf_ofPoint_eq_one_of_genus_pos (hg : 0 < X.genus k) :
    finrank k (Scheme.Modules.Cohomology (sheaf (WeilDivisor.ofPoint p)) 0) = 1 := by
  have : X.IsSeparated := ⟨by rw [← terminal.comp_from (X ↘ Spec (.of k))]; infer_instance⟩
  have hex := (UniversallyClosed.eq_valuativeCriterion.le _ _
    (X ↘ Spec (.of k)) inferInstance).1
  have hF := isFunctionField_functionField_of_forall_coheight_le_one_of_coheight_eq_one
    k hX.out p.2
  have hgF : 0 < genus k X.functionField := by
    rwa [← genus_eq_genus_functionField hex hX.out hF hk]
  rw [finrank_cohomology_zero_sheaf_eq_dim hex hX.out,
    equivFunctionFieldDivisor_ofPoint]
  exact Divisor.dim_ofPoint_eq_one_of_genus_pos hF hk hgF
    (by rw [X.toPlace_degree_eq_residueDegree, hp])

/-- The inclusion `𝒪_X ⟶ 𝒪_X(p)` is a bijection on zeroth cohomology when `p` is rational
and the curve has positive genus. -/
theorem cohomologyMap_sheafHomOfLE_zero_add_ofPoint_bijective_of_genus_pos
    (hg : 0 < X.genus k) :
    Function.Bijective (Scheme.Modules.cohomologyMap
      (sheafHomOfLE (WeilDivisor.le_add_ofPoint (0 : SchemeWeilDivisor X) p)) 0) := by
  have : X.IsSeparated := ⟨by rw [← terminal.comp_from (X ↘ Spec (.of k))]; infer_instance⟩
  have hex := (UniversallyClosed.eq_valuativeCriterion.le _ _
    (X ↘ Spec (.of k)) inferInstance).1
  have hF := isFunctionField_functionField_of_forall_coheight_le_one_of_coheight_eq_one
    k hX.out p.2
  have := finiteDimensional_cohomology_zero_sheaf (k := k) hX.out
    (D := (0 : SchemeWeilDivisor X))
  have := finiteDimensional_cohomology_zero_sheaf (k := k) hX.out
    (D := (0 : SchemeWeilDivisor X) + WeilDivisor.ofPoint p)
  let i := sheafHomOfLE (WeilDivisor.le_add_ofPoint (0 : SchemeWeilDivisor X) p)
  have hi := Scheme.Modules.cohomologyMap_injective i
  have hdim : finrank k (Scheme.Modules.Cohomology (sheaf (0 : SchemeWeilDivisor X)) 0) =
      finrank k (Scheme.Modules.Cohomology (sheaf (0 + WeilDivisor.ofPoint p)) 0) := by
    rw [zero_add, finrank_cohomology_zero_sheaf_zero_eq_one hex hX.out hF hk,
      finrank_cohomology_zero_sheaf_ofPoint_eq_one_of_genus_pos k hk hp hg]
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim
    (f := Scheme.Modules.cohomologyMapBaseLinear k X i 0)).mp (by
      simpa only [Scheme.Modules.coe_cohomologyMapBaseLinear] using hi)
  exact ⟨hi, by simpa only [Scheme.Modules.coe_cohomologyMapBaseLinear] using hsurj⟩

end

end TauCeti.AlgebraicGeometry.SchemeWeilDivisor

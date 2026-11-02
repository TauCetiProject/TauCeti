/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Morphisms.Smooth.GeometricallyIntegral
public import TauCeti.AlgebraicGeometry.Morphisms.Smooth.RelativeDimension
public import TauCeti.AlgebraicGeometry.Scheme.DiscreteValuationStalk
public import TauCeti.AlgebraicGeometry.Geometrically.FunctionField
public import TauCeti.AlgebraicGeometry.LineBundle.HighDegree

/-!
# High-degree line bundles on smooth proper curves

Let `X` be smooth, proper and geometrically connected of relative dimension one over a field
`k`. Every line bundle `L` with `deg L > 2g - 2` has vanishing first cohomology and
`dim H⁰(X, L) = deg L + 1 - g`. These are the numerical inputs for the large-degree Abel maps:
a divisor class of degree `d > 2g - 2` has a space of sections of dimension `d + 1 - g`.

The geometric assumptions imply integrality, regularity, discrete valuation stalks, finite
cohomology, and the constant-field condition used by the function-field comparison. In the
statements, `g` is written as `finrank k H¹(X, 𝒪_X)` so that no finiteness or regularity instance
must be supplied by the caller. The proof establishes finiteness from the geometric assumptions.
Neither a rational point nor a perfectness assumption on `k` is required.

## References

* R. Hartshorne, *Algebraic Geometry*, Chapter IV, Example 1.3.4.
* J. S. Milne, *Jacobian Varieties*, Section 5 (large-degree Abel maps).
-/

public section

open CategoryTheory Limits AlgebraicGeometry Order
open Module (finrank)

namespace TauCeti.AlgebraicGeometry.InvertibleSheaf

universe u

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [IsProper (X ↘ Spec (.of k))] [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))]
  [GeometricallyConnected (X ↘ Spec (.of k))]

/-- A smooth proper geometrically connected curve is integral, has discrete valuation stalks
at codimension-one points and coheight at most one, and its function field has exact constant
field `k`. These are the hypotheses used by the high-degree line-bundle criteria. -/
theorem high_degree_hypotheses_of_smooth :
    ∃ hI : IsIntegral X,
      have := hI
      (∀ x : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (x : X))) ∧
        (∀ x : X, coheight x ≤ 1) ∧ IsFunctionField k X.functionField ∧
          IsIntegrallyClosedIn k X.functionField := by
  have := SmoothOfRelativeDimension.smooth 1 (X ↘ Spec (.of k))
  have : IsIntegral X := GeometricallyIntegral.isIntegral_of_subsingleton (X ↘ Spec (.of k))
  have : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x) :=
    isRegularLocalRing_stalk_of_smooth (X ↘ Spec (.of k))
  have : ∀ x : CodimensionOnePoint X,
      IsDiscreteValuationRing (X.presheaf.stalk (x : X)) := fun x ↦ inferInstance
  have hdim : topologicalKrullDim X = 1 :=
    topologicalKrullDim_eq_of_smoothOfRelativeDimension (X ↘ Spec (.of k))
  have hcoheight (x : X) : coheight x ≤ 1 := by
    exact_mod_cast (coheight_le_topologicalKrullDim x).trans hdim.le
  exact ⟨inferInstance, inferInstance, hcoheight,
    ((isFunctionField_functionField_iff k).mpr hdim),
    isIntegrallyClosedIn_functionField_of_geometricallyIntegral⟩

/-- On a smooth proper geometrically connected curve over any field, a line bundle of degree
above `2g - 2` has vanishing first cohomology. All finiteness and regularity hypotheses are
consequences of the geometric assumptions. -/
theorem subsingleton_cohomology_one_of_smooth_of_two_mul_genus_sub_two_lt_eulerDegree
    (L : InvertibleSheaf X)
    (hL : 2 * (finrank k (Scheme.Modules.Cohomology (trivial X).obj 1) : ℤ) - 2 <
      L.eulerDegree k) :
    Subsingleton (Scheme.Modules.Cohomology L.obj 1) := by
  obtain ⟨hI, h⟩ := high_degree_hypotheses_of_smooth (k := k) (X := X)
  have := hI
  obtain ⟨hDVR, hcoheight, hF, hk⟩ := h
  have := hDVR
  exact subsingleton_cohomology_one_of_two_mul_genus_sub_two_lt_eulerDegree
    hcoheight hF hk L hL

/-- On a smooth proper geometrically connected curve over any field, a line bundle of degree
above `2g - 2` has exactly `deg L + 1 - g` independent sections. The equality is over the integers
and does not assume a rational point. -/
theorem finrank_cohomology_zero_eq_eulerDegree_add_one_sub_genus_of_smooth
    (L : InvertibleSheaf X)
    (hL : 2 * (finrank k (Scheme.Modules.Cohomology (trivial X).obj 1) : ℤ) - 2 <
      L.eulerDegree k) :
    (finrank k (Scheme.Modules.Cohomology L.obj 0) : ℤ) = L.eulerDegree k + 1 -
      finrank k (Scheme.Modules.Cohomology (trivial X).obj 1) := by
  obtain ⟨hI, h⟩ := high_degree_hypotheses_of_smooth (k := k) (X := X)
  have := hI
  obtain ⟨hDVR, hcoheight, hF, hk⟩ := h
  have := hDVR
  exact finrank_cohomology_zero_eq_eulerDegree_add_one_sub_genus hcoheight hF hk L hL

end TauCeti.AlgebraicGeometry.InvertibleSheaf

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Morphisms.Smooth.GeometricallyIntegral
public import TauCeti.AlgebraicGeometry.Morphisms.Smooth.RelativeDimension
public import TauCeti.AlgebraicGeometry.Scheme.DiscreteValuationStalk
public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.RiemannRoch.Finiteness
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.Regular

/-!
# Degree on smooth proper curves

On a proper integral scheme smooth of relative dimension one over a field `k`, principal
divisors have degree zero and the Euler-characteristic degree `χ(L) - χ(𝒪_X)` of a line bundle
is the degree of any of its divisors. On a connected smooth proper curve over a field, the
Euler-characteristic degree of a tensor product is the sum of the degrees. The geometric
hypotheses suffice: regularity gives integral local rings and discrete valuation rings in
codimension one, relative dimension one bounds the codimension of every point by one
(`TauCeti.AlgebraicGeometry.coheight_le_of_relativeDimensionLE_of_field`), and properness gives
finite-dimensional first cohomology. No rational point or perfectness of the field is required.

The field-valued fibres of a smooth proper geometrically connected family of relative dimension
one satisfy these hypotheses. Consequently degree is additive on the Picard group of every such
fibre. This is the fibrewise calculation which makes the classes of degree zero on every
geometric fibre closed under tensor product.

## Main results

* `SchemeWeilDivisor.relativeDegree_principalDivisor_of_smooth`: principal divisors on a proper
  integral smooth curve have degree zero;
* `InvertibleSheaf.eulerDegree_eq_relativeDegree_of_smooth`: on such a curve, the
  Euler-characteristic degree of `𝒪_X(D)` is `Σ_y D(y) [κ(y) : k]`;
* `LineBundleClass.eulerDegree_mul_of_smooth`: additivity on connected smooth proper curves;
* `LineBundleClass.eulerDegree_mul_fieldValuedBaseChange`: additivity on all field-valued fibres
  of a smooth proper geometrically connected family of curves.

## References

* R. Hartshorne, *Algebraic Geometry*, Chapter II, Corollary 6.10, Chapter III,
  Proposition 9.3, and Chapter IV, Section 1.
* S. Kleiman, *The Picard scheme*, in *Fundamental Algebraic Geometry: Grothendieck's FGA
  Explained*, Section 9.5.
-/

public section

open CategoryTheory Limits AlgebraicGeometry Order

namespace TauCeti.AlgebraicGeometry

universe u

noncomputable section

namespace SchemeWeilDivisor

variable (k : Type u) [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsIntegral X]
  [IsProper (X ↘ Spec (.of k))] [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))]

/-- **A principal divisor on a smooth proper curve has degree zero.** On a proper integral scheme
smooth of relative dimension one over a field `k`, the divisor of a nonzero rational function
has degree `Σ_y ord_y(f) [κ(y) : k] = 0`. -/
theorem relativeDegree_principalDivisor_of_smooth [IsNoetherian X]
    (f : Additive X.functionFieldˣ) :
    relativeDegree (X ↘ Spec (.of k))
        ((WeilDivisor.OrderSystem.ofScheme X).principalDivisor f) = 0 := by
  have := SmoothOfRelativeDimension.smooth 1 (X ↘ Spec (.of k))
  have := isDiscreteValuationRing_stalk_of_smooth k (X := X)
  have := finiteDimensional_cohomology_one_trivial_of_smooth k X
  exact relativeDegree_principalDivisor k
    (coheight_le_of_relativeDimensionLE_of_field (d := 1) (X ↘ Spec (.of k))) f

end SchemeWeilDivisor

namespace InvertibleSheaf

variable (k : Type u) [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsIntegral X]
  [IsProper (X ↘ Spec (.of k))] [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))]

/-- **The degree of a line bundle on a smooth proper curve is the degree of its divisors.** On a
proper integral scheme smooth of relative dimension one over a field `k`, a line bundle
`L ≅ 𝒪_X(D)` has `χ(L) - χ(𝒪_X) = Σ_y D(y) [κ(y) : k]`. -/
theorem eulerDegree_eq_relativeDegree_of_smooth [IsLocallyNoetherian X]
    [∀ y : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (y : X))]
    {L : InvertibleSheaf X} {D : SchemeWeilDivisor X} (e : L.obj ≅ SchemeWeilDivisor.sheaf D) :
    L.eulerDegree k = SchemeWeilDivisor.relativeDegree (X ↘ Spec (.of k)) D := by
  have := finiteDimensional_cohomology_one_trivial_of_smooth k X
  exact eulerDegree_eq_relativeDegree k
    (coheight_le_of_relativeDimensionLE_of_field (d := 1) (X ↘ Spec (.of k))) e

end InvertibleSheaf

namespace LineBundleClass

/-- The Euler-characteristic degree is additive on a connected smooth proper curve over any
field. Integrality, discrete valuation stalks, and finiteness of cohomology follow from the
geometric hypotheses; no rational point is required. -/
@[simp]
theorem eulerDegree_mul_of_smooth (k : Type u) [Field k] {X : Scheme.{u}}
    [X.Over (Spec (.of k))] [IsProper (X ↘ Spec (.of k))]
    [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))] [ConnectedSpace X]
    (a b : LineBundleClass X) :
    eulerDegree k (a * b) = eulerDegree k a + eulerDegree k b := by
  have := SmoothOfRelativeDimension.smooth 1 (X ↘ Spec (.of k))
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x) :=
    isRegularLocalRing_stalk_of_smooth (X ↘ Spec (.of k))
  have : IsIntegral X := isIntegral_of_connected_of_isRegularLocalRing_stalk X
  have : ∀ x : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (x : X)) :=
    fun x ↦ inferInstance
  have hdim : topologicalKrullDim X = 1 :=
    topologicalKrullDim_eq_of_smoothOfRelativeDimension (X ↘ Spec (.of k))
  have := finiteDimensional_cohomology_one_trivial_of_isProper k hdim
  exact eulerDegree_mul k (fun x ↦ by
    exact_mod_cast (coheight_le_topologicalKrullDim x).trans hdim.le) a b

/-- On every field-valued fibre of a smooth proper geometrically connected family of curves,
the Euler-characteristic degree is additive. The point may have values in an arbitrary field,
including an imperfect field. -/
@[simp]
theorem eulerDegree_mul_fieldValuedBaseChange {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f]
    [SmoothOfRelativeDimension 1 f] [GeometricallyConnected f]
    (k : Type u) [Field k] (s : Spec (.of k) ⟶ S)
    (a b : LineBundleClass (pullback s f)) :
    letI : (pullback s f).Over (Spec (.of k)) := ⟨pullback.fst s f⟩
    eulerDegree k (a * b) = eulerDegree k a + eulerDegree k b := by
  let _ : (pullback s f).Over (Spec (.of k)) := ⟨pullback.fst s f⟩
  have := SmoothOfRelativeDimension.smooth 1 f
  have : IsProper (pullback s f ↘ Spec (.of k)) :=
    inferInstanceAs (IsProper (pullback.fst s f))
  have : SmoothOfRelativeDimension 1 (pullback s f ↘ Spec (.of k)) :=
    inferInstanceAs (SmoothOfRelativeDimension 1 (pullback.fst s f))
  have : IsIntegral (pullback s f) :=
    GeometricallyIntegral.geometrically_isIntegral s _ _ (IsPullback.of_hasPullback s f).flip
  exact eulerDegree_mul_of_smooth k a b

end LineBundleClass

end

end TauCeti.AlgebraicGeometry

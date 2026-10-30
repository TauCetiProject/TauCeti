/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.TwoChartModel.AntiEquivalence
public import TauCeti.AlgebraicGeometry.Curves.TwoChartModel.ProjectiveEmbedding

/-!
# Regular projective curves are anti-equivalent to algebraic function fields

Let `k` be a field. A regular projective curve over `k` is an integral scheme `X` over `k` that is
projective over `k` (a closed subscheme over `k` of a projective space
`Proj (Sym_k V)`), of dimension one, and whose local rings at the codimension-one points are
discrete valuation rings. This file packages these curves, with the dominant `k`-morphisms, as the
category `RegularProjectiveCurveCat k`, and proves that `X ↦ k(X)` is an anti-equivalence between
it and algebraic function fields of one variable over `k` with `k`-embeddings.

Properness is not part of the definition: a projective scheme over `k` is proper over `k`, so a
regular projective curve is a regular proper curve. Conversely every regular proper curve is
projective (`AlgebraicGeometry.Scheme.isProjectiveOver_of_isCurveOver`), so forgetting
projectivity is an equivalence `RegularProjectiveCurveCat k ≌ RegularProperCurveCat k`. Composing
it with the anti-equivalence of regular proper curves with function fields
(`TauCeti.AlgebraicGeometry.RegularProperCurveCat.equivFunctionFieldCat`) gives the
anti-equivalence for regular projective curves. Its inverse sends a function field to its
two-chart model, the normalization of the projective line in it.

## Main definitions

* `TauCeti.AlgebraicGeometry.RegularProjectiveCurveCat`: the category of regular projective curves
  over `k`, with the dominant `k`-morphisms.
* `TauCeti.AlgebraicGeometry.RegularProjectiveCurveCat.toRegularProperCurveCat`: a regular
  projective curve, as a regular proper curve.
* `TauCeti.AlgebraicGeometry.RegularProjectiveCurveCat.equivRegularProperCurveCat`: the
  equivalence `RegularProjectiveCurveCat k ≌ RegularProperCurveCat k` forgetting projectivity.
* `TauCeti.AlgebraicGeometry.RegularProjectiveCurveCat.equivFunctionFieldCat`:
  **the anti-equivalence** `RegularProjectiveCurveCat k ≌ (FunctionFieldCat k)ᵒᵖ`, sending a curve
  to its function field.

## References

* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Corollary I.6.12.
* Q. Liu, *Algebraic Geometry and Arithmetic Curves*, Oxford GTM 6, 2002, Section 7.3.
* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Appendix B.
-/

@[expose] public section

open CategoryTheory _root_.AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry

/-- A regular projective curve over a field `k`: an integral scheme over `k` that is projective
over `k` and of dimension one, and whose local rings at the codimension-one points are discrete
valuation rings. The morphisms of `RegularProjectiveCurveCat k` are the dominant `k`-morphisms. -/
structure RegularProjectiveCurveCat (k : Type u) [Field k] where
  /-- The underlying scheme. -/
  toScheme : Scheme.{u}
  [over : toScheme.Over (Spec (.of k))]
  [isIntegral : IsIntegral toScheme]
  [isProjectiveOver : toScheme.IsProjectiveOver k]
  /-- The curve has dimension one. -/
  topologicalKrullDim_eq_one : topologicalKrullDim toScheme = 1
  [isDiscreteValuationRing_stalk :
    ∀ y : CodimensionOnePoint toScheme, IsDiscreteValuationRing (toScheme.presheaf.stalk y.1)]

attribute [instance] RegularProjectiveCurveCat.over RegularProjectiveCurveCat.isIntegral
  RegularProjectiveCurveCat.isProjectiveOver RegularProjectiveCurveCat.isDiscreteValuationRing_stalk

namespace RegularProjectiveCurveCat

variable {k : Type u} [Field k]

/-- A regular projective curve over `k` is a curve over `k`: being projective, it is proper
over `k`. -/
instance isCurveOver (X : RegularProjectiveCurveCat k) : X.toScheme.IsCurveOver k where
  topologicalKrullDim_eq_one := X.topologicalKrullDim_eq_one

/-- A regular projective curve over `k`, as a regular proper curve over `k`. -/
abbrev toRegularProperCurveCat (X : RegularProjectiveCurveCat k) : RegularProperCurveCat k :=
  .of X.toScheme

/-- The morphisms of regular projective curves over `k` are the dominant `k`-morphisms: those of
the underlying regular proper curves. -/
instance : Category (RegularProjectiveCurveCat k) :=
  inferInstanceAs (Category (InducedCategory _ (toRegularProperCurveCat (k := k))))

@[simp]
lemma id_hom (X : RegularProjectiveCurveCat k) :
    InducedCategory.Hom.hom (𝟙 X) = 𝟙 X.toRegularProperCurveCat :=
  (rfl)

@[simp]
lemma comp_hom {X Y Z : RegularProjectiveCurveCat k} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom = f.hom ≫ g.hom :=
  (rfl)

@[ext]
lemma hom_ext {X Y : RegularProjectiveCurveCat k} {f g : X ⟶ Y} (h : f.hom = g.hom) : f = g :=
  InducedCategory.hom_ext h

/-- The regular projective curve given by a regular proper curve. -/
abbrev ofRegularProperCurveCat (X : RegularProperCurveCat k) : RegularProjectiveCurveCat k where
  toScheme := X.toScheme
  isProjectiveOver := X.toScheme.isProjectiveOver_of_isCurveOver
  topologicalKrullDim_eq_one := Scheme.IsCurveOver.topologicalKrullDim_eq_one k

variable (k) in
/-- The functor from regular projective curves to regular proper curves forgetting projectivity.
It is the identity on underlying schemes and on morphisms. -/
abbrev toRegularProperCurveCatFunctor : RegularProjectiveCurveCat k ⥤ RegularProperCurveCat k :=
  inducedFunctor _

variable (k) in
/-- The functor from regular proper curves to regular projective curves: every regular proper
curve is projective. It is the identity on underlying schemes and on morphisms. -/
abbrev ofRegularProperCurveCatFunctor : RegularProperCurveCat k ⥤ RegularProjectiveCurveCat k where
  obj := ofRegularProperCurveCat
  map f := InducedCategory.homMk f

variable (k) in
/-- Regular projective curves over `k` are the regular proper curves over `k`: forgetting
projectivity is an equivalence of categories, with inverse `ofRegularProperCurveCatFunctor`. -/
def equivRegularProperCurveCat : RegularProjectiveCurveCat k ≌ RegularProperCurveCat k where
  functor := toRegularProperCurveCatFunctor k
  inverse := ofRegularProperCurveCatFunctor k
  unitIso := NatIso.ofComponents fun _ ↦ Iso.refl _
  counitIso := NatIso.ofComponents fun _ ↦ Iso.refl _

@[simp]
lemma equivRegularProperCurveCat_functor :
    (equivRegularProperCurveCat k).functor = toRegularProperCurveCatFunctor k :=
  (rfl)

@[simp]
lemma equivRegularProperCurveCat_inverse :
    (equivRegularProperCurveCat k).inverse = ofRegularProperCurveCatFunctor k :=
  (rfl)

instance : (toRegularProperCurveCatFunctor k).IsEquivalence :=
  (equivRegularProperCurveCat k).isEquivalence_functor

instance : (ofRegularProperCurveCatFunctor k).IsEquivalence :=
  (equivRegularProperCurveCat k).isEquivalence_inverse

variable (k) in
/-- **The anti-equivalence between regular projective curves and algebraic function fields** over
a field `k`: the functor sending a regular projective curve `X` to its function field `k(X)` and a
dominant `k`-morphism to the pullback of rational functions along it is an equivalence
`RegularProjectiveCurveCat k ≌ (FunctionFieldCat k)ᵒᵖ`. Its inverse sends a function field `F` to
its two-chart model, the normalization of the projective line in `F`. -/
noncomputable def equivFunctionFieldCat : RegularProjectiveCurveCat k ≌ (FunctionFieldCat k)ᵒᵖ :=
  (equivRegularProperCurveCat k).trans (RegularProperCurveCat.equivFunctionFieldCat k)

/-- The anti-equivalence sends a regular projective curve to its function field and a dominant
`k`-morphism to the pullback of rational functions along it. -/
@[simp]
lemma equivFunctionFieldCat_functor :
    (equivFunctionFieldCat k).functor =
      toRegularProperCurveCatFunctor k ⋙ RegularProperCurveCat.functionFieldFunctor k :=
  (rfl)

/-- The inverse of the anti-equivalence sends a function field to its two-chart model, as a
regular projective curve. -/
@[simp]
lemma equivFunctionFieldCat_inverse :
    (equivFunctionFieldCat k).inverse =
      RegularProperCurveCat.twoChartModelFunctor k ⋙ ofRegularProperCurveCatFunctor k :=
  (rfl)

end RegularProjectiveCurveCat

end TauCeti.AlgebraicGeometry

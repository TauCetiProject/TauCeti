/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.Basic
public import TauCeti.AlgebraicGeometry.Scheme.CodimensionOnePoint
public import TauCeti.FieldTheory.FunctionField.Category

/-!
# The category of regular proper curves and the function-field functor

A regular proper curve over a field `k` is a curve over `k` (an integral scheme, proper and of
dimension one over `k`) whose local rings at its codimension-one points, its closed points, are
discrete valuation rings. With the dominant `k`-morphisms as morphisms these curves form a
category, the geometric side of the anti-equivalence with algebraic function fields of one
variable over `k`.

Taking function fields is a contravariant functor from this category to the category
`TauCeti.FunctionFieldCat k` of algebraic function fields over `k`: a curve goes to its function
field `k(X)`, an algebraic function field by `AlgebraicGeometry.Scheme.IsCurveOver.isFunctionField`,
and a dominant `k`-morphism `f : X ⟶ Y` to the pullback of rational functions
`f^* : k(Y) → k(X)`, a `k`-algebra homomorphism by
`AlgebraicGeometry.Scheme.Hom.functionFieldAlgHom`.

## Main definitions

* `TauCeti.AlgebraicGeometry.RegularProperCurveCat k`: the category of regular proper curves
  over `k` with dominant `k`-morphisms.
* `TauCeti.AlgebraicGeometry.RegularProperCurveCat.isoMk`: an isomorphism of regular proper curves
  from an isomorphism of schemes over `k`.
* `TauCeti.AlgebraicGeometry.RegularProperCurveCat.functionFieldFunctor`: the contravariant
  function-field functor `X ↦ k(X)`.

## References

* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Section I.6.
* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Appendix B.
-/

@[expose] public section

open CategoryTheory Opposite _root_.AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry

/-- The category of regular proper curves over a field `k`: curves over `k` (integral schemes,
proper and of dimension one over `k`) whose local rings at the codimension-one points are discrete
valuation rings, with the dominant `k`-morphisms as morphisms. -/
structure RegularProperCurveCat (k : Type u) [Field k] where
  /-- The underlying scheme. -/
  toScheme : Scheme.{u}
  [over : toScheme.Over (Spec (.of k))]
  [isCurveOver : toScheme.IsCurveOver k]
  [isDiscreteValuationRing_stalk :
    ∀ y : CodimensionOnePoint toScheme, IsDiscreteValuationRing (toScheme.presheaf.stalk y.1)]

attribute [instance] RegularProperCurveCat.over RegularProperCurveCat.isCurveOver
  RegularProperCurveCat.isDiscreteValuationRing_stalk

namespace RegularProperCurveCat

variable {k : Type u} [Field k]

/-- The object of `RegularProperCurveCat k` given by a curve over `k` whose local rings at the
codimension-one points are discrete valuation rings. -/
abbrev of (X : Scheme.{u}) [X.Over (Spec (.of k))] [X.IsCurveOver k]
    [∀ y : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk y.1)] :
    RegularProperCurveCat k :=
  ⟨X⟩

/-- The type of morphisms in `RegularProperCurveCat k`: the dominant `k`-morphisms of schemes. -/
@[ext]
structure Hom (X Y : RegularProperCurveCat k) where
  /-- The underlying morphism of schemes. -/
  hom : X.toScheme ⟶ Y.toScheme
  [isOver : hom.IsOver (Spec (.of k))]
  [isDominant : IsDominant hom]

attribute [instance] Hom.isOver Hom.isDominant

instance : Category (RegularProperCurveCat k) where
  Hom := Hom
  id X := ⟨𝟙 X.toScheme⟩
  comp f g := ⟨f.hom ≫ g.hom⟩

@[simp]
lemma id_hom (X : RegularProperCurveCat k) : Hom.hom (𝟙 X) = 𝟙 X.toScheme :=
  rfl

@[simp]
lemma comp_hom {X Y Z : RegularProperCurveCat k} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Hom.hom (f ≫ g) = f.hom ≫ g.hom :=
  rfl

@[ext]
lemma hom_ext {X Y : RegularProperCurveCat k} {f g : X ⟶ Y} (h : f.hom = g.hom) : f = g :=
  Hom.ext h

/-- An isomorphism of regular proper curves over `k` from an isomorphism of the underlying schemes
over `k`. -/
def isoMk {X Y : RegularProperCurveCat k} (e : X.toScheme ≅ Y.toScheme)
    [e.hom.IsOver (Spec (.of k))] : X ≅ Y where
  hom := ⟨e.hom⟩
  inv := ⟨e.inv⟩
  hom_inv_id := by ext1; exact e.hom_inv_id
  inv_hom_id := by ext1; exact e.inv_hom_id

@[simp]
lemma isoMk_hom_hom {X Y : RegularProperCurveCat k} (e : X.toScheme ≅ Y.toScheme)
    [e.hom.IsOver (Spec (.of k))] : (isoMk e).hom.hom = e.hom :=
  (rfl)

@[simp]
lemma isoMk_inv_hom {X Y : RegularProperCurveCat k} (e : X.toScheme ≅ Y.toScheme)
    [e.hom.IsOver (Spec (.of k))] : (isoMk e).inv.hom = e.inv :=
  (rfl)

variable (k) in
/-- **The function-field functor**: the contravariant functor from regular proper curves over `k`
to algebraic function fields over `k` sending a curve `X` to its function field `k(X)` and a
dominant `k`-morphism `f : X ⟶ Y` to the pullback of rational functions `f^* : k(Y) → k(X)`. -/
@[simps obj]
noncomputable def functionFieldFunctor : RegularProperCurveCat k ⥤ (FunctionFieldCat k)ᵒᵖ where
  obj X := op (.of X.toScheme.functionField Scheme.IsCurveOver.isFunctionField)
  map f := (FunctionFieldCat.ofHom (f.hom.functionFieldAlgHom k)).op
  map_id X := by
    refine Quiver.Hom.unop_inj (FunctionFieldCat.hom_ext ?_)
    simp
  map_comp f g := by
    refine Quiver.Hom.unop_inj (FunctionFieldCat.hom_ext ?_)
    simp

/-- The function-field functor sends a dominant `k`-morphism to the pullback of rational
functions along it. -/
@[simp]
lemma functionFieldFunctor_map_unop_hom {X Y : RegularProperCurveCat k} (f : X ⟶ Y) :
    ((functionFieldFunctor k).map f).unop.hom = f.hom.functionFieldAlgHom k :=
  rfl

end RegularProperCurveCat

end TauCeti.AlgebraicGeometry

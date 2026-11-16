/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.GlobalSections
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.Hom.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.Integral
public import TauCeti.AlgebraicGeometry.Rigidity.GroupScheme

/-!
# Pointed morphisms of elliptic curves are group homomorphisms

Let `E` and `E'` be elliptic curves over an arbitrary base scheme `S`. Katz and Mazur's Theorem
2.5.1 states that every morphism of schemes `f : E ⟶ E'` over `S` carrying the zero section of `E`
to the zero section of `E'` is a homomorphism of group schemes. Consequently, homomorphisms
`E.toCommGrp ⟶ E'.toCommGrp` in `CommGrp (Over S)` are in canonical bijection with pointed scheme
morphisms `(E, 0) ⟶ (E', 0)` over `S` (`EllipticCurveGeom.homEquivPointed`), and pointed scheme
isomorphisms over `S` lift uniquely to isomorphisms of commutative group schemes
(`EllipticCurveGeom.isoEquivPointed`).

This file deduces Katz–Mazur 2.5.1 from the relative rigidity lemma
(`TauCeti.AlgebraicGeometry.isMonHom_of_one_hom_of_flat`): the structure morphism
`E.structureMap : E.carrier ⟶ S` is smooth (hence flat), proper, and geometrically integral
(`EllipticCurveGeom.geometricallyIntegral_structureMap`), and satisfies
`E.structureMap_* 𝒪_E = 𝒪_S` (`EllipticCurveGeom.isIso_structureMap_app`). The result holds more
generally for any morphism from `E` to a separated, locally of finite type group scheme over `S`
(`EllipticCurveGeom.isMonHom_of_zero_comp`).

Applying the same rigidity theorem to the identity of `E` shows that the group law
`EllipticCurveGeom.grpObj` (and even its underlying monoid law) is the *unique* group-scheme
structure on `E` over `S` having `E.zero` as identity section
(`EllipticCurveGeom.grpObj_eq_of_one_left_eq` and `EllipticCurveGeom.monObj_eq_of_one_left_eq`):
both addition and negation are intrinsically determined by `(E.carrier, E.structureMap, E.zero)`,
independent of the Bosma–Lenstra Weierstrass charts used to construct them.

## Main definitions

* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.homOfMapsZero`: constructs a homomorphism
  `E.toCommGrp ⟶ E'.toCommGrp` from a pointed morphism of schemes over `S`.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.homEquivPointed`: the equivalence between
  `E.toCommGrp ⟶ E'.toCommGrp` and pointed morphisms `E.carrier ⟶ E'.carrier` over `S`.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.isoOfPointedIso` and
  `TauCeti.AlgebraicGeometry.EllipticCurveGeom.isoEquivPointed`: pointed scheme isomorphisms over
  `S` are equivalent to group-scheme isomorphisms `E.toCommGrp ≅ E'.toCommGrp`.

## Main results

* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.isMonHom_of_zero_comp`: any morphism from `E` to a
  separated locally finite type group scheme `B` over `S` preserving the identity section satisfies
  `IsMonHom`.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.isMonHom_homMk_of_mapsZero`,
  `TauCeti.AlgebraicGeometry.EllipticCurveGeom.existsUnique_hom_of_mapsZero`: **Katz–Mazur 2.5.1**
  — every pointed morphism `E ⟶ E'` over `S` lifts uniquely to a homomorphism of elliptic curves.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.addition_comp_of_mapsZero`,
  `TauCeti.AlgebraicGeometry.EllipticCurveGeom.neg_comp_of_mapsZero`, and
  `TauCeti.AlgebraicGeometry.EllipticCurveGeom.mulBy_left_comp_of_mapsZero`: pointed morphisms
  commute with addition, negation, and multiplication by `n` on underlying schemes.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.monObj_eq_of_one_left_eq` and
  `TauCeti.AlgebraicGeometry.EllipticCurveGeom.grpObj_eq_of_one_left_eq`: uniqueness of the monoid
  and group structures on `E` with identity section `E.zero`.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, Theorem 2.5.1.
* D. Mumford, J. Fogarty, F. Kirwan, *Geometric Invariant Theory*, Proposition 6.1.
-/

public section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

open scoped CategoryTheory.MonObj

universe u

namespace TauCeti.AlgebraicGeometry

namespace EllipticCurveGeom

variable {S : Scheme.{u}} {E E' E'' : EllipticCurveGeom S}

private instance (E : EllipticCurveGeom S) : Smooth (Over.mk E.structureMap).hom :=
  SmoothOfRelativeDimension.smooth 1 E.structureMap

private instance (E : EllipticCurveGeom S) : IsProper (Over.mk E.structureMap).hom :=
  inferInstanceAs (IsProper E.structureMap)

private instance (E : EllipticCurveGeom S) :
    GeometricallyIntegral (Over.mk E.structureMap).hom :=
  inferInstanceAs (GeometricallyIntegral E.structureMap)

/-! ### Katz–Mazur 2.5.1: pointed morphisms are homomorphisms -/

/-- **Pointed morphisms from an elliptic curve to a group scheme are homomorphisms.** Let `E` be an
elliptic curve over `S` and `B` a separated, locally of finite type group scheme over `S`. Any
morphism `f : Over.mk E.structureMap ⟶ B` over `S` sending `E.zero` to the identity section of `B`
is a homomorphism of group schemes. -/
theorem isMonHom_of_zero_comp {B : Over S} [GrpObj B]
    [IsSeparated B.hom] [LocallyOfFiniteType B.hom]
    (f : Over.mk E.structureMap ⟶ B) (h0 : E.zero ≫ f.left = η[B].left) :
    IsMonHom f :=
  isMonHom_of_one_hom_of_flat (fun V ↦ E.isIso_structureMap_app V.1) f
    (Over.OverMorphism.ext (by simpa only [Over.comp_left, one_left] using h0))

/-- **Katz–Mazur Theorem 2.5.1.** Every morphism of schemes `f : E.carrier ⟶ E'.carrier` over `S`
carrying the zero section of `E` to the zero section of `E'` is a homomorphism of group schemes over
`S`. -/
theorem isMonHom_homMk_of_mapsZero (f : E.carrier ⟶ E'.carrier)
    (hf : f ≫ E'.structureMap = E.structureMap) (h0 : E.zero ≫ f = E'.zero) :
    IsMonHom (Over.homMk f hf : Over.mk E.structureMap ⟶ Over.mk E'.structureMap) :=
  isMonHom_of_zero_comp (E := E) (B := Over.mk E'.structureMap) (Over.homMk f hf) h0

/-- **Katz–Mazur 2.5.1, packaged as a homomorphism in `CommGrp (Over S)`.** Given a morphism of
schemes `f : E.carrier ⟶ E'.carrier` over `S` carrying `E.zero` to `E'.zero`, this is the
corresponding homomorphism `E.toCommGrp ⟶ E'.toCommGrp` of elliptic curves over `S`. -/
noncomputable def homOfMapsZero (f : E.carrier ⟶ E'.carrier)
    (hf : f ≫ E'.structureMap = E.structureMap) (h0 : E.zero ≫ f = E'.zero) :
    E.toCommGrp ⟶ E'.toCommGrp :=
  commGrpHomOfOneHom (A := E.toCommGrp) (B := E'.toCommGrp)
    (fun V ↦ E.isIso_structureMap_app V.1) (Over.homMk f hf)
    (Over.OverMorphism.ext (by simp [h0]))

@[simp]
theorem homOfMapsZero_hom_hom_hom (f : E.carrier ⟶ E'.carrier)
    (hf : f ≫ E'.structureMap = E.structureMap) (h0 : E.zero ≫ f = E'.zero) :
    (homOfMapsZero f hf h0).hom.hom.hom = Over.homMk f hf :=
  commGrpHomOfOneHom_hom_hom_hom _ _ _

theorem homOfMapsZero_hom_hom_hom_left (f : E.carrier ⟶ E'.carrier)
    (hf : f ≫ E'.structureMap = E.structureMap) (h0 : E.zero ≫ f = E'.zero) :
    (homOfMapsZero f hf h0).hom.hom.hom.left = f := by
  simp [homOfMapsZero_hom_hom_hom]

/-- **Katz–Mazur 2.5.1, unique lifting.** Every pointed morphism of schemes `f : E ⟶ E'` over `S`
underlies a unique homomorphism `E.toCommGrp ⟶ E'.toCommGrp` of elliptic curves over `S`. -/
theorem existsUnique_hom_of_mapsZero (f : E.carrier ⟶ E'.carrier)
    (hf : f ≫ E'.structureMap = E.structureMap) (h0 : E.zero ≫ f = E'.zero) :
    ∃! F : E.toCommGrp ⟶ E'.toCommGrp, F.hom.hom.hom.left = f :=
  ⟨homOfMapsZero f hf h0, homOfMapsZero_hom_hom_hom_left f hf h0,
    fun _ hF ↦ hom_ext_left _ (hF.trans (homOfMapsZero_hom_hom_hom_left f hf h0).symm)⟩

/-- A pointed morphism of elliptic curves over `S` intertwines their addition morphisms. -/
@[reassoc]
theorem addition_comp_of_mapsZero {f : E.carrier ⟶ E'.carrier}
    (hf : f ≫ E'.structureMap = E.structureMap) (h0 : E.zero ≫ f = E'.zero) :
    E.addition ≫ f =
      pullback.map E.structureMap E.structureMap E'.structureMap E'.structureMap f f (𝟙 S)
        (by simp [hf]) (by simp [hf]) ≫ E'.addition := by
  simpa only [homOfMapsZero_hom_hom_hom_left] using
    addition_comp_hom_hom_hom_left (homOfMapsZero f hf h0)

/-- A pointed morphism of elliptic curves over `S` intertwines their negation morphisms. -/
@[reassoc]
theorem neg_comp_of_mapsZero {f : E.carrier ⟶ E'.carrier}
    (hf : f ≫ E'.structureMap = E.structureMap) (h0 : E.zero ≫ f = E'.zero) :
    E.neg ≫ f = f ≫ E'.neg := by
  simpa only [homOfMapsZero_hom_hom_hom_left] using
    neg_comp_hom_hom_hom_left (homOfMapsZero f hf h0)

/-- A pointed morphism of elliptic curves over `S` commutes with multiplication by any integer
`n`. -/
@[reassoc]
theorem mulBy_left_comp_of_mapsZero {f : E.carrier ⟶ E'.carrier}
    (hf : f ≫ E'.structureMap = E.structureMap) (h0 : E.zero ≫ f = E'.zero) (n : ℤ) :
    (E.mulBy n).left ≫ f = f ≫ (E'.mulBy n).left := by
  simpa only [homOfMapsZero_hom_hom_hom_left] using
    mulBy_left_comp_hom_hom_hom_left (homOfMapsZero f hf h0) n

@[simp]
theorem homOfMapsZero_eta (F : E.toCommGrp ⟶ E'.toCommGrp) :
    homOfMapsZero F.hom.hom.hom.left (hom_hom_hom_left_comp_structureMap F)
        (zero_comp_hom_hom_hom_left F) = F :=
  hom_ext_left _ (homOfMapsZero_hom_hom_hom_left _ _ _)

@[simp]
theorem homOfMapsZero_id (E : EllipticCurveGeom S) :
    homOfMapsZero (𝟙 E.carrier) (Category.id_comp E.structureMap) (Category.comp_id E.zero) =
      𝟙 E.toCommGrp :=
  hom_ext_left _ (by simp)

@[simp]
theorem homOfMapsZero_comp {f : E.carrier ⟶ E'.carrier}
    (hf : f ≫ E'.structureMap = E.structureMap) (hf0 : E.zero ≫ f = E'.zero)
    {g : E'.carrier ⟶ E''.carrier}
    (hg : g ≫ E''.structureMap = E'.structureMap) (hg0 : E'.zero ≫ g = E''.zero) :
    homOfMapsZero (f ≫ g) (by rw [Category.assoc, hg, hf]) (by rw [← Category.assoc, hf0, hg0]) =
      homOfMapsZero f hf hf0 ≫ homOfMapsZero g hg hg0 :=
  hom_ext_left _ (by simp)

@[simp]
theorem homOfMapsZero_zero (E E' : EllipticCurveGeom S) :
    homOfMapsZero (E.structureMap ≫ E'.zero) (by simp) (by simp) =
      (0 : E.toCommGrp ⟶ E'.toCommGrp) :=
  hom_ext_left _ ((homOfMapsZero_hom_hom_hom_left _ _ _).trans (zero_hom_hom_hom_left E).symm)

@[simp]
theorem homOfMapsZero_neg (E : EllipticCurveGeom S) :
    homOfMapsZero E.neg E.neg_structureMap E.zero_neg = -𝟙 E.toCommGrp :=
  hom_ext_left _ <| by rw [homOfMapsZero_hom_hom_hom_left, neg_hom_hom_hom_left]; simp

/-- **Homomorphisms of elliptic curves over `S` are equivalent to pointed morphisms of schemes over
`S` (Katz–Mazur 2.5.1).** -/
noncomputable def homEquivPointed (E E' : EllipticCurveGeom S) :
    (E.toCommGrp ⟶ E'.toCommGrp) ≃
      {f : E.carrier ⟶ E'.carrier //
        f ≫ E'.structureMap = E.structureMap ∧ E.zero ≫ f = E'.zero} :=
  (commGrpHomEquivPointed E.toCommGrp E'.toCommGrp (fun V ↦ E.isIso_structureMap_app V.1)).trans
    { toFun g := ⟨g.1.left, Over.w g.1,
        by simpa only [Over.comp_left, one_left] using congrArg Over.Hom.left g.2⟩
      invFun f := ⟨Over.homMk f.1 f.2.1, Over.OverMorphism.ext (by simp [f.2.2])⟩
      left_inv _ := Subtype.ext (Over.OverMorphism.ext rfl)
      right_inv _ := Subtype.ext rfl }

@[simp]
theorem coe_homEquivPointed_apply (F : E.toCommGrp ⟶ E'.toCommGrp) :
    (homEquivPointed E E' F : E.carrier ⟶ E'.carrier) = F.hom.hom.hom.left := by
  simp [homEquivPointed,
    coe_commGrpHomEquivPointed_apply (A := E.toCommGrp) (B := E'.toCommGrp)]

@[simp]
theorem homEquivPointed_symm_apply
    (f : {f : E.carrier ⟶ E'.carrier //
      f ≫ E'.structureMap = E.structureMap ∧ E.zero ≫ f = E'.zero}) :
    (homEquivPointed E E').symm f = homOfMapsZero f.1 f.2.1 f.2.2 :=
  hom_ext_left _ (by
    simp [homEquivPointed,
      commGrpHomEquivPointed_symm_apply (A := E.toCommGrp) (B := E'.toCommGrp)])

theorem homEquivPointed_symm_apply_hom_hom_hom_left
    (f : {f : E.carrier ⟶ E'.carrier //
      f ≫ E'.structureMap = E.structureMap ∧ E.zero ≫ f = E'.zero}) :
    ((homEquivPointed E E').symm f).hom.hom.hom.left = f.1 := by
  rw [homEquivPointed_symm_apply, homOfMapsZero_hom_hom_hom_left]

/-! ### Pointed isomorphisms -/

/-- A pointed isomorphism of schemes `e : E.carrier ≅ E'.carrier` over `S` lifts to an isomorphism
`E.toCommGrp ≅ E'.toCommGrp` of commutative group schemes over `S`. -/
noncomputable def isoOfPointedIso (e : E.carrier ≅ E'.carrier)
    (he : e.hom ≫ E'.structureMap = E.structureMap) (h0 : E.zero ≫ e.hom = E'.zero) :
    E.toCommGrp ≅ E'.toCommGrp where
  hom := homOfMapsZero e.hom he h0
  inv := homOfMapsZero e.inv
    (by rw [Iso.inv_comp_eq, he])
    (by rw [← h0, Category.assoc, e.hom_inv_id, Category.comp_id])
  hom_inv_id := hom_ext_left _ <| by simp
  inv_hom_id := hom_ext_left _ <| by simp

@[simp]
theorem isoOfPointedIso_hom (e : E.carrier ≅ E'.carrier)
    (he : e.hom ≫ E'.structureMap = E.structureMap) (h0 : E.zero ≫ e.hom = E'.zero) :
    (isoOfPointedIso e he h0).hom = homOfMapsZero e.hom he h0 := by
  simp [isoOfPointedIso]

@[simp]
theorem isoOfPointedIso_inv (e : E.carrier ≅ E'.carrier)
    (he : e.hom ≫ E'.structureMap = E.structureMap) (h0 : E.zero ≫ e.hom = E'.zero) :
    (isoOfPointedIso e he h0).inv =
      homOfMapsZero e.inv (by rw [Iso.inv_comp_eq, he])
        (by rw [← h0, Category.assoc, e.hom_inv_id, Category.comp_id]) := by
  simp [isoOfPointedIso]

theorem isoOfPointedIso_hom_hom_hom_hom_left (e : E.carrier ≅ E'.carrier)
    (he : e.hom ≫ E'.structureMap = E.structureMap) (h0 : E.zero ≫ e.hom = E'.zero) :
    (isoOfPointedIso e he h0).hom.hom.hom.hom.left = e.hom :=
  homOfMapsZero_hom_hom_hom_left e.hom he h0

theorem isoOfPointedIso_inv_hom_hom_hom_left (e : E.carrier ≅ E'.carrier)
    (he : e.hom ≫ E'.structureMap = E.structureMap) (h0 : E.zero ≫ e.hom = E'.zero) :
    (isoOfPointedIso e he h0).inv.hom.hom.hom.left = e.inv := by
  simp

/-- **Isomorphisms of elliptic curves as commutative group schemes over `S` are equivalent to
pointed scheme isomorphisms over `S`.** -/
noncomputable def isoEquivPointed (E E' : EllipticCurveGeom S) :
    (E.toCommGrp ≅ E'.toCommGrp) ≃
      {e : E.carrier ≅ E'.carrier //
        e.hom ≫ E'.structureMap = E.structureMap ∧ E.zero ≫ e.hom = E'.zero} where
  toFun e :=
    ⟨(CommGrp.forget₂Grp (Over S) ⋙ Grp.forget₂Mon (Over S) ⋙ Mon.forget (Over S) ⋙
        Over.forget S).mapIso e,
      hom_hom_hom_left_comp_structureMap e.hom,
      zero_comp_hom_hom_hom_left e.hom⟩
  invFun e := isoOfPointedIso e.1 e.2.1 e.2.2
  left_inv _ := by ext1; exact hom_ext_left _ (isoOfPointedIso_hom_hom_hom_hom_left _ _ _)
  right_inv _ := by ext1; exact Iso.ext (isoOfPointedIso_hom_hom_hom_hom_left _ _ _)

@[simp]
theorem coe_isoEquivPointed_apply_hom (e : E.toCommGrp ≅ E'.toCommGrp) :
    (isoEquivPointed E E' e : E.carrier ≅ E'.carrier).hom = e.hom.hom.hom.hom.left := by
  simp [isoEquivPointed]
  rfl

@[simp]
theorem coe_isoEquivPointed_apply_inv (e : E.toCommGrp ≅ E'.toCommGrp) :
    (isoEquivPointed E E' e : E.carrier ≅ E'.carrier).inv = e.inv.hom.hom.hom.left := by
  simp [isoEquivPointed]
  rfl

@[simp]
theorem isoEquivPointed_symm_apply
    (e : {e : E.carrier ≅ E'.carrier //
      e.hom ≫ E'.structureMap = E.structureMap ∧ E.zero ≫ e.hom = E'.zero}) :
    (isoEquivPointed E E').symm e = isoOfPointedIso e.1 e.2.1 e.2.2 := by
  simp [isoEquivPointed]

/-! ### Uniqueness of the group law -/

section Uniqueness

variable (E : EllipticCurveGeom S)

/-- **Uniqueness of the monoid law on an elliptic curve over a scheme.** Any monoid-object structure
on `Over.mk E.structureMap` whose identity morphism has underlying scheme morphism `E.zero` equals
`E.grpObj.toMonObj`; in particular its multiplication morphism is `E.addition`. -/
theorem monObj_eq_of_one_left_eq (m : MonObj (Over.mk E.structureMap))
    (h0 : m.one.left = E.zero) :
    m = E.grpObj.toMonObj :=
  monObj_eq_of_one_eq_of_flat (fun V ↦ E.isIso_structureMap_app V.1) m E.grpObj
    (Over.OverMorphism.ext h0)

/-- **Uniqueness of the group law on an elliptic curve over a scheme.** Any group-object structure
on `Over.mk E.structureMap` whose identity morphism has underlying scheme morphism `E.zero` equals
`E.grpObj`; thus both addition and negation are uniquely determined by
`(E.carrier, E.structureMap, E.zero)`, independent of any Weierstrass chart. -/
theorem grpObj_eq_of_one_left_eq (g : GrpObj (Over.mk E.structureMap))
    (h0 : g.one.left = E.zero) :
    g = E.grpObj :=
  GrpObj.ext _ _ (E.monObj_eq_of_one_left_eq g.toMonObj h0)

end Uniqueness

end EllipticCurveGeom

end TauCeti.AlgebraicGeometry

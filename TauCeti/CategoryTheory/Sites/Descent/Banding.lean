/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Bicategory.LocallyDiscrete
public import Mathlib.CategoryTheory.Bicategory.Modification.Pseudo
public import Mathlib.CategoryTheory.Sites.Over
public import TauCeti.CategoryTheory.Bicategory.Functor.LocallyDiscrete
public import TauCeti.CategoryTheory.Bicategory.NaturalTransformation.Pseudo

/-!
# Abelian bandings of gerbes and band-preserving transformations

Let `F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat` be a pseudofunctor, `J` a Grothendieck topology on `C`
and `A` a sheaf of abelian groups on `(C, J)`. An `A`-banding of `F` identifies, for every
object `U` of `C` and every object `x` of the fibre over `U`, the group `A(U)` with the
automorphism group `Aut x`, compatibly with pullback along every arrow `V ⟶ U` and with
conjugation along every isomorphism `x ≅ y` (Olsson, Definition 31.1 and Remark 31.2). A gerbe
with an `A`-banding is an `A`-gerbe, the kind of gerbe classified by `H²(A)`. The conjugation
condition forces every automorphism group `Aut x` to be commutative.

A strong transformation `η : F ⟶ G` between banded pseudofunctors is band-preserving when its
component functors carry the band automorphism of each coefficient to the band automorphism of
the same coefficient. Band-preserving transformations are closed under identities and
composition. More generally, for a morphism `φ : A ⟶ B` of sheaves of abelian groups, a strong
transformation from an `A`-banded to a `B`-banded pseudofunctor is compatible with `φ` when its
component functors carry the band automorphism of each coefficient `a` to the band automorphism of
`φ a`; compatibility with the identity is band preservation, and compatibility is closed under
composition and invariant under isomorphisms of transformations.

Both notions restrict to the slice site `(Over U, J.over U)`: an `A`-banding of `F` restricts to an
`A.over U`-banding of the restriction `F.over U`, and the restriction of a band-preserving
transformation, its whiskering by `(Over.forget U).op`, preserves the restricted bands; likewise
the restriction of a transformation compatible with `φ` is compatible with the restriction of `φ`.

## Main declarations

* `CategoryTheory.Pseudofunctor.AbelianBanding`: an `A`-banding of `F`.
* `CategoryTheory.Pseudofunctor.AbelianBanding.mulEquiv_hom_comp`: the band automorphisms
  commute with every isomorphism of the fibre.
* `CategoryTheory.Pseudofunctor.AbelianBanding.aut_mul_comm`: the automorphism groups of a banded
  pseudofunctor are commutative.
* `CategoryTheory.Pseudofunctor.AbelianBanding.over`: the restriction of an `A`-banding to the
  slice site over `U`, an `A.over U`-banding of `F.over U`.
* `CategoryTheory.Pseudofunctor.BandPreserving`: the property of a strong transformation of
  preserving the bands.
* `CategoryTheory.Pseudofunctor.BandPreserving.over`: the restriction of a band-preserving
  transformation to the slice site over `U` preserves the restricted bands.
* `CategoryTheory.Pseudofunctor.BandCompatible`: the property of a strong transformation of
  carrying the band of the source to the band of the target along a morphism `φ : A ⟶ B` of
  sheaves of abelian groups, with `bandCompatible_iff_map_mulEquiv_hom`, `bandCompatible_id_iff`,
  `BandCompatible.comp`, `bandCompatible_iff_of_iso` and `BandCompatible.over`.

## References

* [Martin Olsson, *Stacks* (lecture notes, notes by A. Geraschenko et al.)](https://stacky.net/files/written/Stacks/Stacks.pdf),
  Definition 31.1, Remark 31.2 and Theorem 31.7
* [Michael Groechenig, Dimitri Wyss and Paul Ziegler, *Mirror symmetry for moduli of Higgs
  bundles via p-adic integration*](https://doi.org/10.1007/s00222-020-00957-8),
  Definition 2.6 and Section 2.2.1
-/

public section

universe w v u v' u'

open CategoryTheory Opposite Bicategory

namespace CategoryTheory.Pseudofunctor

variable {C : Type u} [Category.{v} C]

/-- An `A`-banding of a pseudofunctor `F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat`, for a sheaf of abelian
groups `A` on `(C, J)`: group isomorphisms `A(U) ≃* Aut x` for every object `U` of `C` and every
object `x` of the fibre of `F` over `U`, compatible with pullback along every arrow `V ⟶ U` and
with conjugation along every isomorphism `x ≅ y` (Olsson, Definition 31.1 and Remark 31.2). The
additive group `A(U)` enters through `Multiplicative`. -/
structure AbelianBanding (F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}) (J : GrothendieckTopology C)
    (A : Sheaf J AddCommGrpCat.{w}) where
  /-- The identification of the coefficients over `U` with the automorphisms of `x`. -/
  mulEquiv (U : C) (x : F.obj (.mk (op U))) : Multiplicative (A.obj.obj (op U)) ≃* Aut x
  /-- Pullback along `f : V ⟶ U` sends the band automorphism of `a` to the band automorphism of
  the restriction of `a` to `V`. -/
  mapAut_mulEquiv {U V : C} (f : V ⟶ U) (x : F.obj (.mk (op U)))
      (a : Multiplicative (A.obj.obj (op U))) :
    (F.map f.op.toLoc).toFunctor.mapAut x (mulEquiv U x a) =
      mulEquiv V ((F.map f.op.toLoc).toFunctor.obj x) (.ofAdd (A.obj.map f.op a.toAdd))
  /-- Conjugation along an isomorphism `x ≅ y` sends the band automorphism of `a` at `x` to the
  band automorphism of `a` at `y`. -/
  autMulEquivOfIso_mulEquiv {U : C} {x y : F.obj (.mk (op U))} (e : x ≅ y)
      (a : Multiplicative (A.obj.obj (op U))) :
    Aut.autMulEquivOfIso e (mulEquiv U x a) = mulEquiv U y a

attribute [simp] AbelianBanding.mapAut_mulEquiv AbelianBanding.autMulEquivOfIso_mulEquiv

namespace AbelianBanding

variable {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}} {J : GrothendieckTopology C}
  {A : Sheaf J AddCommGrpCat.{w}} (b : F.AbelianBanding J A)

/-- Two bandings are equal if their identifications of coefficients with automorphisms agree. -/
@[ext]
lemma ext {b b' : F.AbelianBanding J A}
    (h : ∀ (U : C) (x : F.obj (.mk (op U))) (a : Multiplicative (A.obj.obj (op U))),
      b.mulEquiv U x a = b'.mulEquiv U x a) : b = b' := by
  obtain ⟨m, _, _⟩ := b
  obtain ⟨m', _, _⟩ := b'
  obtain rfl : m = m' := by
    funext U x
    exact MulEquiv.ext (h U x)
  rfl

/-- Pullback along `f : V ⟶ U` sends the band automorphism of `a` to the band automorphism of the
restriction of `a`, stated on the underlying morphisms. -/
@[simp, reassoc]
lemma map_mulEquiv_hom {U V : C} (f : V ⟶ U) (x : F.obj (.mk (op U)))
    (a : Multiplicative (A.obj.obj (op U))) :
    (F.map f.op.toLoc).toFunctor.map (b.mulEquiv U x a).asIso.hom =
      (b.mulEquiv V ((F.map f.op.toLoc).toFunctor.obj x)
        (.ofAdd (A.obj.map f.op a.toAdd))).asIso.hom :=
  congr($(b.mapAut_mulEquiv f x a).asIso.hom)

/-- The band automorphisms commute with every isomorphism of the fibre: for `e : x ≅ y`, the
band automorphism of `a` at `x` followed by `e` is `e` followed by the band automorphism of `a`
at `y`. -/
@[reassoc]
lemma mulEquiv_hom_comp {U : C} {x y : F.obj (.mk (op U))} (e : x ≅ y)
    (a : Multiplicative (A.obj.obj (op U))) :
    (b.mulEquiv U x a).asIso.hom ≫ e.hom = e.hom ≫ (b.mulEquiv U y a).asIso.hom := by
  have h := congr($(b.autMulEquivOfIso_mulEquiv e a).asIso.hom)
  simp only [Aut.autMulEquivOfIso_apply_asIso, Iso.trans_hom, Iso.symm_hom] at h
  rw [← h]
  simp

/-- Conjugation by an isomorphism `e : x ≅ y` sends the band automorphism of `a` at `x` to the
band automorphism of `a` at `y`, stated on the underlying morphisms. -/
@[reassoc (attr := simp)]
lemma inv_comp_mulEquiv_hom_comp {U : C} {x y : F.obj (.mk (op U))} (e : x ≅ y)
    (a : Multiplicative (A.obj.obj (op U))) :
    e.inv ≫ (b.mulEquiv U x a).asIso.hom ≫ e.hom = (b.mulEquiv U y a).asIso.hom := by
  simp [b.mulEquiv_hom_comp]

include b in
/-- The automorphism groups of a pseudofunctor with an abelian banding are commutative
(Olsson, Remark 31.2). -/
theorem aut_mul_comm {U : C} {x : F.obj (.mk (op U))} (g h : Aut x) : g * h = h * g := by
  obtain ⟨a, rfl⟩ := (b.mulEquiv U x).surjective g
  ext
  simp [b.mulEquiv_hom_comp h.asIso a]

/-- The restriction of an `A`-banding of `F` to the slice site `(Over U, J.over U)`: the
`A.over U`-banding of the restriction `F.over U` that identifies, for `X : Over U` and an object
`x` of the fibre of `F` over `X.left`, the coefficients `A(X.left)` with `Aut x` through `b`. -/
def over (U : C) : (F.over U).AbelianBanding (J.over U) (A.over U) where
  mulEquiv X x := b.mulEquiv X.left x
  mapAut_mulEquiv g x a := b.mapAut_mulEquiv g.left x a
  autMulEquivOfIso_mulEquiv e a := b.autMulEquivOfIso_mulEquiv e a

/-- The restricted banding `b.over U` at `X : Over U` is the banding `b` at `X.left`. -/
@[simp]
lemma over_mulEquiv (U : C) (X : Over U) (x : (F.over U).obj (.mk (op X))) :
    (b.over U).mulEquiv X x = b.mulEquiv X.left x :=
  (rfl)

end AbelianBanding

/-- A strong transformation `η : F ⟶ G` between pseudofunctors with `A`-bandings `bF` and `bG`
preserves the bands if each component functor `η_U` sends the band automorphism of a
coefficient `a` at `x` to the band automorphism of `a` at `η_U x` (Olsson, Definition 31.1). -/
class BandPreserving {F G : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}} {J : GrothendieckTopology C}
    {A : Sheaf J AddCommGrpCat.{w}} (bF : F.AbelianBanding J A) (bG : G.AbelianBanding J A)
    (η : StrongTrans F G) : Prop where
  /-- The component functors carry the band of `F` to the band of `G`. -/
  mapAut_mulEquiv (U : C) (x : F.obj (.mk (op U))) (a : Multiplicative (A.obj.obj (op U))) :
    (η.app (.mk (op U))).toFunctor.mapAut x (bF.mulEquiv U x a) =
      bG.mulEquiv U ((η.app (.mk (op U))).toFunctor.obj x) a

namespace BandPreserving

variable {F G H : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}} {J : GrothendieckTopology C}
  {A : Sheaf J AddCommGrpCat.{w}} {bF : F.AbelianBanding J A} {bG : G.AbelianBanding J A}
  {bH : H.AbelianBanding J A}

variable (bG) in
/-- A band-preserving transformation carries band automorphisms to band automorphisms, stated on
the underlying morphisms. -/
@[reassoc]
lemma map_mulEquiv_hom (η : StrongTrans F G) [BandPreserving bF bG η] (U : C)
    (x : F.obj (.mk (op U))) (a : Multiplicative (A.obj.obj (op U))) :
    (η.app (.mk (op U))).toFunctor.map (bF.mulEquiv U x a).asIso.hom =
      (bG.mulEquiv U ((η.app (.mk (op U))).toFunctor.obj x) a).asIso.hom :=
  congr($(BandPreserving.mapAut_mulEquiv (bG := bG) (η := η) U x a).asIso.hom)

variable (bF) in
/-- The identity transformation preserves every banding. -/
instance id : BandPreserving bF bF (StrongTrans.id F) where
  mapAut_mulEquiv U x a := by
    ext
    rfl

open scoped Pseudofunctor.StrongTrans in
/-- The restriction of a band-preserving transformation `η` to the slice site over `U`, the
whiskering of `η` by `(Over.forget U).op`, preserves the restricted bands. -/
instance over (η : F ⟶ G) [BandPreserving bF bG η] (U : C) :
    BandPreserving (bF.over U) (bG.over U) ((Over.forget U).op.toPseudofunctor.whiskerLeft η) where
  mapAut_mulEquiv X x a := BandPreserving.mapAut_mulEquiv (bG := bG) (η := η) X.left x a

end BandPreserving

/-- A strong transformation `η : F ⟶ G` from a pseudofunctor with an `A`-banding `bF` to one with
a `B`-banding `bG` is compatible with a morphism `φ : A ⟶ B` of sheaves of abelian groups if each
component functor `η_U` sends the band automorphism of a coefficient `a` at `x` to the band
automorphism of `φ a` at `η_U x`; these are the morphisms along which the band is changed in
Olsson, Theorem 31.7. For `φ` the identity this is `BandPreserving` (`bandCompatible_id_iff`). -/
class BandCompatible {F G : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}} {J : GrothendieckTopology C}
    {A B : Sheaf J AddCommGrpCat.{w}} (φ : A ⟶ B) (bF : F.AbelianBanding J A)
    (bG : G.AbelianBanding J B) (η : StrongTrans F G) : Prop where
  /-- The component functors carry the band of `F` to the band of `G` along `φ`. -/
  mapAut_mulEquiv (U : C) (x : F.obj (.mk (op U))) (a : Multiplicative (A.obj.obj (op U))) :
    (η.app (.mk (op U))).toFunctor.mapAut x (bF.mulEquiv U x a) =
      bG.mulEquiv U ((η.app (.mk (op U))).toFunctor.obj x) (.ofAdd (φ.hom.app (op U) a.toAdd))

section BandCompatible

variable {F G H : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}} {J : GrothendieckTopology C}
  {A B D : Sheaf J AddCommGrpCat.{w}} {bF : F.AbelianBanding J A}

variable (bG : G.AbelianBanding J B) in
/-- A transformation compatible with `φ` carries band automorphisms to band automorphisms along
`φ`, stated on the underlying morphisms. -/
@[reassoc]
lemma BandCompatible.map_mulEquiv_hom (φ : A ⟶ B) (η : StrongTrans F G)
    [BandCompatible φ bF bG η] (U : C) (x : F.obj (.mk (op U)))
    (a : Multiplicative (A.obj.obj (op U))) :
    (η.app (.mk (op U))).toFunctor.map (bF.mulEquiv U x a).asIso.hom =
      (bG.mulEquiv U ((η.app (.mk (op U))).toFunctor.obj x)
        (.ofAdd (φ.hom.app (op U) a.toAdd))).asIso.hom :=
  congr($(BandCompatible.mapAut_mulEquiv (bG := bG) (φ := φ) (η := η) U x a).asIso.hom)

variable (bG : G.AbelianBanding J B) in
/-- A transformation is compatible with `φ` if and only if its component functors carry the
underlying morphisms of band automorphisms to the underlying morphisms of the band automorphisms
of their images along `φ`. -/
lemma bandCompatible_iff_map_mulEquiv_hom (φ : A ⟶ B) (η : StrongTrans F G) :
    BandCompatible φ bF bG η ↔ ∀ (U : C) (x : F.obj (.mk (op U)))
      (a : Multiplicative (A.obj.obj (op U))),
      (η.app (.mk (op U))).toFunctor.map (bF.mulEquiv U x a).asIso.hom =
        (bG.mulEquiv U ((η.app (.mk (op U))).toFunctor.obj x)
          (.ofAdd (φ.hom.app (op U) a.toAdd))).asIso.hom :=
  ⟨fun _ ↦ BandCompatible.map_mulEquiv_hom bG φ η, fun h ↦ ⟨fun U x a ↦ Aut.ext <| Iso.ext <| by
    rw [Functor.mapAut_apply_asIso]
    exact h U x a⟩⟩

/-- A transformation is compatible with the identity of `A` if and only if it preserves the
bands. -/
@[simp]
lemma bandCompatible_id_iff {bG : G.AbelianBanding J A} (η : StrongTrans F G) :
    BandCompatible (𝟙 A) bF bG η ↔ BandPreserving bF bG η :=
  ⟨fun h ↦ ⟨h.mapAut_mulEquiv⟩, fun h ↦ ⟨h.mapAut_mulEquiv⟩⟩

/-- A band-preserving transformation is compatible with the identity of the band. -/
instance BandPreserving.bandCompatible {bG : G.AbelianBanding J A} (η : StrongTrans F G)
    [BandPreserving bF bG η] : BandCompatible (𝟙 A) bF bG η :=
  (bandCompatible_id_iff η).2 ‹_›

open scoped Pseudofunctor.StrongTrans in
variable (bG : G.AbelianBanding J B) {bH : H.AbelianBanding J D} in
/-- The composite of a transformation compatible with `φ` and one compatible with `ψ` is
compatible with `φ ≫ ψ`. -/
lemma BandCompatible.comp (φ : A ⟶ B) (ψ : B ⟶ D) (η : F ⟶ G) (θ : G ⟶ H)
    [BandCompatible φ bF bG η] [BandCompatible ψ bG bH θ] :
    BandCompatible (φ ≫ ψ) bF bH (η ≫ θ) where
  mapAut_mulEquiv U x a := by
    ext
    rw [Functor.mapAut_apply_asIso]
    simp only [StrongTrans.comp_app, Cat.Hom.comp_toFunctor, Functor.mapIso_hom, Functor.comp_map]
    rw [BandCompatible.map_mulEquiv_hom bG φ η, BandCompatible.map_mulEquiv_hom bH ψ θ]
    -- The two sides differ only by `Functor.comp_obj` and by the evaluation of `φ ≫ ψ` on
    -- sections, both of which hold by definition.
    rfl

open scoped Pseudofunctor.StrongTrans in
variable {bG : G.AbelianBanding J A} {bH : H.AbelianBanding J A} in
variable (bG) in
/-- The composite of band-preserving transformations is band-preserving. -/
lemma BandPreserving.comp (η : F ⟶ G) (θ : G ⟶ H) [BandPreserving bF bG η]
    [BandPreserving bG bH θ] : BandPreserving bF bH (η ≫ θ) :=
  (bandCompatible_id_iff _).1 (by simpa using BandCompatible.comp bG (𝟙 A) (𝟙 A) η θ)

open scoped Pseudofunctor.StrongTrans in
variable {bG : G.AbelianBanding J B} in
/-- Compatibility with `φ` transfers along an isomorphism of strong transformations: the
components of an isomorphism `η ≅ θ` conjugate the images of band automorphisms under `η` to those
under `θ`, and band automorphisms are invariant under conjugation. -/
lemma BandCompatible.of_iso {φ : A ⟶ B} {η θ : F ⟶ G} (e : η ≅ θ) [BandCompatible φ bF bG η] :
    BandCompatible φ bF bG θ where
  mapAut_mulEquiv U x a := by
    ext
    rw [Functor.mapAut_apply_asIso, Functor.mapIso_hom]
    let e' := (Cat.Hom.toNatIso (StrongTrans.isoApp e (.mk (op U)))).app x
    have he : e'.hom = (e.hom.as.app (.mk (op U))).toNatTrans.app x :=
      congrArg (fun m ↦ m.toNatTrans.app x) (StrongTrans.isoApp_hom e (.mk (op U)))
    have h := (e.hom.as.app (.mk (op U))).toNatTrans.naturality (bF.mulEquiv U x a).asIso.hom
    rw [← he, BandCompatible.map_mulEquiv_hom bG φ η, ← e'.inv_comp_eq] at h
    rw [← h, bG.inv_comp_mulEquiv_hom_comp]

open scoped Pseudofunctor.StrongTrans in
variable {bG : G.AbelianBanding J B} in
/-- Isomorphic strong transformations are compatible with the same morphisms of bands. -/
lemma bandCompatible_iff_of_iso {φ : A ⟶ B} {η θ : F ⟶ G} (e : η ≅ θ) :
    BandCompatible φ bF bG η ↔ BandCompatible φ bF bG θ :=
  ⟨fun _ ↦ .of_iso e, fun _ ↦ .of_iso e.symm⟩

open scoped Pseudofunctor.StrongTrans in
variable {bG : G.AbelianBanding J B} in
/-- The restriction of a transformation `η` compatible with `φ` to the slice site over `U`, the
whiskering of `η` by `(Over.forget U).op`, is compatible with the restriction of `φ`. -/
instance BandCompatible.over (φ : A ⟶ B) (η : F ⟶ G) [BandCompatible φ bF bG η] (U : C) :
    BandCompatible ((J.overPullback _ U).map φ) (bF.over U) (bG.over U)
      ((Over.forget U).op.toPseudofunctor.whiskerLeft η) where
  mapAut_mulEquiv X x a := BandCompatible.mapAut_mulEquiv (bG := bG) (φ := φ) (η := η) X.left x a

end BandCompatible

end CategoryTheory.Pseudofunctor

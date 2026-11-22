/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Bicategory.LocallyDiscrete
public import Mathlib.CategoryTheory.Bicategory.Modification.Pseudo
public import Mathlib.CategoryTheory.Sites.Sheaf

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
composition.

## Main declarations

* `CategoryTheory.Pseudofunctor.AbelianBanding`: an `A`-banding of `F`.
* `CategoryTheory.Pseudofunctor.AbelianBanding.mulEquiv_hom_comp`: the band automorphisms
  commute with every isomorphism of the fibre.
* `CategoryTheory.Pseudofunctor.AbelianBanding.aut_mul_comm`: the automorphism groups of a banded
  pseudofunctor are commutative.
* `CategoryTheory.Pseudofunctor.BandPreserving`: the property of a strong transformation of
  preserving the bands.

## References

* [Martin Olsson, *Stacks* (lecture notes, notes by A. Geraschenko et al.)](https://stacky.net/files/written/Stacks/Stacks.pdf),
  Definition 31.1 and Remark 31.2
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
variable (bG) in
/-- The composite of band-preserving transformations is band-preserving. -/
lemma comp (η : F ⟶ G) (θ : G ⟶ H) [BandPreserving bF bG η] [BandPreserving bG bH θ] :
    BandPreserving bF bH (η ≫ θ) where
  mapAut_mulEquiv U x a := by
    ext
    rw [Functor.mapAut_apply_asIso]
    simp only [StrongTrans.comp_app, Cat.Hom.comp_toFunctor, Functor.mapIso_hom, Functor.comp_map]
    rw [map_mulEquiv_hom bG η, map_mulEquiv_hom bH θ]
    -- The two sides differ only by `Functor.comp_obj`, which holds by definition.
    rfl

end BandPreserving

end CategoryTheory.Pseudofunctor

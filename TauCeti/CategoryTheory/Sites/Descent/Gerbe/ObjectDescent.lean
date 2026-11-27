/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Sites.Descent.DescentData
public import TauCeti.CategoryTheory.Sites.Descent.StrongTrans

/-!
# Lifted overlaps for morphisms of gerbes

Let `η : F ⟶ G` be a strong transformation of pseudofunctors `LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat`, with
component functors `η_U` and naturality isomorphisms `c_f(x) : η_V (F(f) x) ≅ G(f) (η_U x)`
(`StrongTrans.naturalityObjIso`). This file continues the proof that a band-preserving morphism
of gerbes is an equivalence on every fibre (Olsson, Lemma 31.3), by descending objects.

For `z` over `U`, the local-image sieve of `z` (`StrongTrans.localImageSieve`) is covering when `η`
is locally essentially surjective (`StrongTrans.localImageSieve_mem`), in particular when `F` and
`G` are gerbes (`StrongTrans.isLocallyEssSurj_of_isGerbe`). So `z` has local preimages
`e_i : η_(X_i)(x_i) ≅ G(f_i) z` on a covering family `f_i : X_i ⟶ U`. These are isomorphisms to
the objects of the canonical descent datum `(G.toDescentData f).obj z` of `z`, whose target
overlaps `η_Y (F(a) x_i) ≅ η_Y (F(b) x_j)` on common refinements `q = a ≫ f_i = b ≫ f_j` are
`StrongTrans.targetOverlapIso`. When the components of `η` are fully faithful (as they are for a
band-preserving morphism of gerbes, `BandedMorphism.fullyFaithful`), this datum lifts along the
local preimages (`StrongTrans.liftDescentData`). Its gluing isomorphisms `F(a) x_i ≅ F(b) x_j`
(`GerbeMorphismDescent.liftedOverlapIso`) are the unique lifts of the target overlaps
(`mapIso_liftedOverlapIso`), with the same identity and cocycle laws (`liftedOverlapIso_self`,
`liftedOverlapIso_hom_comp_hom`).

## Main declarations

In the namespace `CategoryTheory.Pseudofunctor.GerbeMorphismDescent`:

* `liftedOverlapIso`, `liftedOverlapIso_def`, `mapPullHom_liftedOverlapIso_hom`,
  `map_liftedOverlapIso_hom`, `map_liftedOverlapIso_inv`, `mapIso_liftedOverlapIso`,
  `liftedOverlapIso_self`, `liftedOverlapIso_hom_comp_hom`, `liftedOverlapIso_trans`,
  `liftedOverlapIso_inv`, `liftedOverlapIso_symm`.

## References

* [Martin Olsson, *Stacks* (lecture notes, notes by A. Geraschenko et al.)](https://stacky.net/files/written/Stacks/Stacks.pdf),
  Definition 31.1 and Lemma 31.3
-/

public section

universe v u v' u'

open CategoryTheory Opposite Bicategory

namespace CategoryTheory.Pseudofunctor.GerbeMorphismDescent

variable {C : Type u} [Category.{v} C] {F G : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}}
  (η : StrongTrans F G) {U : C} {ι : Type*} {X : ι → C} (f : ∀ i, X i ⟶ U)
  {x : ∀ i, F.obj (.mk (op (X i)))} (z : G.obj (.mk (op U)))
  (e : ∀ i, (η.app (.mk (op (X i)))).toFunctor.obj (x i) ≅ ((G.toDescentData f).obj z).obj i)
  (hη : ∀ V : C, (η.app (.mk (op V))).toFunctor.FullyFaithful)

/-- The **lifted overlap** `F(a) x_i ≅ F(b) x_j`: the gluing isomorphism of the lift
(`StrongTrans.liftDescentData`) of the canonical descent datum of `z` along local preimages
`e_i : η_(X_i)(x_i) ≅ G(f_i) z`, through fully faithful components of `η` (for a band-preserving
morphism of gerbes, `BandedMorphism.fullyFaithful`). Its image under `η_Y` is the target overlap
(`map_liftedOverlapIso_hom`). -/
noncomputable def liftedOverlapIso {Y : C} (q : Y ⟶ U) {i j : ι} (a : Y ⟶ X i) (b : Y ⟶ X j)
    (ha : a ≫ f i = q) (hb : b ≫ f j = q) :
    (F.map a.op.toLoc).toFunctor.obj (x i) ≅ (F.map b.op.toLoc).toFunctor.obj (x j) :=
  (η.liftDescentData f (hη) ((G.toDescentData f).obj z) e).iso
    q a b ha hb

/-- The lifted overlap is the gluing isomorphism of `StrongTrans.liftDescentData` of the canonical
descent datum of `z` along the local preimages, so the laws of that datum apply to it. -/
theorem liftedOverlapIso_def {Y : C} (q : Y ⟶ U) {i j : ι} (a : Y ⟶ X i) (b : Y ⟶ X j)
    (ha : a ≫ f i = q) (hb : b ≫ f j = q) :
    liftedOverlapIso η f z e hη q a b ha hb =
      (η.liftDescentData f hη ((G.toDescentData f).obj z) e).iso q a b ha hb :=
  (rfl)

/-- Conjugated by the naturality isomorphisms of `η` (`StrongTrans.mapPullHom`), the lifted overlap
is the gluing morphism of the canonical descent datum of `z` transported along the local
preimages: the instance of `StrongTrans.mapPullHom_liftDescentData_hom` for this datum. -/
theorem mapPullHom_liftedOverlapIso_hom {Y : C} (q : Y ⟶ U) {i j : ι} (a : Y ⟶ X i)
    (b : Y ⟶ X j) (ha : a ≫ f i = q) (hb : b ≫ f j = q) :
    η.mapPullHom (liftedOverlapIso η f z e hη q a b ha hb).hom =
      η.liftDescentDataHom f ((G.toDescentData f).obj z) e q a b ha hb :=
  η.mapPullHom_liftDescentData_hom f (hη) _ e q a b ha hb

/-- The image under `η_Y` of the forward arrow of the lifted overlap is that of the target
overlap. -/
@[simp, reassoc]
theorem map_liftedOverlapIso_hom {Y : C} (q : Y ⟶ U) {i j : ι} (a : Y ⟶ X i) (b : Y ⟶ X j)
    (ha : a ≫ f i = q) (hb : b ≫ f j = q) :
    (η.app (.mk (op Y))).toFunctor.map (liftedOverlapIso η f z e hη q a b ha hb).hom =
      (η.targetOverlapIso f ((G.toDescentData f).obj z) e q a b ha hb).hom :=
  η.map_liftDescentData_hom f hη _ e q a b ha hb

/-- The image of the lifted overlap under `η_Y` is the target overlap. -/
@[simp]
theorem mapIso_liftedOverlapIso {Y : C} (q : Y ⟶ U) {i j : ι} (a : Y ⟶ X i) (b : Y ⟶ X j)
    (ha : a ≫ f i = q) (hb : b ≫ f j = q) :
    (η.app (.mk (op Y))).toFunctor.mapIso (liftedOverlapIso η f z e hη q a b ha hb) =
      η.targetOverlapIso f ((G.toDescentData f).obj z) e q a b ha hb :=
  η.mapIso_liftDescentData_iso f hη _ e q a b ha hb

/-- The image under `η_Y` of the inverse arrow of the lifted overlap is that of the target
overlap. In simp normal form both sides are forward arrows of the swapped overlaps
(`liftedOverlapIso_inv`, `targetOverlapIso_inv`). -/
@[reassoc]
theorem map_liftedOverlapIso_inv {Y : C} (q : Y ⟶ U) {i j : ι} (a : Y ⟶ X i) (b : Y ⟶ X j)
    (ha : a ≫ f i = q) (hb : b ≫ f j = q) :
    (η.app (.mk (op Y))).toFunctor.map (liftedOverlapIso η f z e hη q a b ha hb).inv =
      (η.targetOverlapIso f ((G.toDescentData f).obj z) e q a b ha hb).inv :=
  congrArg Iso.inv (mapIso_liftedOverlapIso η f z e hη q a b ha hb)

/-- On the diagonal, the lifted overlap is the identity. -/
@[simp]
theorem liftedOverlapIso_self {Y : C} (q : Y ⟶ U) {i : ι} (a : Y ⟶ X i) (ha : a ≫ f i = q) :
    liftedOverlapIso η f z e hη q a a ha ha = Iso.refl _ :=
  (η.liftDescentData f (hη) _ e).iso_self q a ha

/-- **The cocycle condition** for the forward arrows of lifted overlaps on a common refinement. -/
@[reassoc (attr := simp)]
theorem liftedOverlapIso_hom_comp_hom {Y : C} (q : Y ⟶ U) {i j k : ι} (a : Y ⟶ X i)
    (b : Y ⟶ X j) (c : Y ⟶ X k) (ha : a ≫ f i = q) (hb : b ≫ f j = q) (hc : c ≫ f k = q) :
    (liftedOverlapIso η f z e hη q a b ha hb).hom ≫
        (liftedOverlapIso η f z e hη q b c hb hc).hom =
      (liftedOverlapIso η f z e hη q a c ha hc).hom :=
  (η.liftDescentData f (hη) _ e).hom_comp q a b c ha hb hc

/-- **The cocycle condition** for lifted overlaps on a common refinement. -/
@[simp]
theorem liftedOverlapIso_trans {Y : C} (q : Y ⟶ U) {i j k : ι} (a : Y ⟶ X i) (b : Y ⟶ X j)
    (c : Y ⟶ X k) (ha : a ≫ f i = q) (hb : b ≫ f j = q) (hc : c ≫ f k = q) :
    liftedOverlapIso η f z e hη q a b ha hb ≪≫ liftedOverlapIso η f z e hη q b c hb hc =
      liftedOverlapIso η f z e hη q a c ha hc :=
  (η.liftDescentData f (hη) _ e).iso_trans q a b c ha hb hc

/-- The inverse arrow of the lifted overlap is the forward arrow of the lifted overlap with the
two local preimages interchanged. -/
@[simp]
theorem liftedOverlapIso_inv {Y : C} (q : Y ⟶ U) {i j : ι} (a : Y ⟶ X i) (b : Y ⟶ X j)
    (ha : a ≫ f i = q) (hb : b ≫ f j = q) :
    (liftedOverlapIso η f z e hη q a b ha hb).inv =
      (liftedOverlapIso η f z e hη q b a hb ha).hom :=
  (η.liftDescentData f (hη) _ e).iso_inv q a b ha hb

/-- Interchanging the two local preimages inverts the lifted overlap. -/
@[simp]
theorem liftedOverlapIso_symm {Y : C} (q : Y ⟶ U) {i j : ι} (a : Y ⟶ X i) (b : Y ⟶ X j)
    (ha : a ≫ f i = q) (hb : b ≫ f j = q) :
    (liftedOverlapIso η f z e hη q a b ha hb).symm =
      liftedOverlapIso η f z e hη q b a hb ha :=
  (η.liftDescentData f (hη) _ e).iso_symm q a b ha hb

end CategoryTheory.Pseudofunctor.GerbeMorphismDescent

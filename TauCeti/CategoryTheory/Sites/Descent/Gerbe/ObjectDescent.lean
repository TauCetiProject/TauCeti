/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Sites.Descent.DescentData
public import TauCeti.CategoryTheory.Sites.Descent.RelativeGerbe

/-!
# Local preimages and lifted overlaps for morphisms of gerbes

Let `η : F ⟶ G` be a strong transformation of pseudofunctors `LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat`, with
component functors `η_U` and naturality isomorphisms `c_f(x) : η_V (F(f) x) ≅ G(f) (η_U x)`
(`StrongTrans.naturalityObjIso`). This file begins the proof that a band-preserving morphism of
gerbes is an equivalence on every fibre (Olsson, Lemma 31.3), by descending objects.

For `z` over `U`, the **local-image sieve** `L_z` consists of the arrows `f : V ⟶ U` such that
`G(f) z` is isomorphic to `η_V x` for some `x` over `V`
(`GerbeMorphismDescent.localImageSieve`). It is covering when `η` is locally essentially surjective
(`GerbeMorphismDescent.localImageSieve_mem`, from `StrongTrans.IsLocallyEssSurj`), in particular
when `F` and `G` are gerbes (`StrongTrans.isLocallyEssSurj_of_isGerbe`): `F` has objects locally,
and their images become isomorphic to the restrictions of `z` locally. No band is needed for this.

Given a descent datum `D` for `G` on a family `f_i : X_i ⟶ U` and local preimages
`e_i : η_(X_i)(x_i) ≅ D_i`, the **target overlap** on a common refinement
`q = a ≫ f_i = b ≫ f_j` is the isomorphism `η_Y (F(a) x_i) ≅ η_Y (F(b) x_j)` through `c_a(x_i)`,
`G(a)(e_i)`, the gluing isomorphism of `D`, `G(b)(e_j)⁻¹` and `c_b(x_j)⁻¹`
(`GerbeMorphismDescent.targetOverlapIso`). It is the identity on the diagonal and satisfies the
cocycle condition (`targetOverlapIso_self`, `targetOverlapIso_hom_comp_hom`). When the
components of `η` are fully faithful, it is the image under `η_Y` of the gluing isomorphism of the
lift of `D` along the local preimages (`mapIso_liftDescentData_iso`). For the descent
step, `D` is the canonical descent datum `(G.toDescentData f).obj z` of `z`, whose object over
`X_i` is `G(f_i) z`. When the components of `η` are fully faithful (as they are for a
band-preserving morphism of gerbes, `BandedMorphism.fullyFaithful`), this datum lifts along the
local preimages (`StrongTrans.liftDescentData`). Its gluing isomorphisms `F(a) x_i ≅ F(b) x_j`
(`GerbeMorphismDescent.liftedOverlapIso`) are the unique lifts of the target overlaps
(`mapIso_liftedOverlapIso`), with the same identity and cocycle laws (`liftedOverlapIso_self`,
`liftedOverlapIso_hom_comp_hom`).

## Main declarations

In the namespace `CategoryTheory.Pseudofunctor.GerbeMorphismDescent`:

* `restrictImageIso`, `restrictImageIso_hom`, `localImageSieve`, `mem_localImageSieve_iff`,
  `id_mem_localImageSieve_iff`, `localImageSieve_mem`.
* `targetOverlapIso`, `targetOverlapIso_hom`, `targetOverlapIso_self`,
  `targetOverlapIso_hom_comp_hom`, `targetOverlapIso_trans`, `targetOverlapIso_inv`,
  `targetOverlapIso_symm`, `map_liftDescentData_hom`, `mapIso_liftDescentData_iso`.
* `liftedOverlapIso`, `mapPullHom_liftedOverlapIso_hom`, `map_liftedOverlapIso_hom`,
  `map_liftedOverlapIso_inv`, `mapIso_liftedOverlapIso`, `liftedOverlapIso_self`,
  `liftedOverlapIso_hom_comp_hom`, `liftedOverlapIso_trans`, `liftedOverlapIso_inv`,
  `liftedOverlapIso_symm`.

## References

* [Martin Olsson, *Stacks* (lecture notes, notes by A. Geraschenko et al.)](https://stacky.net/files/written/Stacks/Stacks.pdf),
  Definition 31.1 and Lemma 31.3
-/

public section

universe v u v' u'

open CategoryTheory Opposite Bicategory

namespace CategoryTheory.Pseudofunctor.GerbeMorphismDescent

variable {C : Type u} [Category.{v} C] {F G : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}}
  (η : StrongTrans F G)

/-! ### The local-image sieve -/

/-- An isomorphism `e : η_V x ≅ G(f) z` restricts along `g : W ⟶ V` to an isomorphism
`η_W (F(g) x) ≅ G(g ≫ f) z`, through `c_g(x)` and the composition isomorphism of `G`. -/
noncomputable def restrictImageIso {U V W : C} {z : G.obj (.mk (op U))} {f : V ⟶ U}
    {x : F.obj (.mk (op V))}
    (e : (η.app (.mk (op V))).toFunctor.obj x ≅ (G.map f.op.toLoc).toFunctor.obj z)
    (g : W ⟶ V) :
    (η.app (.mk (op W))).toFunctor.obj ((F.map g.op.toLoc).toFunctor.obj x) ≅
      (G.map (g ≫ f).op.toLoc).toFunctor.obj z :=
  η.naturalityObjIso g.op.toLoc x ≪≫ (G.map g.op.toLoc).toFunctor.mapIso e ≪≫
    ((Cat.Hom.toNatIso (G.mapComp' f.op.toLoc g.op.toLoc (g ≫ f).op.toLoc)).app z).symm

/-- The forward arrow of `restrictImageIso`, as the composite of its three factors. -/
theorem restrictImageIso_hom {U V W : C} {z : G.obj (.mk (op U))} {f : V ⟶ U}
    {x : F.obj (.mk (op V))}
    (e : (η.app (.mk (op V))).toFunctor.obj x ≅ (G.map f.op.toLoc).toFunctor.obj z)
    (g : W ⟶ V) :
    (restrictImageIso η e g).hom =
      (η.naturalityObjIso g.op.toLoc x).hom ≫ (G.map g.op.toLoc).toFunctor.map e.hom ≫
        (G.mapComp' f.op.toLoc g.op.toLoc (g ≫ f).op.toLoc).inv.toNatTrans.app z := by
  simp [restrictImageIso]

/-- The **local-image sieve** of `z` over `U`: the arrows `f : V ⟶ U` such that `G(f) z` is
isomorphic to the image `η_V x` of some object `x` over `V`. -/
def localImageSieve {U : C} (z : G.obj (.mk (op U))) : Sieve U where
  arrows V f := ∃ x : F.obj (.mk (op V)),
    Nonempty ((η.app (.mk (op V))).toFunctor.obj x ≅ (G.map f.op.toLoc).toFunctor.obj z)
  downward_closed := fun ⟨_, ⟨e⟩⟩ g ↦ ⟨_, ⟨restrictImageIso η e g⟩⟩

theorem mem_localImageSieve_iff {U V : C} (z : G.obj (.mk (op U))) (f : V ⟶ U) :
    localImageSieve η z f ↔ ∃ x : F.obj (.mk (op V)),
      Nonempty ((η.app (.mk (op V))).toFunctor.obj x ≅ (G.map f.op.toLoc).toFunctor.obj z) :=
  Iff.rfl

/-- The identity of `U` lies in the local-image sieve of `z` exactly when `z` is isomorphic to
`η_U y` for some `y` over `U`. -/
theorem id_mem_localImageSieve_iff {U : C} (z : G.obj (.mk (op U))) :
    localImageSieve η z (𝟙 U) ↔
      ∃ y : F.obj (.mk (op U)), Nonempty ((η.app (.mk (op U))).toFunctor.obj y ≅ z) := by
  let d := (Cat.Hom.toNatIso (G.mapId' (𝟙 U).op.toLoc (by simp))).app z
  exact ⟨fun ⟨y, ⟨e⟩⟩ ↦ ⟨y, ⟨e ≪≫ d⟩⟩, fun ⟨y, ⟨e⟩⟩ ↦ ⟨y, ⟨e ≪≫ d.symm⟩⟩⟩

/-- **The local-image sieve is covering** when `η` is locally essentially surjective
(`StrongTrans.IsLocallyEssSurj`), in particular when `F` and `G` are gerbes
(`StrongTrans.isLocallyEssSurj_of_isGerbe`). No band is used. -/
theorem localImageSieve_mem (J : GrothendieckTopology C) [η.IsLocallyEssSurj J] {U : C}
    (z : G.obj (.mk (op U))) : localImageSieve η z ∈ J U := by
  obtain ⟨R, hR, h⟩ := StrongTrans.IsLocallyEssSurj.exists_covering_lift (η := η) (J := J) z
  exact J.superset_covering (fun _ f hf ↦ h f hf) hR

/-! ### Target overlaps -/

variable {U : C} {ι : Type*} {X : ι → C} (f : ∀ i, X i ⟶ U) {x : ∀ i, F.obj (.mk (op (X i)))}

section TargetOverlap

variable (D : G.DescentData f) (e : ∀ i, (η.app (.mk (op (X i)))).toFunctor.obj (x i) ≅ D.obj i)

/-- The **target overlap** of local preimages `e_i : η_(X_i)(x_i) ≅ D_i` of a descent datum `D`
on a common refinement `q = a ≫ f_i = b ≫ f_j`: the isomorphism
`η_Y (F(a) x_i) ≅ η_Y (F(b) x_j)` through `c_a(x_i)`, `G(a)(e_i)`, the gluing isomorphism
`G(a) D_i ≅ G(b) D_j` of `D` (`DescentData.iso`), `G(b)(e_j)⁻¹` and `c_b(x_j)⁻¹`. -/
noncomputable def targetOverlapIso {Y : C} (q : Y ⟶ U) {i j : ι} (a : Y ⟶ X i) (b : Y ⟶ X j)
    (ha : a ≫ f i = q) (hb : b ≫ f j = q) :
    (η.app (.mk (op Y))).toFunctor.obj ((F.map a.op.toLoc).toFunctor.obj (x i)) ≅
      (η.app (.mk (op Y))).toFunctor.obj ((F.map b.op.toLoc).toFunctor.obj (x j)) :=
  η.naturalityObjIso a.op.toLoc (x i) ≪≫ (G.map a.op.toLoc).toFunctor.mapIso (e i) ≪≫
    D.iso q a b ha hb ≪≫
      ((G.map b.op.toLoc).toFunctor.mapIso (e j)).symm ≪≫ (η.naturalityObjIso b.op.toLoc (x j)).symm

/-- The forward arrow of the target overlap, as the composite of its five factors. -/
theorem targetOverlapIso_hom {Y : C} (q : Y ⟶ U) {i j : ι} (a : Y ⟶ X i) (b : Y ⟶ X j)
    (ha : a ≫ f i = q) (hb : b ≫ f j = q) :
    (targetOverlapIso η f D e q a b ha hb).hom =
      (η.naturalityObjIso a.op.toLoc (x i)).hom ≫ (G.map a.op.toLoc).toFunctor.map (e i).hom ≫
        D.hom q a b ha hb ≫
          (G.map b.op.toLoc).toFunctor.map (e j).inv ≫ (η.naturalityObjIso b.op.toLoc (x j)).inv :=
  (rfl)

/-- On the diagonal, the target overlap is the identity. -/
@[simp]
theorem targetOverlapIso_self {Y : C} (q : Y ⟶ U) {i : ι} (a : Y ⟶ X i) (ha : a ≫ f i = q) :
    targetOverlapIso η f D e q a a ha ha = Iso.refl _ := by
  ext
  simp [targetOverlapIso_hom, D.hom_self q a ha]

/-- **The cocycle condition** for the forward arrows of target overlaps on a common
refinement. -/
@[reassoc (attr := simp)]
theorem targetOverlapIso_hom_comp_hom {Y : C} (q : Y ⟶ U) {i j k : ι} (a : Y ⟶ X i)
    (b : Y ⟶ X j) (c : Y ⟶ X k) (ha : a ≫ f i = q) (hb : b ≫ f j = q) (hc : c ≫ f k = q) :
    (targetOverlapIso η f D e q a b ha hb).hom ≫ (targetOverlapIso η f D e q b c hb hc).hom =
      (targetOverlapIso η f D e q a c ha hc).hom := by
  simp [targetOverlapIso_hom]

/-- **The cocycle condition** for target overlaps on a common refinement. -/
@[simp]
theorem targetOverlapIso_trans {Y : C} (q : Y ⟶ U) {i j k : ι} (a : Y ⟶ X i) (b : Y ⟶ X j)
    (c : Y ⟶ X k) (ha : a ≫ f i = q) (hb : b ≫ f j = q) (hc : c ≫ f k = q) :
    targetOverlapIso η f D e q a b ha hb ≪≫ targetOverlapIso η f D e q b c hb hc =
      targetOverlapIso η f D e q a c ha hc :=
  Iso.ext (targetOverlapIso_hom_comp_hom η f D e q a b c ha hb hc)

/-- The inverse arrow of the target overlap is the forward arrow of the target overlap with the
two local preimages interchanged. -/
@[simp]
theorem targetOverlapIso_inv {Y : C} (q : Y ⟶ U) {i j : ι} (a : Y ⟶ X i) (b : Y ⟶ X j)
    (ha : a ≫ f i = q) (hb : b ≫ f j = q) :
    (targetOverlapIso η f D e q a b ha hb).inv = (targetOverlapIso η f D e q b a hb ha).hom :=
  Iso.inv_ext (by simp)

/-- Interchanging the two local preimages inverts the target overlap. -/
@[simp]
theorem targetOverlapIso_symm {Y : C} (q : Y ⟶ U) {i j : ι} (a : Y ⟶ X i) (b : Y ⟶ X j)
    (ha : a ≫ f i = q) (hb : b ≫ f j = q) :
    (targetOverlapIso η f D e q a b ha hb).symm = targetOverlapIso η f D e q b a hb ha :=
  Iso.ext (targetOverlapIso_inv η f D e q a b ha hb)

/-- When the components of `η` are fully faithful, the image under `η_Y` of the gluing morphism
of the lift of `D` along `e` (`StrongTrans.liftDescentData`) is the forward arrow of the target
overlap. The objects of the lift are the `x i` only by definition, so the statement names
the domain `F(a) x_i` and codomain `F(b) x_j` of the arrow, as `liftedOverlapIso` does. -/
@[simp, reassoc]
theorem map_liftDescentData_hom
    (hη : ∀ V : C, (η.app (.mk (op V))).toFunctor.FullyFaithful) {Y : C} (q : Y ⟶ U) {i j : ι}
    (a : Y ⟶ X i) (b : Y ⟶ X j) (ha : a ≫ f i = q) (hb : b ≫ f j = q) :
    (η.app (.mk (op Y))).toFunctor.map (X := (F.map a.op.toLoc).toFunctor.obj (x i))
        (Y := (F.map b.op.toLoc).toFunctor.obj (x j))
        ((η.liftDescentData f hη D e).hom q a b ha hb) =
      (targetOverlapIso η f D e q a b ha hb).hom := by
  -- `StrongTrans.mapPullHom_liftDescentData_hom`, with the naturality isomorphisms at the `x i`
  -- rather than at the objects of the lift, which are only definitionally equal to them.
  have h : (η.naturality a.op.toLoc).inv.toNatTrans.app (x i) ≫
      (η.app (.mk (op Y))).toFunctor.map (X := (F.map a.op.toLoc).toFunctor.obj (x i))
        (Y := (F.map b.op.toLoc).toFunctor.obj (x j))
        ((η.liftDescentData f hη D e).hom q a b ha hb) ≫
        (η.naturality b.op.toLoc).hom.toNatTrans.app (x j) =
      η.liftDescentDataHom f D e q a b ha hb :=
    (η.mapPullHom_def _).symm.trans (η.mapPullHom_liftDescentData_hom f hη D e q a b ha hb)
  rw [targetOverlapIso_hom, ← η.liftDescentDataHom_comp_assoc f D e q a b ha hb, ← h]
  simp

/-- When the components of `η` are fully faithful, the image under `η_Y` of the gluing
isomorphism of the lift of `D` along `e` (`StrongTrans.liftDescentData`) is the target
overlap. -/
@[simp]
theorem mapIso_liftDescentData_iso
    (hη : ∀ V : C, (η.app (.mk (op V))).toFunctor.FullyFaithful) {Y : C} (q : Y ⟶ U) {i j : ι}
    (a : Y ⟶ X i) (b : Y ⟶ X j) (ha : a ≫ f i = q) (hb : b ≫ f j = q) :
    (η.app (.mk (op Y))).toFunctor.mapIso (X := (F.map a.op.toLoc).toFunctor.obj (x i))
        (Y := (F.map b.op.toLoc).toFunctor.obj (x j))
        ((η.liftDescentData f hη D e).iso q a b ha hb) =
      targetOverlapIso η f D e q a b ha hb :=
  Iso.ext (map_liftDescentData_hom η f D e hη q a b ha hb)

end TargetOverlap

/-! ### Lifted overlaps -/

variable (z : G.obj (.mk (op U)))
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
      (targetOverlapIso η f ((G.toDescentData f).obj z) e q a b ha hb).hom :=
  map_liftDescentData_hom η f _ e hη q a b ha hb

/-- The image of the lifted overlap under `η_Y` is the target overlap. -/
@[simp]
theorem mapIso_liftedOverlapIso {Y : C} (q : Y ⟶ U) {i j : ι} (a : Y ⟶ X i) (b : Y ⟶ X j)
    (ha : a ≫ f i = q) (hb : b ≫ f j = q) :
    (η.app (.mk (op Y))).toFunctor.mapIso (liftedOverlapIso η f z e hη q a b ha hb) =
      targetOverlapIso η f ((G.toDescentData f).obj z) e q a b ha hb :=
  mapIso_liftDescentData_iso η f _ e hη q a b ha hb

/-- The image under `η_Y` of the inverse arrow of the lifted overlap is that of the target
overlap. In simp normal form both sides are forward arrows of the swapped overlaps
(`liftedOverlapIso_inv`, `targetOverlapIso_inv`). -/
@[reassoc]
theorem map_liftedOverlapIso_inv {Y : C} (q : Y ⟶ U) {i j : ι} (a : Y ⟶ X i) (b : Y ⟶ X j)
    (ha : a ≫ f i = q) (hb : b ≫ f j = q) :
    (η.app (.mk (op Y))).toFunctor.map (liftedOverlapIso η f z e hη q a b ha hb).inv =
      (targetOverlapIso η f ((G.toDescentData f).obj z) e q a b ha hb).inv :=
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

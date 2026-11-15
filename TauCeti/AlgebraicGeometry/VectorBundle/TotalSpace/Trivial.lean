/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.VectorBundle.TotalSpace.AffineSpace

/-!
# The trivial geometric line bundle

The trivial invertible sheaf `𝒪_X = InvertibleSheaf.trivial X`, the free sheaf on one generator,
is a finite locally free sheaf of rank one. Its geometric total space
`𝕍(𝒪_X) = Spec_X (Sym 𝒪_X^∨)` is the affine line `𝔸¹_X = 𝔸(PUnit; X)` over `X`
(`totalSpaceTrivialIso`), and this is an isomorphism of additive group schemes over `X`
(`isAddMonHom_totalSpaceTrivialIso_hom`): the zero section and the fibrewise addition of the
trivial line bundle are the zero and the addition of the ring scheme `𝔸¹_X`.

Consequently the points of the trivial line bundle are the global functions. For a scheme
`q : T ⟶ X` over `X`, the group of morphisms `T ⟶ 𝕍(𝒪_X)` over `X` is the additive group
`Γ(T, ⊤)` of global functions on `T` (`totalSpaceTrivialHomAddEquiv`). Composing a point with a
morphism `g : T' ⟶ T` over `X` pulls back its function along `g`
(`totalSpaceTrivialHomAddEquiv_comp`), and the isomorphism `𝕍(𝒪_X) ≅ 𝔸¹_X` sends a point to the
point of `𝔸¹_X` with the same coordinate (`comp_totalSpaceTrivialIso_hom_left`), and conversely
(`homOfVector_comp_totalSpaceTrivialIso_inv_left`).

Both statements are the case `I = PUnit` of the corresponding statements for the free sheaf `𝒪_X^I`
(`totalSpaceFreeIso`, `isAddMonHom_totalSpaceFreeIso_hom` and `totalSpaceFreeHomEquiv`), transported
along the identification `InvertibleSheaf.trivialIsoFree` of `InvertibleSheaf.trivial X` with the
free sheaf on `PUnit`; in particular the global function of a point is the coordinate of the
corresponding point of `𝕍(𝒪_X^PUnit)` (`totalSpaceTrivialHomAddEquiv_apply`,
`totalSpaceTrivialHomAddEquiv_symm_apply`).

## Main declarations

* `TauCeti.AlgebraicGeometry.totalSpaceTrivialIso`: the isomorphism `𝕍(𝒪_X) ≅ 𝔸¹_X` of affine
  schemes over `X`;
* `TauCeti.AlgebraicGeometry.isAddMonHom_totalSpaceTrivialIso_hom`: it is an isomorphism of
  additive group schemes;
* `TauCeti.AlgebraicGeometry.totalSpaceTrivialHomAddEquiv`: the group of points of `𝕍(𝒪_X)` over
  `T` is the additive group `Γ(T, ⊤)`, naturally in `T`
  (`totalSpaceTrivialHomAddEquiv_comp`).

## References

These use the convention `V(F) = Spec_X (Sym F)`, in which the total space of `E` is `V(E^∨)`; see
`TauCeti.AlgebraicGeometry.totalSpaceScheme`.

* The Stacks Project, [Tag 01M1](https://stacks.math.columbia.edu/tag/01M1).
* A. Grothendieck, J. Dieudonné, *Éléments de géométrie algébrique II*, 1.7.
-/

public section

open CategoryTheory AddMonObj

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry FiniteLocallyFreeSheaf

universe u

noncomputable section

variable (X : Scheme.{u})

/-- **The total space of the trivial line bundle is the affine line.** The geometric total space
`𝕍(𝒪_X) = Spec_X (Sym 𝒪_X^∨)` of the trivial invertible sheaf is isomorphic over `X` to the
affine line `𝔸¹_X = 𝔸(PUnit; X)`, as additive group schemes
(`isAddMonHom_totalSpaceTrivialIso_hom`). -/
def totalSpaceTrivialIso :
    (totalSpaceScheme X).obj
        ((InvertibleSheaf.toFiniteLocallyFree X).obj (InvertibleSheaf.trivial X)) ≅
      affineSpaceOver X PUnit :=
  (totalSpaceScheme X).mapIso (InvertibleSheaf.trivialIsoFree X) ≪≫ totalSpaceFreeIso X PUnit

/-- **The trivial geometric line bundle is the additive group scheme `𝔸¹_X`.** The isomorphism
`totalSpaceTrivialIso` respects the zero sections and the fibrewise additions, for the group
structure of the total space (`addGrpObjTotalSpaceScheme`) and the additive group of the ring
scheme `𝔸¹_X` (`AlgebraicGeometry.AffineSpace.commRingObjAsOver`). -/
instance isAddMonHom_totalSpaceTrivialIso_hom :
    IsAddMonHom (N' := 𝔸(PUnit.{u + 1}; X).asOver X)
      ((MorphismProperty.Over.forget _ _ X).map (totalSpaceTrivialIso X).hom) := by
  -- `totalSpaceTrivialIso` is the map of total spaces induced by an isomorphism of finite locally
  -- free sheaves, a homomorphism of group schemes, followed by `totalSpaceFreeIso`.
  rw [totalSpaceTrivialIso, Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp]
  exact instIsAddMonHomComp _ _

variable {X}

open scoped CommRingObj in
/-- **Points of the trivial line bundle are global functions.** For a scheme `q : T ⟶ X` over `X`,
the group of morphisms `T ⟶ 𝕍(𝒪_X)` over `X`, for the group structure of the total space, is the
additive group `Γ(T, ⊤)` of global functions on `T`: compose with `totalSpaceTrivialIso` and take
the coordinate of the resulting point of `𝔸¹_X`. -/
def totalSpaceTrivialHomAddEquiv (T : Over X) :
    (T ⟶ (MorphismProperty.Over.forget _ _ X).obj ((totalSpaceScheme X).obj
        ((InvertibleSheaf.toFiniteLocallyFree X).obj (InvertibleSheaf.trivial X)))) ≃+
      Γ(T.left, ⊤) :=
  haveI : IsAddMonHom (N' := 𝔸(PUnit.{u + 1}; X).asOver X)
      ((MorphismProperty.Over.forget _ _ X).mapIso (totalSpaceTrivialIso X)).hom :=
    isAddMonHom_totalSpaceTrivialIso_hom X
  (Hom.addEquivCongrRight (N := 𝔸(PUnit.{u + 1}; X).asOver X)
    ((MorphismProperty.Over.forget _ _ X).mapIso (totalSpaceTrivialIso X)) T).trans
      ((AffineSpace.homAsOverRingEquiv (n := PUnit.{u + 1}) T).trans
        (RingEquiv.piUnique _)).toAddEquiv

/-- The function of a point `t` of the trivial line bundle is the coordinate of the corresponding
point of `𝕍(𝒪_X^PUnit)`. -/
lemma totalSpaceTrivialHomAddEquiv_apply (T : Over X)
    (t : T ⟶ (MorphismProperty.Over.forget _ _ X).obj ((totalSpaceScheme X).obj
      ((InvertibleSheaf.toFiniteLocallyFree X).obj (InvertibleSheaf.trivial X)))) :
    totalSpaceTrivialHomAddEquiv T t = totalSpaceFreeHomEquiv PUnit T
      (t ≫ (MorphismProperty.Over.forget _ _ X).map
        ((totalSpaceScheme X).map (InvertibleSheaf.trivialIsoFree X).hom)) PUnit.unit := by
  have : IsAddMonHom (N' := 𝔸(PUnit.{u + 1}; X).asOver X)
      ((MorphismProperty.Over.forget _ _ X).mapIso (totalSpaceTrivialIso X)).hom :=
    isAddMonHom_totalSpaceTrivialIso_hom X
  -- `Hom.addEquivCongrRight` is composition with the isomorphism; its `simps` lemma is stated on
  -- the carrier of an `AddMonCat` object, so it does not rewrite a morphism.
  have he : Hom.addEquivCongrRight (N := 𝔸(PUnit.{u + 1}; X).asOver X)
      ((MorphismProperty.Over.forget _ _ X).mapIso (totalSpaceTrivialIso X)) T t =
        t ≫ ((MorphismProperty.Over.forget _ _ X).mapIso (totalSpaceTrivialIso X)).hom :=
    rfl
  -- `totalSpaceTrivialIso` is the map induced by `trivialIsoFree` followed by `totalSpaceFreeIso`.
  have h : t ≫ ((MorphismProperty.Over.forget _ _ X).mapIso (totalSpaceTrivialIso X)).hom =
      (t ≫ (MorphismProperty.Over.forget _ _ X).map
        ((totalSpaceScheme X).map (InvertibleSheaf.trivialIsoFree X).hom)) ≫
          (MorphismProperty.Over.forget _ _ X).map (totalSpaceFreeIso X PUnit).hom := by
    simp only [Functor.mapIso_hom, totalSpaceTrivialIso, Iso.trans_hom, Functor.map_comp,
      Category.assoc]
  simp only [totalSpaceTrivialHomAddEquiv, AddEquiv.trans_apply, RingEquiv.toAddEquiv_eq_coe,
    RingEquiv.coe_toAddEquiv, RingEquiv.trans_apply, AffineSpace.homAsOverRingEquiv_apply,
    RingEquiv.piUnique_apply]
  exact (congrArg (fun f ↦ AffineSpace.homAsOverEquiv T f PUnit.unit) (he.trans h)).trans
    (congrFun (homAsOverEquiv_comp_totalSpaceFreeIso_hom PUnit T _) PUnit.unit)

/-- The point of the trivial line bundle with function `c` corresponds to the point of
`𝕍(𝒪_X^PUnit)` with coordinate `c`. -/
lemma totalSpaceTrivialHomAddEquiv_symm_apply (T : Over X) (c : Γ(T.left, ⊤)) :
    (totalSpaceTrivialHomAddEquiv T).symm c =
      (totalSpaceFreeHomEquiv PUnit T).symm (fun _ ↦ c) ≫
        (MorphismProperty.Over.forget _ _ X).map
          ((totalSpaceScheme X).map (InvertibleSheaf.trivialIsoFree X).inv) := by
  rw [AddEquiv.symm_apply_eq, totalSpaceTrivialHomAddEquiv_apply, Category.assoc,
    ← Functor.map_comp, ← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
    CategoryTheory.Functor.map_id, Category.comp_id, Equiv.apply_symm_apply]

/-- **Points of the trivial line bundle are natural in the test scheme.** Composing a point with
a morphism `g : T' ⟶ T` over `X` pulls back its global function along `g`. -/
@[simp]
lemma totalSpaceTrivialHomAddEquiv_comp {T' T : Over X} (g : T' ⟶ T)
    (t : T ⟶ (MorphismProperty.Over.forget _ _ X).obj ((totalSpaceScheme X).obj
      ((InvertibleSheaf.toFiniteLocallyFree X).obj (InvertibleSheaf.trivial X)))) :
    totalSpaceTrivialHomAddEquiv T' (g ≫ t) = g.left.appTop (totalSpaceTrivialHomAddEquiv T t) := by
  rw [totalSpaceTrivialHomAddEquiv_apply, totalSpaceTrivialHomAddEquiv_apply, Category.assoc,
    totalSpaceFreeHomEquiv_comp, Function.comp_apply]

/-- The isomorphism `𝕍(𝒪_X) ≅ 𝔸¹_X` sends a point `t` of the trivial line bundle over `X` to the
point of `𝔸¹_X` whose coordinate is the global function of `t`. -/
lemma comp_totalSpaceTrivialIso_hom_left (T : Over X)
    (t : T ⟶ (MorphismProperty.Over.forget _ _ X).obj ((totalSpaceScheme X).obj
      ((InvertibleSheaf.toFiniteLocallyFree X).obj (InvertibleSheaf.trivial X)))) :
    t.left ≫ (totalSpaceTrivialIso X).hom.left =
      AffineSpace.homOfVector T.hom fun _ ↦ totalSpaceTrivialHomAddEquiv T t := by
  -- A function on `PUnit` is the constant function at its value at `PUnit.unit`.
  have hv : (fun _ : PUnit ↦ totalSpaceTrivialHomAddEquiv T t) =
      totalSpaceFreeHomEquiv PUnit T (t ≫ (MorphismProperty.Over.forget _ _ X).map
        ((totalSpaceScheme X).map (InvertibleSheaf.trivialIsoFree X).hom)) := by
    funext i
    rw [Unique.eq_default i, totalSpaceTrivialHomAddEquiv_apply]
  rw [hv, ← comp_totalSpaceFreeIso_hom_left, totalSpaceTrivialIso, Iso.trans_hom,
    Functor.mapIso_hom, Over.comp_left]
  -- The underlying morphism of the image of `a` under the forgetful functor is that of `a`.
  exact (congrArg (t.left ≫ ·) (MorphismProperty.Comma.comp_left _ _)).trans
    (Category.assoc _ _ _).symm

/-- The inverse isomorphism `𝔸¹_X ≅ 𝕍(𝒪_X)` sends the point of `𝔸¹_X` with coordinate `c` to the
point of the trivial line bundle whose global function is `c`. -/
lemma homOfVector_comp_totalSpaceTrivialIso_inv_left (T : Over X) (c : Γ(T.left, ⊤)) :
    AffineSpace.homOfVector T.hom (fun _ ↦ c) ≫ (totalSpaceTrivialIso X).inv.left =
      ((totalSpaceTrivialHomAddEquiv T).symm c).left := by
  have h := comp_totalSpaceTrivialIso_hom_left T ((totalSpaceTrivialHomAddEquiv T).symm c)
  rw [AddEquiv.apply_symm_apply] at h
  -- The underlying morphism of `hom ≫ inv = 𝟙` over `X` is `hom.left ≫ inv.left = 𝟙`.
  exact (congrArg (· ≫ (totalSpaceTrivialIso X).inv.left) h).symm.trans <|
    (Category.assoc _ _ _).trans <| (congrArg (_ ≫ ·)
      (congrArg (fun f ↦ f.left) (totalSpaceTrivialIso X).hom_inv_id)).trans (Category.comp_id _)

end

end TauCeti.AlgebraicGeometry

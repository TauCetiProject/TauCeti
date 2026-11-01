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
along the identification of `InvertibleSheaf.trivial X` with the free sheaf on `PUnit`.

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

/-- The trivial invertible sheaf, as a finite locally free sheaf, is the free sheaf on `PUnit`. -/
private def trivialIsoFree :
    (InvertibleSheaf.toFiniteLocallyFree X).obj (InvertibleSheaf.trivial X) ≅ free X PUnit :=
  ObjectProperty.isoMk _ (eqToIso ((InvertibleSheaf.trivial_obj X).trans (free_obj X PUnit).symm))

/-- **The total space of the trivial line bundle is the affine line.** The geometric total space
`𝕍(𝒪_X) = Spec_X (Sym 𝒪_X^∨)` of the trivial invertible sheaf is isomorphic over `X` to the
affine line `𝔸¹_X = 𝔸(PUnit; X)`, as additive group schemes
(`isAddMonHom_totalSpaceTrivialIso_hom`). -/
def totalSpaceTrivialIso :
    (totalSpaceScheme X).obj
        ((InvertibleSheaf.toFiniteLocallyFree X).obj (InvertibleSheaf.trivial X)) ≅
      affineSpaceOver X PUnit :=
  (totalSpaceScheme X).mapIso (trivialIsoFree X) ≪≫ totalSpaceFreeIso X PUnit

/-- **The trivial geometric line bundle is the additive group scheme `𝔸¹_X`.** The isomorphism
`totalSpaceTrivialIso` respects the zero sections and the fibrewise additions, for the group
structure of the total space (`addGrpObjTotalSpaceScheme`) and the additive group of the ring
scheme `𝔸¹_X` (`AlgebraicGeometry.AffineSpace.commRingObjAsOver`). -/
instance isAddMonHom_totalSpaceTrivialIso_hom :
    IsAddMonHom (N' := 𝔸(PUnit.{u + 1}; X).asOver X)
      ((MorphismProperty.Over.forget _ _ X).map (totalSpaceTrivialIso X).hom) := by
  -- `totalSpaceTrivialIso` is the map of total spaces induced by an isomorphism of finite locally
  -- free sheaves, a homomorphism of group schemes, followed by `totalSpaceFreeIso`.
  have h : IsAddMonHom (N' := 𝔸(PUnit.{u + 1}; X).asOver X)
      ((MorphismProperty.Over.forget _ _ X).map ((totalSpaceScheme X).map (trivialIsoFree X).hom) ≫
        (MorphismProperty.Over.forget _ _ X).map (totalSpaceFreeIso X PUnit).hom :
          _ ⟶ 𝔸(PUnit.{u + 1}; X).asOver X) :=
    instIsAddMonHomComp _ _
  exact h

variable {X}

/-- **Points of the trivial line bundle are global functions.** For a scheme `q : T ⟶ X` over `X`,
the group of morphisms `T ⟶ 𝕍(𝒪_X)` over `X`, for the group structure of the total space, is the
additive group `Γ(T, ⊤)` of global functions on `T`. A point goes to the coordinate of the
corresponding point of `𝕍(𝒪_X^PUnit) ≅ 𝔸¹_X` (`totalSpaceFreeHomEquiv`). -/
def totalSpaceTrivialHomAddEquiv (T : Over X) :
    (T ⟶ (MorphismProperty.Over.forget _ _ X).obj ((totalSpaceScheme X).obj
        ((InvertibleSheaf.toFiniteLocallyFree X).obj (InvertibleSheaf.trivial X)))) ≃+
      Γ(T.left, ⊤) where
  toEquiv := (((MorphismProperty.Over.forget _ _ X).mapIso
      ((totalSpaceScheme X).mapIso (trivialIsoFree X))).homToEquiv.trans
        (totalSpaceFreeHomEquiv PUnit T)).trans (Equiv.funUnique PUnit _)
  map_add' t₁ t₂ := by
    -- the map of total spaces induced by `trivialIsoFree` is additive on points, and so are the
    -- coordinates of points of `𝕍(𝒪_X^PUnit)`
    simp only [Equiv.toFun_as_coe, Equiv.trans_apply, Iso.homToEquiv_apply, Functor.mapIso_hom,
      AddMonObj.add_comp, totalSpaceFreeHomEquiv_add, Equiv.funUnique_apply, Pi.add_apply]

/-- The function of a point `t` of the trivial line bundle is the coordinate of the corresponding
point of `𝕍(𝒪_X^PUnit)`. -/
private lemma totalSpaceTrivialHomAddEquiv_eq (T : Over X)
    (t : T ⟶ (MorphismProperty.Over.forget _ _ X).obj ((totalSpaceScheme X).obj
      ((InvertibleSheaf.toFiniteLocallyFree X).obj (InvertibleSheaf.trivial X)))) :
    totalSpaceTrivialHomAddEquiv T t = totalSpaceFreeHomEquiv PUnit T
      (t ≫ (MorphismProperty.Over.forget _ _ X).map
        ((totalSpaceScheme X).map (trivialIsoFree X).hom)) PUnit.unit :=
  (rfl)

/-- **Points of the trivial line bundle are natural in the test scheme.** Composing a point with
a morphism `g : T' ⟶ T` over `X` pulls back its global function along `g`. -/
lemma totalSpaceTrivialHomAddEquiv_comp {T' T : Over X} (g : T' ⟶ T)
    (t : T ⟶ (MorphismProperty.Over.forget _ _ X).obj ((totalSpaceScheme X).obj
      ((InvertibleSheaf.toFiniteLocallyFree X).obj (InvertibleSheaf.trivial X)))) :
    totalSpaceTrivialHomAddEquiv T' (g ≫ t) = g.left.appTop (totalSpaceTrivialHomAddEquiv T t) := by
  rw [totalSpaceTrivialHomAddEquiv_eq, totalSpaceTrivialHomAddEquiv_eq, Category.assoc,
    totalSpaceFreeHomEquiv_comp, Function.comp_apply]

/-- The isomorphism `𝕍(𝒪_X) ≅ 𝔸¹_X` sends a point `t` of the trivial line bundle over `X` to the
point of `𝔸¹_X` whose coordinate is the global function of `t`. -/
lemma comp_totalSpaceTrivialIso_hom_left (T : Over X)
    (t : T ⟶ (MorphismProperty.Over.forget _ _ X).obj ((totalSpaceScheme X).obj
      ((InvertibleSheaf.toFiniteLocallyFree X).obj (InvertibleSheaf.trivial X)))) :
    t.left ≫ (totalSpaceTrivialIso X).hom.left =
      AffineSpace.homOfVector T.hom fun _ ↦ totalSpaceTrivialHomAddEquiv T t := by
  have h := comp_totalSpaceFreeIso_hom_left PUnit T
    (t ≫ (MorphismProperty.Over.forget _ _ X).map ((totalSpaceScheme X).map (trivialIsoFree X).hom))
  -- The underlying morphism of a composite over `X` is the composite of the underlying morphisms,
  -- and a function on `PUnit` is the constant function at its value at `PUnit.unit`.
  exact (Category.assoc _ _ _).symm.trans h

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

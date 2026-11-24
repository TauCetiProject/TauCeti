/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ClassifyingSpace.Functoriality.Basic
public import TauCeti.AlgebraicTopology.Homotopy.PointedHomotopyCat.Basic
import TauCeti.AlgebraicTopology.ClassifyingSpace.PointedMaps

/-!
# The classifying space as a functor to the pointed homotopy category

Milnor's classifying space is strictly functorial in the group
(`MonoidHom.classifyingSpaceMap`), giving the functor
`TauCeti.classifyingSpaceFunctor : GrpCat ⥤ BasedTopologicalSpace` to based spaces (defined in
`TauCeti.AlgebraicTopology.ClassifyingSpace.Functoriality.Basic`). Composing with the quotient by
pointed homotopy gives the classifying-space functor
`TauCeti.classifyingSpaceHomotopyFunctor : GrpCat ⥤ PointedHomotopyCat` to the pointed homotopy
category, which the strict functor refines by construction.

Under the identifications `TauCeti.classifyingSpaceFundamentalGroupMulEquiv` of the fundamental
groups of the classifying spaces with the groups, the fundamental group undoes the classifying
space: `TauCeti.classifyingSpaceHomotopyFunctorCompFundamentalGroupFunctorIso` is a natural
isomorphism from `B ⋙ π₁` to the identity functor of `GrpCat`. In particular the
classifying-space functor is faithful.

From the classification of pointed maps out of Milnor's classifying space
(`TauCeti.fundamentalGroupFunctor_map_bijective_classifyingSpace` in
`TauCeti.AlgebraicTopology.ClassifyingSpace.PointedMaps`), it follows that
`TauCeti.classifyingSpaceHomotopyFunctor` is **fully faithful**
(`TauCeti.classifyingSpaceHomotopyFunctorFullyFaithful`), expressing the classification of pointed
maps `BG ⟶ BH` in `PointedHomotopyCat` by group homomorphisms `G →* H`.

## Main definitions

* `TauCeti.classifyingSpaceHomotopyFunctor`: the classifying space as a functor to the pointed
  homotopy category.
* `TauCeti.classifyingSpaceHomotopyFunctorCompFundamentalGroupFunctorIso`: the natural
  isomorphism `π₁ ∘ B ≅ 𝟭`.
* `TauCeti.classifyingSpaceHomotopyFunctorFullyFaithful`: full faithfulness of
  `classifyingSpaceHomotopyFunctor`, with explicit `preimage` via `π₁`.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 1.B,
  Proposition 1B.9.
* J. Milnor, *Construction of universal bundles, II*, Ann. of Math. 63 (1956), 430--436.
-/

public section

noncomputable section

open CategoryTheory

open scoped Topology

universe u

namespace TauCeti

/-- **The classifying space as a functor to the pointed homotopy category.** It sends a
homomorphism to the pointed homotopy class of the strictly functorial map of Milnor's classifying
spaces, so `TauCeti.classifyingSpaceFunctor` refines it. -/
@[expose] def classifyingSpaceHomotopyFunctor : GrpCat.{u} ⥤ PointedHomotopyCat.{u} :=
  classifyingSpaceFunctor ⋙ PointedHomotopyCat.quotient

@[simp]
theorem classifyingSpaceHomotopyFunctor_map {G H : GrpCat.{u}} (φ : G ⟶ H) :
    classifyingSpaceHomotopyFunctor.map φ =
      PointedHomotopyCat.quotient.map (classifyingSpaceFunctor.map φ) :=
  (rfl)

/-- **The fundamental group of the classifying space is the group, naturally.** The isomorphisms
`classifyingSpaceFundamentalGroupMulEquiv G` assemble into a natural isomorphism from the
fundamental group of the classifying space, as functors on `GrpCat`, to the identity functor. -/
def classifyingSpaceHomotopyFunctorCompFundamentalGroupFunctorIso :
    classifyingSpaceHomotopyFunctor ⋙ PointedHomotopyCat.fundamentalGroupFunctor ≅
      𝟭 GrpCat.{u} :=
  NatIso.ofComponents (fun G ↦ (classifyingSpaceFundamentalGroupMulEquiv G).toGrpIso)
    fun φ ↦ by
      ext a
      -- The composite sends `φ` to `mapOfEq` along `φ.hom.classifyingSpaceMap`: this is the
      -- definitional chain `classifyingSpaceHomotopyFunctor_map`,
      -- `PointedHomotopyCat.fundamentalGroupFunctor_map_quotient_map`,
      -- `BasedTopologicalSpace.fundamentalGroupFunctor_map_hom` and
      -- `classifyingSpaceFunctor_map_toContinuousMap`, which `rw` cannot apply because the source
      -- and target objects of the composite only agree with theirs up to unfolding.
      change classifyingSpaceFundamentalGroupMulEquiv _ (FundamentalGroup.mapOfEq
          φ.hom.classifyingSpaceMap φ.hom.classifyingSpaceMap_basepoint a) =
        φ.hom (classifyingSpaceFundamentalGroupMulEquiv _ a)
      exact φ.hom.classifyingSpaceFundamentalGroupMulEquiv_mapOfEq a

@[simp]
theorem classifyingSpaceHomotopyFunctorCompFundamentalGroupFunctorIso_hom_app_hom
    (G : GrpCat.{u}) :
    (classifyingSpaceHomotopyFunctorCompFundamentalGroupFunctorIso.hom.app G).hom =
      (classifyingSpaceFundamentalGroupMulEquiv G).toMonoidHom :=
  (rfl)

@[simp]
theorem classifyingSpaceHomotopyFunctorCompFundamentalGroupFunctorIso_inv_app_hom
    (G : GrpCat.{u}) :
    (classifyingSpaceHomotopyFunctorCompFundamentalGroupFunctorIso.inv.app G).hom =
      (classifyingSpaceFundamentalGroupMulEquiv G).symm.toMonoidHom :=
  (rfl)

/-- The classifying-space functor to the pointed homotopy category is faithful: the fundamental
group recovers the homomorphism inducing a map. -/
instance : classifyingSpaceHomotopyFunctor.{u}.Faithful :=
  .of_comp_iso classifyingSpaceHomotopyFunctorCompFundamentalGroupFunctorIso

section FunctorClassification

/-- **The classifying-space functor to the pointed homotopy category is fully faithful.**
Its inverse on morphisms sends a pointed homotopy class `f : BG ⟶ BH` to the homomorphism induced
on `π₁`, transported along `classifyingSpaceHomotopyFunctorCompFundamentalGroupFunctorIso`. -/
def classifyingSpaceHomotopyFunctorFullyFaithful :
    classifyingSpaceHomotopyFunctor.{u}.FullyFaithful where
  preimage {G H} f :=
    classifyingSpaceHomotopyFunctorCompFundamentalGroupFunctorIso.inv.app G ≫
      PointedHomotopyCat.fundamentalGroupFunctor.map f ≫
      classifyingSpaceHomotopyFunctorCompFundamentalGroupFunctorIso.hom.app H
  map_preimage {G H} f := by
    let φ : G ⟶ H :=
      classifyingSpaceHomotopyFunctorCompFundamentalGroupFunctorIso.inv.app G ≫
        PointedHomotopyCat.fundamentalGroupFunctor.map f ≫
        classifyingSpaceHomotopyFunctorCompFundamentalGroupFunctorIso.hom.app H
    have hnat :
        PointedHomotopyCat.fundamentalGroupFunctor.map (classifyingSpaceHomotopyFunctor.map φ) ≫
            classifyingSpaceHomotopyFunctorCompFundamentalGroupFunctorIso.hom.app H =
          classifyingSpaceHomotopyFunctorCompFundamentalGroupFunctorIso.hom.app G ≫ φ :=
      classifyingSpaceHomotopyFunctorCompFundamentalGroupFunctorIso.hom.naturality φ
    have hEq :
        PointedHomotopyCat.fundamentalGroupFunctor.map (classifyingSpaceHomotopyFunctor.map φ) =
          PointedHomotopyCat.fundamentalGroupFunctor.map f := by
      rw [← cancel_mono (classifyingSpaceHomotopyFunctorCompFundamentalGroupFunctorIso.hom.app H),
        hnat]
      exact Iso.hom_inv_id_app_assoc _ G _
    exact (fundamentalGroupFunctor_map_bijective_classifyingSpace G
      (Y := classifyingSpaceFunctor.obj H)
      (fun y n ↦ subsingleton_homotopyGroup_classifyingSpace H n y)).1 hEq
  preimage_map {G H} φ := by
    have hnat :
        PointedHomotopyCat.fundamentalGroupFunctor.map (classifyingSpaceHomotopyFunctor.map φ) ≫
            classifyingSpaceHomotopyFunctorCompFundamentalGroupFunctorIso.hom.app H =
          classifyingSpaceHomotopyFunctorCompFundamentalGroupFunctorIso.hom.app G ≫ φ :=
      classifyingSpaceHomotopyFunctorCompFundamentalGroupFunctorIso.hom.naturality φ
    rw [hnat, Iso.inv_hom_id_app_assoc]

/-- The explicit formula for the inverse on morphisms of
`classifyingSpaceHomotopyFunctorFullyFaithful`. -/
theorem classifyingSpaceHomotopyFunctorFullyFaithful_preimage {G H : GrpCat.{u}}
    (f : classifyingSpaceHomotopyFunctor.obj G ⟶ classifyingSpaceHomotopyFunctor.obj H) :
    classifyingSpaceHomotopyFunctorFullyFaithful.preimage f =
      classifyingSpaceHomotopyFunctorCompFundamentalGroupFunctorIso.inv.app G ≫
        PointedHomotopyCat.fundamentalGroupFunctor.map f ≫
        classifyingSpaceHomotopyFunctorCompFundamentalGroupFunctorIso.hom.app H :=
  (rfl)

/-- The classifying-space functor to the pointed homotopy category is full. Together with
`Faithful`, it is fully faithful (`TauCeti.classifyingSpaceHomotopyFunctorFullyFaithful`) and
therefore reflects isomorphisms (`CategoryTheory.reflectsIsomorphisms_of_full_and_faithful`). -/
instance : classifyingSpaceHomotopyFunctor.{u}.Full :=
  classifyingSpaceHomotopyFunctorFullyFaithful.full

end FunctorClassification

end TauCeti

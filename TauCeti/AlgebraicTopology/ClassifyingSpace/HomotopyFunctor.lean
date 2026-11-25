/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ClassifyingSpace.Comparison
public import TauCeti.AlgebraicTopology.ClassifyingSpace.Functoriality
public import TauCeti.AlgebraicTopology.Homotopy.PointedHomotopyCat
import TauCeti.AlgebraicTopology.ClassifyingSpace.MapsToAspherical
import TauCeti.Topology.Homotopy.Extension.CWComplex
import TauCeti.Topology.Homotopy.Extension.HomotopyEquivRel

/-!
# The classifying space as a functor to the pointed homotopy category

Milnor's classifying space is strictly functorial in the group
(`MonoidHom.classifyingSpaceMap`), so it is a functor
`TauCeti.classifyingSpaceFunctor : GrpCat ⥤ BasedTopologicalSpace` to based spaces. Composing with
the quotient by pointed homotopy gives the classifying-space functor
`TauCeti.classifyingSpaceHomotopyFunctor : GrpCat ⥤ PointedHomotopyCat` to the pointed homotopy
category, which the strict functor refines by construction.

Under the identifications `TauCeti.classifyingSpaceFundamentalGroupMulEquiv` of the fundamental
groups of the classifying spaces with the groups, the fundamental group undoes the classifying
space: `TauCeti.classifyingSpaceHomotopyFunctorCompFundamentalGroupFunctorIso` is a natural
isomorphism from `B ⋙ π₁` to the identity functor of `GrpCat`. By Hatcher's Proposition 1B.9 for
arbitrary path-connected Hausdorff CW complexes
(`TauCeti.fundamentalGroupFunctor_map_bijective_of_cwComplex`), pointed homotopy classes out of any
such `X` into a based space with vanishing higher homotopy groups are in bijection with
homomorphisms on `π₁`. In particular, pointed homotopy classes `X ⟶ BG` are in bijection with
homomorphisms `π₁(X) ⟶ G` (`TauCeti.classifyingSpaceHomotopyFunctorHomEquiv`), and
`TauCeti.classifyingSpaceHomotopyFunctor` is both full and faithful.

The cellular model determines the induced maps up to pointed homotopy, and is isomorphic to
Milnor's model in `PointedHomotopyCat` (`TauCeti.cellularClassifyingSpacePointedHomotopyIso`).
Consequently, for a presentation `e : PresentedGroup R ≃* G` and `φ : G →* H`, every pointed map
from the cellular model of `G` to `classifyingSpace H` that induces `φ` is pointed homotopic to
the comparison map of `TauCeti.cellularHomotopyEquivClassifyingSpace` followed by the map
`classifyingSpaceMap φ` (`TauCeti.quotient_map_eq_quotient_map_comp_cellularClassifyingSpace`).

## Main definitions

* `TauCeti.classifyingSpaceFunctor`: Milnor's classifying space as a functor to based spaces.
* `TauCeti.classifyingSpaceHomotopyFunctor`: the classifying space as a functor to the pointed
  homotopy category (both `Faithful` and `Full`).
* `TauCeti.classifyingSpaceHomotopyFunctorCompFundamentalGroupFunctorIso`: the natural
  isomorphism `π₁ ∘ B ≅ 𝟭`.
* `TauCeti.classifyingSpaceHomotopyFunctorHomEquiv`: the bijection
  `(X ⟶ BG) ≃ (π₁(X) ⟶ G)` in `PointedHomotopyCat` for path-connected Hausdorff CW complexes `X`.
* `TauCeti.cellularClassifyingSpaceBased`: the cellular classifying space as a based space.
* `TauCeti.cellularHomotopyEquivClassifyingSpaceBasedHom` and
  `TauCeti.cellularClassifyingSpacePointedHomotopyIso`: the comparison of the cellular model with
  Milnor's classifying space, as a based map and as an isomorphism in `PointedHomotopyCat`.

## Main results

* `TauCeti.quotient_map_eq_quotient_map_comp_cellularClassifyingSpace`: a pointed map from the
  cellular model realizing a homomorphism is pointed homotopic to the comparison of the two models
  followed by the strictly functorial map.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 1.B, Proposition
  1B.9.
* J. Milnor, *Construction of universal bundles, II*, Ann. of Math. 63 (1956), 430--436.
-/

public section

noncomputable section

open CategoryTheory

open scoped Topology

universe u

namespace TauCeti

/-- **Milnor's classifying space as a functor to based spaces.** A group goes to
`classifyingSpace G` with its base point, and a homomorphism to the strictly functorial map
`MonoidHom.classifyingSpaceMap`. -/
@[expose] def classifyingSpaceFunctor : GrpCat.{u} ⥤ BasedTopologicalSpace.{u} where
  obj G := ⟨classifyingSpace G, classifyingSpaceBasepoint G⟩
  map φ := ⟨φ.hom.classifyingSpaceMap, φ.hom.classifyingSpaceMap_basepoint⟩
  map_id G := BasedTopologicalSpace.Hom.ext (by
    simp only [GrpCat.hom_id, MonoidHom.classifyingSpaceMap_id,
      BasedTopologicalSpace.id_eq_hom_id, BasedTopologicalSpace.Hom.toContinuousMap_id])
  map_comp φ ψ := BasedTopologicalSpace.Hom.ext (by
    simp only [GrpCat.hom_comp, MonoidHom.classifyingSpaceMap_comp,
      BasedTopologicalSpace.comp_eq_hom_comp, BasedTopologicalSpace.Hom.toContinuousMap_comp])

@[simp]
theorem classifyingSpaceFunctor_obj_carrier (G : GrpCat.{u}) :
    (classifyingSpaceFunctor.obj G).carrier = classifyingSpace G :=
  (rfl)

@[simp]
theorem classifyingSpaceFunctor_obj_basepoint (G : GrpCat.{u}) :
    (classifyingSpaceFunctor.obj G).basepoint = classifyingSpaceBasepoint G :=
  (rfl)

@[simp]
theorem classifyingSpaceFunctor_map_toContinuousMap {G H : GrpCat.{u}} (φ : G ⟶ H) :
    (classifyingSpaceFunctor.map φ).toContinuousMap = φ.hom.classifyingSpaceMap :=
  (rfl)

/-- **The classifying space as a functor to the pointed homotopy category.** It sends a
homomorphism to the pointed homotopy class of the strictly functorial map of Milnor's classifying
spaces, so `TauCeti.classifyingSpaceFunctor` refines it. -/
@[expose] def classifyingSpaceHomotopyFunctor : GrpCat.{u} ⥤ PointedHomotopyCat.{u} :=
  classifyingSpaceFunctor ⋙ PointedHomotopyCat.quotient

@[simp]
theorem classifyingSpaceHomotopyFunctor_obj (G : GrpCat.{u}) :
    classifyingSpaceHomotopyFunctor.obj G =
      PointedHomotopyCat.quotient.obj (classifyingSpaceFunctor.obj G) :=
  (rfl)

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

instance (G : GrpCat.{u}) : T2Space (classifyingSpaceFunctor.obj G).carrier :=
  inferInstanceAs (T2Space (classifyingSpace G))

instance (G : GrpCat.{u}) :
    Topology.CWComplex (Set.univ : Set (classifyingSpaceFunctor.obj G).carrier) :=
  inferInstanceAs (Topology.CWComplex (Set.univ : Set (classifyingSpace G)))

instance (G : GrpCat.{u}) : PathConnectedSpace (classifyingSpaceFunctor.obj G).carrier :=
  (isEilenbergMacLaneSpaceOne_classifyingSpace G).isAspherical.pathConnectedSpace

/-- **The classifying-space functor to the pointed homotopy category is full** (and hence fully
faithful): every pointed homotopy class `BG ⟶ BH` is induced by a group homomorphism `G ⟶ H`. -/
instance : classifyingSpaceHomotopyFunctor.{u}.Full where
  map_surjective {G H} f := by
    let η := classifyingSpaceHomotopyFunctorCompFundamentalGroupFunctorIso
    refine ⟨η.inv.app G ≫ PointedHomotopyCat.fundamentalGroupFunctor.map f ≫ η.hom.app H,
      (fundamentalGroupFunctor_map_bijective_of_cwComplex
        (X := classifyingSpaceFunctor.obj G) (Y := classifyingSpaceFunctor.obj H)
        (fun n ↦ subsingleton_homotopyGroup_classifyingSpace H n _)).1 ?_⟩
    have h := η.hom.naturality
      (η.inv.app G ≫ PointedHomotopyCat.fundamentalGroupFunctor.map f ≫ η.hom.app H) =≫
        η.inv.app H
    dsimp only [CategoryTheory.Functor.comp_map, CategoryTheory.Functor.id_map,
      CategoryTheory.Functor.comp_obj, CategoryTheory.Functor.id_obj] at h
    simp only [Category.assoc, Iso.hom_inv_id_app, Iso.hom_inv_id_app_assoc,
      CategoryTheory.Functor.comp_obj, Category.comp_id] at h
    exact h

/-- **Pointed homotopy classes `X ⟶ BG` out of a path-connected Hausdorff CW complex are in
bijection with homomorphisms `π₁(X) ⟶ G`.** Sending a pointed homotopy class `X ⟶ BG` to the
composite `π₁(X) ⟶ π₁(BG) ≅ G` is bijective. -/
def classifyingSpaceHomotopyFunctorHomEquiv
    (X : BasedTopologicalSpace.{u}) [T2Space X.carrier]
    [Topology.CWComplex (Set.univ : Set X.carrier)] [PathConnectedSpace X.carrier]
    (G : GrpCat.{u}) :
    (PointedHomotopyCat.quotient.obj X ⟶ classifyingSpaceHomotopyFunctor.obj G) ≃
      (PointedHomotopyCat.fundamentalGroupFunctor.obj (PointedHomotopyCat.quotient.obj X) ⟶ G) :=
  Equiv.ofBijective
    (fun f ↦ PointedHomotopyCat.fundamentalGroupFunctor.map f ≫
      classifyingSpaceHomotopyFunctorCompFundamentalGroupFunctorIso.hom.app G)
    (((Iso.homCongr (Iso.refl _)
      (classifyingSpaceHomotopyFunctorCompFundamentalGroupFunctorIso.app G)).bijective).comp
      (fundamentalGroupFunctor_map_bijective_of_cwComplex (X := X)
        (Y := classifyingSpaceFunctor.obj G)
        (fun n ↦ subsingleton_homotopyGroup_classifyingSpace G n _)))

@[simp]
theorem classifyingSpaceHomotopyFunctorHomEquiv_apply
    (X : BasedTopologicalSpace.{u}) [T2Space X.carrier]
    [Topology.CWComplex (Set.univ : Set X.carrier)] [PathConnectedSpace X.carrier]
    (G : GrpCat.{u})
    (f : PointedHomotopyCat.quotient.obj X ⟶ classifyingSpaceHomotopyFunctor.obj G) :
    classifyingSpaceHomotopyFunctorHomEquiv X G f =
      PointedHomotopyCat.fundamentalGroupFunctor.map f ≫
        classifyingSpaceHomotopyFunctorCompFundamentalGroupFunctorIso.hom.app G := by
  unfold classifyingSpaceHomotopyFunctorHomEquiv
  rfl

section Cellular

variable {S : Type u} (R : Set (FreeGroup S))

/-- The cellular classifying space `cellularClassifyingSpace R` as a based space, based at the
vertex `cellularClassifyingSpaceBasepoint R`. -/
@[expose] def cellularClassifyingSpaceBased : BasedTopologicalSpace.{u} :=
  ⟨cellularClassifyingSpace R, cellularClassifyingSpaceBasepoint R⟩

@[simp]
theorem cellularClassifyingSpaceBased_carrier :
    (cellularClassifyingSpaceBased R).carrier = cellularClassifyingSpace R :=
  (rfl)

@[simp]
theorem cellularClassifyingSpaceBased_basepoint :
    (cellularClassifyingSpaceBased R).basepoint = cellularClassifyingSpaceBasepoint R :=
  (rfl)

instance : T2Space (cellularClassifyingSpaceBased R).carrier :=
  inferInstanceAs (T2Space (cellularClassifyingSpace R))

instance : Topology.CWComplex (Set.univ : Set (cellularClassifyingSpaceBased R).carrier) :=
  inferInstanceAs (Topology.CWComplex (Set.univ : Set (cellularClassifyingSpace R)))

instance : PathConnectedSpace (cellularClassifyingSpaceBased R).carrier :=
  inferInstanceAs (PathConnectedSpace (cellularClassifyingSpace R))

/-- The comparison `cellularHomotopyEquivClassifyingSpace R e` of the cellular model with Milnor's
classifying space, as a based map. -/
@[expose] def cellularHomotopyEquivClassifyingSpaceBasedHom {G : GrpCat.{u}}
    (e : PresentedGroup R ≃* G) :
    cellularClassifyingSpaceBased R ⟶ classifyingSpaceFunctor.obj G :=
  ⟨(cellularHomotopyEquivClassifyingSpace R e).toFun,
    cellularHomotopyEquivClassifyingSpace_toFun_basepoint R e⟩

@[simp]
theorem cellularHomotopyEquivClassifyingSpaceBasedHom_toContinuousMap {G : GrpCat.{u}}
    (e : PresentedGroup R ≃* G) :
    (cellularHomotopyEquivClassifyingSpaceBasedHom R e).toContinuousMap =
      (cellularHomotopyEquivClassifyingSpace R e).toFun :=
  (rfl)

/-- **The map induced by a homomorphism is determined up to pointed homotopy.** Let
`e : PresentedGroup R ≃* G` be a presentation and `φ : G ⟶ H`. Every pointed map from the cellular
classifying space of `R` to `classifyingSpace H` that induces `φ` under the identifications of both
fundamental groups is pointed homotopic to the comparison map of
`cellularHomotopyEquivClassifyingSpace R e` followed by `classifyingSpaceMap φ`. In the pointed
homotopy category the right-hand side is the comparison map followed by
`classifyingSpaceHomotopyFunctor.map φ`. -/
theorem quotient_map_eq_quotient_map_comp_cellularClassifyingSpace {G H : GrpCat.{u}}
    (e : PresentedGroup R ≃* G) (φ : G ⟶ H)
    (f : cellularClassifyingSpaceBased R ⟶ classifyingSpaceFunctor.obj H)
    (hf : ∀ a, classifyingSpaceFundamentalGroupMulEquiv H
        ((BasedTopologicalSpace.fundamentalGroupFunctor.map f).hom a) =
      φ.hom (e (cellularClassifyingSpaceFundamentalGroupMulEquiv R a))) :
    PointedHomotopyCat.quotient.map f =
      PointedHomotopyCat.quotient.map
        (cellularHomotopyEquivClassifyingSpaceBasedHom R e ≫ classifyingSpaceFunctor.map φ) := by
  refine (fundamentalGroupFunctor_map_bijective_of_cwComplex
    (X := cellularClassifyingSpaceBased R) (Y := classifyingSpaceFunctor.obj H)
    (fun n ↦ subsingleton_homotopyGroup_classifyingSpace H n _)).1 ?_
  rw [PointedHomotopyCat.fundamentalGroupFunctor_map_quotient_map,
    PointedHomotopyCat.fundamentalGroupFunctor_map_quotient_map, Functor.map_comp]
  refine GrpCat.hom_ext <| MonoidHom.ext fun a ↦
    (classifyingSpaceFundamentalGroupMulEquiv H).injective ?_
  simp only [GrpCat.hom_comp, BasedTopologicalSpace.fundamentalGroupFunctor_map_hom,
    cellularHomotopyEquivClassifyingSpaceBasedHom_toContinuousMap] at hf ⊢
  -- Both sides are `φ ∘ e` under the identifications: the comparison induces `e`, and the strict
  -- map induces `φ`.
  exact (hf a).trans <| (congrArg φ.hom
    (classifyingSpaceFundamentalGroupMulEquiv_mapOfEq_cellularHomotopyEquivClassifyingSpace R e
      a).symm).trans (φ.hom.classifyingSpaceFundamentalGroupMulEquiv_mapOfEq _).symm

/-- **The comparison of the cellular classifying space with Milnor's classifying space is an
isomorphism in `PointedHomotopyCat`.** -/
def cellularClassifyingSpacePointedHomotopyIso {G : GrpCat.{u}}
    (e : PresentedGroup R ≃* G) :
    PointedHomotopyCat.quotient.obj (cellularClassifyingSpaceBased R) ≅
      classifyingSpaceHomotopyFunctor.obj G :=
  let h := (hasHomotopyExtensionProperty_singleton_of_cwComplex
    (cellularClassifyingSpaceBasepoint R)).exists_basedInverse_homotopicRel
      (hasHomotopyExtensionProperty_singleton_of_cwComplex (classifyingSpaceBasepoint G))
      (cellularHomotopyEquivClassifyingSpace R e)
      (cellularHomotopyEquivClassifyingSpace_toFun_basepoint R e)
  let gHom : classifyingSpaceFunctor.obj G ⟶ cellularClassifyingSpaceBased R :=
    ⟨h.choose, h.choose_spec.1⟩
  { hom := PointedHomotopyCat.quotient.map (cellularHomotopyEquivClassifyingSpaceBasedHom R e)
    inv := PointedHomotopyCat.quotient.map gHom
    hom_inv_id := PointedHomotopyCat.quotient_map_comp_eq_id _ _ h.choose_spec.2.1
    inv_hom_id := PointedHomotopyCat.quotient_map_comp_eq_id _ _ h.choose_spec.2.2 }

@[simp]
theorem cellularClassifyingSpacePointedHomotopyIso_hom {G : GrpCat.{u}}
    (e : PresentedGroup R ≃* G) :
    (cellularClassifyingSpacePointedHomotopyIso R e).hom =
      PointedHomotopyCat.quotient.map
        (cellularHomotopyEquivClassifyingSpaceBasedHom R e) := by
  unfold cellularClassifyingSpacePointedHomotopyIso
  rfl

end Cellular

end TauCeti

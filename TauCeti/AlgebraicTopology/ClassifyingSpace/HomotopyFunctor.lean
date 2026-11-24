/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Equivalence
public import TauCeti.AlgebraicTopology.ClassifyingSpace.Comparison
public import TauCeti.AlgebraicTopology.ClassifyingSpace.Functoriality
public import TauCeti.AlgebraicTopology.Homotopy.PointedHomotopyCat
import TauCeti.AlgebraicTopology.ClassifyingSpace.Uniqueness
import TauCeti.Topology.Homotopy.Extension.CWComplex

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
isomorphism from `B ⋙ π₁` to the identity functor of `GrpCat`. In particular the
classifying-space functor is faithful.

For a group presentation `e : PresentedGroup R ≃* G`, the comparison equivalence
`TauCeti.cellularHomotopyEquivClassifyingSpace R e` has a pointed inverse
`TauCeti.cellularHomotopyEquivClassifyingSpaceBasedInv R e` with both composites homotopic to the
identities relative to the base points, so the two models are isomorphic in `PointedHomotopyCat`
(`TauCeti.cellularClassifyingSpaceIsoClassifyingSpace`). Out of the cellular classifying space
`TauCeti.cellularClassifyingSpace R`, pointed homotopy classes of maps to a space without higher
homotopy groups are in bijection with homomorphisms of fundamental groups
(`TauCeti.fundamentalGroupFunctor_map_bijective_cellularClassifyingSpace`).

Transporting this property along a pointed homotopy equivalence extends Hatcher's Proposition 1B.9
to every well-pointed aspherical space of CW type
(`TauCeti.fundamentalGroupFunctor_map_bijective_of_isAspherical`) and in particular to Milnor's
classifying space (`TauCeti.fundamentalGroupFunctor_map_bijective_classifyingSpace`). Consequently:

* Every pointed continuous map `classifyingSpace G → classifyingSpace H` inducing `φ : G →* H` on
  `π₁` is homotopic relative to the base point to `φ.classifyingSpaceMap`
  (`TauCeti.homotopicRel_classifyingSpaceMap_of_mapOfEq_eq`,
  `TauCeti.quotient_map_eq_classifyingSpaceHomotopyFunctor_map`).
* `TauCeti.classifyingSpaceHomotopyFunctor` is **fully faithful**
  (`TauCeti.classifyingSpaceHomotopyFunctorFullyFaithful`, with explicit preimage given by
  `PointedHomotopyCat.fundamentalGroupFunctor` conjugated by
  `TauCeti.classifyingSpaceHomotopyFunctorCompFundamentalGroupFunctorIso`), so in particular it is
  **full**.
* Between any two well-pointed aspherical spaces of CW type, every isomorphism `π₁(X) ≅ π₁(Y)` is
  realized by a unique isomorphism `X ≅ Y` in `PointedHomotopyCat`
  (`TauCeti.pointedIsoOfIsAspherical`, specialized to Milnor's model in
  `TauCeti.pointedIsoClassifyingSpace`).
* Restricting to the full subcategory of `PointedHomotopyCat` spanned by
  `TauCeti.isWellPointedAsphericalCWType` (spaces of CW type that are aspherical at the base point
  and whose base point singleton has the homotopy extension property),
  `TauCeti.classifyingSpaceHomotopyFunctor` and `PointedHomotopyCat.fundamentalGroupFunctor` form
  an explicit coherent adjoint equivalence
  `TauCeti.classifyingSpaceEquivalence : GrpCat ≌ isWellPointedAsphericalCWType.FullSubcategory`.

Every object of `isWellPointedAsphericalCWType` lies in `classifyingSpaceHomotopyFunctor.essImage`
(`TauCeti.isWellPointedAsphericalCWType_le_essImage`). This inclusion is proper in general: for an
uncountable index set `I`, the cube `[0, 1]^I` based at `0` is pointed-contractible (hence
isomorphic to `classifyingSpace Unit` in `PointedHomotopyCat`), yet `{0}` is closed without being a
`G_δ` set and therefore does not satisfy the homotopy extension property by Strøm's theorem on
closed cofibrations (Strøm, 1966).

## Main definitions

* `TauCeti.classifyingSpaceFunctor`: Milnor's classifying space as a functor to based spaces.
* `TauCeti.classifyingSpaceHomotopyFunctor`: the classifying space as a functor to the pointed
  homotopy category.
* `TauCeti.classifyingSpaceHomotopyFunctorCompFundamentalGroupFunctorIso`: the natural
  isomorphism `π₁ ∘ B ≅ 𝟭`.
* `TauCeti.cellularClassifyingSpaceBased`: the cellular classifying space as a based space.
* `TauCeti.cellularHomotopyEquivClassifyingSpaceBasedHom` and
  `TauCeti.cellularHomotopyEquivClassifyingSpaceBasedInv`: the comparison of the cellular model
  with Milnor's classifying space and its pointed inverse, as based maps.
* `TauCeti.cellularClassifyingSpaceIsoClassifyingSpace`: the resulting isomorphism between the
  cellular and simplicial models in `PointedHomotopyCat`.
* `TauCeti.classifyingSpaceHomotopyFunctorFullyFaithful`: explicit fully faithful data for
  `TauCeti.classifyingSpaceHomotopyFunctor`.
* `TauCeti.pointedIsoOfIsAspherical` and `TauCeti.pointedIsoClassifyingSpace`: unique isomorphisms
  in `PointedHomotopyCat` realizing prescribed isomorphisms of fundamental groups.
* `TauCeti.isWellPointedAsphericalCWType`: the `ObjectProperty` of well-pointed aspherical spaces
  of CW type in `PointedHomotopyCat`.
* `TauCeti.classifyingSpaceEquivalence`: the explicit adjoint equivalence
  `GrpCat ≌ isWellPointedAsphericalCWType.FullSubcategory`.

## Main results

* `TauCeti.fundamentalGroupFunctor_map_bijective_cellularClassifyingSpace`: pointed homotopy
  classes of maps out of a cellular classifying space into a space with no higher homotopy groups
  are classified by their effect on `π₁`.
* `TauCeti.quotient_map_eq_quotient_map_comp_cellularClassifyingSpace`: a pointed map from the
  cellular model realizing a homomorphism is pointed homotopic to the comparison of the two models
  followed by the strictly functorial map.
* `TauCeti.fundamentalGroupFunctor_map_bijective_of_isAspherical` and
  `TauCeti.fundamentalGroupFunctor_map_bijective_classifyingSpace`: **Hatcher's Proposition 1B.9**
  in `PointedHomotopyCat` for arbitrary well-pointed aspherical spaces of CW type and for Milnor's
  classifying space.
* `TauCeti.homotopicRel_classifyingSpaceMap_of_mapOfEq_eq` and
  `TauCeti.quotient_map_eq_classifyingSpaceHomotopyFunctor_map`: pointed maps between Milnor
  classifying spaces are determined up to pointed homotopy by the strict map of their induced
  homomorphism.
* `classifyingSpaceHomotopyFunctor.Full`: `TauCeti.classifyingSpaceHomotopyFunctor` is full.
* `TauCeti.isWellPointedAsphericalCWType_le_essImage`: every well-pointed aspherical space of CW
  type lies in the essential image of `TauCeti.classifyingSpaceHomotopyFunctor`.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Chapter 0 (Proposition 0.19),
  Section 1.B, Theorem 1B.8 and Proposition 1B.9.
* J. Milnor, *Construction of universal bundles, II*, Ann. of Math. 63 (1956), 430--436.
* A. Strøm, *Note on cofibrations*, Math. Scand. 19 (1966), 11--14.
-/

public section

noncomputable section

open CategoryTheory

open scoped Topology

universe u v

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

/-- The pointed inverse of `cellularHomotopyEquivClassifyingSpace R e`, as a based map from
Milnor's classifying space to the cellular classifying space. -/
def cellularHomotopyEquivClassifyingSpaceBasedInv {G : GrpCat.{u}}
    (e : PresentedGroup R ≃* G) :
    classifyingSpaceFunctor.obj G ⟶ cellularClassifyingSpaceBased R :=
  ⟨(cellularHomotopyEquivClassifyingSpace R e).invFun,
    cellularHomotopyEquivClassifyingSpace_invFun_basepoint R e⟩

@[simp]
theorem cellularHomotopyEquivClassifyingSpaceBasedInv_toContinuousMap {G : GrpCat.{u}}
    (e : PresentedGroup R ≃* G) :
    (cellularHomotopyEquivClassifyingSpaceBasedInv R e).toContinuousMap =
      (cellularHomotopyEquivClassifyingSpace R e).invFun :=
  (rfl)

/-- The pointed inverse `cellularHomotopyEquivClassifyingSpaceBasedInv R e` induces `e⁻¹` on
fundamental groups under the identifications with `G` and `PresentedGroup R`. -/
@[simp]
theorem fundamentalGroupFunctor_map_cellularHomotopyEquivClassifyingSpaceBasedInv {G : GrpCat.{u}}
    (e : PresentedGroup R ≃* G) :
    BasedTopologicalSpace.fundamentalGroupFunctor.map
        (cellularHomotopyEquivClassifyingSpaceBasedInv R e) =
      GrpCat.ofHom
        ((classifyingSpaceFundamentalGroupMulEquiv G).trans
          (e.symm.trans (cellularClassifyingSpaceFundamentalGroupMulEquiv R).symm)).toMonoidHom :=
  GrpCat.hom_ext <| MonoidHom.ext fun a ↦
    mapOfEq_cellularHomotopyEquivClassifyingSpace_invFun R e a

/-- **The cellular and simplicial classifying spaces are isomorphic in the pointed homotopy
category.** For a presentation `e : PresentedGroup R ≃* G`, the comparison map
`cellularHomotopyEquivClassifyingSpaceBasedHom R e` and its pointed inverse
`cellularHomotopyEquivClassifyingSpaceBasedInv R e` form an isomorphism in `PointedHomotopyCat`. -/
def cellularClassifyingSpaceIsoClassifyingSpace {G : GrpCat.{u}} (e : PresentedGroup R ≃* G) :
    PointedHomotopyCat.quotient.obj (cellularClassifyingSpaceBased R) ≅
      classifyingSpaceHomotopyFunctor.obj G :=
  PointedHomotopyCat.isoMk
    (cellularHomotopyEquivClassifyingSpaceBasedHom R e)
    (cellularHomotopyEquivClassifyingSpaceBasedInv R e)
    (cellularHomotopyEquivClassifyingSpace_left_inv_homotopicRel R e)
    (cellularHomotopyEquivClassifyingSpace_right_inv_homotopicRel R e)

@[simp]
theorem cellularClassifyingSpaceIsoClassifyingSpace_hom {G : GrpCat.{u}}
    (e : PresentedGroup R ≃* G) :
    (cellularClassifyingSpaceIsoClassifyingSpace R e).hom =
      PointedHomotopyCat.quotient.map (cellularHomotopyEquivClassifyingSpaceBasedHom R e) :=
  PointedHomotopyCat.isoMk_hom ..

@[simp]
theorem cellularClassifyingSpaceIsoClassifyingSpace_inv {G : GrpCat.{u}}
    (e : PresentedGroup R ≃* G) :
    (cellularClassifyingSpaceIsoClassifyingSpace R e).inv =
      PointedHomotopyCat.quotient.map (cellularHomotopyEquivClassifyingSpaceBasedInv R e) :=
  PointedHomotopyCat.isoMk_inv ..

instance isIso_quotient_map_cellularHomotopyEquivClassifyingSpaceBasedHom {G : GrpCat.{u}}
    (e : PresentedGroup R ≃* G) :
    IsIso (PointedHomotopyCat.quotient.map
      (cellularHomotopyEquivClassifyingSpaceBasedHom R e)) := by
  rw [← cellularClassifyingSpaceIsoClassifyingSpace_hom R e]
  exact (cellularClassifyingSpaceIsoClassifyingSpace R e).isIso_hom

@[simp]
theorem inv_quotient_map_cellularHomotopyEquivClassifyingSpaceBasedHom {G : GrpCat.{u}}
    (e : PresentedGroup R ≃* G) :
    inv (PointedHomotopyCat.quotient.map
        (cellularHomotopyEquivClassifyingSpaceBasedHom R e)) =
      PointedHomotopyCat.quotient.map (cellularHomotopyEquivClassifyingSpaceBasedInv R e) :=
  IsIso.inv_eq_of_hom_inv_id <| by
    rw [← cellularClassifyingSpaceIsoClassifyingSpace_hom R e,
      ← cellularClassifyingSpaceIsoClassifyingSpace_inv R e]
    exact (cellularClassifyingSpaceIsoClassifyingSpace R e).hom_inv_id

/-- Based maps out of the cellular classifying space into a space without higher homotopy groups
that induce the same homomorphism of fundamental groups have the same pointed homotopy class. -/
private theorem quotient_map_eq_cellularClassifyingSpace {Y : BasedTopologicalSpace.{u}}
    (hY : ∀ (y : Y.carrier) (n : ℕ), Subsingleton (π_ (n + 2) Y.carrier y))
    {f g : cellularClassifyingSpaceBased R ⟶ Y}
    (h : BasedTopologicalSpace.fundamentalGroupFunctor.map f =
      BasedTopologicalSpace.fundamentalGroupFunctor.map g) :
    PointedHomotopyCat.quotient.map f = PointedHomotopyCat.quotient.map g :=
  (PointedHomotopyCat.quotient_map_eq_iff f g).2
    (homotopicRel_of_mapOfEq_eq_cellularClassifyingSpace R hY f.map_basepoint g.map_basepoint
      (by
        have h' := congrArg GrpCat.Hom.hom h
        rw [BasedTopologicalSpace.fundamentalGroupFunctor_map_hom,
          BasedTopologicalSpace.fundamentalGroupFunctor_map_hom] at h'
        exact h'))

/-- **Pointed maps out of a cellular classifying space are classified by `π₁`.** If the homotopy
groups of `Y` vanish from degree `2` on, at every point, then a pointed homotopy class of maps from
the cellular classifying space `cellularClassifyingSpace R` to `Y` is determined by the homomorphism
it induces on fundamental groups, and every homomorphism is induced by such a class. -/
theorem fundamentalGroupFunctor_map_bijective_cellularClassifyingSpace
    {Y : BasedTopologicalSpace.{u}}
    (hY : ∀ (y : Y.carrier) (n : ℕ), Subsingleton (π_ (n + 2) Y.carrier y)) :
    Function.Bijective (PointedHomotopyCat.fundamentalGroupFunctor.map
      (X := PointedHomotopyCat.quotient.obj (cellularClassifyingSpaceBased R))
      (Y := PointedHomotopyCat.quotient.obj Y)) := by
  refine ⟨fun a b hab ↦ ?_, fun ψ ↦ ?_⟩
  · obtain ⟨f, rfl⟩ := PointedHomotopyCat.quotient.map_surjective a
    obtain ⟨g, rfl⟩ := PointedHomotopyCat.quotient.map_surjective b
    simp only [PointedHomotopyCat.fundamentalGroupFunctor_map_quotient_map] at hab
    exact quotient_map_eq_cellularClassifyingSpace R hY hab
  · obtain ⟨f, hf, hfψ⟩ := exists_mapOfEq_cellularClassifyingSpace R
      (fun k hk ↦ by
        obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hk
        exact hY _ n) ψ.hom
    exact ⟨PointedHomotopyCat.quotient.map ⟨f, hf⟩, GrpCat.hom_ext <|
      (congrArg GrpCat.Hom.hom
        (PointedHomotopyCat.fundamentalGroupFunctor_map_quotient_map _)).trans
        ((BasedTopologicalSpace.fundamentalGroupFunctor_map_hom _).trans hfψ)⟩

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
  refine quotient_map_eq_cellularClassifyingSpace R
    (fun y n ↦ subsingleton_homotopyGroup_classifyingSpace H n y) ?_
  rw [Functor.map_comp]
  refine GrpCat.hom_ext <| MonoidHom.ext fun a ↦
    (classifyingSpaceFundamentalGroupMulEquiv H).injective ?_
  simp only [GrpCat.hom_comp, BasedTopologicalSpace.fundamentalGroupFunctor_map_hom,
    cellularHomotopyEquivClassifyingSpaceBasedHom_toContinuousMap] at hf ⊢
  -- Both sides are `φ ∘ e` under the identifications: the comparison induces `e`, and the strict
  -- map induces `φ`.
  exact (hf a).trans <| (congrArg φ.hom
    (classifyingSpaceFundamentalGroupMulEquiv_mapOfEq_cellularHomotopyEquivClassifyingSpace R e
      a).symm).trans (φ.hom.classifyingSpaceFundamentalGroupMulEquiv_mapOfEq _).symm

end Cellular

section Classification

/-- **Pointed maps out of a well-pointed aspherical space of CW type are classified by `π₁`**
(Hatcher, Proposition 1B.9). If `X` is a well-pointed aspherical space of CW type and the homotopy
groups of `Y` vanish from degree `2` on, at every point, then `fundamentalGroupFunctor.map` is a
bijection from pointed homotopy classes `X ⟶ Y` to homomorphisms `π₁(X) ⟶ π₁(Y)`. -/
theorem fundamentalGroupFunctor_map_bijective_of_isAspherical
    {X Y : PointedHomotopyCat.{u}} [CWType X.as.carrier]
    (hX : IsAspherical X.as.carrier X.as.basepoint)
    (hx : HasHomotopyExtensionProperty ({X.as.basepoint} : Set X.as.carrier))
    (hY : ∀ (y : Y.as.carrier) (n : ℕ), Subsingleton (π_ (n + 2) Y.as.carrier y)) :
    Function.Bijective (PointedHomotopyCat.fundamentalGroupFunctor.map (X := X) (Y := Y)) := by
  refine ⟨fun a b hab ↦ ?_, fun ψ ↦ ?_⟩
  · obtain ⟨f, hf⟩ := PointedHomotopyCat.quotient.map_surjective (X := X.as) (Y := Y.as) a
    obtain ⟨g, hg⟩ := PointedHomotopyCat.quotient.map_surjective (X := X.as) (Y := Y.as) b
    rw [← hf, ← hg] at hab ⊢
    refine (PointedHomotopyCat.quotient_map_eq_iff f g).2
      (hX.homotopicRel_of_mapOfEq_eq hx hY f.map_basepoint g.map_basepoint ?_)
    have h' := congrArg GrpCat.Hom.hom
      ((PointedHomotopyCat.fundamentalGroupFunctor_map_quotient_map f).symm.trans <|
        hab.trans (PointedHomotopyCat.fundamentalGroupFunctor_map_quotient_map g))
    rw [BasedTopologicalSpace.fundamentalGroupFunctor_map_hom,
      BasedTopologicalSpace.fundamentalGroupFunctor_map_hom] at h'
    exact h'
  · obtain ⟨f, hf, hfψ⟩ := hX.exists_mapOfEq hx
      (fun k hk ↦ by
        obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hk
        exact hY _ n) ψ.hom
    exact ⟨PointedHomotopyCat.quotient.map (X := X.as) (Y := Y.as) ⟨f, hf⟩, GrpCat.hom_ext <|
      (congrArg GrpCat.Hom.hom
        (PointedHomotopyCat.fundamentalGroupFunctor_map_quotient_map
          (X := X.as) (Y := Y.as) ⟨f, hf⟩)).trans
        ((BasedTopologicalSpace.fundamentalGroupFunctor_map_hom _).trans hfψ)⟩

instance (G : GrpCat.{u}) : CWType (classifyingSpaceHomotopyFunctor.obj G).as.carrier :=
  inferInstanceAs (CWType (classifyingSpace G))

/-- **Pointed maps out of Milnor's classifying space are classified by `π₁`.** If the homotopy
groups of `Y` vanish from degree `2` on, at every point, then `fundamentalGroupFunctor.map` is a
bijection from pointed homotopy classes `classifyingSpaceHomotopyFunctor.obj G ⟶ Y` to
homomorphisms `π₁(BG) ⟶ π₁(Y)`. -/
theorem fundamentalGroupFunctor_map_bijective_classifyingSpace
    (G : GrpCat.{u}) {Y : PointedHomotopyCat.{u}}
    (hY : ∀ (y : Y.as.carrier) (n : ℕ), Subsingleton (π_ (n + 2) Y.as.carrier y)) :
    Function.Bijective (PointedHomotopyCat.fundamentalGroupFunctor.map
      (X := classifyingSpaceHomotopyFunctor.obj G) (Y := Y)) :=
  fundamentalGroupFunctor_map_bijective_of_isAspherical
    (isEilenbergMacLaneSpaceOne_classifyingSpace G).isAspherical
    (hasHomotopyExtensionProperty_singleton_of_cwComplex (classifyingSpaceBasepoint G)) hY

/-- **Every pointed map between Milnor classifying spaces is pointed homotopic to the strict map
induced by its homomorphism on `π₁`.** For `φ : G →* H`, any continuous map
`f : C(classifyingSpace G, classifyingSpace H)` sending the base point to the base point and
inducing `φ` under `classifyingSpaceFundamentalGroupMulEquiv` is homotopic relative to
`{classifyingSpaceBasepoint G}` to `φ.classifyingSpaceMap`. -/
theorem homotopicRel_classifyingSpaceMap_of_mapOfEq_eq {G : Type u} {H : Type v}
    [Group G] [Group H]
    (φ : G →* H) {f : C(classifyingSpace G, classifyingSpace H)}
    (hf : f (classifyingSpaceBasepoint G) = classifyingSpaceBasepoint H)
    (hfφ : ∀ a, classifyingSpaceFundamentalGroupMulEquiv H (FundamentalGroup.mapOfEq f hf a) =
      φ (classifyingSpaceFundamentalGroupMulEquiv G a)) :
    f.HomotopicRel φ.classifyingSpaceMap {classifyingSpaceBasepoint G} := by
  refine homotopicRel_of_mapOfEq_eq_classifyingSpace
    (fun z n ↦ subsingleton_homotopyGroup_classifyingSpace H n z) hf
    φ.classifyingSpaceMap_basepoint (MonoidHom.ext fun a ↦
      (classifyingSpaceFundamentalGroupMulEquiv H).injective ?_)
  rw [hfφ, φ.classifyingSpaceFundamentalGroupMulEquiv_mapOfEq]

/-- A based map `f : classifyingSpaceFunctor.obj G ⟶ classifyingSpaceFunctor.obj H` inducing
`φ : G ⟶ H` on fundamental groups under `classifyingSpaceFundamentalGroupMulEquiv` has pointed
homotopy class `classifyingSpaceHomotopyFunctor.map φ`. -/
theorem quotient_map_eq_classifyingSpaceHomotopyFunctor_map {G H : GrpCat.{u}} (φ : G ⟶ H)
    (f : classifyingSpaceFunctor.obj G ⟶ classifyingSpaceFunctor.obj H)
    (hf : ∀ a, classifyingSpaceFundamentalGroupMulEquiv H
        ((BasedTopologicalSpace.fundamentalGroupFunctor.map f).hom a) =
      φ.hom (classifyingSpaceFundamentalGroupMulEquiv G a)) :
    PointedHomotopyCat.quotient.map f = classifyingSpaceHomotopyFunctor.map φ :=
  (PointedHomotopyCat.quotient_map_eq_iff _ _).2
    (homotopicRel_classifyingSpaceMap_of_mapOfEq_eq φ.hom f.map_basepoint hf)

/-- **The classifying-space functor to the pointed homotopy category is fully faithful**, with
explicit inverse sending a pointed homotopy class `f : BG ⟶ BH` to the homomorphism it induces on
fundamental groups, conjugated by
`classifyingSpaceHomotopyFunctorCompFundamentalGroupFunctorIso`. -/
def classifyingSpaceHomotopyFunctorFullyFaithful :
    classifyingSpaceHomotopyFunctor.{u}.FullyFaithful where
  preimage {G H} f :=
    classifyingSpaceHomotopyFunctorCompFundamentalGroupFunctorIso.inv.app G ≫
      PointedHomotopyCat.fundamentalGroupFunctor.map f ≫
      classifyingSpaceHomotopyFunctorCompFundamentalGroupFunctorIso.hom.app H
  map_preimage {G H} f := by
    apply (fundamentalGroupFunctor_map_bijective_classifyingSpace G
      (Y := classifyingSpaceHomotopyFunctor.obj H)
      (fun z n ↦ subsingleton_homotopyGroup_classifyingSpace H n z)).injective
    apply (cancel_mono
      (classifyingSpaceHomotopyFunctorCompFundamentalGroupFunctorIso.hom.app H)).1
    have hnat := classifyingSpaceHomotopyFunctorCompFundamentalGroupFunctorIso.hom.naturality
      (classifyingSpaceHomotopyFunctorCompFundamentalGroupFunctorIso.inv.app G ≫
        PointedHomotopyCat.fundamentalGroupFunctor.map f ≫
        classifyingSpaceHomotopyFunctorCompFundamentalGroupFunctorIso.hom.app H)
    simpa [Category.assoc] using hnat
  preimage_map {G H} φ := by
    have hnat := classifyingSpaceHomotopyFunctorCompFundamentalGroupFunctorIso.hom.naturality φ
    simp only [Functor.comp_map, Functor.id_map] at hnat
    rw [hnat, Iso.inv_hom_id_app_assoc]

/-- The explicit preimage formula for `TauCeti.classifyingSpaceHomotopyFunctorFullyFaithful`. -/
theorem classifyingSpaceHomotopyFunctorFullyFaithful_preimage {G H : GrpCat.{u}}
    (f : classifyingSpaceHomotopyFunctor.obj G ⟶ classifyingSpaceHomotopyFunctor.obj H) :
    classifyingSpaceHomotopyFunctorFullyFaithful.preimage f =
      classifyingSpaceHomotopyFunctorCompFundamentalGroupFunctorIso.inv.app G ≫
        PointedHomotopyCat.fundamentalGroupFunctor.map f ≫
        classifyingSpaceHomotopyFunctorCompFundamentalGroupFunctorIso.hom.app H :=
  (rfl)

/-- The classifying-space functor to the pointed homotopy category is full: every pointed homotopy
class of maps between Milnor classifying spaces is represented by the strict map of a group
homomorphism. -/
instance : classifyingSpaceHomotopyFunctor.{u}.Full :=
  classifyingSpaceHomotopyFunctorFullyFaithful.full

/-- The typeclass preimage `classifyingSpaceHomotopyFunctor.preimage f` agrees with the explicit
conjugation formula via `PointedHomotopyCat.fundamentalGroupFunctor`. -/
theorem classifyingSpaceHomotopyFunctor_preimage_eq {G H : GrpCat.{u}}
    (f : classifyingSpaceHomotopyFunctor.obj G ⟶ classifyingSpaceHomotopyFunctor.obj H) :
    classifyingSpaceHomotopyFunctor.preimage f =
      classifyingSpaceHomotopyFunctorCompFundamentalGroupFunctorIso.inv.app G ≫
        PointedHomotopyCat.fundamentalGroupFunctor.map f ≫
        classifyingSpaceHomotopyFunctorCompFundamentalGroupFunctorIso.hom.app H :=
  classifyingSpaceHomotopyFunctor.map_injective (by
    rw [Functor.map_preimage, ← classifyingSpaceHomotopyFunctorFullyFaithful_preimage,
      classifyingSpaceHomotopyFunctorFullyFaithful.map_preimage])

/-- **Unique isomorphism in `PointedHomotopyCat` realizing a prescribed isomorphism on `π₁`.**
Between two well-pointed aspherical spaces of CW type, every isomorphism `φ : π₁(X) ≅ π₁(Y)` is
induced by a unique isomorphism `X ≅ Y` in `PointedHomotopyCat`. -/
def pointedIsoOfIsAspherical {X Y : PointedHomotopyCat.{u}}
    [CWType X.as.carrier] [CWType Y.as.carrier]
    (hX : IsAspherical X.as.carrier X.as.basepoint)
    (hY : IsAspherical Y.as.carrier Y.as.basepoint)
    (hx : HasHomotopyExtensionProperty ({X.as.basepoint} : Set X.as.carrier))
    (hy : HasHomotopyExtensionProperty ({Y.as.basepoint} : Set Y.as.carrier))
    (φ : PointedHomotopyCat.fundamentalGroupFunctor.obj X ≅
      PointedHomotopyCat.fundamentalGroupFunctor.obj Y) :
    X ≅ Y :=
  let bijXY := fundamentalGroupFunctor_map_bijective_of_isAspherical hX hx
    (fun z n ↦ (hY.of_basepoint z).subsingleton_homotopyGroup n)
  let bijYX := fundamentalGroupFunctor_map_bijective_of_isAspherical hY hy
    (fun z n ↦ (hX.of_basepoint z).subsingleton_homotopyGroup n)
  let bijXX := fundamentalGroupFunctor_map_bijective_of_isAspherical hX hx
    (fun z n ↦ (hX.of_basepoint z).subsingleton_homotopyGroup n)
  let bijYY := fundamentalGroupFunctor_map_bijective_of_isAspherical hY hy
    (fun z n ↦ (hY.of_basepoint z).subsingleton_homotopyGroup n)
  { hom := (bijXY.surjective φ.hom).choose
    inv := (bijYX.surjective φ.inv).choose
    hom_inv_id := bijXX.injective <| by
      rw [PointedHomotopyCat.fundamentalGroupFunctor.map_comp,
        (bijXY.surjective φ.hom).choose_spec, (bijYX.surjective φ.inv).choose_spec,
        φ.hom_inv_id, PointedHomotopyCat.fundamentalGroupFunctor.map_id]
    inv_hom_id := bijYY.injective <| by
      rw [PointedHomotopyCat.fundamentalGroupFunctor.map_comp,
        (bijYX.surjective φ.inv).choose_spec, (bijXY.surjective φ.hom).choose_spec,
        φ.inv_hom_id, PointedHomotopyCat.fundamentalGroupFunctor.map_id] }

@[simp]
theorem fundamentalGroupFunctor_map_pointedIsoOfIsAspherical_hom {X Y : PointedHomotopyCat.{u}}
    [CWType X.as.carrier] [CWType Y.as.carrier]
    (hX : IsAspherical X.as.carrier X.as.basepoint)
    (hY : IsAspherical Y.as.carrier Y.as.basepoint)
    (hx : HasHomotopyExtensionProperty ({X.as.basepoint} : Set X.as.carrier))
    (hy : HasHomotopyExtensionProperty ({Y.as.basepoint} : Set Y.as.carrier))
    (φ : PointedHomotopyCat.fundamentalGroupFunctor.obj X ≅
      PointedHomotopyCat.fundamentalGroupFunctor.obj Y) :
    PointedHomotopyCat.fundamentalGroupFunctor.map
        (pointedIsoOfIsAspherical hX hY hx hy φ).hom =
      φ.hom :=
  ((fundamentalGroupFunctor_map_bijective_of_isAspherical hX hx
    (fun z n ↦ (hY.of_basepoint z).subsingleton_homotopyGroup n)).surjective φ.hom).choose_spec

@[simp]
theorem fundamentalGroupFunctor_map_pointedIsoOfIsAspherical_inv {X Y : PointedHomotopyCat.{u}}
    [CWType X.as.carrier] [CWType Y.as.carrier]
    (hX : IsAspherical X.as.carrier X.as.basepoint)
    (hY : IsAspherical Y.as.carrier Y.as.basepoint)
    (hx : HasHomotopyExtensionProperty ({X.as.basepoint} : Set X.as.carrier))
    (hy : HasHomotopyExtensionProperty ({Y.as.basepoint} : Set Y.as.carrier))
    (φ : PointedHomotopyCat.fundamentalGroupFunctor.obj X ≅
      PointedHomotopyCat.fundamentalGroupFunctor.obj Y) :
    PointedHomotopyCat.fundamentalGroupFunctor.map
        (pointedIsoOfIsAspherical hX hY hx hy φ).inv =
      φ.inv :=
  ((fundamentalGroupFunctor_map_bijective_of_isAspherical hY hy
    (fun z n ↦ (hX.of_basepoint z).subsingleton_homotopyGroup n)).surjective φ.inv).choose_spec

@[simp]
theorem fundamentalGroupFunctor_mapIso_pointedIsoOfIsAspherical {X Y : PointedHomotopyCat.{u}}
    [CWType X.as.carrier] [CWType Y.as.carrier]
    (hX : IsAspherical X.as.carrier X.as.basepoint)
    (hY : IsAspherical Y.as.carrier Y.as.basepoint)
    (hx : HasHomotopyExtensionProperty ({X.as.basepoint} : Set X.as.carrier))
    (hy : HasHomotopyExtensionProperty ({Y.as.basepoint} : Set Y.as.carrier))
    (φ : PointedHomotopyCat.fundamentalGroupFunctor.obj X ≅
      PointedHomotopyCat.fundamentalGroupFunctor.obj Y) :
    PointedHomotopyCat.fundamentalGroupFunctor.mapIso
        (pointedIsoOfIsAspherical hX hY hx hy φ) =
      φ :=
  Iso.ext (fundamentalGroupFunctor_map_pointedIsoOfIsAspherical_hom hX hY hx hy φ)

/-- A morphism `f : X ⟶ Y` between well-pointed aspherical spaces of CW type inducing `φ.hom` on
`π₁` equals `(pointedIsoOfIsAspherical hX hY hx hy φ).hom`. -/
theorem eq_pointedIsoOfIsAspherical_hom {X Y : PointedHomotopyCat.{u}}
    [CWType X.as.carrier] [CWType Y.as.carrier]
    (hX : IsAspherical X.as.carrier X.as.basepoint)
    (hY : IsAspherical Y.as.carrier Y.as.basepoint)
    (hx : HasHomotopyExtensionProperty ({X.as.basepoint} : Set X.as.carrier))
    (hy : HasHomotopyExtensionProperty ({Y.as.basepoint} : Set Y.as.carrier))
    (φ : PointedHomotopyCat.fundamentalGroupFunctor.obj X ≅
      PointedHomotopyCat.fundamentalGroupFunctor.obj Y)
    {f : X ⟶ Y} (hf : PointedHomotopyCat.fundamentalGroupFunctor.map f = φ.hom) :
    f = (pointedIsoOfIsAspherical hX hY hx hy φ).hom :=
  (fundamentalGroupFunctor_map_bijective_of_isAspherical hX hx
    (fun z n ↦ (hY.of_basepoint z).subsingleton_homotopyGroup n)).injective <|
    hf.trans (fundamentalGroupFunctor_map_pointedIsoOfIsAspherical_hom hX hY hx hy φ).symm

@[simp]
theorem pointedIsoOfIsAspherical_refl {X : PointedHomotopyCat.{u}} [CWType X.as.carrier]
    (hX : IsAspherical X.as.carrier X.as.basepoint)
    (hx : HasHomotopyExtensionProperty ({X.as.basepoint} : Set X.as.carrier)) :
    pointedIsoOfIsAspherical hX hX hx hx (Iso.refl _) = Iso.refl X :=
  Iso.ext (eq_pointedIsoOfIsAspherical_hom hX hX hx hx (Iso.refl _) (by simp)).symm

@[simp]
theorem pointedIsoOfIsAspherical_symm {X Y : PointedHomotopyCat.{u}}
    [CWType X.as.carrier] [CWType Y.as.carrier]
    (hX : IsAspherical X.as.carrier X.as.basepoint)
    (hY : IsAspherical Y.as.carrier Y.as.basepoint)
    (hx : HasHomotopyExtensionProperty ({X.as.basepoint} : Set X.as.carrier))
    (hy : HasHomotopyExtensionProperty ({Y.as.basepoint} : Set Y.as.carrier))
    (φ : PointedHomotopyCat.fundamentalGroupFunctor.obj X ≅
      PointedHomotopyCat.fundamentalGroupFunctor.obj Y) :
    (pointedIsoOfIsAspherical hX hY hx hy φ).symm =
      pointedIsoOfIsAspherical hY hX hy hx φ.symm :=
  Iso.ext <| eq_pointedIsoOfIsAspherical_hom hY hX hy hx φ.symm
    (fundamentalGroupFunctor_map_pointedIsoOfIsAspherical_inv hX hY hx hy φ)

@[simp]
theorem pointedIsoOfIsAspherical_trans {X Y Z : PointedHomotopyCat.{u}}
    [CWType X.as.carrier] [CWType Y.as.carrier] [CWType Z.as.carrier]
    (hX : IsAspherical X.as.carrier X.as.basepoint)
    (hY : IsAspherical Y.as.carrier Y.as.basepoint)
    (hZ : IsAspherical Z.as.carrier Z.as.basepoint)
    (hx : HasHomotopyExtensionProperty ({X.as.basepoint} : Set X.as.carrier))
    (hy : HasHomotopyExtensionProperty ({Y.as.basepoint} : Set Y.as.carrier))
    (hz : HasHomotopyExtensionProperty ({Z.as.basepoint} : Set Z.as.carrier))
    (φ : PointedHomotopyCat.fundamentalGroupFunctor.obj X ≅
      PointedHomotopyCat.fundamentalGroupFunctor.obj Y)
    (ψ : PointedHomotopyCat.fundamentalGroupFunctor.obj Y ≅
      PointedHomotopyCat.fundamentalGroupFunctor.obj Z) :
    pointedIsoOfIsAspherical hX hY hx hy φ ≪≫ pointedIsoOfIsAspherical hY hZ hy hz ψ =
      pointedIsoOfIsAspherical hX hZ hx hz (φ ≪≫ ψ) :=
  Iso.ext <| eq_pointedIsoOfIsAspherical_hom hX hZ hx hz (φ ≪≫ ψ) (by simp)

/-- **Unique isomorphism in `PointedHomotopyCat` between a well-pointed aspherical space of CW
type and Milnor's classifying space**, realizing a prescribed identification `eX : π₁(X) ≅ G`
compatibly with `classifyingSpaceHomotopyFunctorCompFundamentalGroupFunctorIso`. -/
def pointedIsoClassifyingSpace {X : PointedHomotopyCat.{u}} {G : GrpCat.{u}}
    [CWType X.as.carrier]
    (hX : IsAspherical X.as.carrier X.as.basepoint)
    (hx : HasHomotopyExtensionProperty ({X.as.basepoint} : Set X.as.carrier))
    (eX : PointedHomotopyCat.fundamentalGroupFunctor.obj X ≅ G) :
    X ≅ classifyingSpaceHomotopyFunctor.obj G :=
  pointedIsoOfIsAspherical hX
    (isEilenbergMacLaneSpaceOne_classifyingSpace G).isAspherical hx
    (hasHomotopyExtensionProperty_singleton_of_cwComplex (classifyingSpaceBasepoint G))
    (eX ≪≫ (classifyingSpaceHomotopyFunctorCompFundamentalGroupFunctorIso.app G).symm)

@[simp]
theorem fundamentalGroupFunctor_map_pointedIsoClassifyingSpace_hom {X : PointedHomotopyCat.{u}}
    {G : GrpCat.{u}} [CWType X.as.carrier]
    (hX : IsAspherical X.as.carrier X.as.basepoint)
    (hx : HasHomotopyExtensionProperty ({X.as.basepoint} : Set X.as.carrier))
    (eX : PointedHomotopyCat.fundamentalGroupFunctor.obj X ≅ G) :
    PointedHomotopyCat.fundamentalGroupFunctor.map
        (pointedIsoClassifyingSpace hX hx eX).hom =
      eX.hom ≫ classifyingSpaceHomotopyFunctorCompFundamentalGroupFunctorIso.inv.app G :=
  fundamentalGroupFunctor_map_pointedIsoOfIsAspherical_hom ..

@[simp]
theorem fundamentalGroupFunctor_map_pointedIsoClassifyingSpace_inv {X : PointedHomotopyCat.{u}}
    {G : GrpCat.{u}} [CWType X.as.carrier]
    (hX : IsAspherical X.as.carrier X.as.basepoint)
    (hx : HasHomotopyExtensionProperty ({X.as.basepoint} : Set X.as.carrier))
    (eX : PointedHomotopyCat.fundamentalGroupFunctor.obj X ≅ G) :
    PointedHomotopyCat.fundamentalGroupFunctor.map
        (pointedIsoClassifyingSpace hX hx eX).inv =
      classifyingSpaceHomotopyFunctorCompFundamentalGroupFunctorIso.hom.app G ≫ eX.inv :=
  fundamentalGroupFunctor_map_pointedIsoOfIsAspherical_inv ..

/-- A morphism `f : X ⟶ classifyingSpaceHomotopyFunctor.obj G` out of a well-pointed aspherical
space of CW type whose induced map on `π₁`, followed by
`classifyingSpaceHomotopyFunctorCompFundamentalGroupFunctorIso.hom.app G`, equals `eX.hom` is
`(pointedIsoClassifyingSpace hX hx eX).hom`. -/
theorem eq_pointedIsoClassifyingSpace_hom {X : PointedHomotopyCat.{u}} {G : GrpCat.{u}}
    [CWType X.as.carrier]
    (hX : IsAspherical X.as.carrier X.as.basepoint)
    (hx : HasHomotopyExtensionProperty ({X.as.basepoint} : Set X.as.carrier))
    (eX : PointedHomotopyCat.fundamentalGroupFunctor.obj X ≅ G)
    {f : X ⟶ classifyingSpaceHomotopyFunctor.obj G}
    (hf : PointedHomotopyCat.fundamentalGroupFunctor.map f ≫
      classifyingSpaceHomotopyFunctorCompFundamentalGroupFunctorIso.hom.app G = eX.hom) :
    f = (pointedIsoClassifyingSpace hX hx eX).hom :=
  eq_pointedIsoOfIsAspherical_hom (Y := classifyingSpaceHomotopyFunctor.obj G) hX
    (isEilenbergMacLaneSpaceOne_classifyingSpace G).isAspherical hx
    (hasHomotopyExtensionProperty_singleton_of_cwComplex (classifyingSpaceBasepoint G)) _
    (by
      apply (cancel_mono
        (classifyingSpaceHomotopyFunctorCompFundamentalGroupFunctorIso.hom.app G)).1
      simpa [Category.assoc] using hf)

end Classification

section Equivalence

/-- **Well-pointed aspherical spaces of CW type** as an `ObjectProperty` on `PointedHomotopyCat`:
the underlying space has CW type, is aspherical at its base point, and the base point singleton
satisfies the homotopy extension property. -/
def isWellPointedAsphericalCWType : ObjectProperty PointedHomotopyCat.{u} := fun X ↦
  CWType X.as.carrier ∧ IsAspherical X.as.carrier X.as.basepoint ∧
    HasHomotopyExtensionProperty ({X.as.basepoint} : Set X.as.carrier)

theorem isWellPointedAsphericalCWType_iff (X : PointedHomotopyCat.{u}) :
    isWellPointedAsphericalCWType X ↔
      CWType X.as.carrier ∧ IsAspherical X.as.carrier X.as.basepoint ∧
        HasHomotopyExtensionProperty ({X.as.basepoint} : Set X.as.carrier) :=
  Iff.rfl

instance (X : isWellPointedAsphericalCWType.{u}.FullSubcategory) : CWType X.obj.as.carrier :=
  ((isWellPointedAsphericalCWType_iff X.obj).1 X.property).1

/-- Every aspherical Hausdorff CW complex (at any base point) satisfies
`isWellPointedAsphericalCWType`. -/
theorem isWellPointedAsphericalCWType_of_cwComplex {X : PointedHomotopyCat.{u}}
    [T2Space X.as.carrier] [Topology.CWComplex (Set.univ : Set X.as.carrier)]
    (hX : IsAspherical X.as.carrier X.as.basepoint) :
    isWellPointedAsphericalCWType X :=
  ⟨inferInstance, hX, hasHomotopyExtensionProperty_singleton_of_cwComplex X.as.basepoint⟩

/-- Milnor's classifying space `classifyingSpaceHomotopyFunctor.obj G` belongs to
`isWellPointedAsphericalCWType`. -/
theorem isWellPointedAsphericalCWType_classifyingSpace (G : GrpCat.{u}) :
    isWellPointedAsphericalCWType (classifyingSpaceHomotopyFunctor.obj G) :=
  ⟨inferInstance, (isEilenbergMacLaneSpaceOne_classifyingSpace G).isAspherical,
    hasHomotopyExtensionProperty_singleton_of_cwComplex (classifyingSpaceBasepoint G)⟩

/-- Every cellular classifying space belongs to `isWellPointedAsphericalCWType`. -/
theorem isWellPointedAsphericalCWType_cellularClassifyingSpace {S : Type u}
    (R : Set (FreeGroup S)) :
    isWellPointedAsphericalCWType
      (PointedHomotopyCat.quotient.obj (cellularClassifyingSpaceBased R)) :=
  ⟨inferInstanceAs (CWType (cellularClassifyingSpace R)),
    (isEilenbergMacLaneSpaceOne_cellularClassifyingSpace R).isAspherical,
    hasHomotopyExtensionProperty_singleton_of_cwComplex
      (cellularClassifyingSpaceBasepoint R)⟩

/-- Every well-pointed aspherical space of CW type lies in the essential image of
`TauCeti.classifyingSpaceHomotopyFunctor`.

This inclusion is proper in general: for an uncountable index set `I`, `[0, 1]^I` based at `0` is
pointed-contractible (hence isomorphic to `classifyingSpace Unit` in `PointedHomotopyCat`), while
`{0}` is closed without being a `G_δ` set and therefore lacks the homotopy extension property by
Strøm's theorem on closed cofibrations (Strøm, *Note on cofibrations*, 1966). -/
theorem isWellPointedAsphericalCWType_le_essImage :
    isWellPointedAsphericalCWType.{u} ≤ classifyingSpaceHomotopyFunctor.{u}.essImage := by
  intro X hX
  have : CWType X.as.carrier := ((isWellPointedAsphericalCWType_iff X).1 hX).1
  exact ⟨PointedHomotopyCat.fundamentalGroupFunctor.obj X,
    ⟨(pointedIsoClassifyingSpace ((isWellPointedAsphericalCWType_iff X).1 hX).2.1
      ((isWellPointedAsphericalCWType_iff X).1 hX).2.2 (Iso.refl _)).symm⟩⟩

/-- **Equivalence between groups and well-pointed aspherical spaces of CW type.**
The classifying-space functor `GrpCat ⥤ isWellPointedAsphericalCWType.FullSubcategory` and the
fundamental-group functor `isWellPointedAsphericalCWType.FullSubcategory ⥤ GrpCat` form an explicit
adjoint equivalence of categories. Unlike `CategoryTheory.Equivalence.mk`, both unit and counit are
given directly and already satisfy the triangle identity: the unit is the inverse of
`classifyingSpaceHomotopyFunctorCompFundamentalGroupFunctorIso`, and the counit at `X` is the
unique pointed homotopy equivalence `B(π₁(X)) ≅ X` inducing the identity on `π₁`. -/
-- The functor projections must reduce to type the dependent unit and counit comparisons.
@[expose] def classifyingSpaceEquivalence :
    GrpCat.{u} ≌ isWellPointedAsphericalCWType.{u}.FullSubcategory where
  functor := isWellPointedAsphericalCWType.lift classifyingSpaceHomotopyFunctor
    isWellPointedAsphericalCWType_classifyingSpace
  inverse := isWellPointedAsphericalCWType.ι ⋙ PointedHomotopyCat.fundamentalGroupFunctor
  unitIso := classifyingSpaceHomotopyFunctorCompFundamentalGroupFunctorIso.symm
  counitIso := NatIso.ofComponents
    (fun X ↦ isWellPointedAsphericalCWType.isoMk
      (pointedIsoClassifyingSpace
        ((isWellPointedAsphericalCWType_iff X.obj).1 X.property).2.1
        ((isWellPointedAsphericalCWType_iff X.obj).1 X.property).2.2 (Iso.refl _)).symm)
    (fun {X Y} f ↦ by
      apply ObjectProperty.hom_ext
      -- Unfold the full-subcategory lift and `isoMk` projections so `fundamentalGroupFunctor.map`
      -- injectivity applies directly.
      change classifyingSpaceHomotopyFunctor.map
          (PointedHomotopyCat.fundamentalGroupFunctor.map f.hom) ≫
          (pointedIsoClassifyingSpace
            ((isWellPointedAsphericalCWType_iff Y.obj).1 Y.property).2.1
            ((isWellPointedAsphericalCWType_iff Y.obj).1 Y.property).2.2 (Iso.refl _)).inv =
        (pointedIsoClassifyingSpace
            ((isWellPointedAsphericalCWType_iff X.obj).1 X.property).2.1
            ((isWellPointedAsphericalCWType_iff X.obj).1 X.property).2.2 (Iso.refl _)).inv ≫
          f.hom
      apply (fundamentalGroupFunctor_map_bijective_classifyingSpace
        (PointedHomotopyCat.fundamentalGroupFunctor.obj X.obj) (Y := Y.obj)
        (fun z n ↦ (((isWellPointedAsphericalCWType_iff Y.obj).1
          Y.property).2.1.of_basepoint z).subsingleton_homotopyGroup n)).injective
      rw [PointedHomotopyCat.fundamentalGroupFunctor.map_comp,
        PointedHomotopyCat.fundamentalGroupFunctor.map_comp,
        fundamentalGroupFunctor_map_pointedIsoClassifyingSpace_inv,
        fundamentalGroupFunctor_map_pointedIsoClassifyingSpace_inv]
      simp only [Iso.refl_inv]
      exact classifyingSpaceHomotopyFunctorCompFundamentalGroupFunctorIso.hom.naturality
        (PointedHomotopyCat.fundamentalGroupFunctor.map f.hom))
  functor_unitIso_comp G := by
    apply ObjectProperty.hom_ext
    -- Unfold the full-subcategory lift and `NatIso.ofComponents` projections so injectivity on
    -- `π₁` reduces the triangle identity directly to naturality of `B ⋙ π₁ ≅ 𝟭`.
    change classifyingSpaceHomotopyFunctor.map
        (classifyingSpaceHomotopyFunctorCompFundamentalGroupFunctorIso.inv.app G) ≫
        (pointedIsoClassifyingSpace
          ((isWellPointedAsphericalCWType_iff _).1
            (isWellPointedAsphericalCWType_classifyingSpace G)).2.1
          ((isWellPointedAsphericalCWType_iff _).1
            (isWellPointedAsphericalCWType_classifyingSpace G)).2.2
          (Iso.refl _)).inv =
      𝟙 (classifyingSpaceHomotopyFunctor.obj G)
    apply (fundamentalGroupFunctor_map_bijective_classifyingSpace G
      (Y := classifyingSpaceHomotopyFunctor.obj G)
      (fun z n ↦ subsingleton_homotopyGroup_classifyingSpace G n z)).injective
    rw [PointedHomotopyCat.fundamentalGroupFunctor.map_comp,
      PointedHomotopyCat.fundamentalGroupFunctor.map_id,
      fundamentalGroupFunctor_map_pointedIsoClassifyingSpace_inv, Iso.refl_inv]
    have hnat := classifyingSpaceHomotopyFunctorCompFundamentalGroupFunctorIso.hom.naturality
      (classifyingSpaceHomotopyFunctorCompFundamentalGroupFunctorIso.inv.app G)
    exact hnat.trans
      (classifyingSpaceHomotopyFunctorCompFundamentalGroupFunctorIso.hom_inv_id_app G)

@[simp]
theorem classifyingSpaceEquivalence_functor :
    classifyingSpaceEquivalence.{u}.functor =
      isWellPointedAsphericalCWType.lift classifyingSpaceHomotopyFunctor
        isWellPointedAsphericalCWType_classifyingSpace :=
  (rfl)

@[simp]
theorem classifyingSpaceEquivalence_inverse :
    classifyingSpaceEquivalence.{u}.inverse =
      isWellPointedAsphericalCWType.ι ⋙ PointedHomotopyCat.fundamentalGroupFunctor :=
  (rfl)

@[simp]
theorem classifyingSpaceEquivalence_unitIso :
    classifyingSpaceEquivalence.{u}.unitIso =
      classifyingSpaceHomotopyFunctorCompFundamentalGroupFunctorIso.symm :=
  (rfl)

theorem classifyingSpaceEquivalence_counitIso_hom_app_hom
    (X : isWellPointedAsphericalCWType.{u}.FullSubcategory) :
    (classifyingSpaceEquivalence.counitIso.hom.app X).hom =
      (pointedIsoClassifyingSpace
        ((isWellPointedAsphericalCWType_iff X.obj).1 X.property).2.1
        ((isWellPointedAsphericalCWType_iff X.obj).1 X.property).2.2 (Iso.refl _)).inv :=
  (rfl)

theorem classifyingSpaceEquivalence_counitIso_inv_app_hom
    (X : isWellPointedAsphericalCWType.{u}.FullSubcategory) :
    (classifyingSpaceEquivalence.counitIso.inv.app X).hom =
      (pointedIsoClassifyingSpace
        ((isWellPointedAsphericalCWType_iff X.obj).1 X.property).2.1
        ((isWellPointedAsphericalCWType_iff X.obj).1 X.property).2.2 (Iso.refl _)).hom :=
  (rfl)

@[simp]
theorem fundamentalGroupFunctor_map_classifyingSpaceEquivalence_counitIso_hom_app
    (X : isWellPointedAsphericalCWType.{u}.FullSubcategory) :
    PointedHomotopyCat.fundamentalGroupFunctor.map
        (classifyingSpaceEquivalence.counitIso.hom.app X).hom =
      classifyingSpaceHomotopyFunctorCompFundamentalGroupFunctorIso.hom.app
        (PointedHomotopyCat.fundamentalGroupFunctor.obj X.obj) :=
  (fundamentalGroupFunctor_map_pointedIsoClassifyingSpace_inv
    ((isWellPointedAsphericalCWType_iff X.obj).1 X.property).2.1
    ((isWellPointedAsphericalCWType_iff X.obj).1 X.property).2.2 (Iso.refl _)).trans
    (Category.comp_id _)

@[simp]
theorem fundamentalGroupFunctor_map_classifyingSpaceEquivalence_counitIso_inv_app
    (X : isWellPointedAsphericalCWType.{u}.FullSubcategory) :
    PointedHomotopyCat.fundamentalGroupFunctor.map
        (classifyingSpaceEquivalence.counitIso.inv.app X).hom =
      classifyingSpaceHomotopyFunctorCompFundamentalGroupFunctorIso.inv.app
        (PointedHomotopyCat.fundamentalGroupFunctor.obj X.obj) :=
  (fundamentalGroupFunctor_map_pointedIsoClassifyingSpace_hom
    ((isWellPointedAsphericalCWType_iff X.obj).1 X.property).2.1
    ((isWellPointedAsphericalCWType_iff X.obj).1 X.property).2.2 (Iso.refl _)).trans
    (Category.id_comp _)

instance : (isWellPointedAsphericalCWType.lift classifyingSpaceHomotopyFunctor
    isWellPointedAsphericalCWType_classifyingSpace).IsEquivalence :=
  classifyingSpaceEquivalence.isEquivalence_functor

instance : (isWellPointedAsphericalCWType.{u}.ι ⋙
    PointedHomotopyCat.fundamentalGroupFunctor).IsEquivalence :=
  classifyingSpaceEquivalence.isEquivalence_inverse

end Equivalence

end TauCeti

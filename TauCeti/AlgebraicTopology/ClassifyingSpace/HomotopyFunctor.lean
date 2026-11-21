/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.EssentialImage
public import TauCeti.AlgebraicTopology.ClassifyingSpace.Comparison
public import TauCeti.AlgebraicTopology.ClassifyingSpace.Functoriality
public import TauCeti.AlgebraicTopology.Homotopy.PointedHomotopyCat
import TauCeti.AlgebraicTopology.ClassifyingSpace.Uniqueness
import TauCeti.AlgebraicTopology.EilenbergMacLane.HomotopyEquiv
import TauCeti.AlgebraicTopology.EilenbergMacLane.PointedMaps

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

Both models of the classifying space are well-pointed: their base points are `0`-cells of their
Hausdorff CW structures, so they have the homotopy extension property
(`TauCeti.hasHomotopyExtensionProperty_cellularClassifyingSpaceBasepoint`,
`TauCeti.hasHomotopyExtensionProperty_classifyingSpaceBasepoint`). Consequently the comparison
homotopy equivalence `TauCeti.cellularHomotopyEquivClassifyingSpace` upgrades to an isomorphism
`TauCeti.cellularHomotopyEquivClassifyingSpaceIso` in `PointedHomotopyCat` whose inverse is
pointed and induces `e⁻¹` on `π₁` with no base-point change.

From the general classification of pointed maps out of well-pointed aspherical spaces of CW type
(`TauCeti.IsAspherical.fundamentalGroupFunctor_map_bijective` in
`TauCeti.AlgebraicTopology.EilenbergMacLane.PointedMaps`), specializing to Milnor's classifying
space yields the categorical bijection for pointed maps out of `classifyingSpaceHomotopyFunctor`
(`TauCeti.fundamentalGroupFunctor_map_bijective_classifyingSpace`) and establishes that
`TauCeti.classifyingSpaceHomotopyFunctor` is **fully faithful**
(`TauCeti.classifyingSpaceHomotopyFunctorFullyFaithful`).

Specializing the pointed uniqueness isomorphism `TauCeti.IsAspherical.pointedHomotopyCatIso` from
`TauCeti.AlgebraicTopology.ClassifyingSpace.Uniqueness` shows that every well-pointed aspherical
space of CW type is canonically isomorphic in `PointedHomotopyCat` to `classifyingSpace G`
(`TauCeti.IsAspherical.pointedHomotopyCatIsoClassifyingSpace`), so it lies in the essential image of
`classifyingSpaceHomotopyFunctor`
(`TauCeti.IsAspherical.mem_essImage_classifyingSpaceHomotopyFunctor`). Conversely every object in
that essential image is aspherical and of CW type
(`TauCeti.isAspherical_of_mem_essImage_classifyingSpaceHomotopyFunctor`,
`TauCeti.cwType_of_mem_essImage_classifyingSpaceHomotopyFunctor`). Both halves are sharp with
respect to well-pointedness: without the homotopy extension property at the base point, an
aspherical space of CW type need not be pointed homotopy equivalent to a classifying space (for
example, the comb space based at a non-locally-contractible point), while an object in the
essential image need not be well-pointed (for example, `[0, 1]^ℝ` based at `0` is pointed
contractible, hence isomorphic to `classifyingSpace PUnit`, yet `{0}` is not `G_δ`).

## Main definitions

* `TauCeti.classifyingSpaceFunctor`: Milnor's classifying space as a functor to based spaces.
* `TauCeti.classifyingSpaceHomotopyFunctor`: the classifying space as a functor to the pointed
  homotopy category.
* `TauCeti.classifyingSpaceHomotopyFunctorCompFundamentalGroupFunctorIso`: the natural
  isomorphism `π₁ ∘ B ≅ 𝟭`.
* `TauCeti.cellularHomotopyEquivClassifyingSpaceBasedHom`: the comparison of the cellular model
  with Milnor's classifying space, as a based map.
* `TauCeti.cellularHomotopyEquivClassifyingSpaceIso`: pointed isomorphism comparing the cellular
  and simplicial models of the classifying space.
* `TauCeti.classifyingSpaceHomotopyFunctorFullyFaithful`: full faithfulness of
  `classifyingSpaceHomotopyFunctor`, with explicit `preimage` via `π₁`.
* `TauCeti.IsAspherical.pointedHomotopyCatIsoClassifyingSpace`: the unique isomorphism in
  `PointedHomotopyCat` from a well-pointed aspherical space of CW type to
  `classifyingSpaceHomotopyFunctor.obj G` realizing a given identification on `π₁`.

## Main results

* `TauCeti.fundamentalGroupFunctor_map_bijective_cellularClassifyingSpace`: pointed homotopy
  classes of maps out of a cellular classifying space into a space with no higher homotopy groups
  are classified by their effect on `π₁`.
* `TauCeti.quotient_map_eq_quotient_map_comp_cellularClassifyingSpace`: a pointed map from the
  cellular model realizing a homomorphism is pointed homotopic to the comparison of the two models
  followed by the strictly functorial map.
* `TauCeti.fundamentalGroupFunctor_map_bijective_classifyingSpace`: pointed homotopy classes of
  maps out of `classifyingSpaceHomotopyFunctor.obj G` into a space without higher homotopy groups
  are classified by `π₁`.
* `TauCeti.IsAspherical.mem_essImage_classifyingSpaceHomotopyFunctor`,
  `TauCeti.isAspherical_of_mem_essImage_classifyingSpaceHomotopyFunctor`,
  `TauCeti.cwType_of_mem_essImage_classifyingSpaceHomotopyFunctor`: characterization of the
  essential image of `classifyingSpaceHomotopyFunctor`.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Chapter 0 (Proposition 0.19)
  and Section 1.B (Theorem 1B.8 and Proposition 1B.9).
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

/-- The underlying space of `classifyingSpaceFunctor.obj G` has CW type. -/
instance instCWTypeClassifyingSpaceFunctorObj (G : GrpCat.{u}) :
    CWType (classifyingSpaceFunctor.obj G).carrier :=
  inferInstanceAs (CWType (classifyingSpace G))

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

/-- **The cellular and the simplicial classifying spaces are isomorphic in `PointedHomotopyCat`.**
For a presentation `e : PresentedGroup R ≃* G`, the forward morphism is the pointed homotopy class
of `cellularHomotopyEquivClassifyingSpaceBasedHom R e` (inducing `e` on `π₁`), and the inverse
induces `e⁻¹` with no base-point change. -/
def cellularHomotopyEquivClassifyingSpaceIso {G : GrpCat.{u}} (e : PresentedGroup R ≃* G) :
    PointedHomotopyCat.quotient.obj (cellularClassifyingSpaceBased R) ≅
      classifyingSpaceHomotopyFunctor.obj G :=
  PointedHomotopyCat.isoOfHomotopyEquiv
    (hasHomotopyExtensionProperty_cellularClassifyingSpaceBasepoint R)
    (hasHomotopyExtensionProperty_classifyingSpaceBasepoint G)
    (cellularHomotopyEquivClassifyingSpace R e)
    (cellularHomotopyEquivClassifyingSpace_toFun_basepoint R e)

/-- The forward morphism of `cellularHomotopyEquivClassifyingSpaceIso` is the pointed homotopy
class of `cellularHomotopyEquivClassifyingSpaceBasedHom`. -/
theorem cellularHomotopyEquivClassifyingSpaceIso_hom {G : GrpCat.{u}}
    (e : PresentedGroup R ≃* G) :
    (cellularHomotopyEquivClassifyingSpaceIso R e).hom =
      PointedHomotopyCat.quotient.map (cellularHomotopyEquivClassifyingSpaceBasedHom R e) :=
  PointedHomotopyCat.isoOfHomotopyEquiv_hom _ _ _ _

/-- The forward morphism of `cellularHomotopyEquivClassifyingSpaceIso` induces `e` on `π₁`, under
the identifications of both fundamental groups. -/
@[simp]
theorem fundamentalGroupFunctor_map_cellularHomotopyEquivClassifyingSpaceIso_hom
    {G : GrpCat.{u}} (e : PresentedGroup R ≃* G) :
    PointedHomotopyCat.fundamentalGroupFunctor.map
        (cellularHomotopyEquivClassifyingSpaceIso R e).hom =
      GrpCat.ofHom ((cellularClassifyingSpaceFundamentalGroupMulEquiv R).trans
        (e.trans (classifyingSpaceFundamentalGroupMulEquiv G).symm)).toMonoidHom := by
  rw [cellularHomotopyEquivClassifyingSpaceIso_hom]
  refine GrpCat.hom_ext <| MonoidHom.ext fun a ↦
    (classifyingSpaceFundamentalGroupMulEquiv G).injective ?_
  exact (classifyingSpaceFundamentalGroupMulEquiv_mapOfEq_cellularHomotopyEquivClassifyingSpace
    R e a).trans ((classifyingSpaceFundamentalGroupMulEquiv G).apply_symm_apply _).symm

/-- The inverse morphism of `cellularHomotopyEquivClassifyingSpaceIso` induces `e⁻¹` on `π₁`, under
the identifications of both fundamental groups. -/
@[simp]
theorem fundamentalGroupFunctor_map_cellularHomotopyEquivClassifyingSpaceIso_inv
    {G : GrpCat.{u}} (e : PresentedGroup R ≃* G) :
    PointedHomotopyCat.fundamentalGroupFunctor.map
        (cellularHomotopyEquivClassifyingSpaceIso R e).inv =
      GrpCat.ofHom ((classifyingSpaceFundamentalGroupMulEquiv G).trans
        (e.symm.trans (cellularClassifyingSpaceFundamentalGroupMulEquiv R).symm)).toMonoidHom := by
  let ψ := (cellularClassifyingSpaceFundamentalGroupMulEquiv R).trans
    (e.trans (classifyingSpaceFundamentalGroupMulEquiv G).symm)
  have hcomp := congrArg PointedHomotopyCat.fundamentalGroupFunctor.map
    (cellularHomotopyEquivClassifyingSpaceIso R e).inv_hom_id
  rw [CategoryTheory.Functor.map_comp,
    fundamentalGroupFunctor_map_cellularHomotopyEquivClassifyingSpaceIso_hom,
    CategoryTheory.Functor.map_id] at hcomp
  refine GrpCat.hom_ext <| MonoidHom.ext fun a ↦ ψ.injective ?_
  have ha := congrArg (fun f ↦ f.hom a) hcomp
  exact ha.trans (ψ.apply_symm_apply a).symm

end Cellular

section FunctorClassification

/-- **Pointed maps out of Milnor's classifying space are classified by `π₁`.** If the homotopy
groups of `Y` vanish from degree `2` on, at every point, then pointed homotopy classes
`classifyingSpace G → Y` correspond bijectively to homomorphisms `π₁(classifyingSpace G) ⟶ π₁(Y)`.
-/
theorem fundamentalGroupFunctor_map_bijective_classifyingSpace (G : GrpCat.{u})
    {Y : BasedTopologicalSpace.{u}}
    (hY : ∀ (y : Y.carrier) (n : ℕ), Subsingleton (π_ (n + 2) Y.carrier y)) :
    Function.Bijective (PointedHomotopyCat.fundamentalGroupFunctor.map
      (X := classifyingSpaceHomotopyFunctor.obj G) (Y := PointedHomotopyCat.quotient.obj Y)) :=
  IsAspherical.fundamentalGroupFunctor_map_bijective (X := classifyingSpaceFunctor.obj G)
    (isEilenbergMacLaneSpaceOne_classifyingSpace G).isAspherical
    (hasHomotopyExtensionProperty_classifyingSpaceBasepoint G) hY

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

/-- **Every well-pointed `K(G, 1)` of CW type is canonically isomorphic in `PointedHomotopyCat` to
Milnor's classifying space `classifyingSpace G`.** -/
def IsAspherical.pointedHomotopyCatIsoClassifyingSpace {G : GrpCat.{u}}
    {X : BasedTopologicalSpace.{u}} [CWType X.carrier] (hX : IsAspherical X.carrier X.basepoint)
    (hX_hep : HasHomotopyExtensionProperty ({X.basepoint} : Set X.carrier))
    (eX : FundamentalGroup X.carrier X.basepoint ≃* G) :
    PointedHomotopyCat.quotient.obj X ≅ classifyingSpaceHomotopyFunctor.obj G :=
  hX.pointedHomotopyCatIso (Y := classifyingSpaceFunctor.obj G)
    (isEilenbergMacLaneSpaceOne_classifyingSpace G).isAspherical hX_hep
    (hasHomotopyExtensionProperty_classifyingSpaceBasepoint G)
    (eX.trans (classifyingSpaceFundamentalGroupMulEquiv G).symm)

/-- The forward morphism of `IsAspherical.pointedHomotopyCatIsoClassifyingSpace` realizes `eX`
under the identification of `π₁(classifyingSpace G)` with `G`. -/
@[simp]
theorem IsAspherical.fundamentalGroupFunctor_map_pointedHomotopyCatIsoClassifyingSpace_hom
    {G : GrpCat.{u}} {X : BasedTopologicalSpace.{u}} [CWType X.carrier]
    (hX : IsAspherical X.carrier X.basepoint)
    (hX_hep : HasHomotopyExtensionProperty ({X.basepoint} : Set X.carrier))
    (eX : FundamentalGroup X.carrier X.basepoint ≃* G) :
    PointedHomotopyCat.fundamentalGroupFunctor.map
        (hX.pointedHomotopyCatIsoClassifyingSpace hX_hep eX).hom =
      GrpCat.ofHom (eX.trans (classifyingSpaceFundamentalGroupMulEquiv G).symm).toMonoidHom :=
  hX.fundamentalGroupFunctor_map_pointedHomotopyCatIso_hom (Y := classifyingSpaceFunctor.obj G)
    (isEilenbergMacLaneSpaceOne_classifyingSpace G).isAspherical hX_hep
    (hasHomotopyExtensionProperty_classifyingSpaceBasepoint G)
    (eX.trans (classifyingSpaceFundamentalGroupMulEquiv G).symm)

/-- The inverse morphism of `IsAspherical.pointedHomotopyCatIsoClassifyingSpace` realizes `eX⁻¹`
under the identification of `π₁(classifyingSpace G)` with `G`. -/
@[simp]
theorem IsAspherical.fundamentalGroupFunctor_map_pointedHomotopyCatIsoClassifyingSpace_inv
    {G : GrpCat.{u}} {X : BasedTopologicalSpace.{u}} [CWType X.carrier]
    (hX : IsAspherical X.carrier X.basepoint)
    (hX_hep : HasHomotopyExtensionProperty ({X.basepoint} : Set X.carrier))
    (eX : FundamentalGroup X.carrier X.basepoint ≃* G) :
    PointedHomotopyCat.fundamentalGroupFunctor.map
        (hX.pointedHomotopyCatIsoClassifyingSpace hX_hep eX).inv =
      GrpCat.ofHom ((classifyingSpaceFundamentalGroupMulEquiv G).trans eX.symm).toMonoidHom :=
  hX.fundamentalGroupFunctor_map_pointedHomotopyCatIso_inv (Y := classifyingSpaceFunctor.obj G)
    (isEilenbergMacLaneSpaceOne_classifyingSpace G).isAspherical hX_hep
    (hasHomotopyExtensionProperty_classifyingSpaceBasepoint G)
    (eX.trans (classifyingSpaceFundamentalGroupMulEquiv G).symm)

/-- **Every well-pointed aspherical space of CW type lies in the essential image of
`classifyingSpaceHomotopyFunctor`.** Well-pointedness cannot be dropped here (e.g. the comb space
based at a non-locally-contractible point), though the converse does not recover well-pointedness
(e.g. `[0, 1]^ℝ` based at `0` is pointed contractible while `{0}` fails the homotopy extension
property). -/
theorem IsAspherical.mem_essImage_classifyingSpaceHomotopyFunctor {X : BasedTopologicalSpace.{u}}
    [CWType X.carrier] (hX : IsAspherical X.carrier X.basepoint)
    (hX_hep : HasHomotopyExtensionProperty ({X.basepoint} : Set X.carrier)) :
    classifyingSpaceHomotopyFunctor.essImage (PointedHomotopyCat.quotient.obj X) :=
  ⟨GrpCat.of (FundamentalGroup X.carrier X.basepoint),
    ⟨(hX.pointedHomotopyCatIsoClassifyingSpace hX_hep (MulEquiv.refl _)).symm⟩⟩

/-- **Every object in the essential image of `classifyingSpaceHomotopyFunctor` is aspherical.** -/
theorem isAspherical_of_mem_essImage_classifyingSpaceHomotopyFunctor
    {X : BasedTopologicalSpace.{u}}
    (hX : classifyingSpaceHomotopyFunctor.essImage (PointedHomotopyCat.quotient.obj X)) :
    IsAspherical X.carrier X.basepoint := by
  obtain ⟨G, ⟨e⟩⟩ := hX
  exact (isEilenbergMacLaneSpaceOne_classifyingSpace G).isAspherical.of_homotopyEquiv
    (PointedHomotopyCat.homotopyEquivOfIso e) X.basepoint

/-- **Every object in the essential image of `classifyingSpaceHomotopyFunctor` has CW type.** -/
theorem cwType_of_mem_essImage_classifyingSpaceHomotopyFunctor
    {X : BasedTopologicalSpace.{u}}
    (hX : classifyingSpaceHomotopyFunctor.essImage (PointedHomotopyCat.quotient.obj X)) :
    CWType X.carrier := by
  obtain ⟨G, ⟨e⟩⟩ := hX
  exact (PointedHomotopyCat.homotopyEquivOfIso e).symm.cwType

end FunctorClassification

end TauCeti

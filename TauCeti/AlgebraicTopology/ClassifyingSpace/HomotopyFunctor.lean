/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ClassifyingSpace.Comparison
public import TauCeti.AlgebraicTopology.ClassifyingSpace.Functoriality
public import TauCeti.AlgebraicTopology.Homotopy.PointedHomotopyCat

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

The cellular model determines the induced maps up to pointed homotopy. Out of the
cellular classifying space `TauCeti.cellularClassifyingSpace R` of a presentation, pointed homotopy
classes of maps to a space without higher homotopy groups are exactly the homomorphisms of
fundamental groups (`TauCeti.cellularClassifyingSpace_bijective_fundamentalGroupFunctor_map`).
Consequently, for a presentation `e : PresentedGroup R ≃* G` and `φ : G →* H`, every pointed map
from the cellular model of `G` to `classifyingSpace H` that induces `φ` is pointed homotopic to
the comparison map of `TauCeti.cellularHomotopyEquivClassifyingSpace` followed by the map
`classifyingSpaceMap φ` (`TauCeti.cellularClassifyingSpace_quotient_map_eq_quotient_map_comp`).

## Main definitions

* `TauCeti.classifyingSpaceFunctor`: Milnor's classifying space as a functor to based spaces.
* `TauCeti.classifyingSpaceHomotopyFunctor`: the classifying space as a functor to the pointed
  homotopy category.
* `TauCeti.classifyingSpaceHomotopyFunctorCompFundamentalGroupFunctorIso`: the natural
  isomorphism `π₁ ∘ B ≅ 𝟭`.

## Main results

* `TauCeti.cellularClassifyingSpace_bijective_fundamentalGroupFunctor_map`: pointed homotopy
  classes of maps out of a cellular classifying space are classified by their effect on `π₁`.
* `TauCeti.cellularClassifyingSpace_quotient_map_eq_quotient_map_comp`: a pointed map from the
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

/-- Based maps out of the cellular classifying space into a space without higher homotopy groups
that induce the same homomorphism of fundamental groups have the same pointed homotopy class. -/
private theorem cellularClassifyingSpace_quotient_map_eq {Y : BasedTopologicalSpace.{u}}
    (hY : ∀ (y : Y.carrier) (n : ℕ), Subsingleton (π_ (n + 2) Y.carrier y))
    {f g : (⟨cellularClassifyingSpace R, cellularClassifyingSpaceBasepoint R⟩ :
      BasedTopologicalSpace.{u}) ⟶ Y}
    (h : BasedTopologicalSpace.fundamentalGroupFunctor.map f =
      BasedTopologicalSpace.fundamentalGroupFunctor.map g) :
    PointedHomotopyCat.quotient.map f = PointedHomotopyCat.quotient.map g :=
  (PointedHomotopyCat.quotient_map_eq_iff f g).2
    (homotopicRel_of_mapOfEq_eq_cellularClassifyingSpace R hY f.map_basepoint g.map_basepoint
      (congrArg GrpCat.Hom.hom h))

/-- **Pointed maps out of a cellular classifying space are classified by `π₁`.** If the homotopy
groups of `Y` vanish from degree `2` on, at every point, then a pointed homotopy class of maps from
the cellular classifying space `cellularClassifyingSpace R` to `Y` is determined by the homomorphism
it induces on fundamental groups, and every homomorphism is induced by such a class. -/
theorem cellularClassifyingSpace_bijective_fundamentalGroupFunctor_map
    {Y : BasedTopologicalSpace.{u}}
    (hY : ∀ (y : Y.carrier) (n : ℕ), Subsingleton (π_ (n + 2) Y.carrier y)) :
    Function.Bijective (PointedHomotopyCat.fundamentalGroupFunctor.map
      (X := PointedHomotopyCat.quotient.obj
        ⟨cellularClassifyingSpace R, cellularClassifyingSpaceBasepoint R⟩)
      (Y := PointedHomotopyCat.quotient.obj Y)) := by
  refine ⟨fun a b hab ↦ ?_, fun ψ ↦ ?_⟩
  · obtain ⟨f, rfl⟩ := PointedHomotopyCat.quotient.map_surjective a
    obtain ⟨g, rfl⟩ := PointedHomotopyCat.quotient.map_surjective b
    exact cellularClassifyingSpace_quotient_map_eq R hY hab
  · obtain ⟨f, hf, hfψ⟩ := exists_mapOfEq_cellularClassifyingSpace R
      (fun k hk ↦ by
        obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hk
        exact hY _ n) ψ.hom
    exact ⟨PointedHomotopyCat.quotient.map ⟨f, hf⟩, GrpCat.hom_ext hfψ⟩

/-- **The map induced by a homomorphism is determined up to pointed homotopy.** Let
`e : PresentedGroup R ≃* G` be a presentation and `φ : G ⟶ H`. Every pointed map from the cellular
classifying space of `R` to `classifyingSpace H` that induces `φ` under the identifications of both
fundamental groups is pointed homotopic to the comparison map of
`cellularHomotopyEquivClassifyingSpace R e` followed by `classifyingSpaceMap φ`. In the pointed
homotopy category the right-hand side is the comparison map followed by
`classifyingSpaceHomotopyFunctor.map φ`. -/
theorem cellularClassifyingSpace_quotient_map_eq_quotient_map_comp {G H : GrpCat.{u}}
    (e : PresentedGroup R ≃* G) (φ : G ⟶ H)
    (f : (⟨cellularClassifyingSpace R, cellularClassifyingSpaceBasepoint R⟩ :
      BasedTopologicalSpace.{u}) ⟶ classifyingSpaceFunctor.obj H)
    (hf : ∀ a, classifyingSpaceFundamentalGroupMulEquiv H
        (FundamentalGroup.mapOfEq f.toContinuousMap f.map_basepoint a) =
      φ.hom (e (cellularClassifyingSpaceFundamentalGroupMulEquiv R a))) :
    PointedHomotopyCat.quotient.map f =
      PointedHomotopyCat.quotient.map
        ((⟨(cellularHomotopyEquivClassifyingSpace R e).toFun,
            cellularHomotopyEquivClassifyingSpace_toFun_basepoint R e⟩ :
            (⟨cellularClassifyingSpace R, cellularClassifyingSpaceBasepoint R⟩ :
              BasedTopologicalSpace.{u}) ⟶ classifyingSpaceFunctor.obj G) ≫
          classifyingSpaceFunctor.map φ) := by
  refine cellularClassifyingSpace_quotient_map_eq R
    (fun y n ↦ subsingleton_homotopyGroup_classifyingSpace H n y) ?_
  rw [Functor.map_comp]
  refine GrpCat.hom_ext <| MonoidHom.ext fun a ↦
    (classifyingSpaceFundamentalGroupMulEquiv H).injective ?_
  rw [GrpCat.hom_comp, MonoidHom.comp_apply, BasedTopologicalSpace.fundamentalGroupFunctor_map_hom,
    BasedTopologicalSpace.fundamentalGroupFunctor_map_hom,
    BasedTopologicalSpace.fundamentalGroupFunctor_map_hom]
  -- Both sides are `φ ∘ e` under the identifications: the comparison induces `e`, and the strict
  -- map induces `φ`.
  exact (hf a).trans <| (congrArg φ.hom
    (classifyingSpaceFundamentalGroupMulEquiv_mapOfEq_cellularHomotopyEquivClassifyingSpace R e
      a).symm).trans (φ.hom.classifyingSpaceFundamentalGroupMulEquiv_mapOfEq _).symm

end Cellular

end TauCeti

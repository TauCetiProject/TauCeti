/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Unramified.Diagonal
public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Pointed étale neighbourhoods

Étale algebras with a map to a fixed commutative algebra form the indexing category for strict
henselization.

For `R : Type u` and `Ω : Type v`, source algebras live in `Type (max u v)`.
The target is lifted to this universe, so the base algebra and tensor-product refinements belong
to the same category even when the base and target have different universes.

## References

* Stacks Project, Tag 04GW.
* Taylor Dupuy, Thomas Tucker, and Zhuoran Wang, pcfawd-formalization at `9a20b3f`,
  `StrictHenselizationConstruction.lean`, `PointedEtaleNeighborhood`.
-/

public section

open CategoryTheory TensorProduct

universe u v

namespace TauCeti.StrictHenselization

variable (R : Type u) (Ω : Type v) [CommRing R] [CommRing Ω] [Algebra R Ω]

/-- An étale algebra equipped with a point valued in the universe lift of `Ω`. -/
def IsPointedNeighbourhood : ObjectProperty (Over (CommAlgCat.of R (ULift.{u} Ω))) :=
  fun point ↦ Algebra.Etale R point.left

/-- The category of pointed étale neighbourhoods. -/
abbrev Neighbourhood := (IsPointedNeighbourhood R Ω).FullSubcategory

/-- The defining property of a pointed neighbourhood. -/
@[simp]
theorem isPointedNeighbourhood_iff (point : Over (CommAlgCat.of R (ULift.{u} Ω))) :
    IsPointedNeighbourhood R Ω point ↔ Algebra.Etale R point.left :=
  Iff.rfl

/-- Pointed neighbourhoods agree when their source algebras and point maps agree. -/
@[ext]
theorem Neighbourhood.ext (first second : Neighbourhood R Ω)
    (hleft : first.obj.left = second.obj.left)
    (hpoint : HEq first.obj.hom.hom second.obj.hom.hom) : first = second := by
  cases first with
  | mk firstObj firstProperty =>
    cases second with
    | mk secondObj secondProperty =>
      cases firstObj with
      | mk firstLeft firstRight firstHom =>
        cases secondObj with
        | mk secondLeft secondRight secondHom =>
          have hright : firstRight = secondRight := Subsingleton.elim _ _
          cases hright
          cases hleft
          have hmap : firstHom.hom = secondHom.hom := eq_of_heq hpoint
          have hhom : firstHom = secondHom := CommAlgCat.hom_ext hmap
          cases hhom
          rfl

/-- The base algebra with its given point is a pointed étale neighbourhood. -/
private def base : Neighbourhood R Ω :=
  ⟨Over.mk (CommAlgCat.ofHom
    ((Algebra.ofId R (ULift.{u} Ω)).comp ULift.algEquiv.toAlgHom)),
    Algebra.Etale.of_equiv (ULift.algEquiv (R := R) (A := R)).symm⟩

/-- Tensor products provide common targets of pointed étale neighbourhoods. -/
private theorem exists_common_target (first second : Neighbourhood R Ω) :
    ∃ target : Neighbourhood R Ω,
      Nonempty (first ⟶ target) ∧ Nonempty (second ⟶ target) := by
  let : Algebra.Etale R first.obj.left := first.property
  let : Algebra.Etale R second.obj.left := second.property
  let point := Algebra.TensorProduct.productMap first.obj.hom.hom second.obj.hom.hom
  let target : Neighbourhood R Ω :=
    ⟨Over.mk (CommAlgCat.ofHom point),
      Algebra.Etale.comp R first.obj.left (first.obj.left ⊗[R] second.obj.left)⟩
  refine ⟨target, ⟨ObjectProperty.homMk (Over.homMk
    (CommAlgCat.ofHom Algebra.TensorProduct.includeLeft) ?_)⟩,
    ⟨ObjectProperty.homMk (Over.homMk
    (CommAlgCat.ofHom Algebra.TensorProduct.includeRight) ?_)⟩⟩
  · ext element
    simp [target, point]
  · ext element
    simp [target, point]

/-- Parallel maps become equal after a pointed étale refinement. -/
private theorem parallel_equalization {first second : Neighbourhood R Ω}
    (left right : first ⟶ second) :
    ∃ (target : Neighbourhood R Ω) (refinement : second ⟶ target),
      left ≫ refinement = right ≫ refinement := by
  let leftMap := left.hom.left.hom
  let rightMap := right.hom.left.hom
  let point := second.obj.hom.hom
  let diagonal := Algebra.TensorProduct.productMap leftMap rightMap
  let : Algebra.Etale R first.obj.left := first.property
  let : Algebra.Etale R second.obj.left := second.property
  obtain ⟨idem, hidem, hkernel⟩ :=
    TauCeti.Algebra.FormallyUnramified.exists_isIdempotentElem_ker_lmul_eq_span R first.obj.left
  have hagree : point.comp leftMap = point.comp rightMap := by
    exact congrArg CommAlgCat.Hom.hom (left.hom.w.trans right.hom.w.symm)
  have hproduct : point.comp diagonal =
      (point.comp leftMap).comp (Algebra.TensorProduct.lmul' R) := by
    ext element
    · simp [diagonal]
    · simpa [diagonal] using DFunLike.congr_fun hagree.symm element
  have hzero : point (diagonal idem) = 0 := by
    have hmem : Algebra.TensorProduct.lmul' R idem = 0 :=
      RingHom.mem_ker.mp (hkernel ▸ Ideal.mem_span_singleton_self idem)
    simpa only [AlgHom.comp_apply, hmem, map_zero] using DFunLike.congr_fun hproduct idem
  have hunit : IsUnit (point (1 - diagonal idem)) := by
    rw [map_sub, map_one, hzero, sub_zero]
    exact isUnit_one
  let localized := Localization.Away (1 - diagonal idem)
  let lifted : localized →ₐ[R] ULift.{u} Ω :=
    IsLocalization.Away.liftAlgHom (1 - diagonal idem) hunit
  let target : Neighbourhood R Ω :=
    ⟨Over.mk (CommAlgCat.ofHom lifted), inferInstanceAs (Algebra.Etale R localized)⟩
  let refinementMap : second.obj.left →ₐ[R] localized :=
    IsScalarTower.toAlgHom R second.obj.left localized
  have hrefines : CommAlgCat.ofHom refinementMap ≫ CommAlgCat.ofHom lifted =
      second.obj.hom := by
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro element
    exact IsLocalization.Away.lift_eq (S := localized) _ hunit element
  refine ⟨target, ObjectProperty.homMk (Over.homMk
    (CommAlgCat.ofHom refinementMap) hrefines), ?_⟩
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  apply CommAlgCat.hom_ext
  exact TauCeti.Algebra.FormallyUnramified.comp_eq_comp_of_isUnit_one_sub_productMap
    hidem hkernel.le leftMap rightMap refinementMap
    (IsLocalization.Away.algebraMap_isUnit _)

/-- The pointed étale neighbourhood category is filtered. -/
@[stacks 04GW "the category is filtered"]
instance neighbourhood_isFiltered : IsFiltered (Neighbourhood R Ω) where
  cocone_objs first second := by
    obtain ⟨target, ⟨left⟩, ⟨right⟩⟩ := exists_common_target R Ω first second
    exact ⟨target, left, right, trivial⟩
  cocone_maps := fun {_ _} left right ↦ parallel_equalization R Ω left right
  nonempty := ⟨base R Ω⟩

end TauCeti.StrictHenselization

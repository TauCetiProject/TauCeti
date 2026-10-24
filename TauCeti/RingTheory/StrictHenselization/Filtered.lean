/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.StrictHenselization.Neighbourhood
public import TauCeti.RingTheory.Unramified.Diagonal
public import Mathlib.CategoryTheory.Filtered.Basic

/-!
# Filtered pointed étale neighbourhoods

Tensor products give common refinements of pointed étale algebras. The unramified diagonal
and localization at an idempotent equalize parallel pointed maps.

## References

* Stacks Project, Tag 04GW.
* Tau Ceti, `TauCeti.RingTheory.Henselization.Filtered`, for the tensor-product and
  idempotent-localization filteredness method.
* Taylor Dupuy, Thomas Tucker, and Zhuoran Wang, pcfawd-formalization at `9a20b3f`,
  `StrictHenselizationConstruction.lean`, `PointedEtaleNeighborhood`.
-/

public section

open CategoryTheory TensorProduct

universe u v

namespace TauCeti.StrictHenselization

variable (R : Type u) (Ω : Type v) [CommRing R] [CommRing Ω] [Algebra R Ω]

/-- The base algebra with its given point is a pointed étale neighbourhood. -/
private def base : Neighbourhood R Ω :=
  ⟨Over.mk (CommAlgCat.ofHom
    ((Algebra.ofId R (ULift.{u} Ω)).comp ULift.algEquiv.toAlgHom)),
    (isPointedNeighbourhood_iff R Ω _).mpr
      (Algebra.Etale.of_equiv (ULift.algEquiv (R := R) (A := R)).symm)⟩

/-- Tensor products provide common targets of pointed étale neighbourhoods. -/
private theorem exists_common_target (first second : Neighbourhood R Ω) :
    ∃ target : Neighbourhood R Ω,
      Nonempty (first ⟶ target) ∧ Nonempty (second ⟶ target) := by
  let : Algebra.Etale R first.obj.left := (isPointedNeighbourhood_iff R Ω _).mp first.property
  let : Algebra.Etale R second.obj.left := (isPointedNeighbourhood_iff R Ω _).mp second.property
  let point := Algebra.TensorProduct.productMap first.obj.hom.hom second.obj.hom.hom
  let target : Neighbourhood R Ω :=
    ⟨Over.mk (CommAlgCat.ofHom point),
      (isPointedNeighbourhood_iff R Ω _).mpr
        (Algebra.Etale.comp R first.obj.left (first.obj.left ⊗[R] second.obj.left))⟩
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
  let : Algebra.Etale R first.obj.left := (isPointedNeighbourhood_iff R Ω _).mp first.property
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
  obtain ⟨target, refinement, hunit⟩ := Neighbourhood.exists_refinement_isUnit R Ω second (1 - diagonal idem) hunit
  refine ⟨target, refinement, ?_⟩
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  apply CommAlgCat.hom_ext
  exact TauCeti.Algebra.FormallyUnramified.comp_eq_comp_of_isUnit_one_sub_productMap
    hidem hkernel.le leftMap rightMap refinement.hom.left.hom hunit

/-- The pointed étale neighbourhood category is filtered. -/
@[stacks 04GW "the category is filtered"]
instance neighbourhood_isFiltered : IsFiltered (Neighbourhood R Ω) where
  cocone_objs first second := by
    obtain ⟨target, ⟨left⟩, ⟨right⟩⟩ := exists_common_target R Ω first second
    exact ⟨target, left, right, trivial⟩
  cocone_maps := fun {_ _} left right ↦ parallel_equalization R Ω left right
  nonempty := ⟨base R Ω⟩

end TauCeti.StrictHenselization

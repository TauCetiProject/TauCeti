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
private noncomputable def base : Neighbourhood R Ω :=
  haveI : Algebra.Etale R (ULift.{max u v} R) :=
    Algebra.Etale.of_equiv (ULift.algEquiv (R := R) (A := R)).symm
  Neighbourhood.mk' (ULift.{max u v} R) ((Algebra.ofId R Ω).comp ULift.algEquiv.toAlgHom)

/-- Tensor products provide common targets of pointed étale neighbourhoods. -/
private theorem exists_common_target (first second : Neighbourhood R Ω) :
    ∃ target : Neighbourhood R Ω,
      Nonempty (first ⟶ target) ∧ Nonempty (second ⟶ target) := by
  have : Algebra.Etale R (first.obj.left ⊗[R] second.obj.left) :=
    Algebra.Etale.comp R first.obj.left _
  let target := Neighbourhood.mk' (first.obj.left ⊗[R] second.obj.left)
    (Algebra.TensorProduct.productMap first.point second.point)
  refine ⟨target, ⟨Neighbourhood.homMk' Algebra.TensorProduct.includeLeft ?_⟩,
    ⟨Neighbourhood.homMk' Algebra.TensorProduct.includeRight ?_⟩⟩
  · rw [Neighbourhood.point_mk']
    exact Algebra.TensorProduct.productMap_left first.point second.point
  · rw [Neighbourhood.point_mk']
    exact Algebra.TensorProduct.productMap_right first.point second.point

/-- Parallel maps become equal after a pointed étale refinement. -/
private theorem parallel_equalization {first second : Neighbourhood R Ω}
    (left right : first ⟶ second) :
    ∃ (target : Neighbourhood R Ω) (refinement : second ⟶ target),
      left ≫ refinement = right ≫ refinement := by
  obtain ⟨idem, hidem, hkernel⟩ :=
    TauCeti.Algebra.FormallyUnramified.exists_isIdempotentElem_ker_lmul_eq_span R first.obj.left
  have hzero := Algebra.TensorProduct.map_productMap_eq_zero_of_comp_eq
    (RingHom.mem_ker.mp (hkernel ▸ Ideal.mem_span_singleton_self idem)) second.point
    ((Neighbourhood.point_comp_hom left).trans (Neighbourhood.point_comp_hom right).symm)
  obtain ⟨target, refinement, hunit⟩ := Neighbourhood.exists_refinement_isUnit second
    (1 - Algebra.TensorProduct.productMap left.hom.left.hom right.hom.left.hom idem)
    (by rw [map_sub, map_one, hzero, sub_zero]; exact isUnit_one)
  refine ⟨target, refinement, Neighbourhood.hom_ext ?_⟩
  exact TauCeti.Algebra.FormallyUnramified.comp_eq_comp_of_isUnit_one_sub_productMap
    hidem hkernel.le left.hom.left.hom right.hom.left.hom refinement.hom.left.hom hunit

/-- The pointed étale neighbourhood category is filtered. -/
@[stacks 04GW "the category is filtered"]
instance neighbourhood_isFiltered : IsFiltered (Neighbourhood R Ω) where
  cocone_objs first second := by
    obtain ⟨target, ⟨left⟩, ⟨right⟩⟩ := exists_common_target R Ω first second
    exact ⟨target, left, right, trivial⟩
  cocone_maps := fun {_ _} left right ↦ parallel_equalization R Ω left right
  nonempty := ⟨base R Ω⟩

end TauCeti.StrictHenselization

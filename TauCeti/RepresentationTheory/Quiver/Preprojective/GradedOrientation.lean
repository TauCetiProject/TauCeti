/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Preprojective.Grading
public import TauCeti.RepresentationTheory.Quiver.Preprojective.Orientation

/-!
# Orientation comparisons preserve path length

The existing isomorphism between preprojective algebras of two orientations is built from a
doubled-quiver identification and arrow rescalings. These operations preserve path length, so the
orientation comparison sends each homogeneous quotient class to one of the same degree. This is
the algebra-level input for comparing graded constructions, including Koszul resolutions, across
orientations.

## Main results

* `TauCeti.reorientDoubledEquiv_mem_grade`: the doubled-quiver comparison identifies each
  homogeneous path-length piece in both directions.
* `TauCeti.reorientPreprojectiveAlgebraEquiv_mem_preprojectiveGrade`: the orientation comparison
  identifies each homogeneous quotient piece in both directions.

## References

The local preprojective relations and orientation comparison follow Crawley-Boevey,
*Quiver algebras, weighted projective lines, and the Deligne--Simpson problem*, Section 1.
-/

public section

namespace TauCeti

open _root_.Quiver PathAlgebra

universe u v w

section Doubled

variable (k : Type w) {Q : Type u} [CommSemiring k] [Quiver.{v} Q] [Finite Q]
  (σ : ∀ ⦃i j : Q⦄, (i ⟶ j) → Bool)

/-- **The doubled-quiver comparison identifies path-length pieces.** Both prefunctors map each
arrow to one arrow, so the path-algebra equivalence and its inverse preserve degree. -/
@[simp]
theorem reorientDoubledEquiv_mem_grade {n : ℕ}
    {x : pathAlgebra k (Symmetrify (Reorient Q σ))} :
    reorientDoubledEquiv k σ x ∈ PathAlgebra.grade k (Symmetrify Q) n ↔
      x ∈ PathAlgebra.grade k (Symmetrify (Reorient Q σ)) n := by
  constructor
  · intro hx
    have h : (reorientDoubledEquiv k σ).symm (reorientDoubledEquiv k σ x) ∈
        PathAlgebra.grade k (Symmetrify (Reorient Q σ)) n := by
      rw [← PathAlgebra.gradeBy_const_one] at hx ⊢
      rw [reorientDoubledEquiv_symm_apply]
      exact PathAlgebra.mapAlgHom_mem_gradeBy k (reorientSymmetrifyInv σ)
        ((reorientSymmetrifyInv σ).obj_bijective_of_comp_eq_id (reorientSymmetrify σ)
          (reorientSymmetrifyInv_comp_reorientSymmetrify σ)
          (reorientSymmetrify_comp_reorientSymmetrifyInv σ)) (fun {_ _} _ => (1 : ℕ)) hx
    simpa only [AlgEquiv.symm_apply_apply] using h
  · intro hx
    rw [← PathAlgebra.gradeBy_const_one] at hx ⊢
    rw [reorientDoubledEquiv_apply]
    exact PathAlgebra.mapAlgHom_mem_gradeBy k (reorientSymmetrify σ)
      ((reorientSymmetrify σ).obj_bijective_of_comp_eq_id (reorientSymmetrifyInv σ)
        (reorientSymmetrify_comp_reorientSymmetrifyInv σ)
        (reorientSymmetrifyInv_comp_reorientSymmetrify σ)) (fun {_ _} _ => (1 : ℕ)) hx

end Doubled

variable (k : Type w) {Q : Type u} [CommRing k] [Quiver.{v} Q] [Fintype Q]
  [∀ i j : Q, Fintype (i ⟶ j)]
  (σ : ∀ ⦃i j : Q⦄, (i ⟶ j) → Bool)

/-- **The orientation comparison identifies the path-length grading.** A quotient class has
degree `n` exactly when its image in the original orientation has degree `n`. This is kept as an
explicit characterization since `mem_preprojectiveGrade_iff` already supplies the simp normal
form for grade membership. -/
theorem reorientPreprojectiveAlgebraEquiv_mem_preprojectiveGrade {n : ℕ}
    {x : preprojectiveAlgebra k (Reorient Q σ)} :
    reorientPreprojectiveAlgebraEquiv k σ x ∈ preprojectiveGrade k Q n ↔
      x ∈ preprojectiveGrade k (Reorient Q σ) n := by
  constructor
  · intro hx
    obtain ⟨y, hy, hxy⟩ := (mem_preprojectiveGrade_iff k Q).1 hx
    let c := doubledLabelling k fun _ _ a => reorientSign k σ a
    let z := (reorientDoubledEquiv k σ).symm (rescale c y)
    have hz : z ∈ PathAlgebra.grade k (Symmetrify (Reorient Q σ)) n := by
      apply (reorientDoubledEquiv_mem_grade k σ).1
      simpa only [z, AlgEquiv.apply_symm_apply] using PathAlgebra.rescale_mem_grade c hy
    have hzz : preprojectiveMk k (Reorient Q σ) z = x := by
      apply (reorientPreprojectiveAlgebraEquiv k σ).injective
      have hmap : reorientDoubledEquiv k σ z = rescale c y := by
        exact AlgEquiv.apply_symm_apply _ _
      rw [reorientPreprojectiveAlgebraEquiv_preprojectiveMk]
      rw [hmap,
        rescale_doubledLabelling_rescale_doubledLabelling k _ _ (fun _ _ a => by
          by_cases ha : σ a
          · rw [reorientSign_of_true k ha]
            simp
          · rw [reorientSign_of_false k ha]
            simp)]
      exact hxy
    rw [← hzz]
    exact preprojectiveMk_mem_preprojectiveGrade k (Reorient Q σ) hz
  · intro hx
    obtain ⟨y, hy, hxy⟩ := (mem_preprojectiveGrade_iff k (Reorient Q σ)).1 hx
    rw [← hxy, reorientPreprojectiveAlgebraEquiv_preprojectiveMk]
    exact preprojectiveMk_mem_preprojectiveGrade k Q
      (PathAlgebra.rescale_mem_grade _ ((reorientDoubledEquiv_mem_grade k σ).2 hy))

end TauCeti

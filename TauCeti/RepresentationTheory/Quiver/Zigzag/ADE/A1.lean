/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Zigzag.Componentwise.Grading
public import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# The graded Cartan entry of the one-vertex zigzag algebra

The zigzag algebra of the one-vertex graph is the dual numbers, with its infinitesimal generator
in degree two. Its unique vertex idempotent is the unit, so its sole graded Cartan entry is the
Hilbert polynomial of the algebra. This file computes that entry from the grading of the public
componentwise zigzag algebra, including the exceptional `A₁` convention.

See Huerfano--Khovanov, *A category for the adjoint representation*, Section 3, for the
one-vertex convention and the graded Cartan polynomial.
-/

public section

namespace TauCeti

open Polynomial

universe u

section Ring

variable (k : Type u) [CommRing k]

/-- The unique vertex basis element of the public `A₁` zigzag algebra is its unit. -/
@[simp]
theorem zigzagAlgebraBasis_A1_vertex_eq_one :
    zigzagAlgebraBasis k (⊥ : SimpleGraph (Fin 1)) (.inl 0) = 1 := by
  have h : zigzagComponentProjection k (⊥ : SimpleGraph (Fin 1)) default
      (zigzagAlgebraBasis k (⊥ : SimpleGraph (Fin 1)) (.inl 0)) =
        zigzagComponentBasis k (⊥ : SimpleGraph (Fin 1)) default
          (.inl ⟨0, rfl⟩) := by
    simpa only [zigzagComponentBasisIndexEquiv_inl] using
      (zigzagComponentProjection_zigzagAlgebraBasis
        (G := (⊥ : SimpleGraph (Fin 1))) (k := k) default (.inl ⟨0, rfl⟩))
  apply (zigzagAlgebraEquivA1 k).injective
  rw [map_one, zigzagAlgebraEquivA1_apply, h]
  rw [zigzagComponentAlgebraEquivULiftDualNumber_zigzagComponentBasis_inl]
  rfl

private noncomputable def dualNumberGradeZeroEquiv : dualNumberGrade k 0 ≃ₗ[k] k where
  toFun x := x.1.fst
  invFun r := ⟨TrivSqZeroExt.inl r, inl_mem_dualNumberGrade_zero k r⟩
  left_inv x := by
    apply Subtype.ext
    apply TrivSqZeroExt.ext
    · simp
    · simp [(mem_dualNumberGrade_zero (R := k)).mp x.2]
  right_inv r := by simp
  map_add' x y := by simp
  map_smul' r x := by simp

private noncomputable def dualNumberGradeTwoEquiv : dualNumberGrade k 2 ≃ₗ[k] k where
  toFun x := x.1.snd
  invFun r := ⟨TrivSqZeroExt.inr r, inr_mem_dualNumberGrade_two k r⟩
  left_inv x := by
    apply Subtype.ext
    apply TrivSqZeroExt.ext
    · simp [(mem_dualNumberGrade_two (R := k)).mp x.2]
    · simp
  right_inv r := by simp
  map_add' x y := by simp
  map_smul' r x := by simp

/-- The rank-one zigzag comparison respects the degree pieces: the generator of the dual
numbers and the volume basis vector both have degree two. -/
theorem mem_zigzagAlgebraGrade_A1_iff {n : ℕ}
    {x : zigzagAlgebra k (⊥ : SimpleGraph (Fin 1))} :
    x ∈ zigzagAlgebraGrade k (⊥ : SimpleGraph (Fin 1)) n ↔
      zigzagAlgebraEquivA1 k x ∈ dualNumberGrade k n := by
  rw [mem_zigzagAlgebraGrade]
  constructor
  · intro hx
    simpa only [zigzagAlgebraEquivA1_apply,
      mem_zigzagComponentGrade_of_subsingleton] using hx default
  · intro hx C
    have hC : C = default := Subsingleton.elim _ _
    subst C
    simpa only [zigzagAlgebraEquivA1_apply,
      mem_zigzagComponentGrade_of_subsingleton] using hx

/-- The degree-one part of the one-vertex zigzag algebra is zero. -/
theorem zigzagAlgebraGrade_A1_one_eq_bot :
    zigzagAlgebraGrade k (⊥ : SimpleGraph (Fin 1)) 1 = ⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  apply (zigzagAlgebraEquivA1 k).injective
  rw [map_zero]
  have h' := (mem_zigzagAlgebraGrade_A1_iff k (n := 1)).mp hx
  rw [dualNumberGrade_eq_bot k (by decide) (by decide)] at h'
  exact h'

end Ring

section Field

variable (k : Type u) [Field k]

/-- Each graded part of the public `A₁` algebra has the dimension of the corresponding
dual-number grade. -/
theorem finrank_zigzagAlgebraGrade_A1 (n : ℕ) :
    Module.finrank k (zigzagAlgebraGrade k (⊥ : SimpleGraph (Fin 1)) n) =
      Module.finrank k (dualNumberGrade k n) := by
  let e := (zigzagAlgebraEquivA1 k).toLinearEquiv
  have h : (zigzagAlgebraGrade k (⊥ : SimpleGraph (Fin 1)) n).map e.toLinearMap =
      dualNumberGrade k n := by
    ext x
    rw [Submodule.mem_map_equiv]
    simpa only [show zigzagAlgebraEquivA1 k (e.symm x) = x from e.apply_symm_apply x]
      using (mem_zigzagAlgebraGrade_A1_iff k (n := n) (x := e.symm x))
  rw [← LinearEquiv.finrank_map_eq e (zigzagAlgebraGrade k (⊥ : SimpleGraph (Fin 1)) n), h]

/-- The degree-zero part of the one-vertex zigzag algebra has dimension one. -/
@[simp]
theorem finrank_zigzagAlgebraGrade_A1_zero :
    Module.finrank k (zigzagAlgebraGrade k (⊥ : SimpleGraph (Fin 1)) 0) = 1 := by
  rw [finrank_zigzagAlgebraGrade_A1, (dualNumberGradeZeroEquiv k).finrank_eq]
  simp

/-- The degree-one part of the one-vertex zigzag algebra vanishes. -/
@[simp]
theorem finrank_zigzagAlgebraGrade_A1_one :
    Module.finrank k (zigzagAlgebraGrade k (⊥ : SimpleGraph (Fin 1)) 1) = 0 := by
  rw [zigzagAlgebraGrade_A1_one_eq_bot]
  simp

/-- The degree-two part of the one-vertex zigzag algebra has dimension one. -/
@[simp]
theorem finrank_zigzagAlgebraGrade_A1_two :
    Module.finrank k (zigzagAlgebraGrade k (⊥ : SimpleGraph (Fin 1)) 2) = 1 := by
  rw [finrank_zigzagAlgebraGrade_A1, (dualNumberGradeTwoEquiv k).finrank_eq]
  simp

/-- The one-by-one graded Cartan matrix of the public `A₁` zigzag algebra. Since its vertex
idempotent is the unit, the sole graded corner is the whole algebra in each degree. -/
noncomputable def zigzagA1GradedCartanMatrix : Matrix (Fin 1) (Fin 1) ℤ[X] :=
  Matrix.of fun _ _ =>
    ∑ n ∈ Finset.range 3,
      (Module.finrank k (zigzagAlgebraGrade k (⊥ : SimpleGraph (Fin 1)) n) : ℤ[X]) * X ^ n

/-- The graded Cartan matrix of the one-vertex zigzag algebra is `[1 + q²]`. -/
@[simp]
theorem zigzagA1GradedCartanMatrix_apply (i j : Fin 1) :
    zigzagA1GradedCartanMatrix k i j = 1 + X ^ 2 := by
  rw [zigzagA1GradedCartanMatrix, Matrix.of_apply, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_one]
  simp [finrank_zigzagAlgebraGrade_A1_zero, finrank_zigzagAlgebraGrade_A1_one,
    finrank_zigzagAlgebraGrade_A1_two]

/-- The `A₁` graded Cartan matrix, written as a one-by-one matrix. -/
theorem zigzagA1GradedCartanMatrix_eq :
    zigzagA1GradedCartanMatrix k = !![1 + X ^ 2] := by
  ext i j
  fin_cases i
  fin_cases j
  simp

end Field

end TauCeti

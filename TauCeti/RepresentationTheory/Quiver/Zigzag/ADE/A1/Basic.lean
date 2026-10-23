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

It also names the unique volume basis vector `TauCeti.zigzagA1Volume`, the element
corresponding to `ε` under the comparison with the dual numbers.

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

/-- The unique volume basis vector of the one-vertex zigzag algebra. -/
noncomputable def zigzagA1Volume : zigzagAlgebra k (⊥ : SimpleGraph (Fin 1)) :=
  (zigzagAlgebraEquivA1 k).symm DualNumber.eps

/-- Under the comparison with the dual numbers, the `A₁` volume is `ε`. Its `simp` priority is
high so that it fires before the general unfolding lemma `TauCeti.zigzagAlgebraEquivA1_apply`. -/
@[simp high]
theorem zigzagAlgebraEquivA1_zigzagA1Volume :
    zigzagAlgebraEquivA1 k (zigzagA1Volume k) = DualNumber.eps :=
  (zigzagAlgebraEquivA1 k).apply_symm_apply DualNumber.eps

/-- The element transported from `ε` is the volume vector in the standard zigzag basis. -/
theorem zigzagA1Volume_eq_basis :
    zigzagA1Volume k =
      zigzagAlgebraBasis k (⊥ : SimpleGraph (Fin 1)) (.inr (.inr 0)) := by
  apply (zigzagAlgebraEquivA1 k).injective
  rw [zigzagAlgebraEquivA1_zigzagA1Volume, zigzagAlgebraEquivA1_apply]
  have h : zigzagComponentProjection k (⊥ : SimpleGraph (Fin 1)) default
      (zigzagAlgebraBasis k (⊥ : SimpleGraph (Fin 1)) (.inr (.inr 0))) =
        zigzagComponentBasis k (⊥ : SimpleGraph (Fin 1)) default
          (.inr (.inr ⟨0, rfl⟩)) := by
    simpa only [zigzagComponentBasisIndexEquiv_inr_inr] using
      (zigzagComponentProjection_zigzagAlgebraBasis
        (G := (⊥ : SimpleGraph (Fin 1))) (k := k) default (.inr (.inr ⟨0, rfl⟩)))
  rw [h, zigzagComponentAlgebraEquivULiftDualNumber_zigzagComponentBasis_inr_inr]

/-- The rank-one zigzag comparison respects the degree pieces: the generator of the dual
numbers and the volume basis vector both have degree two. -/
@[simp]
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

/-- Every degree of the one-vertex zigzag algebra other than zero and two vanishes. -/
@[simp]
theorem zigzagAlgebraGrade_A1_eq_bot {n : ℕ} (h0 : n ≠ 0) (h2 : n ≠ 2) :
    zigzagAlgebraGrade k (⊥ : SimpleGraph (Fin 1)) n = ⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  apply (zigzagAlgebraEquivA1 k).injective
  rw [map_zero]
  have h' := (mem_zigzagAlgebraGrade_A1_iff k (n := n)).mp hx
  rw [dualNumberGrade_eq_bot k h0 h2] at h'
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
  have he (y : zigzagAlgebra k (⊥ : SimpleGraph (Fin 1))) :
      e y = zigzagAlgebraEquivA1 k y := rfl
  have h : (zigzagAlgebraGrade k (⊥ : SimpleGraph (Fin 1)) n).map e.toLinearMap =
      dualNumberGrade k n := by
    ext x
    rw [Submodule.mem_map_equiv]
    simpa only [← he (e.symm x), e.apply_symm_apply]
      using (mem_zigzagAlgebraGrade_A1_iff k (n := n) (x := e.symm x))
  rw [← LinearEquiv.finrank_map_eq e (zigzagAlgebraGrade k (⊥ : SimpleGraph (Fin 1)) n), h]

/-- The degree-zero part of the one-vertex zigzag algebra has dimension one. -/
@[simp]
theorem finrank_zigzagAlgebraGrade_A1_zero :
    Module.finrank k (zigzagAlgebraGrade k (⊥ : SimpleGraph (Fin 1)) 0) = 1 := by
  rw [finrank_zigzagAlgebraGrade_A1, (dualNumberGradeZeroEquiv k).finrank_eq]
  simp

/-- Every graded part of the one-vertex zigzag algebra outside degrees zero and two
has dimension zero. -/
@[simp]
theorem finrank_zigzagAlgebraGrade_A1_eq_zero {n : ℕ} (h0 : n ≠ 0) (h2 : n ≠ 2) :
    Module.finrank k (zigzagAlgebraGrade k (⊥ : SimpleGraph (Fin 1)) n) = 0 := by
  rw [zigzagAlgebraGrade_A1_eq_bot k h0 h2]
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
  simp [finrank_zigzagAlgebraGrade_A1_zero, finrank_zigzagAlgebraGrade_A1_two]

/-- The `A₁` graded Cartan matrix, written as a one-by-one matrix. -/
theorem zigzagA1GradedCartanMatrix_eq :
    zigzagA1GradedCartanMatrix k = !![1 + X ^ 2] := by
  ext i j
  fin_cases i
  fin_cases j
  simp

end Field

end TauCeti

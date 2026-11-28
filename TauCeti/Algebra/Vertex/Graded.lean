/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Vertex.Axioms
public import Mathlib.Algebra.DirectSum.Module

/-!
# Graded formal vertex algebras

A graded formal vertex algebra (`TauCeti.GradedFormalVertexAxioms`) is a formal vertex algebra
`V` together with a decomposition `V = ⨁_{p : ℕ} V_p` into weight spaces such that

* the weight-zero space is spanned by the vacuum, `V_0 = R |0⟩`;
* modes shift weights: if `a ∈ V_p` and `b ∈ V_q`, then `a₍ₙ₎ b ∈ V_{p+q-n-1}` when
  `p + q - n - 1 ≥ 0`, and `a₍ₙ₎ b = 0` otherwise.

These are the `ℤ₊`-graded vertex algebras whose weight-zero space is spanned by the vacuum
(vertex algebras of CFT type), the setting in which the weight-one space `V_1` carries a Lie
algebra structure given by the zero product `a₍₀₎ b` (`TauCeti.Algebra.Vertex.WeightOne`). The
basic examples are the affine and Heisenberg vertex algebras, in which a creation mode `x₋ₙ`
raises the weight by `n`; their gradings are not constructed in this file.

## Main definitions

* `TauCeti.GradedFormalVertexAxioms`: a formal vertex algebra with an `ℕ`-grading of the above
  kind.

## Main results

* `TauCeti.GradedFormalVertexAxioms.ext`: a graded formal vertex algebra is determined by its
  underlying formal vertex algebra and its weight spaces.
* `TauCeti.GradedFormalVertexAxioms.vacuum_mem_grading_zero`: `|0⟩ ∈ V_0`.
* `TauCeti.GradedFormalVertexAxioms.translation_apply_mem_grading`: the translation operator
  raises weights by one, `T V_p ⊆ V_{p+1}`.
* `TauCeti.GradedFormalVertexAxioms.translation_apply_eq_zero_of_mem_grading_zero`: `T` kills
  `V_0`.

## References

* E. Frenkel, D. Ben-Zvi, *Vertex Algebras and Algebraic Curves*, 2nd ed., §1.3
  (`ℤ`-graded vertex algebras).
-/

public section

open scoped VertexOperator

namespace TauCeti

variable (R V : Type*) [CommRing R] [AddCommGroup V] [Module R V]

/-- A graded formal vertex algebra: a formal vertex algebra on `V` together with weight spaces
`grading p` (`p : ℕ`) forming an internal direct sum decomposition of `V`, such that the
weight-zero space is spanned by the vacuum and, for `a` of weight `p` and `b` of weight `q`, the
product `a₍ₙ₎ b` has weight `p + q - n - 1` when this is nonnegative and vanishes otherwise. -/
structure GradedFormalVertexAxioms extends FormalVertexAxioms R V where
  /-- The weight spaces `V_p`. -/
  grading : ℕ → Submodule R V
  /-- `V` is the internal direct sum of its weight spaces. -/
  isInternal_grading : DirectSum.IsInternal grading
  /-- The weight-zero space is spanned by the vacuum. -/
  grading_zero : grading 0 = R ∙ vacuum
  /-- The mode `a₍ₙ₎` maps `V_q` into `V_{p+q-n-1}` for `a ∈ V_p`. -/
  ncoeff_field_apply_mem_grading : ∀ {p q r : ℕ} {n : ℤ} {a b : V}, a ∈ grading p →
    b ∈ grading q → (r : ℤ) = p + q - n - 1 → ((field a)[[n]]) b ∈ grading r
  /-- The mode `a₍ₙ₎` kills `V_q` for `a ∈ V_p` when `p + q - n - 1 < 0`. -/
  ncoeff_field_apply_eq_zero : ∀ {p q : ℕ} {n : ℤ} {a b : V}, a ∈ grading p →
    b ∈ grading q → (p + q : ℤ) ≤ n → ((field a)[[n]]) b = 0

namespace GradedFormalVertexAxioms

variable {R V}
variable (A : GradedFormalVertexAxioms R V)

/-- A graded formal vertex algebra is determined by its underlying formal vertex algebra and its
weight spaces. -/
@[ext]
theorem ext {A B : GradedFormalVertexAxioms R V}
    (h : A.toFormalVertexAxioms = B.toFormalVertexAxioms) (hg : A.grading = B.grading) : A = B := by
  cases A
  cases B
  simp_all

/-- The vacuum has weight zero. -/
@[simp]
theorem vacuum_mem_grading_zero : A.vacuum ∈ A.grading 0 := by
  rw [A.grading_zero]
  exact Submodule.mem_span_singleton_self _

/-- The translation operator kills the weight-zero space. -/
theorem translation_apply_eq_zero_of_mem_grading_zero {a : V} (ha : a ∈ A.grading 0) :
    A.translation a = 0 := by
  rw [A.grading_zero] at ha
  obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 ha
  rw [map_smul, A.translation_vacuum, smul_zero]

/-- The translation operator raises weights by one: `T V_p ⊆ V_{p+1}`. -/
theorem translation_apply_mem_grading {p : ℕ} {a : V} (ha : a ∈ A.grading p) :
    A.translation a ∈ A.grading (p + 1) := by
  rw [A.translation_apply]
  exact A.ncoeff_field_apply_mem_grading ha A.vacuum_mem_grading_zero (by push_cast; ring)

end GradedFormalVertexAxioms

end TauCeti

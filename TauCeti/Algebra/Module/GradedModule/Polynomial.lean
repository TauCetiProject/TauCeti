/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Grading
public import TauCeti.Algebra.Module.GradedModule.Internal

/-!
# The negative-degree grading on a polynomial ring

This file equips `k[X]` with the internal grading that places `X ^ n` in degree `-n`. It records
the characteristic membership criterion and the resulting behavior of multiplication by powers
of `X`.

## Main definitions

* `TauCeti.Polynomial.negDegreeGrading`: the grading of `k[X]` placing `X ^ n` in degree `-n`.

## Main results

* `TauCeti.Polynomial.mem_negDegreeGrading_piece`: membership in a homogeneous piece is
  characterized coefficientwise.
* `TauCeti.Polynomial.X_smul_mem_negDegreeGrading_piece`: multiplication by `X` lowers degree by
  one.
* `TauCeti.Polynomial.X_pow_mem_negDegreeGrading_piece`: `X ^ n` has degree `-n`.
-/

public section

open Polynomial

namespace TauCeti

namespace Polynomial

variable (k : Type*) [CommSemiring k]

/-- The grading of the polynomial ring `k[X]` placing the monomial `X ^ n` in degree `-n`, so that
multiplication by `X` lowers degree by one. -/
noncomputable def negDegreeGrading : InternalGrading k k[X] :=
  InternalGrading.map
    ⟨AddMonoidAlgebra.gradeBy k ⇑(-Nat.castAddMonoidHom ℤ), AddMonoidAlgebra.gradeBy.isInternal _⟩
    (toFinsuppIsoLinear k).symm

variable {k}

/-- A polynomial has degree `p` in `negDegreeGrading` exactly when each of its monomials `X ^ n`
has `-n = p`. -/
@[simp]
theorem mem_negDegreeGrading_piece {p : ℤ} {x : k[X]} :
    x ∈ (negDegreeGrading k).piece p ↔ ∀ n, x.coeff n ≠ 0 → -(n : ℤ) = p := by
  rw [negDegreeGrading, InternalGrading.mem_map_piece_iff]
  simp [AddMonoidAlgebra.mem_gradeBy_iff, Set.subset_def, toFinsupp_apply]

/-- Multiplication by `X` lowers the degree of `negDegreeGrading` by one. -/
theorem X_smul_mem_negDegreeGrading_piece {p : ℤ} {x : k[X]}
    (hx : x ∈ (negDegreeGrading k).piece p) :
    (X : k[X]) • x ∈ (negDegreeGrading k).piece (p - 1) := by
  rw [mem_negDegreeGrading_piece] at hx ⊢
  intro n hn
  rw [smul_eq_mul] at hn
  cases n with
  | zero => simp at hn
  | succ n =>
    have := hx n (by rwa [coeff_X_mul] at hn)
    push_cast
    omega

/-- The monomial `X ^ n` has degree `-n` in `negDegreeGrading`. -/
theorem X_pow_mem_negDegreeGrading_piece (n : ℕ) :
    (X ^ n : k[X]) ∈ (negDegreeGrading k).piece (-n) := by
  rw [mem_negDegreeGrading_piece]
  intro m hm
  rw [coeff_X_pow] at hm
  split_ifs at hm with h
  · rw [h]
  · exact absurd rfl hm

end Polynomial

end TauCeti

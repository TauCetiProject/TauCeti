/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Frobenius equations over an algebraically closed field

A nonzero linear combination of iterates of a positive power of Frobenius defines a
nonconstant polynomial, since its monomials have distinct positive degrees.
Its surjectivity gives the residue-field input for difference equations on series.
-/

public section

open Finset Function Polynomial

namespace TauCeti

variable {p : ℕ} {k : Type*} [Field k] [Fact p.Prime] [CharP k p] [IsAlgClosed k]

/-- A nonzero scalar combination of distinct iterates of positive Frobenius is surjective
over an algebraically closed field. -/
theorem surjective_sum_mul_iterateFrobenius (s : Finset ℕ) (a : ℕ → k)
    {f : ℕ} (hf : 0 < f) (ha : ∃ i ∈ s, a i ≠ 0) :
    Surjective (fun x => ∑ i ∈ s, a i * iterateFrobenius k p (f * i) x) := by
  classical
  let q := p ^ f
  have hq : 1 < q := one_lt_pow₀ (Fact.out : p.Prime).one_lt hf.ne'
  let P : k[X] := ∑ i ∈ s, monomial (q ^ i) (a i)
  obtain ⟨i, hi, hai⟩ := ha
  have he (j : ℕ) : q ^ j = q ^ i ↔ j = i := (Nat.pow_right_injective hq).eq_iff
  have hcoeff : P.coeff (q ^ i) = a i := by
    simp only [P, finsetSum_coeff, coeff_monomial_apply, he]
    simp [hi]
  have hdegree : P.natDegree ≠ 0 := ((pow_pos (by omega : 0 < q) i).trans_le
    (Polynomial.le_natDegree_of_ne_zero (hcoeff.trans_ne hai))).ne'
  simpa only [P, eval_finsetSum, eval_monomial, iterateFrobenius_def, pow_mul, q] using
    IsAlgClosed.eval_surjective hdegree

end TauCeti

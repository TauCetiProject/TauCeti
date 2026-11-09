/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.Jump.Low

/-!
# Finite iterates of the Turing jump

The `n`-th jump `Z⁽ⁿ⁾` of a set `Z ⊆ ℕ` is the iterate `Set.jump^[n] Z`, with `Z⁽⁰⁾ = Z` and
`Z⁽ⁿ⁺¹⁾ = (Z⁽ⁿ⁾)'`. These are the oracles of the arithmetical hierarchy relative to `Z`: Post's
theorem, which is not proved here, identifies the sets c.e. in `Z⁽ⁿ⁾` with the `Σ⁰ₙ₊₁(Z)` sets.

This file proves that the iterated jumps form a strictly increasing chain in the Turing order,
and that iterating the jump transports reductions. The reductions between iterated jumps are
one-one reductions: computable injective maps of indices, as in Mathlib's `OneOneReducible`.
Beyond the first jump, a Turing reduction `A ≤_T B` is transported to a one-one reduction
`A⁽ⁿ⁺¹⁾ ≤₁ B⁽ⁿ⁺¹⁾`. At level zero the transported reduction is the given Turing reduction
itself, which need not be one-one.

## Main results

* `Set.oneOneReducible_iterate_jump_of_le`, `Set.turingReducible_iterate_jump_iff`: `Z⁽ᵐ⁾`
  reduces one-one to `Z⁽ⁿ⁾` when `m ≤ n`, and is Turing reducible to it only then.
* `Set.turingEquivalent_iterate_jump_iff`: distinct iterated jumps are Turing inequivalent.
* `Set.strictMono_degree_iterate_jump`: in Mathlib's degree quotient, the degrees represented by
  the iterated jumps are strictly increasing.
* `Set.turingReducible_iterate_jump_iterate_jump`,
  `Set.oneOneReducible_iterate_jump_iterate_jump`: if `A ≤_T B`, then `A⁽ⁿ⁾ ≤_T B⁽ⁿ⁾`, and
  `A⁽ⁿ⁺¹⁾ ≤₁ B⁽ⁿ⁺¹⁾`.
* `Set.turingEquivalent_iterate_jump_iterate_jump`,
  `Set.oneOneEquiv_iterate_jump_iterate_jump`: Turing equivalent sets have Turing equivalent
  iterated jumps, one-one equivalent from the first jump on.
* `Set.Low.turingEquivalent_iterate_jump`: a low set has the iterated jumps of the empty set
  from the first jump on.

## References

* R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, Chapter III.2 and
  Chapter IV.2.
-/

public section

namespace Set

variable (Z : Set ℕ) {A B : Set ℕ} {m n : ℕ}

/-! ### The chain of iterated jumps of a fixed set -/

/-- Each iterated jump reduces one-one to the next one. -/
theorem oneOneReducible_iterate_jump_succ (n : ℕ) :
    OneOneReducible (· ∈ jump^[n] Z) (· ∈ jump^[n + 1] Z) := by
  rw [Function.iterate_succ_apply']
  exact oneOneReducible_jump _

/-- **The iterated jumps increase:** `Z⁽ᵐ⁾` reduces one-one to `Z⁽ⁿ⁾` when `m ≤ n`. -/
theorem oneOneReducible_iterate_jump_of_le (h : m ≤ n) :
    OneOneReducible (· ∈ jump^[m] Z) (· ∈ jump^[n] Z) := by
  induction h with
  | refl => exact oneOneReducible_refl _
  | step _ ih => exact ih.trans (oneOneReducible_iterate_jump_succ Z _)

/-- `Z⁽ᵐ⁾` is Turing reducible to `Z⁽ⁿ⁾` when `m ≤ n`. -/
theorem turingReducible_iterate_jump_of_le (h : m ≤ n) :
    TuringReducible (jump^[m] Z).oracle (jump^[n] Z).oracle :=
  (oneOneReducible_iterate_jump_of_le Z h).to_many_one.turingReducible_oracle

/-- **The iterated jumps increase strictly:** a later iterated jump is not computable relative
to an earlier one. -/
theorem not_iterate_jump_turingReducible_of_lt (h : m < n) :
    ¬TuringReducible (jump^[n] Z).oracle (jump^[m] Z).oracle := fun h' => by
  -- `Z⁽ᵐ⁾'` would be computable relative to `Z⁽ᵐ⁾`
  have h'' := (turingReducible_iterate_jump_of_le Z h).trans h'
  rw [Function.iterate_succ_apply'] at h''
  exact not_jump_turingReducible _ h''

/-- `Z⁽ᵐ⁾` is Turing reducible to `Z⁽ⁿ⁾` exactly when `m ≤ n`. -/
@[simp]
theorem turingReducible_iterate_jump_iff :
    TuringReducible (jump^[m] Z).oracle (jump^[n] Z).oracle ↔ m ≤ n :=
  ⟨fun h => not_lt.1 fun hnm => not_iterate_jump_turingReducible_of_lt Z hnm h,
    turingReducible_iterate_jump_of_le Z⟩

/-- `Z⁽ᵐ⁾` and `Z⁽ⁿ⁾` are Turing equivalent exactly when `m = n`. -/
@[simp]
theorem turingEquivalent_iterate_jump_iff :
    TuringEquivalent (jump^[m] Z).oracle (jump^[n] Z).oracle ↔ m = n :=
  ⟨fun h => le_antisymm ((turingReducible_iterate_jump_iff Z).1 h.1)
    ((turingReducible_iterate_jump_iff Z).1 h.2), fun h => h ▸ TuringEquivalent.refl _⟩

/-- In Mathlib's quotient of partial functions, the degrees represented by the iterated jumps
of `Z` are strictly increasing. -/
theorem strictMono_degree_iterate_jump :
    StrictMono fun n => toAntisymmetrization TuringReducible (jump^[n] Z).oracle := by
  intro m n h
  rw [lt_iff_le_not_ge, TauCeti.turingDegree_le_iff, TauCeti.turingDegree_le_iff,
    turingReducible_iterate_jump_iff, turingReducible_iterate_jump_iff]
  exact ⟨h.le, not_le.2 h⟩

/-! ### Transport of reductions along the iterated jump -/

/-- **Iterating the jump is monotone:** if `A ≤_T B`, then `A⁽ⁿ⁾ ≤_T B⁽ⁿ⁾`. -/
theorem turingReducible_iterate_jump_iterate_jump (h : TuringReducible A.oracle B.oracle)
    (n : ℕ) : TuringReducible (jump^[n] A).oracle (jump^[n] B).oracle := by
  induction n with
  | zero => exact h
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact turingReducible_jump_jump ih

/-- If `A ≤_T B`, then `A⁽ⁿ⁺¹⁾` reduces one-one to `B⁽ⁿ⁺¹⁾`. The first jump turns a Turing
reduction into a one-one reduction. -/
theorem oneOneReducible_iterate_jump_iterate_jump (h : TuringReducible A.oracle B.oracle)
    (n : ℕ) : OneOneReducible (· ∈ jump^[n + 1] A) (· ∈ jump^[n + 1] B) := by
  rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
  exact oneOneReducible_jump_jump (turingReducible_iterate_jump_iterate_jump h n)

/-- Turing equivalent sets have Turing equivalent iterated jumps. -/
theorem turingEquivalent_iterate_jump_iterate_jump (h : TuringEquivalent A.oracle B.oracle)
    (n : ℕ) : TuringEquivalent (jump^[n] A).oracle (jump^[n] B).oracle :=
  ⟨turingReducible_iterate_jump_iterate_jump h.1 n,
    turingReducible_iterate_jump_iterate_jump h.2 n⟩

/-- Turing equivalent sets have one-one equivalent iterated jumps from the first jump on. -/
theorem oneOneEquiv_iterate_jump_iterate_jump (h : TuringEquivalent A.oracle B.oracle)
    (n : ℕ) : OneOneEquiv (· ∈ jump^[n + 1] A) (· ∈ jump^[n + 1] B) :=
  ⟨oneOneReducible_iterate_jump_iterate_jump h.1 n,
    oneOneReducible_iterate_jump_iterate_jump h.2 n⟩

/-- **A low set has the iterated jumps of the empty set** from the first jump on:
`A⁽ⁿ⁺¹⁾ ≡_T ∅⁽ⁿ⁺¹⁾`. -/
theorem Low.turingEquivalent_iterate_jump (hA : A.Low) (n : ℕ) :
    TuringEquivalent (jump^[n + 1] A).oracle (jump^[n + 1] (∅ : Set ℕ)).oracle := by
  rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
  exact turingEquivalent_iterate_jump_iterate_jump ((low_def A).1 hA) n

end Set

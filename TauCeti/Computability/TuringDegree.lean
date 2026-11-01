/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Indicator
public import Mathlib.Computability.Reduce
public import Mathlib.Computability.TuringDegree

/-!
# Set oracles

Mathlib's `TuringReducible` compares partial functions `ℕ →. ℕ`. A set of naturals is used as an
oracle through its characteristic function: `A.oracle` is the total partial function with values
`A.indicator 1`, answering `1` on `A` and `0` off it. Turing reducibility of sets is Turing
reducibility of these oracles.

## Main definitions

* `Set.oracle`: the characteristic function of a set of naturals, as an oracle.

## Main results

* `ManyOneReducible.turingReducible_oracle`: a many-one reduction of sets gives a Turing reduction
  of their oracles.
* `Set.partrec_oracle_iff`: partial computability of a set oracle is equivalent to computability
  of membership.
* `Set.turingReducible_empty_iff`: reducibility to the empty oracle characterizes computable sets.

## References

* R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, Chapter III.1.
-/

public section

namespace Set

/-- The oracle of a set of naturals: its characteristic function `A.indicator 1`, as a total
partial function. -/
noncomputable def oracle (A : Set ℕ) : ℕ →. ℕ :=
  fun n => Part.some (A.indicator 1 n)

/-- The oracle of `A` answers `A.indicator 1 n` at `n`. -/
@[simp]
theorem oracle_apply (A : Set ℕ) (n : ℕ) : A.oracle n = Part.some (A.indicator 1 n) :=
  (rfl)

/-- The empty set answers zero on every input. -/
@[simp]
theorem oracle_empty : (∅ : Set ℕ).oracle = fun _ => Part.some 0 := by
  ext n
  simp

/-- A set oracle is partial computable exactly when membership in the set is computable. -/
@[simp]
theorem partrec_oracle_iff (A : Set ℕ) : Partrec A.oracle ↔ ComputablePred (· ∈ A) := by
  classical
  constructor
  · intro h
    have hχ : Computable (A.indicator 1 : ℕ → ℕ) :=
      h.of_eq_tot fun n => by simp
    refine Computable.computablePred <|
      (Primrec.beq.to_comp.comp hχ (Computable.const 1)).of_eq fun n => ?_
    by_cases hn : n ∈ A <;> simp [hn]
  · intro h
    exact ((h.ite (Computable.const 1) (Computable.const 0)).partrec).of_eq fun n => by
      by_cases hn : n ∈ A <;> simp [hn]

/-- The empty oracle is Turing reducible to every oracle. -/
theorem empty_turingReducible (A : Set ℕ) : TuringReducible (∅ : Set ℕ).oracle A.oracle := by
  rw [oracle_empty]
  exact (Computable.const 0).partrec.turingReducible

/-- A set is Turing reducible to the empty oracle exactly when its membership is computable. -/
theorem turingReducible_empty_iff (A : Set ℕ) :
    TuringReducible A.oracle (∅ : Set ℕ).oracle ↔ ComputablePred (· ∈ A) := by
  rw [oracle_empty, ← partrec_oracle_iff]
  exact ⟨TuringReducible.partrec_of_const, Partrec.turingReducible⟩

end Set

/-- A many-one reduction of sets of naturals gives a Turing reduction of their oracles: query the
oracle of `B` at the image of the input. -/
theorem ManyOneReducible.turingReducible_oracle {A B : Set ℕ}
    (h : ManyOneReducible (· ∈ A) (· ∈ B)) : TuringReducible A.oracle B.oracle := by
  obtain ⟨f, hf, hAB⟩ := h
  refine RecursiveIn.iff_nat.2 <|
    ((Nat.RecursiveIn.oracle _ rfl).comp (Partrec.nat_iff.1 hf).recursiveIn).of_eq fun n =>
    (Part.bind_some _ _).trans ?_
  by_cases hn : n ∈ A
  · simp [hn, (hAB n).1 hn]
  · simp [hn, mt (hAB n).2 hn]

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.Jump.Basic

/-!
# Low sets

A set of naturals is low when its Turing jump is Turing equivalent to the jump of the empty
set. Lowness is invariant under Turing equivalence and downward closed under Turing
reducibility. In particular, computable sets are low.

Every low set is strictly below the jump of the empty set, even without a c.e. hypothesis.
Thus a noncomputable low c.e. set has an intermediate c.e. degree. The strictness statement
uses Mathlib's degree quotient only on classes represented by total set oracles; it makes
no assertion about whether arbitrary partial-function degrees have such representatives.

## Main results

* `Set.low_iff_jump_turingReducible`: to establish lowness it suffices to reduce the jump
  to the jump of the empty set; the reverse reduction always holds.
* `Set.Low.of_turingReducible`: every set Turing reducible to a low set is low.
* `Set.low_congr`: Turing equivalent sets are low together.
* `Set.Low.not_jump_empty_turingReducible`: no low set computes the jump of the empty set.
* `Set.Low.degree_lt_jump_empty`: the degree of a low set is strictly below that jump.

## References

* R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987,
  Chapters III.2 and VII.1.
-/

public section

namespace Set

variable {A B : Set ℕ}

/-- A set is **low** when its jump is Turing equivalent to the jump of the empty set. -/
def Low (A : Set ℕ) : Prop :=
  TuringEquivalent A.jump.oracle (∅ : Set ℕ).jump.oracle

/-- Lowness means Turing equivalence of the two jumps. -/
theorem low_def (A : Set ℕ) :
    A.Low ↔ TuringEquivalent A.jump.oracle (∅ : Set ℕ).jump.oracle :=
  Iff.rfl

/-- It suffices to prove the upper reduction for lowness: the jump of the empty set always
reduces to the jump of any set. -/
theorem low_iff_jump_turingReducible :
    A.Low ↔ TuringReducible A.jump.oracle (∅ : Set ℕ).jump.oracle :=
  ⟨fun h => h.1, fun h => ⟨h, turingReducible_jump_jump (empty_turingReducible A.oracle)⟩⟩

/-- The empty set is low. -/
@[simp]
theorem low_empty : (∅ : Set ℕ).Low :=
  TuringEquivalent.refl _

/-- Lowness is downward closed under Turing reducibility. -/
theorem Low.of_turingReducible (hB : B.Low) (hAB : TuringReducible A.oracle B.oracle) :
    A.Low :=
  low_iff_jump_turingReducible.2 ((turingReducible_jump_jump hAB).trans hB.1)

/-- Turing equivalent sets are low together. -/
theorem low_congr (h : TuringEquivalent A.oracle B.oracle) : A.Low ↔ B.Low :=
  ⟨fun hA => hA.of_turingReducible h.2, fun hB => hB.of_turingReducible h.1⟩

/-- Every computable set is low. -/
theorem low_of_computablePred (hA : ComputablePred (· ∈ A)) : A.Low :=
  low_empty.of_turingReducible ((turingReducible_empty_iff A).2 hA)

/-- Every low set is Turing reducible to the jump of the empty set. -/
theorem Low.turingReducible_jump_empty (hA : A.Low) :
    TuringReducible A.oracle (∅ : Set ℕ).jump.oracle :=
  (turingReducible_jump A).trans hA.1

/-- No low set computes the jump of the empty set. In particular, every low c.e. set is
incomplete. No enumerability hypothesis is needed for this nonreduction. -/
theorem Low.not_jump_empty_turingReducible (hA : A.Low) :
    ¬TuringReducible (∅ : Set ℕ).jump.oracle A.oracle := by
  intro h
  exact not_jump_turingReducible (∅ : Set ℕ).jump <|
    (turingReducible_jump_jump h).trans hA.1

/-- In Mathlib's quotient of partial functions, the degree represented by a low set is
strictly below the degree represented by the jump of the empty set. -/
theorem Low.degree_lt_jump_empty (hA : A.Low) :
    toAntisymmetrization TuringReducible A.oracle <
      toAntisymmetrization TuringReducible (∅ : Set ℕ).jump.oracle := by
  rw [lt_iff_le_not_ge, TauCeti.turingDegree_le_iff, TauCeti.turingDegree_le_iff]
  exact ⟨hA.turingReducible_jump_empty, hA.not_jump_empty_turingReducible⟩

/-- No jump is low. In particular, the jump of the empty set is not low. -/
@[simp]
theorem not_low_jump (A : Set ℕ) : ¬A.jump.Low :=
  fun h => h.not_jump_empty_turingReducible
    (turingReducible_jump_jump (empty_turingReducible A.oracle))

end Set

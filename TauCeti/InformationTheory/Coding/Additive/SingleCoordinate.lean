/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.InformationTheory.Coding.Puncture.Basic

/-!
# Deleting one coordinate of an additive code

Puncturing at a coordinate deletes it, while shortening at that coordinate first imposes zero
there and then deletes it. Both operations retain the singleton complement, on an arbitrary
coordinate type and over an arbitrary abelian alphabet. Their membership criteria and the
comparison with linear codes allow single-coordinate distance calculations without field
linearity.

## References

* W. C. Huffman and V. Pless, *Fundamentals of Error-Correcting Codes*, §1.5 and Chapter 9.
-/

public section

namespace TauCeti

namespace AdditiveCode

variable {A ι : Type*} [AddCommGroup A]

/-- Puncturing an additive code at `i` deletes that coordinate and retains all the others. -/
def punctureAt (C : AdditiveCode A ι) (i : ι) : AdditiveCode A ({i}ᶜ : Set ι) :=
  puncture C {i}ᶜ

/-- Single-coordinate puncturing retains the singleton complement. -/
theorem punctureAt_def (C : AdditiveCode A ι) (i : ι) :
    punctureAt C i = puncture C {i}ᶜ := (rfl)

/-- Shortening an additive code at `i` imposes zero there and retains all other coordinates. -/
noncomputable def shortenAt (C : AdditiveCode A ι) (i : ι) : AdditiveCode A ({i}ᶜ : Set ι) :=
  shorten C {i}ᶜ

/-- Single-coordinate shortening retains the singleton complement. -/
theorem shortenAt_def (C : AdditiveCode A ι) (i : ι) :
    shortenAt C i = shorten C {i}ᶜ := (rfl)

/-- A punctured word is the restriction of a codeword to the coordinates other than `i`. -/
@[simp]
theorem mem_punctureAt {C : AdditiveCode A ι} {i : ι} {y : ({i}ᶜ : Set ι) → A} :
    y ∈ punctureAt C i ↔ ∃ x ∈ C, ∀ j : ({i}ᶜ : Set ι), x j = y j := by
  rw [punctureAt_def, mem_puncture]

/-- A shortened word extends to a codeword that is zero at the deleted coordinate. -/
@[simp]
theorem mem_shortenAt {C : AdditiveCode A ι} {i : ι} {y : ({i}ᶜ : Set ι) → A} :
    y ∈ shortenAt C i ↔ ∃ x ∈ C, x i = 0 ∧ ∀ j : ({i}ᶜ : Set ι), x j = y j := by
  rw [shortenAt_def, mem_shorten]
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff, not_not, forall_eq]

end AdditiveCode

variable {F ι : Type*} [Field F]

/-- Forgetting scalar closure commutes with single-coordinate puncturing. -/
@[simp]
theorem LinearCode.punctureAt_toAddSubgroup (C : LinearCode F ι) (i : ι) :
    (punctureAt C i).toAddSubgroup = AdditiveCode.punctureAt C.toAddSubgroup i := by
  rw [punctureAt_def, AdditiveCode.punctureAt_def, LinearCode.puncture_toAddSubgroup]

/-- Forgetting scalar closure commutes with single-coordinate shortening. -/
@[simp]
theorem LinearCode.shortenAt_toAddSubgroup (C : LinearCode F ι) (i : ι) :
    (shortenAt C i).toAddSubgroup = AdditiveCode.shortenAt C.toAddSubgroup i := by
  rw [shortenAt_def, AdditiveCode.shortenAt_def, LinearCode.shorten_toAddSubgroup]

end TauCeti

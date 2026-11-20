/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Action.Faithful

/-!
# One-sided identities in semigroups with faithful left multiplication

In any semigroup `R` whose left regular action on itself is faithful (`FaithfulSMul R R`), a left
identity exists if and only if a two-sided identity exists.

## Main results

* `FaithfulSMul.exists_left_identity_iff`: in a semigroup with `FaithfulSMul R R`, a left identity
  exists if and only if a two-sided identity exists.
-/

public section

namespace FaithfulSMul

/-- In a semigroup whose left regular action is faithful, a left identity exists if and only if a
two-sided identity exists. -/
theorem exists_left_identity_iff {R : Type*} [Semigroup R] [FaithfulSMul R R] :
    (∃ e : R, ∀ b : R, e * b = b) ↔ ∃ e : R, ∀ b : R, e * b = b ∧ b * e = b := by
  refine ⟨fun ⟨e, he⟩ ↦ ⟨e, fun b ↦ ⟨he b, ?_⟩⟩, fun ⟨e, he⟩ ↦ ⟨e, fun b ↦ (he b).1⟩⟩
  refine eq_of_smul_eq_smul (α := R) fun c ↦ ?_
  simpa [smul_eq_mul, mul_assoc] using congrArg (b * ·) (he c)

end FaithfulSMul

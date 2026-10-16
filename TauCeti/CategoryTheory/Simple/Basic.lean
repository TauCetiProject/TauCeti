/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Simple

/-!
# Witnesses of non-simplicity

Mathlib's `CategoryTheory.Simple X` says that a monomorphism into `X` is an isomorphism exactly
when it is nonzero. This file records the contrapositive used to split a non-simple object: a
nonzero object which is not simple receives a nonzero monomorphism that is not an isomorphism,
that is, it has a nonzero proper subobject.

## Main results

* `TauCeti.exists_mono_ne_zero_not_isIso_of_not_simple`: a nonzero object which is not simple is
  the target of a nonzero monomorphism which is not an isomorphism.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

variable {C : Type*} [Category* C] [HasZeroMorphisms C]

/-- A nonzero object which is not simple has a nonzero proper subobject: it is the target of a
nonzero monomorphism which is not an isomorphism. -/
theorem exists_mono_ne_zero_not_isIso_of_not_simple {X : C} (hX : ¬IsZero X) (hs : ¬Simple X) :
    ∃ (Y : C) (f : Y ⟶ X), Mono f ∧ f ≠ 0 ∧ ¬IsIso f := by
  by_contra! h
  refine hs ⟨fun {Y} f _ => ⟨fun _ hf => ?_, h Y f inferInstance⟩⟩
  -- An isomorphism `0 : Y ⟶ X` would make the identity of `X` zero.
  subst hf
  exact hX ((IsZero.iff_id_eq_zero X).2 (by rw [← IsIso.inv_hom_id (0 : Y ⟶ X), comp_zero]))

end TauCeti

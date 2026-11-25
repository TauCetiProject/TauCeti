/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Sites.Coverage

/-!
# Coverage pullback refinements

The pullback axiom for a coverage supplies a covering presieve whose generated sieve
refines the pullback of the original generated sieve.
-/

public section

namespace CategoryTheory.Coverage

variable {C : Type*} [Category* C] (K : Coverage C)

/-- A coverage pullback witness refines the pullback of the generated sieve. -/
lemma exists_generate_le_pullback {Y : C} {R : Presieve Y} (hR : R ∈ K Y)
    {X : C} (f : X ⟶ Y) :
    ∃ P ∈ K X, Sieve.generate P ≤ (Sieve.generate R).pullback f := by
  obtain ⟨P, hP, hf⟩ := K.pullback f R hR
  refine ⟨P, hP, ?_⟩
  rw [Sieve.generate_le_iff]
  exact fun Z g hg ↦ hf hg

end CategoryTheory.Coverage

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Sifted

/-!
# Lemmas about sifted categories

For a sifted (or empty-or-sifted) category `C`, finality of the diagonal functor `C ⥤ C × C`
yields common target objects for any pair of objects
(`CategoryTheory.IsSifted.cocone_objs`).
-/

public section

namespace CategoryTheory.IsSifted

open Limits

/-- Every pair of objects in a sifted (or empty-or-sifted) category admits a common target
object. -/
theorem cocone_objs {C : Type*} [Category* C] [IsSiftedOrEmpty C] (j₁ j₂ : C) :
    ∃ k : C, Nonempty (j₁ ⟶ k) ∧ Nonempty (j₂ ⟶ k) := by
  let S : Functor.Final (Functor.diag C) := inferInstance
  obtain ⟨X⟩ := (S.out (j₁, j₂)).is_nonempty
  exact ⟨X.right, ⟨X.hom.fst⟩, ⟨X.hom.snd⟩⟩

end CategoryTheory.IsSifted

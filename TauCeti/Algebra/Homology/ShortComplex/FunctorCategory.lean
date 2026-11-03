/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Exact

/-!
# Exactness in functor categories

A short complex of functors into an abelian category is exact if and only if its
value at each object is exact. This allows sectionwise exact sequences of
presheaves to be sheafified using exactness of sheafification.
-/

public section

namespace CategoryTheory.ShortComplex

variable {J C : Type*} [Category* J] [Category* C] [Abelian C]

/-- Exactness of a short complex in an abelian functor category is objectwise. -/
lemma exact_iff_evaluation (S : ShortComplex (J ⥤ C)) :
    S.Exact ↔ ∀ j, (S.map ((evaluation J C).obj j)).Exact := by
  have h : JointlyFaithful (fun j ↦ (evaluation J C).obj j) :=
    ⟨fun h ↦ NatTrans.ext (funext h)⟩
  exact h.jointlyReflectsIsomorphisms.exact_iff S

end CategoryTheory.ShortComplex

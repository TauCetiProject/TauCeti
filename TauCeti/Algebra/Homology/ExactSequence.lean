/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ExactSequence

/-!
# Exactness of composable arrows given by their objects and successive maps

Mathlib's `CategoryTheory.ComposableArrows.mkOfObjOfMapSucc obj mapSucc` is the sequence of
composable arrows with objects `obj i` and arrows `mapSucc i`. It is exact as soon as consecutive
arrows compose to zero and the short complexes they form are exact
(`CategoryTheory.ComposableArrows.exact_mkOfObjOfMapSucc`). This is the form in which sequences
built term by term, for instance by splicing, are shown to be exact.

## Main results

* `CategoryTheory.ComposableArrows.exact_mkOfObjOfMapSucc`: exactness of `mkOfObjOfMapSucc` from
  that of its consecutive short complexes.
-/

public section

namespace CategoryTheory.ComposableArrows

open Limits

variable {C : Type*} [Category* C] [HasZeroMorphisms C] {m : ℕ} (obj : Fin (m + 1) → C)
  (mapSucc : ∀ i : Fin m, obj i.castSucc ⟶ obj i.succ)

/-- The composable arrows `mkOfObjOfMapSucc obj mapSucc` are exact as soon as consecutive
`mapSucc` compose to zero and form exact short complexes. -/
theorem exact_mkOfObjOfMapSucc
    (w : ∀ (i : ℕ) (hi : i + 2 ≤ m), mapSucc ⟨i, by omega⟩ ≫ mapSucc ⟨i + 1, by omega⟩ = 0)
    (h : ∀ (i : ℕ) (hi : i + 2 ≤ m), (ShortComplex.mk _ _ (w i hi)).Exact) :
    (mkOfObjOfMapSucc obj mapSucc).Exact where
  zero i hi := by
    rw [mkOfObjOfMapSucc_map_succ obj mapSucc i (by omega),
      mkOfObjOfMapSucc_map_succ obj mapSucc (i + 1) (by omega)]
    exact w i hi
  exact i hi := by
    refine ShortComplex.exact_of_iso ?_ (h i hi)
    exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simp [mkOfObjOfMapSucc_map_succ obj mapSucc i (by omega)])
      (by simp [mkOfObjOfMapSucc_map_succ obj mapSucc (i + 1) (by omega)])

end CategoryTheory.ComposableArrows

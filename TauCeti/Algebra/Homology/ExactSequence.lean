/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ExactSequence
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-!
# Exactness of composable arrows built term by term, and under exact functors

Mathlib's `CategoryTheory.ComposableArrows.mkOfObjOfMapSucc obj mapSucc` is the sequence of
composable arrows with objects `obj i` and arrows `mapSucc i`. It is exact as soon as consecutive
arrows compose to zero and the short complexes they form are exact
(`CategoryTheory.ComposableArrows.exact_mkOfObjOfMapSucc`). This is the form in which sequences
built term by term, for instance by splicing, are shown to be exact.

Exact sequences are also carried to exact sequences by functors preserving homology
(`CategoryTheory.ComposableArrows.Exact.map`), the composable-arrows form of Mathlib's
`CategoryTheory.ShortComplex.Exact.map`.

## Main results

* `CategoryTheory.ComposableArrows.exact_mkOfObjOfMapSucc`: exactness of `mkOfObjOfMapSucc` from
  that of its consecutive short complexes.
* `CategoryTheory.ComposableArrows.Exact.map`: a functor preserving zero morphisms and homology
  carries exact sequences to exact sequences.
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

/-- **Exact functors preserve exact sequences.** A functor preserving zero morphisms and homology
carries an exact sequence of composable arrows to an exact sequence. -/
theorem Exact.map {D : Type*} [Category* D] [HasZeroMorphisms D] {n : ℕ}
    {S : ComposableArrows C n} (hS : S.Exact) (F : C ⥤ D) [F.PreservesZeroMorphisms]
    [F.PreservesHomology] : ((F.mapComposableArrows n).obj S).Exact where
  zero i hi := by
    simpa only [Functor.mapComposableArrows_obj_map, Functor.map_comp, F.map_zero] using
      congrArg F.map (hS.zero i hi)
  exact i hi := (hS.exact i hi).map F

end CategoryTheory.ComposableArrows

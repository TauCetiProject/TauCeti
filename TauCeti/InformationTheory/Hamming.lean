/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.InformationTheory.Hamming

/-!
# Hamming data under coordinate reindexing

This file proves that Hamming distance and Hamming weight are invariant under relabelling a finite
coordinate type along an equivalence.
-/

public section

open Function

namespace TauCeti

variable {α ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq α]

/-- Relabelling coordinates along an equivalence preserves the Hamming distance. -/
theorem hammingDist_comp_equiv (e : κ ≃ ι) (x y : ι → α) :
    hammingDist (x ∘ e) (y ∘ e) = hammingDist x y := by
  simp only [hammingDist, comp_apply]
  exact Finset.card_equiv e (by simp)

/-- Relabelling coordinates along an equivalence preserves the Hamming weight. -/
theorem hammingNorm_comp_equiv [Zero α] (e : κ ≃ ι) (x : ι → α) :
    hammingNorm (x ∘ e) = hammingNorm x := by
  simp only [hammingNorm, comp_apply]
  exact Finset.card_equiv e (by simp)

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.List.FinRange
import Mathlib.Data.List.NodupEquivFin

/-!
# Permutations as lists

A permutation of `Fin n` can be written in one-line notation as a list containing every element
of `Fin n` exactly once. This file packages that correspondence as an equivalence.
-/

public section

namespace TauCeti

open List

/-- Permutations of `Fin n` correspond to lists containing every element of `Fin n` exactly
once, by writing a permutation in one-line notation. The inverse sends a list to the permutation
whose value at `i` is the `i`-th entry of the list. -/
def permutationWordEquiv (n : ℕ) :
    Equiv.Perm (Fin n) ≃ {w : List (Fin n) // w.Perm (finRange n)} where
  toFun σ := ⟨ofFn σ, by simpa [List.ofFn_eq_map] using σ.map_finRange_perm⟩
  invFun w := (finCongr (w.property.length_eq.trans length_finRange).symm).trans
    ((w.property.nodup_iff.mpr (nodup_finRange n)).getEquivOfForallMemList w.val
      fun x => w.property.symm.subset (mem_finRange x))
  left_inv σ := by ext i; simp
  right_inv w := Subtype.ext <| List.ext_getElem (by simp [w.property.length_eq]) (by simp)

/-- The forward permutation-to-word equivalence is `List.ofFn`. -/
@[simp]
theorem permutationWordEquiv_apply_coe (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    ((permutationWordEquiv n σ : {w : List (Fin n) // w.Perm (finRange n)}) : List (Fin n)) =
      List.ofFn σ :=
  (rfl)

/-- The inverse word-to-permutation equivalence reads off the entries of the word. -/
@[simp]
theorem permutationWordEquiv_symm_apply (n : ℕ) (w : {w : List (Fin n) // w.Perm (finRange n)})
    (i : Fin n) :
    (permutationWordEquiv n).symm w i =
      w.val[i.val]'(by simp [w.property.length_eq]) :=
  (rfl)

end TauCeti

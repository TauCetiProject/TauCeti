/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fin.SuccPred

/-!
# The face-index involution

Deleting first the coordinate `i : Fin (n + 2)` and then the coordinate `j : Fin (n + 1)` of an
`(n + 2)`-cube or simplex gives the same face as deleting first `i.succAbove j` and then
`j.predAbove i`. The map `Fin.faceSwap : (i, j) ↦ (i.succAbove j, j.predAbove i)` is a
fixed-point-free involution on such pairs, so the terms of `∂ ∘ ∂` cancel in pairs under it
whenever the two signs are opposite, as they are by `Fin.neg_one_pow_succAbove_add_predAbove`.

## Main definitions

* `Fin.faceSwap`: the involution `(i, j) ↦ (i.succAbove j, j.predAbove i)`.

## Main results

* `Fin.faceSwap_faceSwap`: `faceSwap` is an involution.
* `Fin.faceSwap_ne`: `faceSwap` has no fixed points.
-/

public section

namespace Fin

/-- The involution on pairs of face indices behind `∂ ∘ ∂ = 0`: `(i, j)` goes to
`(i.succAbove j, j.predAbove i)`. -/
def faceSwap {n : ℕ} (p : Fin (n + 2) × Fin (n + 1)) : Fin (n + 2) × Fin (n + 1) :=
  (p.1.succAbove p.2, p.2.predAbove p.1)

/-- The coordinate formula for the face-index involution `faceSwap`. -/
theorem faceSwap_def {n : ℕ} (p : Fin (n + 2) × Fin (n + 1)) :
    faceSwap p = (p.1.succAbove p.2, p.2.predAbove p.1) :=
  (rfl)

@[simp]
theorem faceSwap_faceSwap {n : ℕ} (p : Fin (n + 2) × Fin (n + 1)) : faceSwap (faceSwap p) = p := by
  obtain ⟨i, j⟩ := p
  simp [faceSwap, succAbove_succAbove_predAbove, predAbove_predAbove_succAbove]

theorem faceSwap_ne {n : ℕ} (p : Fin (n + 2) × Fin (n + 1)) : faceSwap p ≠ p := by
  obtain ⟨i, j⟩ := p
  intro h
  exact succAbove_ne i j (congrArg Prod.fst h)

end Fin

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Finite ordinal maps at explicit points

This file evaluates `finRotate` and `Fin.succAbove` at points written `⟨k, h⟩`. The
corresponding Mathlib lemmas are not usable by `simp` on such points: `finRotate_of_lt` uses its
hypothesis in the bound proof of its left-hand side, `finRotate_last'` needs the index to be
syntactically the last one, and `Fin.succAbove_of_castSucc_lt` and `Fin.succAbove_of_le_castSucc`
compare `Fin` values. Here every side condition is an inequality or equation of natural numbers
that does not occur in the left-hand side, so `simp (disch := omega)` can use the lemmas to compute
these maps on explicit points of a `Fin` type of variable size.

The `succAbove` lemmas are `@[simp]`. The `finRotate` lemmas are not: Mathlib's simp lemma
`finRotate_apply` already rewrites their left-hand side to `⟨k, _⟩ + 1`, so they are passed to
`simp only` explicitly.

## Main results

* `Fin.finRotate_mk` and `Fin.finRotate_mk_of_eq`: the cyclic successor of `⟨k, _⟩` below and at
  the last index.
* `Fin.succAbove_mk_of_lt` and `Fin.succAbove_mk_of_le`: `succAbove` on points written `⟨i, _⟩`.
-/

public section

namespace Fin

/-- The cyclic successor of `⟨k, _⟩` is `⟨k + 1, _⟩` away from the last index. Unlike
`finRotate_of_lt`, the hypothesis does not occur in the left-hand side, so `simp` can discharge
it. -/
theorem finRotate_mk {n k : ℕ} (h : k + 1 < n + 1) :
    finRotate (n + 1) ⟨k, by omega⟩ = ⟨k + 1, h⟩ :=
  finRotate_of_lt (by omega)

/-- The cyclic successor of the last index `⟨k, _⟩`, with `k = n`, is `⟨0, _⟩`. -/
theorem finRotate_mk_of_eq {n k : ℕ} (h : k = n) :
    finRotate (n + 1) ⟨k, by omega⟩ = ⟨0, by omega⟩ := by
  subst h
  exact finRotate_last'

/-- `succAbove` fixes the values below the skipped point. -/
@[simp]
theorem succAbove_mk_of_lt {n p i : ℕ} (hp : p < n + 1) (hi : i < n) (h : i < p) :
    (⟨p, hp⟩ : Fin (n + 1)).succAbove ⟨i, hi⟩ = ⟨i, by omega⟩ :=
  succAbove_of_castSucc_lt _ _ h

/-- `succAbove` shifts the values at or above the skipped point up by one. -/
@[simp]
theorem succAbove_mk_of_le {n p i : ℕ} (hp : p < n + 1) (hi : i < n) (h : p ≤ i) :
    (⟨p, hp⟩ : Fin (n + 1)).succAbove ⟨i, hi⟩ = ⟨i + 1, by omega⟩ :=
  succAbove_of_le_castSucc _ _ h

end Fin

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Init

/-!
# Entries of nested `Array.ofFn`

This file reads an entry of a two-dimensional array built with `Array.ofFn`.

## Main results

* `Array.getElem_getElem_ofFn_ofFn`: the `(i, k)` entry of
  `Array.ofFn fun a ↦ Array.ofFn (F a)` is `F i k`.
-/

public section

namespace Array

/-- The `(i, k)` entry of the two-dimensional array `Array.ofFn fun a ↦ Array.ofFn (F a)` is
`F i k`. -/
theorem getElem_getElem_ofFn_ofFn {β : Type*} {m n : Nat} (F : Fin m → Fin n → β)
    (i : Fin m) (k : Fin n) (h₁ : i.val < (ofFn fun a ↦ ofFn (F a)).size)
    (h₂ : k.val < ((ofFn fun a ↦ ofFn (F a))[i.val]'h₁).size) :
    ((ofFn fun a ↦ ofFn (F a))[i.val]'h₁)[k.val]'h₂ = F i k := by
  simp

end Array

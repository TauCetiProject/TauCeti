/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finsupp.Order
import Mathlib.Data.Finsupp.PWO

/-!
# Well-foundedness of monotone orders on finitely supported functions

Pulling back a preorder along a monotone map from `ι →₀ ℕ` (with `ι` finite) yields a well-founded
strict order, as an immediate consequence of Dickson's lemma (`Finsupp.wellQuasiOrdered_le`).

## Main results

* `Finsupp.wellFounded_lt_of_monotone`: if `ι` is finite and `c : (ι →₀ ℕ) → α` is monotone into a
  preorder `α`, then `fun a b ↦ c a < c b` is well founded.
-/

public section

namespace Finsupp

/-- Comparing natural-valued finitely supported functions on a finite index type by a monotone
function into a preorder is well founded (by Dickson's lemma). -/
theorem wellFounded_lt_of_monotone {ι α : Type*} [Finite ι] [Preorder α] {c : (ι →₀ ℕ) → α}
    (hc : Monotone c) : WellFounded fun a b : ι →₀ ℕ ↦ c a < c b := by
  have := Fintype.ofFinite ι
  let e : (fun a b : ι →₀ ℕ ↦ a ≤ b) →r fun a b : ι →₀ ℕ ↦ c a ≤ c b := ⟨id, fun h ↦ hc h⟩
  have h_wqo : WellQuasiOrdered fun a b : ι →₀ ℕ ↦ c a ≤ c b :=
    wellQuasiOrdered_le.of_surjective e Function.surjective_id
  simpa only [lt_iff_le_not_ge] using h_wqo.wellFounded

end Finsupp

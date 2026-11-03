/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Sym.Sym2

/-!
# Unordered-pair infrastructure

This file supplies elementary lemmas for transporting endpoint properties across equality of
unordered pairs and for distinguishing unordered pairs by membership.
-/

public section

namespace Sym2

variable {α : Type*}

/-- A property holds equivalently at the two ends of an unordered pair independently of the
chosen ordering of those ends. -/
theorem iff_iff_of_mk_eq {P : α → Prop} {a b c d : α} (h : s(a, b) = s(c, d)) :
    (P a ↔ P b) ↔ (P c ↔ P d) := by
  rcases eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  exacts [Iff.rfl, iff_comm]

/-- Two unordered pairs differ if an element belongs to one but not the other. -/
theorem ne_of_mem_notMem {x : α} {e e' : Sym2 α} (he : x ∈ e) (he' : x ∉ e') : e ≠ e' :=
  fun h ↦ he' (h ▸ he)

end Sym2

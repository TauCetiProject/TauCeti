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
unordered pairs and for distinguishing unordered pairs by membership, and the equivalence of
unordered pairs induced by an equivalence of their entries.
-/

public section

namespace Sym2

variable {α β : Type*}

/-- An equivalence `α ≃ β` induces an equivalence `Sym2 α ≃ Sym2 β` by `Sym2.map` on both
entries. This is the unordered-pair analogue of `Sym.equivCongr`. -/
def equivCongr (e : α ≃ β) : Sym2 α ≃ Sym2 β where
  toFun := map e
  invFun := map e.symm
  left_inv x := by simp [map_map]
  right_inv x := by simp [map_map]

@[simp]
theorem equivCongr_apply (e : α ≃ β) (x : Sym2 α) : equivCongr e x = map e x :=
  (rfl)

@[simp]
theorem equivCongr_symm_apply (e : α ≃ β) (x : Sym2 β) :
    (equivCongr e).symm x = map e.symm x :=
  (rfl)

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

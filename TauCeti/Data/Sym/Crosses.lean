/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Sym.Sym2

/-!
# Unordered pairs crossing a set

This file defines when an unordered pair has one endpoint in a set and the other endpoint outside
the set.

## Main definition

* `Sym2.Crosses`: an unordered pair crosses a set when its endpoints lie on opposite sides.
-/

public section

namespace Sym2

variable {V : Type*}

/-- An unordered pair crosses `S` when its two endpoints lie on opposite sides of `S`. -/
def Crosses (p : Sym2 V) (S : Set V) : Prop :=
  (∃ x ∈ p, x ∈ S) ∧ ∃ y ∈ p, y ∉ S

/-- A displayed unordered pair crosses a set exactly when its endpoints lie on opposite sides. -/
@[simp]
theorem crosses_mk_iff {S : Set V} {x y : V} :
    s(x, y).Crosses S ↔ (x ∈ S ∧ y ∉ S) ∨ (y ∈ S ∧ x ∉ S) := by
  simp only [Crosses, Sym2.mem_iff]
  aesop

/-- Crossing a set is unchanged by exchanging the set with its complement. -/
@[simp]
theorem crosses_compl (p : Sym2 V) (S : Set V) : p.Crosses Sᶜ ↔ p.Crosses S := by
  induction p using Sym2.inductionOn with
  | _ x y =>
      simp only [crosses_mk_iff, Set.mem_compl_iff, not_not]
      tauto

/-- A diagonal unordered pair crosses no set. -/
theorem not_crosses_diag (x : V) (S : Set V) : ¬s(x, x).Crosses S := by
  simp

/-- A crossing unordered pair is not diagonal. -/
theorem Crosses.not_isDiag {p : Sym2 V} {S : Set V} (h : p.Crosses S) : ¬p.IsDiag := by
  induction p using Sym2.inductionOn with
  | _ x y =>
      simp only [crosses_mk_iff, mk_isDiag_iff] at h ⊢
      rintro rfl
      simp at h

end Sym2

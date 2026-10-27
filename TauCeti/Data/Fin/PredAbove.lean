/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fin.SuccPred

/-!
# Pairs of elements identified by `Fin.predAbove`

The map `Fin.predAbove i : Fin (n + 2) → Fin (n + 1)` underlies the codegeneracy
`SimplexCategory.σ i`.  It identifies exactly one pair of distinct elements, namely
`Fin.castSucc i` and `Fin.succ i` (`Fin.predAbove_eq_predAbove_iff`).
-/

public section

namespace Fin

/-- Two elements `a < b` have the same image under `Fin.predAbove i` exactly when they are
`Fin.castSucc i` and `Fin.succ i`. -/
theorem predAbove_eq_predAbove_iff {n : ℕ} (i : Fin (n + 1)) {a b : Fin (n + 2)} (hab : a < b) :
    i.predAbove a = i.predAbove b ↔ a = i.castSucc ∧ b = i.succ := by
  refine ⟨fun h ↦ ?_, fun ⟨ha, hb⟩ ↦ by rw [ha, hb, predAbove_castSucc_self, predAbove_succ_self]⟩
  simp only [predAbove, Fin.ext_iff, Fin.lt_def] at h hab ⊢
  split_ifs at h with h₁ h₂ h₂ <;>
    simp only [Fin.val_pred, Fin.coe_castPred, Fin.val_castSucc] at h h₁ h₂ <;>
    simp only [Fin.val_castSucc, Fin.val_succ] <;> omega

end Fin

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fin.Tuple.Basic

/-!
# Contracting adjacent entries and dropping the last entry of a tuple

`Fin.contractNth j op g` replaces the adjacent entries `gⱼ, gⱼ₊₁` of a tuple by `op gⱼ gⱼ₊₁`,
and `Fin.init g` drops the last entry. This file records how the two interact. They are the
relations used to run inductions on the length of a tuple through the faces of the Hochschild
and bar complexes, which are contractions of adjacent entries.

## Main results

* `Fin.contractNth_last`: contracting at the last position drops the last entry.
* `Fin.init_contractNth_castSucc`: dropping the last entry commutes with a contraction away from
  the last entry.
* `Fin.contractNth_castSucc_castSucc_apply_last` and `Fin.contractNth_castSucc_last_apply_last`:
  the last entry of a contraction.
-/

public section

namespace Fin

variable {n : ℕ} {α : Sort*} (op : α → α → α)

/-- Contracting at the last position, which has no successor, drops the last entry. -/
@[simp]
theorem contractNth_last (g : Fin (n + 1) → α) : contractNth (last n) op g = init g := by
  funext k
  rw [contractNth_apply_of_lt _ _ _ _ (by simp), init]

/-- Dropping the last entry commutes with contracting entries other than the last two. -/
@[simp]
theorem init_contractNth_castSucc (j : Fin (n + 1)) (g : Fin (n + 2) → α) :
    init (contractNth j.castSucc op g) = contractNth j op (init g) := by
  funext k
  rcases lt_trichotomy (k : ℕ) j with h | h | h
  · rw [init, contractNth_apply_of_lt _ _ _ _ (by simpa using h),
      contractNth_apply_of_lt _ _ _ _ h, init]
  · rw [init, contractNth_apply_of_eq _ _ _ _ (by simpa using h),
      contractNth_apply_of_eq _ _ _ _ h, init, init, succ_castSucc]
  · rw [init, contractNth_apply_of_gt _ _ _ _ (by simpa using h),
      contractNth_apply_of_gt _ _ _ _ h, init, succ_castSucc]

/-- A contraction of entries other than the last two keeps the last entry. -/
@[simp]
theorem contractNth_castSucc_castSucc_apply_last (j : Fin n) (g : Fin (n + 2) → α) :
    contractNth j.castSucc.castSucc op g (last n) = g (last (n + 1)) := by
  rw [contractNth_apply_of_gt _ _ _ _ (by simp [j.isLt]), succ_last]

/-- Contracting the last two entries makes their product the last entry. -/
@[simp]
theorem contractNth_castSucc_last_apply_last (g : Fin (n + 2) → α) :
    contractNth (last n).castSucc op g (last n) = op (g (last n).castSucc) (g (last (n + 1))) := by
  rw [contractNth_apply_of_eq _ _ _ _ (by simp), succ_last]

end Fin

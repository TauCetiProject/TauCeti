/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Fintype.Card

/-!
# Parity counts on initial segments

The odd indices of `Fin n` are in bijection with the indices of `Fin (n / 2)`.
-/

public section

namespace Fin

/-- There are `⌊n / 2⌋` odd indices in the zero-based initial segment `Fin n`. -/
@[simp] theorem card_filter_odd (n : ℕ) :
    (Finset.univ.filter fun i : Fin n ↦ Odd i.val).card = n / 2 := by
  let e : Fin (n / 2) ↪ Fin n :=
    ⟨fun i ↦ ⟨2 * i.val + 1, by have := i.isLt; omega⟩,
      fun i j h ↦ Fin.ext (by have := congrArg Fin.val h; dsimp at this; omega)⟩
  have heval (j : Fin (n / 2)) : (e j).val = 2 * j.val + 1 := rfl
  have he : Finset.univ.map e = Finset.univ.filter (fun i : Fin n ↦ Odd i.val) := by
    ext i
    simp only [Finset.mem_map, Finset.mem_univ, true_and, Finset.mem_filter, Nat.odd_iff]
    constructor
    · rintro ⟨j, rfl⟩
      rw [heval]
      omega
    · intro hi
      refine ⟨⟨i.val / 2, by omega⟩, Fin.ext ?_⟩
      rw [heval]
      exact (by omega : 2 * (i.val / 2) + 1 = i.val)
  rw [← he, Finset.card_map, Finset.card_univ, Fintype.card_fin]

end Fin

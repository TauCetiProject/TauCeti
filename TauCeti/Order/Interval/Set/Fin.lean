/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Fin.Basic
public import Mathlib.Order.Interval.Set.UnorderedInterval

/-!
# Intervals in `Fin n`

Membership in the unordered open interval `Set.uIoo a b` of `Fin n`, read off the values of the
points as natural numbers. Mathlib's `Fin.preimage_val_uIoo_val` identifies `Set.uIoo a b` with
the preimage of the corresponding interval of `ℕ`; `Fin.mem_uIoo_iff_val` unfolds this into two
strict inequalities against the minimum and maximum of the values of the endpoints, the form
consumed by `omega`.

A closed interval also carries the order embedding from the finite type of its consecutive
indices. The strict-endpoint form records its first and last indices separately.

## Main results

* `Fin.mem_uIoo_iff_val`: a point of `Fin n` lies strictly between `a` and `b` exactly when its
  value lies strictly between theirs.
* `Fin.intervalOrderEmb` and `Fin.intervalOrderEmbOfLt`: order embeddings onto closed intervals.
-/

public section

namespace Fin

/-- A point of `Fin n` lies strictly between `a` and `b` exactly when its value lies strictly
between theirs. -/
theorem mem_uIoo_iff_val {n : ℕ} {a b x : Fin n} :
    x ∈ Set.uIoo a b ↔ min (a : ℕ) b < x ∧ (x : ℕ) < max (a : ℕ) b := by
  rw [← Set.Ioo_min_max, Set.mem_Ioo, Fin.lt_def, Fin.lt_def, Fin.val_min, Fin.val_max]

/-- Embed a consecutive block of `d + 1` indices starting at `a` into `Fin m`. -/
def intervalOrderEmb {m d : ℕ} (a : ℕ) (h : a + (d + 1) ≤ m) :
    Fin (d + 1) ↪o Fin m :=
  (Fin.natAddOrderEmb a).trans (Fin.castLEOrderEmb h)

/-- The value of an embedded interval index is shifted by `a`. -/
@[simp]
theorem intervalOrderEmb_apply_val {m d : ℕ} (a : ℕ) (h : a + (d + 1) ≤ m)
    (k : Fin (d + 1)) : (intervalOrderEmb a h k).val = a + k.val := by
  simp [intervalOrderEmb]

/-- Membership in the consecutive index block is a pair of bounds. -/
theorem mem_range_intervalOrderEmb {m d : ℕ} (a : ℕ) (h : a + (d + 1) ≤ m)
    (k : Fin m) : k ∈ Set.range (intervalOrderEmb a h) ↔ a ≤ k.val ∧ k.val ≤ a + d := by
  constructor
  · rintro ⟨t, rfl⟩
    simp only [intervalOrderEmb_apply_val]
    have ht := t.isLt
    omega
  · intro hk
    let t : Fin (d + 1) := ⟨k.val - a, by omega⟩
    refine ⟨t, Fin.ext ?_⟩
    simp only [intervalOrderEmb_apply_val]
    dsimp only [t]
    omega

/-- The consecutive index block is the closed interval between its endpoints. -/
theorem range_intervalOrderEmb {m d : ℕ} (a : ℕ) (h : a + (d + 1) ≤ m) :
    Set.range (intervalOrderEmb a h) =
      Set.Icc (intervalOrderEmb a h 0) (intervalOrderEmb a h (Fin.last d)) := by
  ext k
  simp only [mem_range_intervalOrderEmb, Set.mem_Icc, Fin.le_iff_val_le_val,
    intervalOrderEmb_apply_val, Fin.val_zero, Fin.val_last, Nat.add_zero]

/-- Embed the interval between distinct endpoints, with at least two indices. -/
def intervalOrderEmbOfLt {m : ℕ} (i j : Fin m) (hij : i < j) :
    Fin ((j.val - i.val - 1) + 2) ↪o Fin m :=
  intervalOrderEmb i.val (by have _ := j.isLt; have _ := hij; omega)

/-- The value of a strict-endpoint interval index is shifted by the left endpoint. -/
@[simp]
theorem intervalOrderEmbOfLt_apply_val {m : ℕ} (i j : Fin m) (hij : i < j)
    (k : Fin ((j.val - i.val - 1) + 2)) : (intervalOrderEmbOfLt i j hij k).val = i.val + k.val :=
  intervalOrderEmb_apply_val _ _ _

/-- The strict-endpoint interval embedding starts at the left endpoint. -/
@[simp]
theorem intervalOrderEmbOfLt_apply_zero {m : ℕ} (i j : Fin m) (hij : i < j) :
    intervalOrderEmbOfLt i j hij 0 = i := by
  apply Fin.ext
  simp [intervalOrderEmbOfLt]

/-- The strict-endpoint interval embedding ends at the right endpoint. -/
@[simp]
theorem intervalOrderEmbOfLt_apply_last {m : ℕ} (i j : Fin m) (hij : i < j) :
    intervalOrderEmbOfLt i j hij (Fin.last ((j.val - i.val - 1) + 1)) = j := by
  apply Fin.ext
  simp only [intervalOrderEmbOfLt, intervalOrderEmb_apply_val, Fin.val_last]
  omega

/-- The strict-endpoint interval embedding enumerates the closed interval. -/
theorem range_intervalOrderEmbOfLt {m : ℕ} (i j : Fin m) (hij : i < j) :
    Set.range (intervalOrderEmbOfLt i j hij) = Set.Icc i j := by
  have hrange : Set.range (intervalOrderEmbOfLt i j hij) =
      Set.Icc (intervalOrderEmbOfLt i j hij 0)
        (intervalOrderEmbOfLt i j hij (Fin.last ((j.val - i.val - 1) + 1))) :=
    range_intervalOrderEmb i.val (d := (j.val - i.val - 1) + 1) (by
      omega)
  simpa only [intervalOrderEmbOfLt_apply_zero, intervalOrderEmbOfLt_apply_last] using hrange

end Fin

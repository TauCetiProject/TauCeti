/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.RandomMatrix.Wigner.Basic

/-!
# Column enumeration of strictly upper Wigner entries

In column order, the strictly upper entries of the corner of size `n` form an initial segment
of length `n.choose 2`. The entry `(i, j)` with `i < j` has index `j.choose 2 + i`, and simp
reduces membership of this index in the initial segment to the column bound `j < n`. Conversely,
simp reduces corner membership of the entry with index `k` to the bound `k < n.choose 2`.
-/

public section

noncomputable section

namespace TauCeti

/-- The column-order index `j.choose 2 + i` of a strictly upper entry `(i, j)` is below
`n.choose 2` exactly when its column `j` is below `n`. This is the simp normal form of
`strictUpperEquivNat_lt_choose_iff`, after `strictUpperEquivNat_apply` unfolds the enumeration. -/
@[simp]
theorem strictUpperIndex_lt_choose_iff (ij : StrictUpper) (n : ℕ) :
    ij.val.2.choose 2 + ij.val.1 < n.choose 2 ↔ ij.val.2 < n := by
  constructor
  · contrapose!
    intro h
    exact (Nat.choose_mono 2 h).trans (Nat.le_add_right _ _)
  · intro h
    calc
      _ < (ij.val.2 + 1).choose 2 := by
        rw [Nat.choose_succ_succ' _ 1, Nat.choose_one_right, Nat.add_comm ij.val.2]
        exact Nat.add_lt_add_left ij.prop _
      _ ≤ _ := Nat.choose_mono 2 h

/-- The column-by-column enumeration of strictly upper-triangular indices. -/
def strictUpperEquivNat : StrictUpper ≃ ℕ := by
  refine Equiv.ofBijective (fun ij ↦ ij.val.2.choose 2 + ij.val.1) ⟨?_, ?_⟩
  · intro x y h
    dsimp only at h
    have hx := (strictUpperIndex_lt_choose_iff x (y.val.2 + 1)).mp (h.symm ▸
      (strictUpperIndex_lt_choose_iff y (y.val.2 + 1)).mpr (Nat.lt_succ_self _))
    have hy := (strictUpperIndex_lt_choose_iff y (x.val.2 + 1)).mp (h ▸
      (strictUpperIndex_lt_choose_iff x (x.val.2 + 1)).mpr (Nat.lt_succ_self _))
    have hs : x.val.2 = y.val.2 := by omega
    exact Subtype.ext (Prod.ext (by rw [hs, Nat.add_right_inj] at h; exact h) hs)
  · intro k
    induction k with
    | zero => exact ⟨⟨(0, 1), by decide⟩, by simp⟩
    | succ k ih =>
      obtain ⟨⟨⟨i, j⟩, hij⟩, hk⟩ := ih
      dsimp only at hk
      by_cases h : i + 1 < j
      · refine ⟨⟨(i + 1, j), h⟩, ?_⟩
        dsimp only
        omega
      · refine ⟨⟨(0, j + 1), Nat.zero_lt_succ _⟩, ?_⟩
        dsimp only
        rw [Nat.choose_succ_succ' j 1, Nat.choose_one_right]
        simp only [Nat.reduceAdd]
        omega

/-- The index of a strictly upper entry is the size of the preceding columns plus its row. -/
@[simp]
theorem strictUpperEquivNat_apply (ij : StrictUpper) :
    strictUpperEquivNat ij = ij.val.2.choose 2 + ij.val.1 :=
  (rfl)

/-- The upper entries of the corner of size `n` are the initial segment of length `n.choose 2`. -/
theorem strictUpperEquivNat_lt_choose_iff (ij : StrictUpper) (n : ℕ) :
    strictUpperEquivNat ij < n.choose 2 ↔ ij.val.2 < n := by
  simp

/-- The entry with index `k` in the column enumeration lies in the corner of size `n` exactly
when `k` is below `n.choose 2`. -/
@[simp]
theorem strictUpperEquivNat_symm_apply_val_snd_lt_iff (k n : ℕ) :
    (strictUpperEquivNat.symm k).val.2 < n ↔ k < n.choose 2 := by
  rw [← strictUpperEquivNat_lt_choose_iff, Equiv.apply_symm_apply]

/-- The column-order enumeration restricted to strictly upper entries of a finite corner. -/
def strictUpperFinEquiv (n : ℕ) : StrictUpperFin n ≃ Fin (n.choose 2) :=
  ((strictUpperFinEquivSubtype n).trans (strictUpperEquivNat.subtypeEquiv fun ij ↦
    (strictUpperEquivNat_lt_choose_iff ij n).symm)).trans Fin.equivSubtype.symm

/-- The finite enumeration gives the same index as the infinite column enumeration. -/
@[simp]
theorem strictUpperFinEquiv_apply_val (n : ℕ) (ij : StrictUpperFin n) :
    (strictUpperFinEquiv n ij).val = strictUpperEquivNat (wignerUpperIndex ij) := by
  simp only [strictUpperFinEquiv, Equiv.trans_apply, Fin.equivSubtype_symm_apply,
    Equiv.subtypeEquiv_apply, strictUpperFinEquivSubtype_apply_val]

/-- An index of the finite enumeration corresponds to the same strictly upper entry as in the
infinite column enumeration. -/
@[simp]
theorem wignerUpperIndex_strictUpperFinEquiv_symm_apply (n : ℕ) (k : Fin (n.choose 2)) :
    wignerUpperIndex ((strictUpperFinEquiv n).symm k) = strictUpperEquivNat.symm k := by
  simp only [strictUpperFinEquiv, Equiv.symm_trans_apply, Equiv.subtypeEquiv_symm,
    Equiv.subtypeEquiv_apply, Equiv.symm_symm, Fin.equivSubtype_apply,
    wignerUpperIndex_strictUpperFinEquivSubtype_symm_apply]

/-- A sum over a finite strictly upper corner is the sum over the corresponding prefix
of the column-order enumeration. -/
theorem sum_strictUpperFin_eq_sum_range {E : Type*} [AddCommMonoid E]
    (n : ℕ) (f : StrictUpper → E) :
    ∑ ij : StrictUpperFin n, f (wignerUpperIndex ij) =
      ∑ k ∈ Finset.range (n.choose 2), f (strictUpperEquivNat.symm k) := by
  calc
    _ = ∑ k : Fin (n.choose 2), f (strictUpperEquivNat.symm k) :=
      Fintype.sum_equiv (strictUpperFinEquiv n) _ _ fun ij ↦ by
        rw [strictUpperFinEquiv_apply_val, Equiv.symm_apply_apply]
    _ = _ := by
      rw [Finset.sum_fin_eq_sum_range]
      exact Finset.sum_congr rfl fun k hk ↦ dite_eq_left (Finset.mem_range.mp hk)

end TauCeti

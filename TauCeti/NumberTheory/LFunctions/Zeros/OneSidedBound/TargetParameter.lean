/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.Order.Group.Unbundled.Int
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The target row parameter of a theta-lift chain

At each infinite place the target parameter has a stem of `k - 1` successive integers, followed
by an arithmetic progression. The finite parameter for a chain of length `m`
takes the first `m` entries of that progression, and the enlarged target takes one more entry.
We give the block decomposition and the distance of the doubled parameter from the signed lift
centres. The latter is used when inserting the blocks of the discrete-series parameters.

The normalization is that of `New.Data.targetParameter` and `New.Data.targetParameter_eq` in
`grh/src/New/Reduction/Data/LevelAndTwists.lean` of lsernau/grh-lean (`72fead1`).
-/

public section

namespace TauCeti.OneSidedBound

/-- The zero-indexed target row at one place, with source rank `k`, base weight `κ`, and half-gap
`g`. For positive `k`, the stem decreases by one and the tail starts at `-κ - 2g` and
has step `-2g`. -/
def targetParameter (k κ g i : ℕ) : ℤ :=
  if i + 1 < k then (↑(k / 2) : ℤ) - 1 - i else -((κ : ℤ) + ((i : ℤ) + 2 - k) * (2 * g))

/-- The initial `k - 1` entries of the row decrease by one. -/
@[simp] theorem targetParameter_of_succ_lt {k i : ℕ} (κ g : ℕ) (hi : i + 1 < k) :
    targetParameter k κ g i = (↑(k / 2) : ℤ) - 1 - i := by
  rw [targetParameter, ite_eq_left hi]

/-- The shifted part of the row is an arithmetic progression of step `-2g`. -/
@[simp] theorem targetParameter_of_le_succ {k i : ℕ} (κ g : ℕ) (hi : k ≤ i + 1) :
    targetParameter k κ g i = -((κ : ℤ) + ((i : ℤ) + 2 - k) * (2 * g)) := by
  rw [targetParameter, ite_eq_right (not_lt.mpr hi)]

/-- Indexing from the beginning of the tail gives the centre `κ + (2(j + 1) + 1)g` with its
sign reversed and with the half-gap `g` added back. -/
@[simp] theorem targetParameter_sub_one_add {k : ℕ} (hk : 0 < k) (κ g j : ℕ) :
    targetParameter k κ g (k - 1 + j) = (g : ℤ) - (κ + (2 * (j + 1) + 1) * g) := by
  rw [targetParameter_of_le_succ _ _ (by omega)]
  have h : ((k - 1 + j : ℕ) : ℤ) + 2 - k = (j : ℤ) + 1 := by omega
  rw [h]
  ring

/-- The finite row is the stem of length `k - 1` followed by the `m` shifted entries. -/
theorem targetParameter_fin_eq_append {k : ℕ} (hk : 0 < k) (κ g m : ℕ) :
    (fun i : Fin (k - 1 + m) ↦ targetParameter k κ g i) =
      Fin.append (fun i : Fin (k - 1) ↦ (↑(k / 2) : ℤ) - 1 - (i : ℕ))
        (fun j : Fin m ↦ (g : ℤ) - (κ + (2 * ((j : ℕ) + 1) + 1) * g)) := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    rw [Fin.append_left, Fin.val_castAdd]
    exact targetParameter_of_succ_lt _ _ (by omega)
  · intro j
    rw [Fin.append_right, Fin.val_natAdd]
    exact targetParameter_sub_one_add hk _ _ _

/-- The row is strictly decreasing exactly when the tail gap is positive and, if the stem is
nonempty, the first tail entry is strictly below the last stem entry. -/
theorem strictAnti_targetParameter_iff {k κ g : ℕ} :
    StrictAnti (targetParameter k κ g) ↔ 0 < g ∧ (2 ≤ k → k ≤ κ + 2 * g + k / 2) := by
  constructor
  · intro h
    have ht := h (Nat.lt_succ_self k)
    rw [targetParameter_of_le_succ _ _ (by omega), targetParameter_of_le_succ _ _ (by omega)] at ht
    constructor
    · by_contra! hg
      have : g = 0 := by omega
      simp [this] at ht
    · intro hk
      have hb := h (Nat.lt_succ_self (k - 2))
      rw [targetParameter_of_le_succ _ _ (by omega),
        targetParameter_of_succ_lt _ _ (by omega)] at hb
      have he : ((k - 2 + 1 : ℕ) : ℤ) + 2 - k = 1 := by omega
      rw [he, one_mul] at hb
      omega
  · rintro ⟨hg, hb⟩
    apply strictAnti_nat_of_succ_lt
    intro i
    by_cases hi : i + 2 < k
    · rw [targetParameter_of_succ_lt _ _ hi, targetParameter_of_succ_lt _ _ (by omega)]
      omega
    · rw [targetParameter_of_le_succ _ _ (by omega)]
      by_cases hj : i + 1 < k
      · rw [targetParameter_of_succ_lt _ _ hj]
        have he : ((i + 1 : ℕ) : ℤ) + 2 - k = 1 := by omega
        rw [he, one_mul]
        have := hb (by omega)
        omega
      · rw [targetParameter_of_le_succ _ _ (by omega)]
        push_cast
        have hgap : (0 : ℤ) < 2 * g := by omega
        nlinarith only [hgap]

/-- Every doubled row entry is at distance at least `2g` from the doubled negative lift centre
`-2(κ + (2j + 1)g)` when `κ + 2jg` is at least `⌈k/2⌉ - 1`. -/
theorem le_abs_two_mul_targetParameter_add {k κ g i j : ℕ}
    (hk : k ≤ k / 2 + κ + 2 * j * g + 1) :
    (2 : ℤ) * g ≤ |2 * targetParameter k κ g i + 2 * (κ + (2 * (j : ℤ) + 1) * g)| := by
  by_cases hi : i + 1 < k
  · rw [targetParameter_of_succ_lt _ _ hi]
    have hbound : (k : ℤ) ≤ ↑(k / 2) + κ + 2 * (j : ℤ) * g + 1 := by exact_mod_cast hk
    refine le_trans ?_ (le_abs_self _)
    have hstem : (↑(k / 2) : ℤ) + 1 - k ≤ (↑(k / 2) : ℤ) - 1 - i := by omega
    nlinarith only [hstem, hbound]
  · rw [targetParameter_of_le_succ _ _ (by omega)]
    -- Tail entries are at odd multiples of the doubled half-gap from every negative centre.
    have he : 2 * (-((κ : ℤ) + ((i : ℤ) + 2 - k) * (2 * g))) +
        2 * (κ + (2 * (j : ℤ) + 1) * g) = (2 * (j - ((i : ℤ) + 2 - k)) + 1) * (2 * g) := by ring
    rw [he, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (2 : ℤ) * g)]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (Int.one_le_abs (by omega : 2 * (j - ((i : ℤ) + 2 - k)) + 1 ≠ 0)) (by positivity)

/-- Every doubled row entry is at distance at least `2g` from the doubled positive lift centre
`2(κ + (2j + 1)g)` when `κ + 2jg` is at least `⌊k/2⌋ - 1`. -/
theorem le_abs_two_mul_targetParameter_sub {k κ g i j : ℕ}
    (hk : k / 2 ≤ κ + 2 * j * g + 1) :
    (2 : ℤ) * g ≤ |2 * targetParameter k κ g i - 2 * (κ + (2 * (j : ℤ) + 1) * g)| := by
  refine le_trans ?_ (neg_le_abs _)
  by_cases hi : i + 1 < k
  · rw [targetParameter_of_succ_lt _ _ hi]
    have hbound : (↑(k / 2) : ℤ) ≤ κ + 2 * (j : ℤ) * g + 1 := by exact_mod_cast hk
    have hstem : (↑(k / 2) : ℤ) - 1 - i ≤ (↑(k / 2) : ℤ) - 1 := by omega
    nlinarith only [hstem, hbound]
  · rw [targetParameter_of_le_succ _ _ (by omega)]
    have hz : 0 ≤ ((i : ℤ) + 2 - k) * ((2 : ℤ) * g) :=
      mul_nonneg (by omega) (by positivity)
    have hjg : 0 ≤ (j : ℤ) * g := by positivity
    nlinarith only [hz, hjg, Nat.cast_nonneg (α := ℤ) κ]

end TauCeti.OneSidedBound

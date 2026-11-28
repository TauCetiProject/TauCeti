/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.GelfandTsetlin.Basic
public import TauCeti.RepresentationTheory.DiscreteSeries.RegularParameter.Basic
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Branching of highest weights by shortening columns

Keeping some columns of a highest weight and shortening the others by one box gives an
interlacing weight in the next smaller rank, with the same determinant shift if no column
of the new full height is kept. The difference of the weight sums, which is the exponent
of the last diagonal coordinate in branching, is the shift plus the number of shortened columns.
-/

public section

open Finset

namespace TauCeti

/-- The column count at height `h` after retaining `kept h` of the columns at each height
and shortening the other columns by one box. Only positive heights in the new rank matter. -/
def branchColumnCount (c kept : ℕ → ℕ) (h : ℕ) : ℕ :=
  kept h + (c (h + 1) - kept (h + 1))

/-- The new columns at height `h` consist of the kept columns at that height and the
shortened columns of height `h + 1`. -/
theorem branchColumnCount_def (c kept : ℕ → ℕ) (h : ℕ) :
    branchColumnCount c kept h = kept h + (c (h + 1) - kept (h + 1)) := (rfl)

/-- For a rank-`n + 1` weight, shortening the specified columns gives the next row of the
original weight plus the columns kept at height `i + 1`. The determinant shift is unchanged. -/
theorem columnHighestWeight_branchColumnCount {n i : ℕ} (hi : i < n)
    {c kept : ℕ → ℕ} (hle : ∀ h ∈ Ioo (i + 1) (n + 1), kept h ≤ c h)
    (hn : kept n = 0) (e : ℤ) :
    columnHighestWeight n (branchColumnCount c kept) e i =
      columnHighestWeight (n + 1) c e (i + 1) + kept (i + 1) := by
  have hkept : (∑ h ∈ Ioo i n, (kept h : ℤ)) =
      (∑ h ∈ Ioo (i + 1) (n + 1), (kept h : ℤ)) + kept (i + 1) := by
    simpa only [Nat.succ_eq_add_one, Ico_add_one_left_eq_Ioo, hn, Nat.cast_zero, add_zero] using
      (sum_Ico_succ_top (Nat.succ_le_of_lt hi) (fun h ↦ (kept h : ℤ))).symm.trans
        (sum_Ioo_add_eq_sum_Ico (f := fun h ↦ (kept h : ℤ)) (Nat.succ_lt_succ hi)).symm
  have hshift (f : ℕ → ℤ) : ∑ h ∈ Ioo i n, f (h + 1) =
      ∑ h ∈ Ioo (i + 1) (n + 1), f h := by
    simpa only [Ico_add_one_left_eq_Ioo] using sum_Ico_add' f (i + 1) n 1
  rw [columnHighestWeight_def, columnHighestWeight_def]
  simp_rw [branchColumnCount_def, Nat.cast_add]
  rw [sum_add_distrib, hkept]
  have hc : (∑ h ∈ Ioo i n, ((c (h + 1) - kept (h + 1) : ℕ) : ℤ)) =
      ∑ h ∈ Ioo i n, ((c (h + 1) : ℤ) - kept (h + 1)) := by
    refine sum_congr rfl fun h hh ↦ Nat.cast_sub (hle _ ?_)
    have := mem_Ioo.mp hh
    exact mem_Ioo.mpr (by omega)
  rw [hc, sum_sub_distrib, hshift (fun h ↦ (c h : ℤ)), hshift (fun h ↦ (kept h : ℤ))]
  omega

/-- Shortening columns as prescribed by `branchColumnCount` gives interlacing in rank
one less. The hypothesis on `kept n` ensures the resulting weight has the same determinant shift. -/
theorem interlaces_columnHighestWeight_branchColumnCount {n : ℕ} {c kept : ℕ → ℕ}
    (hle : ∀ h ∈ Ioo 0 (n + 1), kept h ≤ c h) (hn : kept n = 0) (e : ℤ) :
    Interlaces (fun i : Fin (n + 1) ↦ columnHighestWeight (n + 1) c e i)
      (fun i : Fin n ↦ columnHighestWeight n (branchColumnCount c kept) e i) := by
  refine interlaces_iff.mpr fun i ↦ ?_
  have hi := i.isLt
  have hrow := columnHighestWeight_branchColumnCount hi
    (fun h hh ↦ hle h (Ioo_subset_Ioo_left (Nat.zero_le _) hh)) hn e
  simp only [Fin.val_castSucc, Fin.val_succ, hrow]
  constructor
  · have hs : (∑ h ∈ Ioo i.val (n + 1), (c h : ℤ)) =
        (∑ h ∈ Ioo (i.val + 1) (n + 1), (c h : ℤ)) + c (i.val + 1) := by
      simpa only [Nat.succ_eq_add_one, Ico_add_one_left_eq_Ioo] using
        (sum_Ioo_add_eq_sum_Ico (f := fun h ↦ (c h : ℤ)) (Nat.succ_lt_succ hi)).symm
    rw [columnHighestWeight_def, columnHighestWeight_def, hs]
    have h := hle (i.val + 1) (mem_Ioo.mpr (by omega))
    omega
  · exact le_add_of_nonneg_right (Int.natCast_nonneg _)

/-- The branching exponent is the determinant shift plus the number of shortened columns. -/
theorem sum_columnHighestWeight_sub_sum_branchColumnCount {n : ℕ} {c kept : ℕ → ℕ}
    (hle : ∀ h ∈ Ioo 0 (n + 1), kept h ≤ c h) (hn : kept n = 0) (e : ℤ) :
    (∑ i : Fin (n + 1), columnHighestWeight (n + 1) c e i) -
      (∑ i : Fin n, columnHighestWeight n (branchColumnCount c kept) e i) =
      e + ∑ h ∈ Ioo 0 (n + 1), ((c h - kept h : ℕ) : ℤ) := by
  have hk : (∑ i : Fin n, (kept (i.val + 1) : ℤ)) = ∑ h ∈ Ioo 0 (n + 1), (kept h : ℤ) := by
    rw [Fin.sum_univ_eq_sum_range (fun h : ℕ ↦ (kept (h + 1) : ℤ)), ← Nat.Ico_zero_eq_range]
    rw [sum_Ico_add' (fun h ↦ (kept h : ℤ)), ← Ico_add_one_left_eq_Ioo]
  rw [Fin.sum_univ_succ]
  have hrow (i : Fin n) := columnHighestWeight_branchColumnCount i.isLt
    (fun h hh ↦ hle h (Ioo_subset_Ioo_left (Nat.zero_le _) hh)) hn e
  simp_rw [Fin.val_succ, hrow]
  rw [sum_add_distrib, hk, columnHighestWeight_def, Fin.val_zero]
  have hc : (∑ h ∈ Ioo 0 (n + 1), ((c h - kept h : ℕ) : ℤ)) =
      (∑ h ∈ Ioo 0 (n + 1), (c h : ℤ)) - ∑ h ∈ Ioo 0 (n + 1), (kept h : ℤ) := by
    rw [← sum_sub_distrib]
    exact sum_congr rfl fun h hh ↦ Nat.cast_sub (hle h hh)
  omega

end TauCeti

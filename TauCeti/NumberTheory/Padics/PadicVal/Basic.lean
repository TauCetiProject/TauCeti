/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Nat.PadicValNat
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Action.Defs
import TauCeti.Data.Nat.Interval

/-!
# Sums of `p`-adic valuations over intervals

Double counting prime powers `p ^ i` (`1 ≤ i ≤ a`) over the interval `[1, n)` gives
`(∑ h ∈ Finset.Ico 1 n, (a - padicValNat p h)) + ∑ i ∈ Finset.Icc 1 a, n / p ^ i = a * n`
whenever `0 < n` and `a ≤ padicValNat p n`.
-/

public section

namespace TauCeti

/-- For `0 < n` and `a ≤ v_p(n)`,
`(∑_{1 ≤ h < n} (a - v_p(h))) + ∑_{1 ≤ i ≤ a} n / p ^ i = a * n`. -/
theorem sum_Ico_sub_padicValNat_add_sum_Icc_div (p : ℕ) {n a : ℕ} (hn : 0 < n)
    (ha : a ≤ padicValNat p n) :
    (∑ h ∈ Finset.Ico 1 n, (a - padicValNat p h)) +
      ∑ i ∈ Finset.Icc 1 a, n / p ^ i = a * n := by
  rcases eq_or_ne p 1 with rfl | hp1
  · have ha0 : a = 0 := by simpa [Nat.padicValNat_def] using ha
    subst ha0
    simp
  have ha' : a ≤ multiplicity p n := by rwa [← Nat.padicValNat_def]
  have hterm : ∀ h ∈ Finset.Ico 1 n,
      a - padicValNat p h = ∑ i ∈ Finset.Icc 1 a, if ¬ p ^ i ∣ h then 1 else 0 := by
    intro h hh
    rw [Finset.mem_Ico] at hh
    rw [Finset.sum_boole, Nat.cast_id]
    have hfilt : {i ∈ Finset.Icc 1 a | ¬ p ^ i ∣ h} = Finset.Icc (padicValNat p h + 1) a := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_Icc, Nat.padicValNat_def,
        Nat.pow_dvd_iff_le_multiplicity hp1 (by omega : h ≠ 0)]
      omega
    rw [hfilt, Nat.card_Icc]
    omega
  rw [Finset.sum_congr rfl hterm, Finset.sum_comm, ← Finset.sum_add_distrib]
  have hinner : ∀ i ∈ Finset.Icc 1 a,
      (∑ h ∈ Finset.Ico 1 n, if ¬ p ^ i ∣ h then 1 else 0) + n / p ^ i = n := by
    intro i hi
    rw [Finset.mem_Icc] at hi
    have hdvd : p ^ i ∣ n := (Nat.pow_dvd_iff_le_multiplicity hp1 hn.ne').mpr (hi.2.trans ha')
    have hdiv : n / p ^ i = (n - 1) / p ^ i + 1 := by
      conv_lhs => rw [← Nat.sub_add_cancel hn]
      exact Nat.succ_div_of_dvd (by rw [Nat.sub_add_cancel hn]; exact hdvd)
    rw [Finset.sum_boole, Nat.cast_id, hdiv, ← add_assoc, Nat.Ico_filter_not_dvd_card_add_div,
      Nat.sub_add_cancel hn]
  rw [Finset.sum_congr rfl hinner, Finset.sum_const, Nat.card_Icc, smul_eq_mul,
    Nat.add_sub_cancel]

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.GelfandTsetlin.InterlacingCounts
public import TauCeti.RepresentationTheory.DiscreteSeries.RegularParameter.Basic
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Data.Fin.Rev

/-!
# From Harish-Chandra parameters to interlacing weights

In the compact branching problem for `U(n + 1)` and `U(n)`, the larger parameter
interlaces the negative of the parameter of the smaller form in the bilinear pairing.
Negating reverses the sorted order. After this reversal, the two Weyl shifts differ by
one at either end of each comparison, so interlacing of the doubled parameters is
exactly weak interlacing of the highest weights. This also bounds the exponent of the
added `U(1)` factor in terms of the larger weight's boxes and determinant power.

This is the weight comparison used by `New.Exchange.exists_isBranchingPairing` in
`grh/src/New/Determinant/AuxiliaryForms/LastPath.lean` of [lsernau/grh-lean][short-proof].
For compact branching, see Goodman and Wallach, *Symmetry, Representations, and Invariants*,
Theorem 8.1.1.

[short-proof]: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/New/Determinant/AuxiliaryForms/LastPath.lean
-/

public section

open Finset

namespace TauCeti

/-- The threshold criterion for compact branching against the dual smaller weight.
The given parameters may be listed in any order; the highest weights are listed in
weakly decreasing order. -/
theorem interlaces_iff_card_filter_doubledHCParameter {ι ι' : Type*} [Fintype ι] [Fintype ι']
    {n : ℕ} (hι : Fintype.card ι = n + 1) (hι' : Fintype.card ι' = n)
    {κ η : ℕ → ℕ} {e d : ℤ} {l : ι → ℤ} {m : ι' → ℤ}
    (hl : IsDoubledHCParameter κ e l) (hm : IsDoubledHCParameter η d m) :
    Interlaces (fun i : Fin (n + 1) ↦ columnHighestWeight (n + 1) κ e i)
      (fun i : Fin n ↦ -columnHighestWeight n η d i.rev) ↔
      ∀ x : ℤ, #{i | x < -m i} ≤ #{i | x < l i} ∧ #{i | x < l i} ≤ #{i | x < -m i} + 1 := by
  obtain ⟨σ, hσ⟩ := hl.exists_equiv
  obtain ⟨τ, hτ⟩ := hm.exists_equiv
  let σ' := σ.trans (finCongr hι)
  let τ' := τ.trans (finCongr hι')
  let a (i : Fin (n + 1)) := doubledHCParameter (n + 1) κ e i
  let b (i : Fin n) := -doubledHCParameter n η d i.rev
  have ha : Antitone a := fun _ _ h ↦ (doubledHCParameter_strictAnti _ _ _).antitone h
  have hb : Antitone b := fun _ _ h ↦ neg_le_neg
    ((doubledHCParameter_strictAnti _ _ _).antitone (Fin.rev_anti h))
  have hca (x : ℤ) : #{i | x < l i} = #{i | x < a i} := by
    exact card_equiv σ' fun i ↦ by simp [a, σ', hσ, hι]
  have hcb (x : ℤ) : #{i | x < -m i} = #{i | x < b i} := by
    exact card_equiv (τ'.trans Fin.revPerm) fun i ↦ by
      simp only [mem_filter, mem_univ, true_and, Equiv.trans_apply, Fin.revPerm_apply, b,
        Fin.rev_rev, τ', finCongr_apply, Fin.val_cast, hτ, hι']
  simp only [hca, hcb, ← interlaces_iff_card_filter ha hb, interlaces_iff]
  refine forall_congr' fun i ↦ ?_
  simp only [a, b, doubledHCParameter_def, Nat.cast_add, Nat.cast_one,
    Fin.val_castSucc, Fin.val_succ, Fin.val_rev]
  have hi := i.isLt
  omega

/-- The branching exponent for a row interlacing the larger column weight is bounded by
that weight's number of boxes below the top height plus the absolute value of its determinant
power. The smaller row need not be given in column coordinates. -/
theorem abs_sum_sub_sum_le_of_interlaces_columnHighestWeight {n : ℕ} {κ : ℕ → ℕ} {e : ℤ}
    {m : Fin n → ℤ}
    (h : Interlaces (fun i : Fin (n + 1) ↦ columnHighestWeight (n + 1) κ e i) m) :
    |(∑ i : Fin (n + 1), columnHighestWeight (n + 1) κ e i) - ∑ i, m i| ≤
      (boxesBelow (n + 1) κ : ℤ) + |e| := by
  have hb := h.sum_sub_sum_mem_Icc
  have hlast : Ioo n (n + 1) = ∅ := by grind
  have he_last : columnHighestWeight (n + 1) κ e (Fin.last n) = e := by
    simp [columnHighestWeight_def, hlast]
  rw [Set.mem_Icc, he_last] at hb
  have hboxes : ∑ j ∈ Ioo 0 (n + 1), κ j ≤ boxesBelow (n + 1) κ := by
    rw [boxesBelow_eq_sum_sum_Ioo]
    exact single_le_sum (f := fun i ↦ ∑ j ∈ Ioo i (n + 1), κ j)
      (fun _ _ ↦ Nat.zero_le _) (mem_range.mpr (Nat.zero_lt_succ n))
  have hboxes' : ∑ j ∈ Ioo 0 (n + 1), (κ j : ℤ) ≤ (boxesBelow (n + 1) κ : ℤ) := by
    exact_mod_cast hboxes
  have hu : columnHighestWeight (n + 1) κ e (0 : Fin (n + 1)) ≤
      (boxesBelow (n + 1) κ : ℤ) + |e| := by
    simpa only [Fin.val_zero, columnHighestWeight_def, add_comm e] using
      add_le_add hboxes' (le_abs_self e)
  have he : -((boxesBelow (n + 1) κ : ℤ) + |e|) ≤ e := by
    have := neg_abs_le e
    omega
  exact abs_le.mpr ⟨he.trans hb.1, hb.2.trans hu⟩

end TauCeti

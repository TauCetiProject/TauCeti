/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.PartnerLoss
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# Paying for a selected term in a local prime sum

At a place with a near partner, a coupling at exponent `e` contributes a credit of
`⌊l / p ^ e⌋` for degree `l`. Remove that partner term from the local minimum sum and charge
only the rounding remainder, rather than charging the whole partner term as a loss. Places
without a coupling incur no rounding charge. This separates the local prime-sum comparison
from the subsequent estimates on the uncoupled terms and on factorial valuations.

The comparison is the small-prime accounting step in
`New.Data.gammaPrime_mul_degree_sub_le_localPrimeSumTotal_add` in
`grh/src/New/Derivatives/Sharpness/Cases.lean` of lsernau/grh-lean (revision `72fead1`).
-/

public section

open Filter Finset

namespace TauCeti.OneSidedBound

/-- If `κ ≤ l`, omitting the contribution of `p ^ a` from the partner minima costs at most the
coupling multiplicity `l / p ^ a` plus the fractional part of the quotient. This also holds when
`a` is not a contributing exponent: in that case no term is removed. -/
theorem localPrimeSum_min_le_omit_add_div {d p : ℕ} [Fact d.Prime]
    {κ l : ℕ} (hκ : κ ≤ l) (w : ℕ → ℝ) (a : ℕ) :
    localPrimeSum d p (fun n ↦ min ((κ : ℝ) / n) (w n)) ≤
      localPrimeSum d p (fun n ↦ if n = p ^ a then 0 else min ((κ : ℝ) / n) (w n)) +
        ((l / p ^ a : ℕ) : ℝ) + (l % p ^ a : ℕ) / (p ^ a : ℕ) := by
  classical
  rcases le_or_gt p 1 with hp | hp
  · obtain rfl | rfl : p = 0 ∨ p = 1 := by omega
    · have hz (g : ℕ → ℝ) : localPrimeSum d 0 g = 0 := by
        simp [localPrimeSum_def, (Fact.out : d.Prime).ne_zero.symm]
      rw [hz, hz, zero_add]
      positivity
    · simp [legendreSym.at_one, Nat.mod_one]
  let f (n : ℕ) : ℝ := min ((κ : ℝ) / n) (w n)
  let t (e : ℕ) : ℝ := if 0 < e ∧ (p = d ∨ legendreSym d p = -1 ∧ Odd e) then f (p ^ e) else 0
  have hmask : (∑' e, if e = a then 0 else t e) =
      ∑' e, if 0 < e ∧ (p = d ∨ legendreSym d p = -1 ∧ Odd e) then
        (if p ^ e = p ^ a then 0 else f (p ^ e)) else 0 := by
    apply tsum_congr
    intro e
    have he : p ^ e = p ^ a ↔ e = a := (pow_right_injective₀ (by omega) hp.ne').eq_iff
    by_cases h : e = a <;> simp [he, h, t]
  rw [localPrimeSum_def, localPrimeSum_def, ← hmask]
  by_cases hs : Summable t
  swap
  · -- Removing one term preserves nonsummability, so both totalized sums are zero.
    have ho : ¬ Summable (fun e ↦ if e = a then 0 else t e) := by
      apply mt (summable_congr_atTop ?_).mpr hs
      filter_upwards [eventually_gt_atTop a] with e he
      simp [he.ne']
    rw [tsum_eq_zero_of_not_summable hs, tsum_eq_zero_of_not_summable ho, mul_zero, zero_add]
    positivity
  have hd : (0 : ℝ) < (p ^ a : ℕ) := by exact_mod_cast pow_pos (by omega : 0 < p) a
  have hdiv : (l : ℝ) / (p ^ a : ℕ) =
      ((l / p ^ a : ℕ) : ℝ) + (l % p ^ a : ℕ) / (p ^ a : ℕ) := by
    apply (div_eq_iff hd.ne').2
    field_simp
    exact_mod_cast (Nat.div_add_mod' l (p ^ a)).symm
  have ht : t a ≤ (l : ℝ) / (p ^ a : ℕ) := by
    have hκ' : (κ : ℝ) ≤ l := by exact_mod_cast hκ
    refine le_trans ?_ (div_le_div_of_nonneg_right hκ' hd.le)
    unfold t f
    split_ifs
    · exact min_le_left _ _
    · positivity
  have ht' : (if p = d then (1 / 2 : ℝ) else 1) * t a ≤ (l : ℝ) / (p ^ a : ℕ) :=
    (mul_le_mul_of_nonneg_left ht (by split <;> norm_num)).trans
      (mul_le_of_le_one_left (by positivity) (by split <;> norm_num))
  rw [hs.tsum_eq_add_tsum_ite a, mul_add]
  linarith

/-- Compare the reciprocal rate at the jet degrees with the capped prime sum at the reference
weights, after subtracting the multiplicities of the selected couplings. The remaining cost is
bounded by three terms: the increase in orders at the reciprocal rate, the minima at
uncoupled prime powers, and the sum of the fractional parts charged at selected powers.
A choice of `none` leaves all prime powers in the minimum sum and contributes no credit or
rounding error. -/
theorem mul_sum_sub_coupling_le_localPrimeSum_add {ι : Type*} {d p : ℕ} [Fact d.Prime]
    (s : Finset ι) (κ l : ι → ℕ) (w : ℕ → ι → ℝ) (e : ι → Option ℕ)
    (hκ : ∀ i ∈ s, (e i).isSome → κ i ≤ l i)
    (hw : ∀ i ∈ s, ∀ᶠ j : ℕ in atTop, 0 ≤ w (p ^ j) i) :
    localPrimeSum d p (fun n ↦ (n : ℝ)⁻¹) * (∑ i ∈ s, (l i : ℝ)) -
        (∑ i ∈ s, (e i).elim 0 fun a ↦ ((l i / p ^ a : ℕ) : ℝ)) ≤
      (∑ i ∈ s, localPrimeSum d p (fun n ↦ max ((κ i : ℝ) / n - w n i) 0)) +
      localPrimeSum d p (fun n ↦ (n : ℝ)⁻¹) * (∑ i ∈ s, ((l i : ℝ) - κ i)) +
      (∑ i ∈ s, localPrimeSum d p (fun n ↦
        if (e i).map (p ^ ·) = some n then 0 else min ((κ i : ℝ) / n) (w n i))) +
      ∑ i ∈ s, (e i).elim 0 fun a ↦ ((l i % p ^ a : ℕ) : ℝ) / (p ^ a : ℕ) := by
  have hdeficit := mul_sum_weight_sub_localPrimeSum_total (d := d) (p := p) s
    (fun i ↦ (κ i : ℝ)) w hw
  have hsplit : (∑ i ∈ s, (l i : ℝ)) =
      (∑ i ∈ s, (κ i : ℝ)) + ∑ i ∈ s, ((l i : ℝ) - κ i) := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro i _
    ring
  have hcredit := sum_le_sum (s := s) (f := fun i ↦
    localPrimeSum d p (fun n ↦ min ((κ i : ℝ) / n) (w n i)))
    (g := fun i ↦ localPrimeSum d p (fun n ↦
        if (e i).map (p ^ ·) = some n then 0 else min ((κ i : ℝ) / n) (w n i)) +
      (e i).elim 0 (fun a ↦ ((l i / p ^ a : ℕ) : ℝ)) +
      (e i).elim 0 (fun a ↦ ((l i % p ^ a : ℕ) : ℝ) / (p ^ a : ℕ))) (fun i hi ↦ by
        cases he : e i with
        | none => simp
        | some a =>
          simpa only [he, Option.map_some, Option.some.injEq, Option.elim_some, eq_comm] using
            localPrimeSum_min_le_omit_add_div (d := d) (hκ i hi (by simp [he])) (fun n ↦ w n i) a)
  rw [hsplit, mul_add]
  simp only [sum_add_distrib] at hcredit
  linarith

end TauCeti.OneSidedBound

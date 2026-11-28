/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.PrimeCounting

import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import TauCeti.Analysis.SpecialFunctions.Log.Bounds
import TauCeti.Analysis.SpecialFunctions.Pow.Asymptotics
import TauCeti.NumberTheory.Chebyshev.Mertens

/-!
# Selecting top weights with a small prime-weighted defect

Each candidate prime has a nonnegative colength share for each admissible vector of top
weights. The cost includes both the share and a charge for dropping the prime when that
share is too large. Bounds for the mean shares over the finite box of weight choices suffice
for a single vector with small total cost. Mertens' bound makes the selection uniform in the
prime set. The power cutoffs used for the small- and medium-prime shares leave enough room to
absorb the logarithmic factors in that bound.

The cost and the two regimes are from Levent Alpöge's theta-chain argument, in particular
`Formalism.MainNotions.AuxBlock8.ArchimedeanSignatureMatching` in
`Formalism/SharpRestriction/GrowthBounds/SmallOrderPrimes.lean` of the
[published formalization](https://github.com/leanprover-community/riemann-hypothesis/tree/40e56bab026552e089d7afcfeff08d2defb9c005).
-/

public section

open Filter Finset Real
open scoped BigOperators NNReal

namespace TauCeti.ThetaLift

/-- Choose one admissible vector with a small total prime-weighted cost. `share p w` is the
colength share at `p` for the vector `w`; a share strictly greater than `δ` triggers a charge
of two. The input bounds only the uniform mean share at each candidate prime, not its
pointwise size. The parameter `L` is the logarithm of the prime cutoff. -/
theorem exists_topWeights_badShareCost_le {Ω : Type*} (W : Finset Ω) (hW : W.Nonempty)
    (P : Finset ℕ) {L δ B : ℝ} (hL : 0 ≤ L) (hP : P ⊆ Nat.primesLE ⌊exp L⌋₊) (hδ : 0 < δ)
    (share : ℕ → Ω → ℝ≥0) (S : ℝ≥0) (hshare : ∀ p ∈ P, (𝔼 w ∈ W, (share p w : ℝ)) ≤ S)
    (hbudget : (2 / δ + 4) * (L + (log 4 + 4)) * S ≤ B) :
    ∃ w ∈ W, ∑ p ∈ P, log p / p * ((if δ < (share p w : ℝ) then 2 else 0) +
      4 * (share p w : ℝ)) ≤ B := by
  let cost (p : ℕ) (w : Ω) : ℝ := (if δ < (share p w : ℝ) then 2 else 0) + 4 * (share p w : ℝ)
  have hcost (p : ℕ) (w : Ω) : cost p w ≤ (2 / δ + 4) * (share p w : ℝ) := by
    have hc : 0 ≤ (2 / δ : ℝ) := by positivity
    dsimp only [cost]
    rw [add_mul]
    apply add_le_add_left
    split_ifs with hw
    · simpa only [div_mul_cancel₀ _ hδ.ne'] using mul_le_mul_of_nonneg_left hw.le hc
    · positivity
  have hp (p : ℕ) (hp : p ∈ Nat.primesLE ⌊exp L⌋₊) : 0 ≤ log p / p :=
    div_nonneg (log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primesLE hp).one_lt.le))
      (Nat.cast_nonneg _)
  have hsum : ∑ p ∈ P, log p / p ≤ L + (log 4 + 4) := by
    have hX : 1 ≤ exp L := by simpa only [exp_zero] using Real.exp_le_exp.mpr hL
    have h := Chebyshev.sum_primesLE_log_div_le hX
    rw [log_exp] at h
    exact (sum_le_sum_of_subset_of_nonneg hP fun p hpm _ ↦ hp p hpm).trans h
  have hC : 0 ≤ 2 / δ + 4 := by positivity
  refine exists_le_of_expect_le hW ?_
  calc
    (𝔼 w ∈ W, ∑ p ∈ P, log p / p * cost p w) =
        ∑ p ∈ P, log p / p * (𝔼 w ∈ W, cost p w) := by
      rw [expect_sum_comm]
      simp only [mul_expect]
    _ ≤ ∑ p ∈ P, log p / p * ((2 / δ + 4) * S) := by
      refine sum_le_sum fun p hpP ↦ mul_le_mul_of_nonneg_left ?_ (hp p (hP hpP))
      refine (expect_le_expect fun w _ ↦ hcost p w).trans ?_
      rw [← mul_expect]
      exact mul_le_mul_of_nonneg_left (hshare p hpP) hC
    _ = (2 / δ + 4) * (∑ p ∈ P, log p / p) * S := by rw [← sum_mul]; ring
    _ ≤ _ := by gcongr
    _ ≤ B := hbudget

private theorem topWeightSelection_factor_le {x ε : ℝ} (hx : 1 ≤ x) (hε : 0 ≤ ε) :
    (2 / x ^ (-ε) + 4) * (x ^ (ε / 3) + (log 4 + 4)) ≤ 42 * x ^ (4 * ε / 3) := by
  have hx₀ : 0 < x := zero_lt_one.trans_le hx
  rw [rpow_neg hx₀.le, div_inv_eq_mul]
  calc
    _ ≤ (6 * x ^ ε) * (7 * x ^ (ε / 3)) := by
      gcongr
      · linarith [one_le_rpow hx hε]
      · linarith [one_le_rpow hx (by positivity : 0 ≤ ε / 3), log_four_le_two]
    _ = _ := by
      rw [mul_mul_mul_comm, ← rpow_add hx₀, show ε + ε / 3 = 4 * ε / 3 by ring]
      norm_num

/-- The small- and medium-prime share budgets fit inside the saving `x ^ (-c)` with
cutoffs `x ^ A_w` and `x ^ (A_w / 2)` respectively. The bounds on the two exponents leave
room for the constant from Mertens' estimate and for the logarithmic growth of `s_max`.
In particular they hold when `0 < ε < 1/52`, `1 ≤ c`, and `2*c + 2*A + 4 ≤ A_w`.
The threshold is uniform in the chain length `m`, the number `n` of tops, the rank `k`, and
the local count bound `s_max`. The prime cutoff is `exp (x ^ (ε / 3))`. -/
theorem eventually_topWeightSelection_budget_le {ε c A A_w : ℝ} (hε : 0 ≤ ε)
    (hI : 1 / 2 + A + c + (11 / 6) * ε < A_w / 2)
    (hII : 3 + 2 * A + c + (23 / 6) * ε < A_w) (C C_N : ℝ≥0) (r : ℕ) :
    ∀ᶠ x : ℝ in atTop, ∀ (m n k s_max : ℕ),
      (m : ℝ) ≤ x ^ (1 / 2 + ε / 2) → (n : ℝ) ≤ 2 * x ^ A →
      (k : ℝ) ≤ 2 * x ^ (A + 5 / 2 + 2 * ε) → (s_max : ℝ) ≤ C_N * log x →
      (2 / x ^ (-ε) + 4) * (x ^ (ε / 3) + (log 4 + 4)) *
        max ((C : ℝ) * m * n * s_max / x ^ (A_w / 2))
          ((C : ℝ) * m * n * (r : ℝ) ^ 2 * k / x ^ A_w) ≤ x ^ (-c) := by
  let aI : ℝ := 1 / 2 + A + (11 / 6) * ε
  let aII : ℝ := 3 + 2 * A + (23 / 6) * ε
  have hgI : aI < A_w / 2 - c := by dsimp [aI]; linarith
  have hgII : aII < A_w - c := by dsimp [aII]; linarith
  have hlog := ((isLittleO_log_rpow_atTop (sub_pos.mpr hgI)).const_mul_left
    (84 * (C : ℝ) * C_N)).eventuallyLE
  filter_upwards [eventually_ge_atTop (1 : ℝ), hlog,
    eventually_const_mul_rpow_le_rpow hgII (168 * (C : ℝ) * (r : ℝ) ^ 2)] with x hx hxlog hxII
  intro m n k s_max hm hn hk hs
  have hx₀ : 0 < x := zero_lt_one.trans_le hx
  have hnormalizeI : A_w / 2 - c - aI + aI = -c + A_w / 2 := by ring
  have hnormalizeII : A_w - c = -c + A_w := by ring
  rw [mul_max_of_nonneg _ _ (by positivity), max_le_iff]
  constructor
  · rw [← mul_div_assoc, div_le_iff₀ (rpow_pos_of_pos hx₀ _), ← rpow_add hx₀]
    calc
      _ ≤ (42 * x ^ (4 * ε / 3)) * (C * x ^ (1 / 2 + ε / 2) * (2 * x ^ A) *
          (C_N * log x)) :=
        mul_le_mul (topWeightSelection_factor_le hx hε) (by gcongr) (by positivity) (by positivity)
      _ = (84 * (C : ℝ) * C_N * log x) * x ^ aI := by
        have he : aI = 4 * ε / 3 + (1 / 2 + ε / 2) + A := by dsimp [aI]; ring
        rw [he]
        simp only [rpow_add hx₀]
        ring
      _ ≤ _ := by
        rw [← hnormalizeI, rpow_add hx₀ (A_w / 2 - c - aI) aI]
        exact mul_le_mul_of_nonneg_right ((le_abs_self _).trans
          (by simpa only [Real.norm_eq_abs, abs_of_pos (rpow_pos_of_pos hx₀ _)] using hxlog))
          (rpow_nonneg hx₀.le _)
  · rw [← mul_div_assoc, div_le_iff₀ (rpow_pos_of_pos hx₀ _), ← rpow_add hx₀]
    calc
      _ ≤ (42 * x ^ (4 * ε / 3)) * (C * x ^ (1 / 2 + ε / 2) * (2 * x ^ A) *
          (r : ℝ) ^ 2 * (2 * x ^ (A + 5 / 2 + 2 * ε))) :=
        mul_le_mul (topWeightSelection_factor_le hx hε) (by gcongr) (by positivity) (by positivity)
      _ = (168 * (C : ℝ) * (r : ℝ) ^ 2) * x ^ aII := by
        have he : aII = 4 * ε / 3 + (1 / 2 + ε / 2) + A + (A + 5 / 2 + 2 * ε) := by
          dsimp [aII]; ring
        rw [he]
        simp only [rpow_add hx₀]
        ring
      _ ≤ _ := by rwa [hnormalizeII] at hxII

/-- For large `x`, bounds for the mean shares in the two prime ranges give one top-weight
vector with total cost at most `x ^ (-c)`. The mean bound below `p₀` uses the rank `k` and the
fixed orbit parameter `r`; the bound from `p₀` onward uses the local count bound `s_max`.
The threshold does not depend on the candidate primes, the split point `p₀`, or the weight box. -/
theorem eventually_exists_topWeights_badShareCost_le {ε c A A_w : ℝ}
    (hI : 1 / 2 + A + c + (11 / 6) * ε < A_w / 2)
    (hII : 3 + 2 * A + c + (23 / 6) * ε < A_w) (C C_N : ℝ≥0) (r : ℕ) :
    ∀ᶠ x : ℝ in atTop, ∀ (m n k s_max : ℕ),
      (m : ℝ) ≤ x ^ (1 / 2 + ε / 2) → (n : ℝ) ≤ 2 * x ^ A →
      (k : ℝ) ≤ 2 * x ^ (A + 5 / 2 + 2 * ε) → (s_max : ℝ) ≤ C_N * log x →
      ∀ {Ω : Type*} (W : Finset Ω), W.Nonempty →
      ∀ (P : Finset ℕ), P ⊆ Nat.primesLE ⌊exp (x ^ (ε / 3))⌋₊ →
      ∀ (p₀ : ℝ) (share : ℕ → Ω → ℝ≥0),
        (∀ p ∈ P, (𝔼 w ∈ W, (share p w : ℝ)) ≤
          if (p : ℝ) < p₀ then (C : ℝ) * m * n * (r : ℝ) ^ 2 * k / x ^ A_w
          else (C : ℝ) * m * n * s_max / x ^ (A_w / 2)) →
        ∃ w ∈ W, ∑ p ∈ P, log p / p * ((if x ^ (-ε) < (share p w : ℝ) then 2 else 0) +
          4 * (share p w : ℝ)) ≤ x ^ (-c) := by
  rcases lt_or_ge ε 0 with hε | hε
  · -- With a negative exponent the prime cutoff eventually falls below the first prime.
    have hlim : Tendsto (fun x : ℝ ↦ x ^ (ε / 3)) atTop (nhds 0) := by
      simpa only [neg_neg] using tendsto_rpow_neg_atTop (y := -(ε / 3)) (by linarith)
    filter_upwards [eventually_ge_atTop (0 : ℝ), hlim.eventually_lt_const (log_pos one_lt_two)]
      with x hx hlog
    intro _ _ _ _ _ _ _ _ _ W hW P hP _ _ _
    have hcut : ⌊exp (x ^ (ε / 3))⌋₊ < 2 := by
      apply (Nat.floor_lt (exp_pos _).le).mpr
      exact_mod_cast (exp_lt_exp.mpr hlog).trans_eq (exp_log (by norm_num : 0 < (2 : ℝ)))
    have hempty : P = ∅ := eq_empty_iff_forall_notMem.mpr fun p hp ↦
      (not_le_of_gt hcut) ((Nat.prime_of_mem_primesLE (hP hp)).two_le.trans
        (Nat.le_of_mem_primesLE (hP hp)))
    obtain ⟨w, hw⟩ := hW
    exact ⟨w, hw, by simpa only [hempty, sum_empty] using rpow_nonneg hx (-c)⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    eventually_topWeightSelection_budget_le hε hI hII C C_N r] with x hx hbudget
  intro m n k s_max hm hn hk hs Ω W hW P hP p₀ share hshare
  have hx₀ : 0 < x := zero_lt_one.trans_le hx
  let S : ℝ≥0 := ⟨max ((C : ℝ) * m * n * s_max / x ^ (A_w / 2))
    ((C : ℝ) * m * n * (r : ℝ) ^ 2 * k / x ^ A_w), le_max_of_le_left (by positivity)⟩
  refine exists_topWeights_badShareCost_le W hW P (rpow_nonneg hx₀.le _) hP
    (rpow_pos_of_pos hx₀ _) share S (fun p hp ↦ (hshare p hp).trans ?_)
    (hbudget m n k s_max hm hn hk hs)
  split_ifs
  · exact le_max_right ..
  · exact le_max_left ..

end TauCeti.ThetaLift

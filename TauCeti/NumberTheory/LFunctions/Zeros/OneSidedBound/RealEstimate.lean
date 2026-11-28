/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.TotalRemainder
import TauCeti.Analysis.Asymptotics.NatFloor
import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.IntegerEstimate
import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.PlaceCount

/-!
# From the total prime remainder to a real-cutoff bound

An upper bound on the total remainder controls the signed remainder at integer cutoffs.
The second cutoff contributes only logarithmic errors, which decay as powers of the
first cutoff because the cutoffs are far apart. The signed remainder can increase by at
most `O(1 / y)` between `⌊y⌋₊` and `y`, so an arbitrarily small exponent loss suffices to
transfer the bound to real cutoffs.

The exponents and the final estimate are those of `New.eventually_primeRemainder_natCast_le`
and `New.eventually_primeRemainder_le_rpow` in `New/Reduction/OneSidedBound.lean` of
[lsernau/grh-lean](https://github.com/lsernau/grh-lean) at `72fead1`.
-/

public section

open Filter Real

namespace TauCeti.OneSidedBound

/-- Given admissible scales carrying the total remainder bound at every large integer,
logarithmic decay at the second cutoff yields an upper bound with exponent `-1/2 + 6ε`
at the first cutoff. Only the scale and place conditions that enter this estimate are needed. -/
theorem Parameters.eventually_primeRemainder_natCast_le_of_totalRemainder_bound (P : Parameters)
    {ε : ℝ} {j : ℕ} (hj : 24 ≤ ε * (j : ℝ))
    (hdecay : ∀ᶠ y : ℝ in atTop,
      |primeRemainder P.d P.q₀ y| ≤ log y ^ (-(j : ℝ)) ∧
      |primeRemainder P.d 1 y| ≤ log y ^ (-(j : ℝ)))
    (hdata : ∀ᶠ x : ℕ in atTop, ∃ x₁ b m s : ℕ, ∃ B : Finset (ZMod (P.q₁ s))ˣ,
      x₁ ≤ x * b ∧ (x : ℝ) ^ (ε / 6) - 1 ≤ log x₁ ∧
      log b ≤ (x : ℝ) ^ ε + 1 ∧ √(x : ℝ) ≤ (m : ℝ) ∧
      (∀ τ ∈ B, ZMod.unitsMap (P.q₀_dvd_q₁ s) τ = -1) ∧
      (towerDeg s : ℝ) ≤ B.card * log b ∧
      (m : ℝ) * P.totalRemainder s B (x * b) (x * b : ℕ) x x₁ ≤
        (Fintype.card (ZMod (P.q₁ s))ˣ : ℝ) * (x * b : ℕ) * log b ^ 5) :
    ∀ᶠ x : ℕ in atTop, primeRemainder P.d P.q₀ x ≤
      (64 * (P.q₀.totient : ℝ) + 3) * (x : ℝ) ^ (-(1 / 2) + 6 * ε) := by
  apply eventually_le_rpow_natCast_of_two_cutoffs (Nat.cast_nonneg _) hj
    (hdecay.mono fun _ h ↦ h.1) (hdecay.mono fun _ h ↦ h.2)
  have hε : 0 < ε := pos_of_mul_pos_left (by linarith only [hj]) (Nat.cast_nonneg j)
  filter_upwards [eventually_gt_atTop (1 : ℕ), hdata] with x hx
    ⟨x₁, b, m, s, B, hcut, hlog₁, hlogb, hmsq, hclass, hsize, hmain⟩
  have hx' : (1 : ℝ) < x := by exact_mod_cast hx
  have hx₁ : (0 : ℝ) < x₁ := by
    have h := one_lt_rpow hx' (by positivity : 0 < ε / 6)
    exact (Nat.cast_nonneg x₁).lt_of_ne' (fun hz ↦ by rw [hz, log_zero] at hlog₁; linarith)
  have ha : 0 < x * b := (Nat.cast_pos.mp hx₁).trans_le hcut
  have hb : 0 < b := Nat.pos_of_mul_pos_left ha
  have hmax : max x x₁ ≤ x * b := max_le (Nat.le_mul_of_pos_right _ hb) hcut
  have hm : (0 : ℝ) < m := (sqrt_pos.mpr (zero_lt_one.trans hx')).trans_le hmsq
  refine ⟨x₁, hx₁, log b, log_nonneg (by exact_mod_cast hb), m, hlog₁, hlogb, hmsq, ?_⟩
  refine P.primeRemainder_le_of_totalRemainder_bound hclass (by exact_mod_cast ha)
    (zero_lt_one.trans hx') hx₁ ?_ hm ?_ hmain
  · simpa only [Nat.floor_natCast] using Nat.floor_mono
      (by exact_mod_cast hmax : max (x : ℝ) (x₁ : ℝ) ≤ ((x * b : ℕ) : ℝ))
  · simpa only [P.card_filter_unitsMap_eq_one] using hsize

/-- The signed prime remainder satisfies the one-sided bound with exponent `-1/2 + ε` for
every `ε > 0` at large real cutoffs if and only if it does so at large integer cutoffs, there
allowing a constant depending on `ε`. This uses no positivity of the remainder. -/
theorem eventually_primeRemainder_le_rpow_iff_natCast (d q : ℕ) [Fact d.Prime] [NeZero q] :
    (∀ ε > (0 : ℝ), ∀ᶠ y : ℝ in atTop, primeRemainder d q y ≤ y ^ (-(1 / 2) + ε)) ↔
      (∀ ε > (0 : ℝ), ∃ C : ℝ, ∀ᶠ x : ℕ in atTop,
        primeRemainder d q x ≤ C * (x : ℝ) ^ (-(1 / 2) + ε)) := by
  apply eventually_le_rpow_add_iff_natCast (D := 26) (by norm_num)
  have hinterval : ∀ᶠ n : ℕ in atTop, ∀ y : ℝ, (n : ℝ) ≤ y → y < (n : ℝ) + 1 →
      primeRemainder d q y - primeRemainder d q n ≤ 13 * (y - n) / n := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn y hny _
    exact (le_abs_self _).trans (abs_primeRemainder_sub_le d q (Nat.cast_pos.mpr hn) hny)
  have hconst : (2 : ℝ) * |(13 : ℝ)| = 26 := by norm_num
  simpa only [hconst] using eventually_sub_nat_floor_le_div hinterval

end TauCeti.OneSidedBound

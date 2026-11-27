/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.Parameters
import Mathlib.Algebra.Order.Group.Indicator
import TauCeti.Analysis.SpecificLimits.GeometricTailBound

/-!
# Bounds for the partner-weight minima

The loss from capping a reciprocal prime-power contribution is the minimum of that
contribution and the weight at the partner place. For a two-valued weight and a fixed
starting place, all short exponents other than a single exceptional one have a contribution
at most the smaller weight. All large exponents can be bounded without using sparsity.

The estimate follows `New.Data.partnerMinSum_le` in `New/Derivatives/Sharpness/NearPairs.lean`
of [grh-lean](https://github.com/lsernau/grh-lean) at `72fead1`.
-/

public section

open scoped NNReal

namespace TauCeti.OneSidedBound

/-- The dyadic tower is long enough that the first exponent with `2 * e ≥ l₀(22 * a)`
already has reciprocal weight at most `1 / (k * p)`. Here `x ≤ (2 ^ a) ^ 2`, and
`k ≤ 3 * x ^ 5` bounds the initial rank. -/
theorem mul_le_pow_half_l₀ {a x k p : ℕ} (hp : 2 ≤ p)
    (hx : x ≤ (2 ^ a) ^ 2) (hk : k ≤ 3 * x ^ 5) :
    k * p ≤ p ^ ((l₀ (22 * a) + 1) / 2) := by
  have hL := lt_l₀ (22 * a)
  have hpow : 2 + 10 * a + 1 ≤ (l₀ (22 * a) + 1) / 2 := by
    obtain rfl | ha := Nat.eq_zero_or_pos a
    · norm_num [l₀_def, Nat.log_zero_right]
    · omega
  have hexp : (((2 : ℕ) ^ a) ^ 2) ^ 5 = 2 ^ (10 * a) := by
    simp only [← pow_mul]
    congr 1
    omega
  calc
    k * p ≤ (3 * x ^ 5) * p := Nat.mul_le_mul_right _ hk
    _ ≤ (4 * ((2 ^ a) ^ 2) ^ 5) * p := by gcongr; omega
    _ = 2 ^ (2 + 10 * a) * p := by simp only [pow_add, ← hexp, Nat.reducePow]
    _ ≤ p ^ (2 + 10 * a) * p := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hp _)
    _ = p ^ (2 + 10 * a + 1) := (pow_succ _ _).symm
    _ ≤ p ^ ((l₀ (22 * a) + 1) / 2) := Nat.pow_le_pow_right (by omega) hpow

/-- For a fixed place `τ` with two-valued weights, bound the sum of the partner minima. At short
exponents, `hnear` controls the only term for which both weights can be `b`. At exponents
`e` with `L ≤ 2 * e`, the starting weight divided by `p ^ e` gives a geometric tail, bounded
by `2 * b / (k * p)` once the first such power of `p` is at least `k * p`. -/
theorem tsum_indicator_min_partnerWeight_le {ι : Type*} {S : Set ι} {I : Set ℕ}
    (pr : ℕ → ι → ι) (τ : ι) {p L : ℕ} {w b k C : ℝ} {j : ℕ}
    (hp : 2 ≤ p) (hw : 0 ≤ w) (hwb : w ≤ b) (hk : 0 < k) (hC : 0 ≤ C)
    (hpower : k * p ≤ (p : ℝ) ^ ((L + 1) / 2))
    (hnear : ∀ e ∈ I, 2 * e < L → τ ∈ S → pr e τ ∈ S → e = j ∧ b / (p : ℝ) ^ e ≤ C) :
    let κ (v : ι) := w + S.indicator (fun _ ↦ b - w) v
    ∑' e : ℕ, I.indicator (fun e ↦ min (κ τ / (p : ℝ) ^ e) (κ (pr e τ))) e ≤
      C + L * w + 2 * b / (k * p) := by
  classical
  intro κ
  let f (e : ℕ) := I.indicator (fun e ↦ min (κ τ / (p : ℝ) ^ e) (κ (pr e τ))) e
  let N := (L + 1) / 2
  have hp₂ : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hb := hw.trans hwb
  have hκ (v : ι) : κ v ∈ Set.Icc 0 b := by
    by_cases hv : v ∈ S <;> simp [κ, hv, hb, hw, hwb]
  have hshort (e : ℕ) (he : e < N) : f e ≤ w + if e = j then C else 0 := by
    have hallow : w ≤ w + if e = j then C else 0 :=
      le_add_of_nonneg_right (by split <;> positivity)
    by_cases heI : e ∈ I
    · dsimp only [f]
      rw [Set.indicator_of_mem heI]
      by_cases hpr : pr e τ ∈ S
      · by_cases hτ : τ ∈ S
        · obtain ⟨rfl, h⟩ := hnear e heI (by dsimp [N] at he; omega) hτ hpr
          have hleft : κ τ / (p : ℝ) ^ e ≤ C := by simpa [κ, hτ] using h
          exact (min_le_left _ _).trans (hleft.trans (by simpa using hw))
        · have hq : (1 : ℝ) ≤ (p : ℝ) ^ e := one_le_pow₀ (by linarith)
          have hleft : κ τ / (p : ℝ) ^ e ≤ w := by simpa [κ, hτ] using div_le_self hw hq
          exact (min_le_left _ _).trans (hleft.trans hallow)
      · exact (min_le_right _ _).trans (by simpa [κ, hpr] using hallow)
    · simpa [f, heI] using hw.trans hallow
  have hf (e : ℕ) : 0 ≤ f e :=
    Set.indicator_apply_nonneg (fun _ ↦ le_min (div_nonneg (hκ τ).1 (by positivity)) (hκ _).1)
  have htail (e : ℕ) : f e ≤ b * (p : ℝ)⁻¹ ^ e := by
    refine Set.indicator_apply_le' (fun _ ↦ ?_) (fun _ ↦ by positivity)
    rw [inv_pow, ← div_eq_mul_inv]
    exact (min_le_left _ _).trans (div_le_div_of_nonneg_right (hκ τ).2 (by positivity))
  let q : ℝ≥0 := ⟨(p : ℝ)⁻¹, by positivity⟩
  have hq : (q : ℝ) < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  refine (TauCeti.tsum_le_of_geometric_tail hq hC hf hshort (fun e _ ↦ htail e)).trans ?_
  have hden : (1 / 2 : ℝ) ≤ 1 - (p : ℝ)⁻¹ := by
    have := (inv_le_inv₀ (by positivity : (0 : ℝ) < p) (by norm_num : (0 : ℝ) < 2)).2 hp₂
    linarith
  have htail' : b * (q : ℝ) ^ N / (1 - (q : ℝ)) ≤ 2 * b / (k * p) := by
    calc
      _ ≤ b * (p : ℝ)⁻¹ ^ N / (1 / 2) :=
        div_le_div_of_nonneg_left (by positivity) (by norm_num) hden
      _ = (2 * b) / (p : ℝ) ^ N := by rw [inv_pow]; ring
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity) hpower
  have hNL : N ≤ L := by dsimp [N]; omega
  have hN : (N : ℝ) ≤ L := by exact_mod_cast hNL
  linarith [mul_le_mul_of_nonneg_right hN hw]

end TauCeti.OneSidedBound

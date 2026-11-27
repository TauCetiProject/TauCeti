/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.Real.Sqrt
public import TauCeti.Data.Nat.Log

/-!
# Ranks and tower bounds for one-sided prime sums

The length of the lift chain is the least power of two above `√x`, and the target rank is
the least power of three above `x ^ 5`. At these ranks the cyclotomic order is polynomial
in `x`, and the dyadic part of the tower is large enough for the sparse-set construction.

The rank choices and tower formulas are from `New/Reduction/Data/Existence.lean` and
`New/Reduction/Data/Magnitudes.lean` of the `grh` folder of lsernau/grh-lean, revision `72fead1`.
-/

public section

namespace TauCeti.OneSidedBound

open Filter Real

/-- The prescribed dyadic chain length and ternary target rank exist at every integer `x > 1`.
Rounding increases the lower thresholds by factors strictly less than two and three. -/
theorem exists_admissible_ranks {x : ℕ} (hx : 1 < x) :
    ∃ e e' : ℕ, 0 < e ∧ 0 < e' ∧
      IsLeast {m : ℕ | (∃ i : ℕ, m = 2 ^ i) ∧ √(x : ℝ) ≤ m} (2 ^ e) ∧
      IsLeast {r : ℕ | (∃ i : ℕ, r = 3 ^ i) ∧ x ^ 5 ≤ r} (3 ^ e') ∧
      ((2 ^ e : ℕ) : ℝ) < 2 * √(x : ℝ) ∧ 3 ^ e' < 3 * x ^ 5 := by
  let e := Nat.clog 4 x
  let e' := Nat.clog 3 (x ^ 5)
  have hx₅ : 1 < x ^ 5 := one_lt_pow₀ hx (by decide)
  have hsq (i : ℕ) : ((2 : ℝ) ^ i) ^ 2 = ((4 ^ i : ℕ) : ℝ) := by
    rw [← pow_mul, pow_mul', Nat.cast_pow]
    norm_num
  refine ⟨e, e', Nat.clog_pos (by decide) hx, Nat.clog_pos (by decide) hx₅, ?_, ?_, ?_, ?_⟩
  · refine ⟨⟨⟨e, rfl⟩, ?_⟩, ?_⟩
    · have hxe := Nat.le_pow_clog (b := 4) (by decide) x
      push_cast
      exact sqrt_le_iff.mpr ⟨by positivity, by rw [hsq]; exact_mod_cast hxe⟩
    · rintro m ⟨⟨i, rfl⟩, hm⟩
      have hxi : x ≤ 4 ^ i := by
        push_cast at hm
        exact_mod_cast (sqrt_le_iff.mp hm).2.trans_eq (hsq i)
      exact Nat.pow_le_pow_right (by decide) ((Nat.clog_le_iff_le_pow (by decide)).mpr hxi)
  · refine ⟨⟨⟨e', rfl⟩, Nat.le_pow_clog (by decide) _⟩, ?_⟩
    rintro r ⟨⟨i, rfl⟩, hi⟩
    exact Nat.pow_le_pow_right (by decide) ((Nat.clog_le_iff_le_pow (by decide)).mpr hi)
  · push_cast
    apply (sq_lt_sq₀ (by positivity) (by positivity)).mp
    rw [hsq, mul_pow, sq_sqrt (by positivity)]
    exact_mod_cast Nat.pow_clog_lt_mul_self (b := 4) (by decide) (zero_lt_one.trans hx)
  · exact Nat.pow_clog_lt_mul_self (by decide) (zero_lt_one.trans hx₅)

/-- A dyadic tower bounded by `2 ^ 22 * x ^ 11` has exponent at most `32 log x` once
`log x ≥ 6`. -/
private theorem towerExponent_le {x s : ℕ} (hlog : 6 ≤ log (x : ℝ))
    (hs : 2 ^ s ≤ 2 ^ 22 * x ^ 11) : (s : ℝ) ≤ 32 * log (x : ℝ) := by
  have hx : 0 < x := Nat.pos_of_ne_zero fun h ↦ by norm_num [h, log_zero] at hlog
  have h := log_le_log (x := (2 : ℝ) ^ s) (by positivity)
    (by exact_mod_cast hs : (2 : ℝ) ^ s ≤ 2 ^ 22 * (x : ℝ) ^ 11)
  simp only [log_mul (by positivity : (2 : ℝ) ^ 22 ≠ 0) (by positivity : (x : ℝ) ^ 11 ≠ 0),
    log_pow, Nat.cast_ofNat] at h
  have hslope : (s : ℝ) / 2 ≤ s * log 2 := by
    calc
      (s : ℝ) / 2 = s * (1 / 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith [log_two_gt_d9]) (by positivity)
  linarith [log_two_lt_d9]

/-- The prescribed prime-search modulus is bounded by a fixed power of `x` when the tower
exponent is at most `32 log x` and `log x ≥ 6`. -/
private theorem primeSearchModulus_le (a : ℕ) {x s : ℕ} (hlog : 6 ≤ log (x : ℝ))
    (hs : (s : ℝ) ≤ 32 * log (x : ℝ)) : a ^ (s + 6) ≤ x ^ (33 * a) := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp
  have hx : 0 < x := Nat.pos_of_ne_zero fun h ↦ by norm_num [h, log_zero] at hlog
  have hexp : ((s + 6 : ℕ) : ℝ) ≤ 33 * log (x : ℝ) := by
    push_cast
    linarith
  have h := calc
    log ((a : ℝ) ^ (s + 6)) = (s + 6) * log (a : ℝ) := by
      simp only [log_pow, Nat.cast_add, Nat.cast_ofNat]
    _ ≤ (s + 6) * a := mul_le_mul_of_nonneg_left (log_le_self (by positivity)) (by positivity)
    _ ≤ (33 * log (x : ℝ)) * a := mul_le_mul_of_nonneg_right (by exact_mod_cast hexp)
      (Nat.cast_nonneg a)
    _ = log ((x : ℝ) ^ (33 * a : ℕ)) := by rw [log_pow]; push_cast; ring
  exact_mod_cast (log_le_log_iff (by positivity) (by positivity)).mp h

/-- Bounds on the dyadic tower obtained by taking the twenty-second power of the rank
bounds. -/
theorem dyadicTower_bounds {x e : ℕ} (hm : √(x : ℝ) ≤ (2 : ℝ) ^ e)
    (hm₂ : (2 : ℝ) ^ e ≤ 2 * √(x : ℝ)) :
    x ^ 11 ≤ 2 ^ (22 * e) ∧ 2 ^ (22 * e) ≤ 2 ^ 22 * x ^ 11 := by
  have hpow : √(x : ℝ) ^ 22 = (x : ℝ) ^ 11 := by
    -- Group the exponent on the square root into eleven pairs.
    rw [← (show 2 * 11 = (22 : ℕ) by decide), pow_mul, sq_sqrt (by positivity)]
  have hlo := pow_le_pow_left₀ (sqrt_nonneg (x : ℝ)) hm 22
  have hhi := pow_le_pow_left₀ (by positivity : 0 ≤ (2 : ℝ) ^ e) hm₂ 22
  refine ⟨?_, ?_⟩
  · exact_mod_cast (by simpa only [hpow, ← pow_mul'] using hlo :
      (x : ℝ) ^ 11 ≤ (2 : ℝ) ^ (22 * e))
  · exact_mod_cast (by simpa only [← pow_mul', mul_pow, hpow] using hhi :
      (2 : ℝ) ^ (22 * e) ≤ 2 ^ 22 * (x : ℝ) ^ 11)

/-- The rank condition bounds the sparsity cutoff `k t + 1` by `46 x ^ 10`. -/
private theorem sparseCutoff_le {x r m : ℕ} (hx : 0 < x) (hm : 0 < m) (hr : r ≤ 3 * x ^ 5) :
    (r + 1 - m) * (5 * r) + 1 ≤ 46 * x ^ 10 := by
  have hk : r + 1 - m ≤ r := by omega
  calc
    _ ≤ (3 * x ^ 5) * (5 * (3 * x ^ 5)) + 1 := by gcongr; omega
    _ = 45 * x ^ 10 + 1 := by ring
    _ ≤ 46 * x ^ 10 := by
      have : (0 : ℕ) < x ^ 10 := pow_pos hx _
      omega

/-- At the prescribed ranks, the tower exponent `s = 22 e` eventually satisfies the logarithmic
bound, the cyclotomic order `q₁` is positive and at most `x ^ 12`, and the prime-search modulus
`q₂` is at most `x ^ (33 * q₀ * d)`. The dyadic order `2 ^ s` also exceeds the threshold for
avoiding short relations at the primes up to `k t`, where `k = r + 1 - m` and `t = 5 r`. -/
theorem eventually_exists_admissible_ranks (q₀ d : ℕ) (hq₀ : 0 < q₀) :
    ∀ᶠ x : ℕ in atTop, ∃ e e' : ℕ,
      let m : ℕ := 2 ^ e
      let r : ℕ := 3 ^ e'
      let s := 22 * e
      let l₀ : ℕ := 3 ^ (Nat.log 3 s + 4)
      let q₁ := q₀ * (3 * l₀ * 2 ^ s)
      0 < e ∧ 0 < e' ∧
        IsLeast {u : ℕ | (∃ i : ℕ, u = 2 ^ i) ∧ √(x : ℝ) ≤ u} m ∧
        IsLeast {u : ℕ | (∃ i : ℕ, u = 3 ^ i) ∧ x ^ 5 ≤ u} r ∧
        (m : ℝ) < 2 * √(x : ℝ) ∧ r < 3 * x ^ 5 ∧
        (s : ℝ) ≤ 32 * log (x : ℝ) ∧ 0 < q₁ ∧ q₁ ≤ x ^ 12 ∧
        (q₀ * d) ^ (s + 6) ≤ x ^ (33 * (q₀ * d)) ∧
        2 * l₀ * ((r + 1 - m) * (5 * r) + 1) < 2 ^ s := by
  -- One logarithmic bound absorbs the extra factor `l₀` in both tower comparisons.
  let C : ℕ := max (q₀ * 3 * 2 ^ 22) (2 * 46)
  have hsmall : ∀ᶠ x : ℕ in atTop, (C : ℝ) * 81 * 32 * log (x : ℝ) < x := by
    have h := (isLittleO_log_id_atTop.const_mul_left ((C : ℝ) * 81 * 32)).bound
      (by norm_num : (0 : ℝ) < 1 / 2)
    filter_upwards [tendsto_natCast_atTop_atTop.eventually h, eventually_ge_atTop 1] with x hb hx
    have hx₀ : (0 : ℝ) < x := by exact_mod_cast (by omega : 0 < x)
    simp only [Real.norm_eq_abs, id_eq, abs_of_pos hx₀] at hb
    linarith [le_abs_self ((C : ℝ) * 81 * 32 * log (x : ℝ))]
  have hlog := (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop (6 : ℝ)
  filter_upwards [eventually_ge_atTop 2, hlog, hsmall] with x hx hlog hsmall
  obtain ⟨e, e', he, he', hm, hr, hm₂, hr₃⟩ := exists_admissible_ranks (by omega : 1 < x)
  let s := 22 * e
  let l₀ : ℕ := 3 ^ (Nat.log 3 s + 4)
  have hdyadic : x ^ 11 ≤ 2 ^ s ∧ 2 ^ s ≤ 2 ^ 22 * x ^ 11 :=
    dyadicTower_bounds (by exact_mod_cast hm.1.2) (by exact_mod_cast hm₂.le)
  have hslog := towerExponent_le hlog hdyadic.2
  have hl₀ : l₀ ≤ 81 * s := by
    have h := Nat.pow_log_le_self 3 (x := s) (by dsimp [s]; omega)
    simpa [l₀, pow_add, Nat.mul_comm] using Nat.mul_le_mul_left 81 h
  have hCl₀ : C * l₀ < x := by
    have hle : (C : ℝ) * (l₀ : ℝ) ≤ C * 81 * 32 * log (x : ℝ) := calc
      _ ≤ (C : ℝ) * (81 * (s : ℝ)) := by
        gcongr
        exact_mod_cast hl₀
      _ ≤ (C : ℝ) * (81 * (32 * log (x : ℝ))) := by gcongr
      _ = _ := by ring
    exact_mod_cast hle.trans_lt hsmall
  refine ⟨e, e', he, he', hm, hr, hm₂, hr₃, hslog, by positivity, ?_,
    primeSearchModulus_le _ hlog hslog, ?_⟩
  · calc
      q₀ * (3 * l₀ * 2 ^ s) ≤ q₀ * (3 * l₀ * (2 ^ 22 * x ^ 11)) := by gcongr; exact hdyadic.2
      _ = (q₀ * 3 * 2 ^ 22) * l₀ * x ^ 11 := by ring
      _ ≤ (C * l₀) * x ^ 11 := by gcongr; exact le_max_left _ _
      _ ≤ x ^ 12 := by simpa only [pow_succ' x 11] using Nat.mul_le_mul_right (x ^ 11) hCl₀.le
  · have hL := sparseCutoff_le (by omega : 0 < x) (pow_pos (by decide : 0 < (2 : ℕ)) e) hr₃.le
    calc
      2 * l₀ * ((3 ^ e' + 1 - 2 ^ e) * (5 * 3 ^ e') + 1) ≤ 2 * l₀ * (46 * x ^ 10) := by gcongr
      _ = (2 * 46) * l₀ * x ^ 10 := by ring
      _ ≤ (C * l₀) * x ^ 10 := by gcongr; exact le_max_right _ _
      _ < x ^ 11 := by
        simpa only [pow_succ' x 10] using
          Nat.mul_lt_mul_of_pos_right hCl₀ (pow_pos (by omega : 0 < x) 10)
      _ ≤ 2 ^ s := hdyadic.1

end TauCeti.OneSidedBound

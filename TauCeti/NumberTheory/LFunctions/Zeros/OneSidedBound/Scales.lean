/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import TauCeti.Algebra.Order.Floor.Semifield
import TauCeti.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Separated integral scales for prime sums

For a large integral cutoff `x`, round down `exp (x ^ (ε/6))` to obtain the second cutoff `x₁`,
and round strictly up from `exp (x ^ ε)` to a multiple of `q * x₁` to obtain `b`. The divisibility
keeps the weights integral, while the separation of the scales allows a logarithmic error at
`x₁` to be small compared to a power of `x`.

The normalization `ε/6` and the rounding choices come from `New.eventually_exists_data` in
`New/Reduction/Data/Existence.lean` of [the shorter GRH formalization] (revision `72fead1`).

[the shorter GRH formalization]: https://github.com/lsernau/grh-lean
-/

public section

open Filter
open scoped Topology

namespace TauCeti.OneSidedBound

/-- Round `exp u` down to a natural number `y` and `exp v` strictly up to the least multiple `b`
of `q * y`. If `0 ≤ u`, `0 < q`, and `q * exp u ≤ exp v`, both cutoffs are positive and rounding
changes their logarithms by at most one. -/
theorem exists_rounded_scales {u v : ℝ} {q : ℕ} (hu : 0 ≤ u) (hq : 0 < q)
    (hstep : (q : ℝ) * Real.exp u ≤ Real.exp v) :
    let y := ⌊Real.exp u⌋₊
    ∃ b : ℕ, 0 < y ∧ 0 < b ∧ IsLeast {n : ℕ | q * y ∣ n ∧ Real.exp v < (n : ℝ)} b ∧
      u - 1 ≤ Real.log y ∧ Real.log y ≤ u ∧ v ≤ Real.log b ∧ Real.log b ≤ v + 1 := by
  intro y
  have hExp : 1 ≤ Real.exp u := Real.one_le_exp_iff.2 hu
  have hy : 0 < y := Nat.le_floor (by simpa using hExp)
  have hy' : (0 : ℝ) < y := by exact_mod_cast hy
  have he : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
  have hlo : u - 1 ≤ Real.log y := by
    refine (Real.le_log_iff_exp_le hy').2 ?_
    rw [Real.exp_sub]
    exact (div_le_div_of_nonneg_left (Real.exp_pos u).le zero_lt_two he).trans
      (Nat.div_two_lt_floor hExp).le
  have hfloor : (y : ℝ) ≤ Real.exp u := Nat.floor_le (Real.exp_pos _).le
  let d := q * y
  have hd : 0 < d := Nat.mul_pos hq hy
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hdv : (d : ℝ) ≤ Real.exp v := by
    rw [Nat.cast_mul]
    exact (mul_le_mul_of_nonneg_left hfloor (Nat.cast_nonneg q)).trans hstep
  obtain ⟨j, _, hlt, hle⟩ := exists_pos_nat_mul_bounds (Real.exp_pos v).le hd'
  have hb : (0 : ℝ) < (j : ℝ) * d := (Real.exp_pos v).trans hlt
  refine ⟨j * d, hy, by exact_mod_cast hb, ⟨⟨dvd_mul_left _ _, by exact_mod_cast hlt⟩, ?_⟩,
    hlo, (Real.log_le_iff_le_exp hy').2 hfloor, ?_, ?_⟩
  · rintro n ⟨⟨k, rfl⟩, hn⟩
    rw [Nat.mul_comm d k]
    apply Nat.mul_le_mul_right
    by_contra! hjk
    have hgap : (k : ℝ) * d + d ≤ (j : ℝ) * d := by
      rw [← add_one_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.succ_le_of_lt hjk) hd'.le
    have hn' : Real.exp v < (d : ℝ) * k := by exact_mod_cast hn
    rw [mul_comm (d : ℝ)] at hn'
    linarith
  · push_cast
    exact (Real.le_log_iff_exp_le hb).2 hlt.le
  · push_cast
    refine (Real.log_le_iff_le_exp hb).2 ?_
    rw [Real.exp_add]
    calc
      _ ≤ Real.exp v + d := hle
      _ ≤ Real.exp v * 2 := by linarith
      _ ≤ Real.exp v * Real.exp 1 := mul_le_mul_of_nonneg_left he (Real.exp_pos _).le

/-- Construct the separated integral scales for large natural `x`. The second cutoff `x₁` is
`⌊exp (x ^ (ε/6))⌋₊` and `b` is the least multiple of `q x * x₁` strictly above `exp (x ^ ε)`.
The modulus can vary with `x`, provided it is eventually positive and bounded by a fixed power.
For `0 < ε < 1 / 100`, one can take `N = M = 10^6` and `p = 100`. -/
theorem eventually_exists_admissible_scales {q : ℕ → ℕ} {A C ε : ℝ} (hε : 0 < ε)
    (N M p : ℕ) (hp : ε * p < 1) (hq₀ : ∀ᶠ x in atTop, 0 < q x)
    (hq : ∀ᶠ x in atTop, (q x : ℝ) ≤ (x : ℝ) ^ A) :
    ∀ᶠ x : ℕ in atTop, ∃ x₁ b : ℕ,
      x₁ = ⌊Real.exp ((x : ℝ) ^ (ε / 6))⌋₊ ∧ 0 < x₁ ∧ 0 < b ∧
      IsLeast {n : ℕ | q x * x₁ ∣ n ∧ Real.exp ((x : ℝ) ^ ε) < (n : ℝ)} b ∧
      (x : ℝ) ^ (ε / 6) - 1 ≤ Real.log x₁ ∧
      (x : ℝ) ^ ε ≤ Real.log b ∧ Real.log b ≤ (x : ℝ) ^ ε + 1 ∧
      C ≤ Real.log (Real.log b) ∧ (Real.log b) ^ p ≤ x ∧
      x ^ N ≤ x₁ ∧ x₁ ^ M ≤ b ∧ (Real.log x₁) ^ 6 ≤ Real.log b := by
  have hnat : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hα : 0 < ε / 6 := by positivity
  have hlog := ((isLittleO_log_rpow_atTop hα).const_mul_left (2 * max (N : ℝ) A)).eventuallyLE
  have hpow := ((isLittleO_rpow_rpow_atTop hp).const_mul_left (2 ^ p : ℝ)).eventuallyLE
  filter_upwards [hq₀, hq, hnat.eventually_ge_atTop 1, hnat.eventually hlog,
    ((tendsto_rpow_atTop hα).comp hnat).eventually_ge_atTop (max 2 (M : ℝ)),
    ((tendsto_rpow_atTop hε).comp hnat).eventually_ge_atTop (Real.exp C),
    hnat.eventually hpow] with x hq₀ hq hx hl hu hv hp'
  set u := (x : ℝ) ^ (ε / 6) with hu_def
  set v := (x : ℝ) ^ ε with hv_def
  have hu₂ : 2 ≤ u := (le_max_left _ _).trans hu
  have huM : (M : ℝ) ≤ u := (le_max_right _ _).trans hu
  have huv : u ^ 6 = v := by
    rw [hu_def, hv_def, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    congr 1
    norm_num
  have huv₂ : u ^ 2 ≤ v := huv ▸ pow_le_pow_right₀ (by linarith) (by norm_num)
  have hhalf (a : ℝ) (ha : a ≤ max (N : ℝ) A) : a * Real.log x ≤ u / 2 := by
    have hmax := (le_abs_self _).trans (hl.trans_eq (Real.norm_of_nonneg (by linarith : 0 ≤ u)))
    linarith [mul_le_mul_of_nonneg_right ha (Real.log_nonneg hx)]
  have hqexp : (q x : ℝ) ≤ Real.exp u := hq.trans <| by
    rw [Real.rpow_def_of_pos (by linarith : (0 : ℝ) < x), mul_comm]
    exact Real.exp_le_exp.mpr (by linarith [hhalf A (le_max_right _ _)])
  have hstep := (mul_le_mul_of_nonneg_right hqexp (Real.exp_pos u).le).trans
    (by rw [← Real.exp_add, Real.exp_le_exp]; nlinarith : Real.exp u * Real.exp u ≤ Real.exp v)
  let x₁ := ⌊Real.exp u⌋₊
  obtain ⟨b, hx₁, hb, hleast, hlo, hhi, hblo, hbhi⟩ := exists_rounded_scales
    (by linarith : 0 ≤ u) hq₀ hstep
  have hlogb : 0 < Real.log b := (Real.exp_pos C).trans_le (hv.trans hblo)
  refine ⟨x₁, b, rfl, hx₁, hb, hleast, hlo, hblo, hbhi,
    (Real.le_log_iff_exp_le hlogb).2 (hv.trans hblo), ?_, ?_, ?_, ?_⟩
  · have hv₁ : 1 ≤ v := Real.one_le_rpow hx hε.le
    calc
      (Real.log b) ^ p ≤ (2 * v) ^ p := pow_le_pow_left₀ hlogb.le (by linarith) _
      _ = 2 ^ p * (x : ℝ) ^ (ε * p) := by
        rw [mul_pow, Real.rpow_mul (by positivity), Real.rpow_natCast]
      _ ≤ x := by simpa [Real.rpow_one, abs_of_nonneg (zero_le_one.trans hx),
        abs_of_nonneg (by positivity : 0 ≤ (x : ℝ) ^ (ε * p))] using hp'
  · have h := (Real.log_pow (x : ℝ) N).trans_le
      (by linarith [hhalf N (le_max_left _ _)] : (N : ℝ) * Real.log x ≤ Real.log x₁)
    exact_mod_cast (Real.log_le_log_iff (by positivity) (by exact_mod_cast hx₁)).1 h
  · have h : Real.log ((x₁ : ℝ) ^ M) ≤ Real.log b := by
      rw [Real.log_pow]
      calc
        _ ≤ (M : ℝ) * u := mul_le_mul_of_nonneg_left hhi (by positivity)
        _ ≤ u ^ 2 := by simpa [sq] using mul_le_mul_of_nonneg_right huM (by linarith)
        _ ≤ Real.log b := huv₂.trans hblo
    exact_mod_cast (Real.log_le_log_iff (by positivity) (by exact_mod_cast hb)).1 h
  · have hnonneg : 0 ≤ Real.log x₁ := by linarith
    exact ((pow_le_pow_left₀ hnonneg hhi _).trans_eq huv).trans hblo

end TauCeti.OneSidedBound

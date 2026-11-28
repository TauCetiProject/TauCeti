/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Nat.Log
import TauCeti.Data.Nat.Log

/-!
# Length bounds for cyclotomic trace-dual frames

When the trace-dual vectors are scaled by a power of a fixed quadratic integer `β`, the exponent
is the ceiling of the base-two logarithm of the cyclotomic order. This keeps the norm of the
scale polynomial in the order. A uniform bound on the unscaled coordinates thus gives a
polynomial upper bound for the corrected frame length. The slow growth of the cyclotomic order
compared to the large prime-sum cutoff puts that length below the cutoff and leaves room to
repeat both frames with large multiplicities at the principal level.

The length and multiplicity budgets are those of `New.Data.le_b_of_eq_dualResolutionFactor`
and `New.Data.exists_isTightFrame` in `grh/src/New/Derivatives/Vacuum/ShortVectors.lean` of
[lsernau/grh-lean](https://github.com/lsernau/grh-lean/tree/72fead1/grh).
-/

public section

open Filter Real

namespace TauCeti.ThetaLift

/-- The corrected trace-dual frame length grows at most polynomially in the cyclotomic order
`q`. Here `w` is the family of coordinates before scaling, with at most `q²` entries of norm
at most `C`. The fixed field-dependent exponent `D` bounds the norm of `β` by `2^D`. -/
theorem correctedFrameLength_le_pow (β : ℂ) (D : ℕ) {C : ℝ}
    (hβ : ‖β‖ ≤ (2 : ℝ) ^ D) {q : ℕ} (hq : 0 < q) {ι : Type*} [Fintype ι]
    {w : ι → ℂ} (hcard : Fintype.card ι ≤ q ^ 2) (hw : ∀ i, ‖w i‖ ≤ C) :
    q * (1 + ∑ i, ‖β ^ Nat.clog 2 q * w i‖ ^ 2) + 2 * (β ^ Nat.clog 2 q).re ≤
      (1 + (|C| * 2 ^ D) ^ 2 + 2 * 2 ^ D) * (q : ℝ) ^ (2 * D + 3) := by
  have hq₁ : 1 ≤ (q : ℝ) := by exact_mod_cast hq
  have hscale : ‖β ^ Nat.clog 2 q‖ ≤ 2 ^ D * (q : ℝ) ^ D := calc
    _ = ‖β‖ ^ Nat.clog 2 q := norm_pow ..
    _ ≤ ((2 : ℝ) ^ D) ^ Nat.clog 2 q := by gcongr
    _ = ((2 : ℝ) ^ Nat.clog 2 q) ^ D := by rw [← pow_mul, Nat.mul_comm, pow_mul]
    _ ≤ (2 * (q : ℝ)) ^ D := by
      gcongr
      exact_mod_cast (Nat.pow_clog_lt_mul_self (by decide : 1 < (2 : ℕ)) hq).le
    _ = _ := mul_pow ..
  have hsum : (∑ i, ‖β ^ Nat.clog 2 q * w i‖ ^ 2) ≤
      (q : ℝ) ^ 2 * ((|C| * 2 ^ D) * q ^ D) ^ 2 := calc
    _ ≤ ∑ _i : ι, ((|C| * 2 ^ D) * (q : ℝ) ^ D) ^ 2 := by
      refine Finset.sum_le_sum fun i _ ↦ ?_
      have hi := mul_le_mul hscale ((hw i).trans (le_abs_self C)) (norm_nonneg _) (by positivity)
      rw [norm_mul]
      apply pow_le_pow_left₀ (by positivity)
      calc
        _ ≤ (2 ^ D * (q : ℝ) ^ D) * |C| := hi
        _ = _ := by ring
    _ = (Fintype.card ι : ℝ) * ((|C| * 2 ^ D) * q ^ D) ^ 2 := by simp
    _ ≤ _ := by gcongr; exact_mod_cast hcard
  have hp₁ : (q : ℝ) ≤ q ^ (2 * D + 3) := by
    simpa using pow_le_pow_right₀ hq₁ (by omega : 1 ≤ 2 * D + 3)
  have hpD : (q : ℝ) ^ D ≤ q ^ (2 * D + 3) := pow_le_pow_right₀ hq₁ (by omega)
  have hsum' : q * (∑ i, ‖β ^ Nat.clog 2 q * w i‖ ^ 2) ≤
      (|C| * 2 ^ D) ^ 2 * (q : ℝ) ^ (2 * D + 3) := calc
    _ ≤ (q : ℝ) * (q ^ 2 * ((|C| * 2 ^ D) * q ^ D) ^ 2) := by gcongr
    _ = _ := by rw [pow_add, pow_mul]; ring
  have hre := (Complex.re_le_norm (β ^ Nat.clog 2 q)).trans
    (hscale.trans (mul_le_mul_of_nonneg_left hpD (by positivity)))
  rw [mul_add, mul_one, add_mul, add_mul, one_mul]
  linarith only [hp₁, hsum', hre]

universe u

/-- At every sufficiently large `x`, a cyclotomic order `q ≤ x¹²` gives a corrected frame length
at most the cutoff `b` whenever `b > 0` and `(log x)² ≤ log b`. The threshold depends only on the
bounds `C` and `D`, not on the order, the cutoff, or the coordinate family. -/
theorem eventually_correctedFrameLength_le_cutoff (D : ℕ) (C : ℝ) :
    ∀ᶠ x : ℝ in atTop, ∀ {q : ℕ} {b : ℝ}, (q : ℝ) ≤ x ^ 12 →
      0 < b → log x ^ 2 ≤ log b →
      ∀ {ι : Type u} [Fintype ι] {w : ι → ℂ} {β : ℂ}, ‖β‖ ≤ (2 : ℝ) ^ D →
        Fintype.card ι ≤ q ^ 2 → (∀ i, ‖w i‖ ≤ C) →
        q * (1 + ∑ i, ‖β ^ Nat.clog 2 q * w i‖ ^ 2) + 2 * (β ^ Nat.clog 2 q).re ≤ b := by
  let A : ℝ := 1 + (|C| * 2 ^ D) ^ 2 + 2 * 2 ^ D
  let n : ℕ := 12 * (2 * D + 3)
  have hA₂ : 2 ≤ A := by
    have hD : (1 : ℝ) ≤ 2 ^ D := one_le_pow₀ (by norm_num)
    dsimp [A]
    linarith only [hD, sq_nonneg (|C| * (2 : ℝ) ^ D)]
  have hA : 0 < A := by linarith
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    tendsto_log_atTop.eventually_ge_atTop (max 1 (log A + n))] with x hx hxlog
  intro q b hqx hb hblog ι _ w β hβ hcard hw
  have hx₀ : 0 < x := zero_lt_one.trans_le hx
  have hlog₁ : 1 ≤ log x := (le_max_left _ _).trans hxlog
  have hlog₂ : log A + n ≤ log x := (le_max_right _ _).trans hxlog
  have hAb : A * x ^ n ≤ b := by
    apply (log_le_log_iff (mul_pos hA (pow_pos hx₀ _)) hb).mp
    rw [log_mul hA.ne' (pow_ne_zero _ hx₀.ne'), log_pow]
    have hm := mul_le_mul_of_nonneg_right hlog₂ (zero_le_one.trans hlog₁)
    have ha : 0 ≤ log A := log_nonneg ((by norm_num : (1 : ℝ) ≤ 2).trans hA₂)
    nlinarith only [hblog, hlog₁, hm, mul_nonneg ha (sub_nonneg.mpr hlog₁)]
  rcases q.eq_zero_or_pos with rfl | hq
  · simp only [Nat.cast_zero, zero_mul, Nat.clog_zero_right, pow_zero, Complex.one_re, zero_add,
      mul_one]
    exact hA₂.trans ((le_mul_of_one_le_right hA.le (one_le_pow₀ hx)).trans hAb)
  calc
    _ ≤ A * (q : ℝ) ^ (2 * D + 3) := correctedFrameLength_le_pow β D hβ hq hcard hw
    _ ≤ A * x ^ n := by
      dsimp only [n]
      rw [pow_mul x 12]
      gcongr
    _ ≤ b := hAb

/-- At level `M ≥ b⁷`, with both frame lengths `q, h ≤ b` and at most `b` places, one can
reserve `6 f b` copies of each block and still have at least `q h` of the length left for
the two-generator Frobenius argument. In particular the principal level `M ≥ b²⁰` suffices. -/
theorem frameMultiplicityReserve_le_level {q h f b M : ℕ} (hb : 2 ≤ b) (hq : q ≤ b)
    (hh : h ≤ b) (hf : f ≤ b) (hM : b ^ 7 ≤ M) :
    q * h + 6 * f * b * (q + h) ≤ M := by
  calc
    _ ≤ b * b + 6 * b * b * (b + b) := by gcongr
    _ = b ^ 2 + 12 * b ^ 3 := by ring
    _ ≤ 13 * b ^ 3 := by
      have h₂ : b ^ 2 ≤ b ^ 3 := Nat.pow_le_pow_right (by omega) (by decide)
      omega
    _ ≤ b ^ 7 := by
      rw [show (7 : ℕ) = 4 + 3 by decide, pow_add]
      exact Nat.mul_le_mul_right _ ((by decide : 13 ≤ 2 ^ 4).trans (Nat.pow_le_pow_left hb _))
    _ ≤ M := hM

end TauCeti.ThetaLift

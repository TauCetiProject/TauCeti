/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
import TauCeti.Data.Int.Sign
import TauCeti.NumberTheory.TsumDivisorsAntidiagonal
import Mathlib.Analysis.Complex.UpperHalfPlane.Exp
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Summable

/-!
# The cotangent over `ℤ` and away from the real axis

Mathlib's partial-fraction expansion of the cotangent (`cot_series_rep`) pairs the poles at `± n`.
Pairing each pole `n` instead with the constant `1 / n` gives an absolutely convergent series over
`ℤ` (`TauCeti.hasSum_one_div_sub_intCast_add_one_div_intCast`):

`π cot (π w) = ∑_{n ∈ ℤ} (1 / (w - n) + 1 / n)` for `w ∉ ℤ`,

the term at `n = 0` being `1 / w`. This is the form in which the cotangent appears as a row of the
lattice series of the Weierstrass `ζ` function.

Away from the real axis, `π cot (π u)` tends to `-π i` as `Im u → ∞`, and to `π i` as
`Im u → -∞`, exponentially fast: with `q = e^(2π i u)`, `π cot (π u) + π i = 2π q / (i (1 - q))`
(`TauCeti.norm_pi_mul_cot_pi_mul_add_pi_mul_I_le`,
`TauCeti.norm_pi_mul_cot_pi_mul_sub_pi_mul_I_le`). Correcting by these limits, the cotangents
`π cot (π m w) + sign(m) π i` are odd in `m ∈ ℤ` and sum to `0`; at the division points
`(c z + b) / M` the `q`-expansion is a series in `e(z / M) = e^(2π i z / M)` with coefficients
`e(k b / M)`.

## Main results

* `Complex.cot_neg`, `Complex.cot_zero`: the cotangent is odd, with junk value `0` at `0`.
* `TauCeti.hasSum_one_div_sub_intCast_add_one_div_intCast`: the expansion over `ℤ`.
* `TauCeti.hasSum_pi_mul_cot_pi_mul_add_pi_mul_I`: the `q`-expansion in the upper half-plane.
* `TauCeti.hasSum_pi_mul_cot_pi_mul_div_add_pi_mul_I`,
  `TauCeti.hasSum_ite_pi_mul_cot_pi_mul_div_add_pi_mul_I`: the `q`-expansion at the division
  points `(c z + b) / M`, for one `c ≥ 1` and summed over a residue class of `c` modulo `M`.
* `TauCeti.hasSum_pi_mul_cot_pi_mul_intCast_mul_add_sign`: the corrected cotangents
  `π cot (π m w) + sign(m) π i` sum to `0` over `m ∈ ℤ`.
* `TauCeti.hasSum_ite_pi_mul_cot_pi_mul_intCast_div_add_sign`: the corrected cotangents
  `π cot (π (n z + b) / M) + sign(n) π i` summed over a residue class of `n ∈ ℤ` modulo `M`.
* `TauCeti.hasSum_pi_mul_cot_pi_mul_div_sub_intCast_mul_add_pi_mul_cot`: the cotangent rows
  `π cot (π (x - m z)) + π cot (π m z)` at a division point `x = (b₀ z + b) / M`, summed over
  `m ∈ ℤ`, as a `q`-expansion in `e(z / M)`.
* `TauCeti.norm_pi_mul_cot_pi_mul_add_pi_mul_I_le`,
  `TauCeti.norm_pi_mul_cot_pi_mul_sub_pi_mul_I_le`: the exponential approach to `∓ π i`.
-/

public section

open Complex
open scoped Real

namespace Complex

/-- The cotangent is odd. -/
@[simp]
theorem cot_neg (z : ℂ) : cot (-z) = -cot z := by
  simp [cot_eq_cos_div_sin, div_neg]

/-- The junk value of the cotangent at its pole `0` is `0`. -/
@[simp]
theorem cot_zero : cot 0 = 0 := by
  simp [cot_eq_cos_div_sin]

end Complex

namespace TauCeti

/-- **The partial-fraction expansion of the cotangent over `ℤ`.** For `w ∉ ℤ`,
`π cot (π w) = ∑_{n ∈ ℤ} (1 / (w - n) + 1 / n)`, the series converging absolutely; its term at
`n = 0` is `1 / w`. -/
theorem hasSum_one_div_sub_intCast_add_one_div_intCast {w : ℂ} (hw : w ∈ integerComplement) :
    HasSum (fun n : ℤ ↦ 1 / (w - n) + 1 / n) (π * cot (π * w)) := by
  set f : ℤ → ℂ := fun n ↦ 1 / (w - n) + 1 / n
  have hsub (n : ℤ) : w - n ≠ 0 := by
    simpa [sub_eq_add_neg] using integerComplement_add_ne_zero hw (-n)
  have hf : Summable f := by
    have hg := (EisensteinSeries.summable_linear_sub_mul_linear_add w 1 0).mul_left w
    have h0 : Summable fun n : ℤ ↦ if n = 0 then 1 / w else 0 :=
      summable_of_ne_finset_zero (s := {0}) fun n hn ↦ by simp_all
    refine (hg.add h0).congr fun n ↦ ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simp [f]
    · have hn' : (n : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hn
      simp only [Int.cast_one, one_mul, Int.cast_zero, zero_mul, zero_add, hn, ↓reduceIte,
        add_zero, f]
      field_simp [hsub n, hn']
      ring
  have h₁ : Summable fun n : ℕ+ ↦ f n :=
    hf.comp_injective (Nat.cast_injective.comp PNat.coe_injective)
  have h₂ : Summable fun n : ℕ+ ↦ f (-n) :=
    hf.comp_injective (neg_injective.comp (Nat.cast_injective.comp PNat.coe_injective))
  convert hf.hasSum using 1
  rw [tsum_int_eq_zero_add_tsum_pnat hf, add_assoc, ← h₁.tsum_add h₂, cot_series_rep hw]
  congr 1
  · simp [f]
  · refine tsum_congr fun n ↦ ?_
    simp only [f, Int.cast_neg, Int.cast_natCast, sub_neg_eq_add]
    ring

/-- **The `q`-expansion of the cotangent in the upper half-plane**: if `0 < Im w`, then
`π cot (π w) + π i = -2π i ∑_{k ≥ 1} e^(2π i k w)`. This is Mathlib's `pi_mul_cot_pi_q_exp` with
the constant term separated from the series. -/
theorem hasSum_pi_mul_cot_pi_mul_add_pi_mul_I {w : ℂ} (hw : 0 < w.im) :
    HasSum (fun k : ℕ+ ↦ -2 * π * I * cexp (2 * π * I * w) ^ (k : ℕ))
      (π * cot (π * w) + π * I) := by
  set q := cexp (2 * π * I * w) with hqdef
  have hq : ‖q‖ < 1 := UpperHalfPlane.norm_exp_two_pi_I_lt_one ⟨w, hw⟩
  have hq1 : 1 - q ≠ 0 := sub_ne_zero.mpr fun h ↦ by simp [← h] at hq
  rw [hasSum_pnat_iff (f := fun k : ℕ ↦ -2 * π * I * q ^ k)]
  convert (hasSum_geometric_of_norm_lt_one hq).mul_left (-2 * π * I) using 1
  rw [cot_pi_eq_exp_ratio, ← hqdef]
  field_simp
  linear_combination (1 + q) * I_sq

/-- **The cotangent tends to `-i` in the upper half-plane**: if `0 < t ≤ Im u`, then
`‖π cot (π u) + π i‖ ≤ 2π e^(-2π Im u) / (1 - e^(-2π t))`. -/
theorem norm_pi_mul_cot_pi_mul_add_pi_mul_I_le {u : ℂ} {t : ℝ} (ht : 0 < t) (hu : t ≤ u.im) :
    ‖π * cot (π * u) + π * I‖ ≤
      2 * π / (1 - Real.exp (-2 * π * t)) * Real.exp (-2 * π * u.im) := by
  set q := cexp (2 * π * I * u) with hqdef
  have hq : ‖q‖ = Real.exp (-2 * π * u.im) := by
    rw [Complex.norm_exp]
    congr 1
    simp
  have hθ : Real.exp (-2 * π * t) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos])
  have hle : ‖q‖ ≤ Real.exp (-2 * π * t) := by
    rw [hq, Real.exp_le_exp]
    nlinarith [Real.pi_pos]
  have h1q : 1 - Real.exp (-2 * π * t) ≤ ‖1 - q‖ :=
    (by linarith : 1 - Real.exp (-2 * π * t) ≤ 1 - ‖q‖).trans
      (by simpa using norm_sub_norm_le (1 : ℂ) q)
  have hpos : 0 < 1 - Real.exp (-2 * π * t) := by linarith
  have hq1 : 1 - q ≠ 0 := norm_pos_iff.mp (hpos.trans_le h1q)
  have heq : π * cot (π * u) + π * I = 2 * π * q / (I * (1 - q)) := by
    rw [cot_pi_eq_exp_ratio, ← hqdef]
    field_simp
    linear_combination (1 - q) * I_sq
  have h2π : ‖(2 * π : ℂ)‖ = 2 * π := by
    simp [abs_of_pos Real.pi_pos]
  rw [heq, norm_div, norm_mul I, norm_I, one_mul, norm_mul, h2π, hq]
  calc 2 * π * Real.exp (-2 * π * u.im) / ‖1 - q‖
      ≤ 2 * π * Real.exp (-2 * π * u.im) / (1 - Real.exp (-2 * π * t)) := by
        gcongr
    _ = _ := by ring

/-- **The cotangent tends to `i` in the lower half-plane**: if `0 < t ≤ -Im u`, then
`‖π cot (π u) - π i‖ ≤ 2π e^(2π Im u) / (1 - e^(-2π t))`. -/
theorem norm_pi_mul_cot_pi_mul_sub_pi_mul_I_le {u : ℂ} {t : ℝ} (ht : 0 < t) (hu : t ≤ -u.im) :
    ‖π * cot (π * u) - π * I‖ ≤
      2 * π / (1 - Real.exp (-2 * π * t)) * Real.exp (2 * π * u.im) := by
  have h := norm_pi_mul_cot_pi_mul_add_pi_mul_I_le ht (u := -u) (by simpa using hu)
  rw [mul_neg, cot_neg, Complex.neg_im, mul_neg, neg_add_eq_sub, norm_sub_rev] at h
  convert h using 3
  ring

/-- **The `q`-expansion of the cotangent at a division point**: if `0 < Im z`, `c ≥ 1` and
`b ∈ ℤ`, then `π cot (π (c z + b) / M) + π i = -2π i ∑_{k ≥ 1} e(k b / M) e(z / M)^(c k)`, where
`e(k b / M) = ZMod.stdAddChar (k b)` and `e(z / M) = e^(2π i z / M)`. -/
theorem hasSum_pi_mul_cot_pi_mul_div_add_pi_mul_I (M : ℕ) [NeZero M] (c : ℕ+) (b : ℤ) {z : ℂ}
    (hz : 0 < z.im) :
    HasSum (fun k : ℕ+ ↦ -2 * π * I * (ZMod.stdAddChar ((k : ZMod M) * (b : ZMod M)) *
        cexp (2 * π * I * z / M) ^ ((c : ℕ) * k)))
      (π * cot (π * ((c * z + b) / M)) + π * I) := by
  have hw : 0 < ((c * z + b) / M).im := by
    have hM : (0 : ℝ) < M := Nat.cast_pos.mpr (NeZero.pos M)
    simpa [Complex.div_natCast_im] using div_pos (mul_pos (by simp) hz) hM
  -- `e((c z + b) / M)^k = e(k b / M) e(z / M)^(c k)`
  have hpow (k : ℕ) : cexp (2 * π * I * ((c * z + b) / M)) ^ k =
      ZMod.stdAddChar ((k : ZMod M) * (b : ZMod M)) * cexp (2 * π * I * z / M) ^ ((c : ℕ) * k) := by
    rw [← Int.cast_natCast (R := ZMod M) k, ← Int.cast_mul, ZMod.stdAddChar_coe,
      ← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  convert hasSum_pi_mul_cot_pi_mul_add_pi_mul_I hw using 3 with k
  rw [hpow]

/-- **The `q`-expansion of the cotangents at the division points of a residue class**: if
`0 < Im z`, the cotangents `π cot (π (c z + b) / M) + π i` with `c ≥ 1` and `c ≡ d` modulo `M` sum
to the absolutely convergent double series `-2π i ∑_{c ≡ d, k ≥ 1} e(k b / M) e(z / M)^(c k)`. -/
theorem hasSum_ite_pi_mul_cot_pi_mul_div_add_pi_mul_I (M : ℕ) [NeZero M] (d : ZMod M) (b : ℤ)
    {z : ℂ} (hz : 0 < z.im) :
    HasSum (fun c : ℕ+ ↦ if (c : ZMod M) = d then
        π * cot (π * ((c * z + b) / M)) + π * I else 0)
      (-2 * π * I * ∑' p : ℕ+ × ℕ+,
        (if (p.1 : ZMod M) = d then ZMod.stdAddChar ((p.2 : ZMod M) * (b : ZMod M)) else 0) *
          cexp (2 * π * I * z / M) ^ ((p.1 : ℕ) * p.2)) := by
  have hr : ‖cexp (2 * π * I * z / M)‖ < 1 := by
    simpa [Function.Periodic.qParam] using
      Function.Periodic.norm_qParam_lt_one (Nat.cast_pos.mpr (NeZero.pos M)) hz
  have hs := summable_mul_pow_mul hr (C := 1)
    (f := fun p : ℕ+ × ℕ+ ↦
      if (p.1 : ZMod M) = d then ZMod.stdAddChar ((p.2 : ZMod M) * (b : ZMod M)) else 0)
    fun p ↦ by split_ifs <;> simp
  rw [← tsum_mul_left]
  refine ((hs.mul_left (-2 * π * I)).hasSum).prod_fiberwise fun c ↦ ?_
  split_ifs with hc
  · simpa [hc] using hasSum_pi_mul_cot_pi_mul_div_add_pi_mul_I M c b hz
  · simp

/-- **The corrected cotangents over `ℤ` sum to zero**: if `0 < Im w`, the terms
`π cot (π m w) + sign(m) π i` are odd in `m ∈ ℤ`, decay geometrically, and sum to `0`. -/
theorem hasSum_pi_mul_cot_pi_mul_intCast_mul_add_sign {w : ℂ} (hw : 0 < w.im) :
    HasSum (fun m : ℤ ↦ π * cot (π * (m * w)) + m.sign * (π * I)) 0 := by
  set β : ℤ → ℂ := fun m ↦ π * cot (π * (m * w)) + m.sign * (π * I) with hβ
  set ρ := Real.exp (-2 * π * w.im)
  have hρ : ρ < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos])
  -- the terms `m ≥ 1` decay geometrically, as the cotangent approaches `-π i`
  have hs : Summable fun n : ℕ ↦ β n := by
    refine ((summable_geometric_of_lt_one (Real.exp_pos _).le hρ).mul_left
      (2 * π / (1 - ρ))).of_norm_bounded fun n ↦ ?_
    have hC : 0 ≤ 2 * π / (1 - ρ) := div_nonneg (by positivity) (by linarith)
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [hβ, CharP.cast_eq_zero, zero_mul, mul_zero, cot_zero,
        Int.sign_zero, Int.cast_zero, add_zero, norm_zero, pow_zero, mul_one]
      exact hC
    have hnw : w.im ≤ ((n : ℂ) * w).im := by
      simpa using le_mul_of_one_le_left hw.le (Nat.one_le_cast.mpr hn)
    have h := norm_pi_mul_cot_pi_mul_add_pi_mul_I_le hw hnw
    have hexp : Real.exp (-2 * π * ((n : ℂ) * w).im) = ρ ^ n := by
      rw [← Real.exp_nat_mul]
      congr 1
      simp
      ring
    rw [hexp] at h
    have hβn : β n = π * cot (π * (n * w)) + π * I := by
      simp [hβ, Int.sign_natCast_of_ne_zero hn.ne']
    rw [hβn]
    exact h
  have hodd (n : ℕ) : β (-((n : ℤ) + 1)) = -β ((n + 1 : ℕ) : ℤ) := by
    simp only [hβ, Int.cast_neg, neg_mul, mul_neg, cot_neg, Int.sign_neg]
    push_cast
    ring
  have h₁ := hs.hasSum
  have h₂ : HasSum (fun n : ℕ ↦ β (-((n : ℤ) + 1))) (-∑' n : ℕ, β n) := by
    have h := ((hasSum_nat_add_iff' 1).mpr h₁).neg
    simp only [Finset.range_one, Finset.sum_singleton] at h
    convert h using 1
    · ext n
      rw [hodd]
    · simp [hβ]
  simpa using h₁.of_nat_of_neg_add_one h₂

/-- **The corrected cotangents along a residue class of `ℤ`**: if `0 < Im z`, the cotangents
`π cot (π (n z + b) / M) + sign(n) π i` over `n ≡ d` modulo `M` sum to the absolutely convergent
double series `-2π i ∑_{c, k ≥ 1} D(c, k) e(z / M)^(c k)`, plus the term `π cot (π b / M)` at
`n = 0` if `d = 0`. Here `D(c, k)` is `e(k b / M)` if `c ≡ d` minus `e(-k b / M)` if `c ≡ -d`:
the classes `n = c ≥ 1` and `n = -c ≤ -1` give its two parts. -/
theorem hasSum_ite_pi_mul_cot_pi_mul_intCast_div_add_sign (M : ℕ) [NeZero M] (d : ZMod M)
    (b : ℤ) {z : ℂ} (hz : 0 < z.im) :
    HasSum (fun n : ℤ ↦ if (n : ZMod M) = d then
        π * cot (π * ((n * z + b) / M)) + n.sign * (π * I) else 0)
      ((if d = 0 then π * cot (π * (b / M)) else 0) +
        ∑' p : ℕ+ × ℕ+, -2 * π * I *
          ((if (p.1 : ZMod M) = d then ZMod.stdAddChar ((p.2 : ZMod M) * (b : ZMod M)) else 0) -
            if (p.1 : ZMod M) = -d then ZMod.stdAddChar (-((p.2 : ZMod M) * (b : ZMod M)))
            else 0) *
          cexp (2 * π * I * z / M) ^ ((p.1 : ℕ) * p.2)) := by
  have hr : ‖cexp (2 * π * I * z / M)‖ < 1 := by
    simpa [Function.Periodic.qParam] using
      Function.Periodic.norm_qParam_lt_one (Nat.cast_pos.mpr (NeZero.pos M)) hz
  set r := cexp (2 * π * I * z / M)
  set Φ : ℤ → ℂ := fun n ↦ if (n : ZMod M) = d then
    π * cot (π * ((n * z + b) / M)) + n.sign * (π * I) else 0 with hΦ
  set P := ∑' p : ℕ+ × ℕ+,
    (if (p.1 : ZMod M) = d then ZMod.stdAddChar ((p.2 : ZMod M) * (b : ZMod M)) else 0) *
      r ^ ((p.1 : ℕ) * p.2)
  set Q := ∑' p : ℕ+ × ℕ+,
    (if (p.1 : ZMod M) = -d then
      ZMod.stdAddChar ((p.2 : ZMod M) * ((-b : ℤ) : ZMod M)) else 0) * r ^ ((p.1 : ℕ) * p.2)
  -- the classes `n ≥ 1`
  have h₁ : HasSum (fun n : ℕ ↦ Φ n) (-2 * π * I * P + Φ 0) := by
    refine hasSum_pnat_iff.mp ?_
    convert hasSum_ite_pi_mul_cot_pi_mul_div_add_pi_mul_I M d b hz using 2 with c
    simp [hΦ, Int.sign_natCast_of_ne_zero c.ne_zero]
  -- the classes `n ≤ -1`, by the oddness of the cotangent
  have h₂ : HasSum (fun n : ℕ ↦ Φ (-((n : ℤ) + 1))) (-(-2 * π * I * Q)) := by
    refine (hasSum_pnat_iff_hasSum_succ (f := fun n : ℕ ↦ Φ (-n))).mp ?_
    convert (hasSum_ite_pi_mul_cot_pi_mul_div_add_pi_mul_I M (-d) (-b) hz).neg using 2 with c
    have hc : ((-((c : ℕ) : ℤ) : ℤ) : ZMod M) = d ↔ ((c : ℕ) : ZMod M) = -d := by
      push_cast
      exact neg_eq_iff_eq_neg
    have harg : π * ((((-((c : ℕ) : ℤ) : ℤ) : ℂ) * z + b) / M) =
        -(π * ((((c : ℕ) : ℂ) * z + ((-b : ℤ) : ℂ)) / M)) := by
      push_cast
      ring
    simp only [hΦ, hc, harg, cot_neg, Int.sign_neg, Int.sign_natCast_of_ne_zero c.ne_zero]
    split_ifs <;> push_cast <;> ring
  convert h₁.of_nat_of_neg_add_one h₂ using 1
  have hsP := summable_mul_pow_mul hr (C := 1)
    (f := fun p : ℕ+ × ℕ+ ↦ if (p.1 : ZMod M) = d then
      ZMod.stdAddChar ((p.2 : ZMod M) * (b : ZMod M)) else 0)
    fun p ↦ by split_ifs <;> simp
  have hsQ := summable_mul_pow_mul hr (C := 1)
    (f := fun p : ℕ+ × ℕ+ ↦ if (p.1 : ZMod M) = -d then
      ZMod.stdAddChar ((p.2 : ZMod M) * ((-b : ℤ) : ZMod M)) else 0)
    fun p ↦ by split_ifs <;> simp
  have hD : ∑' p : ℕ+ × ℕ+, -2 * π * I *
      ((if (p.1 : ZMod M) = d then ZMod.stdAddChar ((p.2 : ZMod M) * (b : ZMod M)) else 0) -
        if (p.1 : ZMod M) = -d then ZMod.stdAddChar (-((p.2 : ZMod M) * (b : ZMod M)))
        else 0) * r ^ ((p.1 : ℕ) * p.2) = -2 * π * I * (P - Q) := by
    rw [← hsP.tsum_sub hsQ, ← tsum_mul_left]
    refine tsum_congr fun p ↦ ?_
    simp only [Int.cast_neg, mul_neg]
    ring
  rw [hD]
  simp only [hΦ, Int.cast_zero, zero_mul, zero_add, Int.sign_zero, add_zero,
    eq_comm (a := (0 : ZMod M))]
  ring

/-- **The cotangent rows at a division point, as a `q`-expansion.** If `0 < Im z` and
`0 ≤ b₀ < M`, the rows `π cot (π (x - m z)) + π cot (π m z)` at `x = (b₀ z + b) / M` sum over
`m ∈ ℤ` to `-2π i ∑_{c, k ≥ 1} D(c, k) e(z / M)^(c k)`, plus the constant `π cot (π b / M)` if
`b₀ = 0` and `-π i` otherwise, with `D` as in
`TauCeti.hasSum_ite_pi_mul_cot_pi_mul_intCast_div_add_sign`. Write `x - m z = (n z + b) / M` with
`n = b₀ - m M`, which runs over the residue class of `b₀`; the signs of `n` and `m` cancel except
at `m = 0`, and the remaining cotangents `π cot (π m z) + sign(m) π i` cancel in pairs. -/
theorem hasSum_pi_mul_cot_pi_mul_div_sub_intCast_mul_add_pi_mul_cot {M b₀ : ℕ} [NeZero M]
    (hb : b₀ < M) (b : ℤ) {z : ℂ} (hz : 0 < z.im) :
    HasSum (fun m : ℤ ↦ π * cot (π * ((b₀ * z + b) / M - m * z)) + π * cot (π * (m * z)))
      ((if b₀ = 0 then π * cot (π * (b / M)) else -(π * I)) +
        ∑' p : ℕ+ × ℕ+, -2 * π * I *
          ((if (p.1 : ZMod M) = b₀ then ZMod.stdAddChar ((p.2 : ZMod M) * (b : ZMod M)) else 0) -
            if (p.1 : ZMod M) = -(b₀ : ZMod M) then
              ZMod.stdAddChar (-((p.2 : ZMod M) * (b : ZMod M))) else 0) *
          cexp (2 * π * I * z / M) ^ ((p.1 : ℕ) * p.2)) := by
  have hb₀ : (b₀ : ZMod M) = 0 ↔ b₀ = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).trans
      ⟨fun h ↦ Nat.eq_zero_of_dvd_of_lt h hb, fun h ↦ h ▸ dvd_zero M⟩
  set Φ : ℤ → ℂ := fun n ↦ if (n : ZMod M) = b₀ then
    π * cot (π * ((n * z + b) / M)) + n.sign * (π * I) else 0 with hΦ
  -- the row `m` lies on the residue class at `n = b₀ - m M`
  have hinj : Function.Injective fun m : ℤ ↦ (b₀ : ℤ) - m * M := fun m m' h ↦ by
    have : (m - m') * (M : ℤ) = 0 := by linear_combination -h
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right (by exact_mod_cast NeZero.ne M))
  have hrange (n : ℤ) (hn : n ∉ Set.range fun m : ℤ ↦ (b₀ : ℤ) - m * M) : Φ n = 0 := by
    simp only [hΦ, ite_eq_right_iff]
    intro h
    rw [← Int.cast_natCast, ZMod.intCast_eq_intCast_iff_dvd_sub] at h
    obtain ⟨m, hm⟩ := h
    exact absurd ⟨m, by dsimp only; linear_combination hm⟩ hn
  have hrows := (hinj.hasSum_iff hrange).mpr
    (hasSum_ite_pi_mul_cot_pi_mul_intCast_div_add_sign M (b₀ : ZMod M) b hz)
  set δ : ℂ := if b₀ = 0 then 0 else -(π * I)
  convert (hrows.add (hasSum_pi_mul_cot_pi_mul_intCast_mul_add_sign hz)).add
    (hasSum_ite_eq (0 : ℤ) δ) using 1
  · ext m
    have hres : (((b₀ : ℤ) - m * M : ℤ) : ZMod M) = b₀ := by simp
    have harg : ((((b₀ : ℤ) - m * M : ℤ) : ℂ) * z + b) / M = (b₀ * z + b) / M - m * z := by
      field_simp [Nat.cast_ne_zero.mpr (NeZero.ne M)]
      push_cast
      ring
    have hs : ((((b₀ : ℤ) - m * M).sign + m.sign : ℤ) : ℂ) = if m = 0 ∧ b₀ ≠ 0 then 1 else 0 := by
      rw [Int.sign_sub_mul_add_sign (Int.natCast_nonneg b₀) (by exact_mod_cast hb) m]
      simp only [ne_eq, Nat.cast_eq_zero]
      split_ifs <;> simp
    have hδ : (if m = 0 then δ else 0) =
        -(if m = 0 ∧ b₀ ≠ 0 then 1 else 0) * (π * I) := by
      by_cases hm : m = 0 <;> by_cases h0 : b₀ = 0 <;> simp [δ, hm, h0]
    simp only [Function.comp_apply, hΦ, hres, ↓reduceIte, harg, hδ, ← hs]
    push_cast
    ring
  · simp only [hb₀, δ]
    split_ifs <;> ring

end TauCeti

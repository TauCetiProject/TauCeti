/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Mathlib.NumberTheory.ZetaValues
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import TauCeti.Analysis.Asymptotics.Sum.EulerMaclaurin
import TauCeti.NumberTheory.ZetaValues

/-!
# Euler–Maclaurin expansion of the harmonic numbers

Applying the even-order Euler–Maclaurin summation formula on `[1, n]` to `x ↦ x⁻¹` expresses the
harmonic numbers `H_n = ∑_{j=1}^n j⁻¹` and the shifted partial sums `∑_{j=1}^{n-1} j⁻¹` in terms
of `log n`, Bernoulli numbers `B_{2s}`, and an integrable tail on `(n, ∞)` against
`B_{2m} - B_{2m}({x})`. Comparing the `n → ∞` limit with `Real.tendsto_harmonic_sub_log`
identifies the constant term as Euler's constant `γ = Real.eulerMascheroniConstant` and yields the
order-`2m` Euler–Maclaurin formula for `γ` itself.

Because consecutive remainders have strict opposite signs, comparing the order-`2m` and
order-`2(m + 1)` formulas shows that the remainder after `m - 1` Bernoulli terms is a strict
fraction `θ ∈ (0, 1)` of the first neglected term `-(B_{2m} / (2m)) * n ^ (-2m)` (DLMF 2.10.8).

## Main results

* `TauCeti.eulerMascheroniConstant_eq_eulerMaclaurin`: for `m ≥ 1`,
  `γ = 1 / 2 + ∑_{s=1}^{m-1} B_{2s} / (2s) + ∫_1^∞ (B_{2m} - B_{2m}({x})) x^{-(2m+1)} dx`.
* `TauCeti.harmonic_eq_eulerMaclaurin` and `TauCeti.sum_Ico_inv_eq_eulerMaclaurin`: exact
  Euler–Maclaurin expansions of `harmonic n` and `∑_{j=1}^{n-1} j⁻¹` for `m ≥ 1`, `n ≥ 1`.
* `TauCeti.exists_Ioo_harmonic_sub_eulerMaclaurin`,
  `TauCeti.exists_Ioo_sum_Ico_inv_sub_eulerMaclaurin`, and
  `TauCeti.abs_harmonic_sub_eulerMaclaurin_lt`: the `θ ∈ (0, 1)` remainder representation and
  strict magnitude bound (DLMF 2.10.8).
* `TauCeti.harmonic_sub_eulerMaclaurin_isBigO` and
  `TauCeti.sum_Ico_inv_sub_eulerMaclaurin_isBigO`: `O(n ^ (-2m))` asymptotic bounds as `n → ∞`.

## References

* NIST *Digital Library of Mathematical Functions*, §2.10(i), formula 2.10.8.
* F. W. J. Olver, *Asymptotics and Special Functions*, Chapter 8, §2.1.
-/

public section

open Filter Finset intervalIntegral MeasureTheory
open scoped Nat Real Topology

namespace TauCeti

/-- Derivative of `x ↦ (-1)^i * i! * x ^ (-(i + 1 : ℤ))` on `(0, ∞)`. -/
private theorem hasDerivAt_inv_iterated (i : ℕ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => (-1 : ℝ) ^ i * i ! * y ^ (-(i + 1 : ℤ)))
      ((-1 : ℝ) ^ (i + 1) * (i + 1)! * x ^ (-((i + 1 : ℕ) + 1 : ℤ))) x := by
  have hd := (hasDerivAt_zpow (-(i + 1 : ℤ)) x (Or.inl hx.ne')).const_mul ((-1 : ℝ) ^ i * i !)
  refine hd.congr_deriv ?_
  rw [Nat.factorial_succ, pow_succ, show (-(i + 1 : ℤ) - 1 : ℤ) = -((i + 1 : ℕ) + 1 : ℤ) by omega]
  push_cast; ring

/-- Integrability of `(B_{2m} - B_{2m}({x})) * x ^ (-(2m + 1 : ℤ))` on `(a, ∞)` for `a > 0`,
`m ≥ 1`. -/
private theorem integrableOn_bernoulli_sub_mul_zpow_neg {m : ℕ} (hm : 1 ≤ m) {a : ℝ}
    (ha : 0 < a) :
    IntegrableOn
      (fun x : ℝ => ((bernoulli (2 * m) : ℝ) - bernoulliFun (2 * m) (Int.fract x)) *
        x ^ (-(2 * m + 1 : ℤ))) (Set.Ioi a) := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hrpow : IntegrableOn (fun x : ℝ => x ^ (-(2 * (m : ℝ) + 1))) (Set.Ioi a) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) ha
  have hzpow : IntegrableOn (fun x : ℝ => x ^ (-(2 * m + 1 : ℤ))) (Set.Ioi a) :=
    hrpow.congr_fun (fun x _ => by rw [← Real.rpow_intCast]; push_cast; rfl) measurableSet_Ioi
  exact hzpow.bernoulli_sub_bernoulliFun_fract_smul (2 * m)

/-- Finite-interval Euler–Maclaurin identity on `[1, n]` for `(harmonic n : ℝ)`. -/
private theorem harmonic_eq_finite_eulerMaclaurin {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    (harmonic n : ℝ) = Real.log n + 1 / 2 + 1 / (2 * (n : ℝ)) +
      ∑ s ∈ Ico 1 m, (bernoulli (2 * s) : ℝ) / (2 * s) -
      ∑ s ∈ Ico 1 m, (bernoulli (2 * s) : ℝ) / (2 * s) * (n : ℝ) ^ (-(2 * s : ℤ)) +
      ∫ x in (1 : ℝ)..n,
        ((bernoulli (2 * m) : ℝ) - bernoulliFun (2 * m) (Int.fract x)) *
          x ^ (-(2 * m + 1 : ℤ)) := by
  set g : ℕ → ℝ → ℝ := fun i x => (-1 : ℝ) ^ i * i ! * x ^ (-(i + 1 : ℤ))
  have hcont : ∀ i, ContinuousOn (g i) (Set.Icc ((1 : ℤ) : ℝ) ((n : ℤ) : ℝ)) := fun i x hx =>
    (continuousAt_const.mul ((hasDerivAt_zpow _ x
      (Or.inl (zero_lt_one.trans_le (by simpa using hx.1)).ne')).continuousAt)).continuousWithinAt
  have hEM := sum_Icc_eq_eulerMaclaurin_of_hasDerivAt_two_mul (g := g)
    (a := 1) (n := (n : ℤ)) (by exact_mod_cast hn) hm (fun i _ => hcont i)
    (fun i _ x hx => hasDerivAt_inv_iterated i (zero_lt_one.trans (by simpa using hx.1)))
    ((hcont (2 * m)).intervalIntegrable_of_Icc (by exact_mod_cast hn))
  have hsum : (harmonic n : ℝ) = ∑ j ∈ Icc (1 : ℤ) n, g 0 j := by
    have himg : (range n).image (fun i : ℕ => (i + 1 : ℤ)) = Icc (1 : ℤ) n := by
      ext z; simp only [mem_image, mem_range, mem_Icc]
      exact ⟨fun ⟨i, hi, hiz⟩ => ⟨by omega, by omega⟩,
        fun hz => ⟨(z - 1).toNat, by omega, by omega⟩⟩
    rw [harmonic, Rat.cast_sum, ← himg,
      Finset.sum_image (f := fun j : ℤ => g 0 (j : ℝ)) (fun a _ b _ h => by omega)]
    exact sum_congr rfl fun i _ => by simp [g]
  have hint0 : ∫ x in (1 : ℝ)..n, g 0 x = Real.log n := by
    have h0 : (0 : ℝ) ∉ Set.uIcc (1 : ℝ) n := by
      rw [Set.uIcc_of_le (by exact_mod_cast hn), Set.mem_Icc]; intro h; linarith [h.1]
    rw [show (fun x : ℝ => g 0 x) = fun x : ℝ => x⁻¹ by ext x; simp [g], integral_inv h0, div_one]
  have hmid : ∀ s ∈ Ico 1 m, ((bernoulli (2 * s) : ℝ) / (2 * s)!) •
        (g (2 * s - 1) n - g (2 * s - 1) 1) =
      (bernoulli (2 * s) : ℝ) / (2 * s) -
        (bernoulli (2 * s) : ℝ) / (2 * s) * (n : ℝ) ^ (-(2 * s : ℤ)) := fun s hs => by
    have hs1 : 1 ≤ s := (mem_Ico.mp hs).1
    have hpow : (-1 : ℝ) ^ (2 * s - 1) = -1 := Odd.neg_one_pow ⟨s - 1, by omega⟩
    have hfact : ((2 * s)! : ℝ) = (2 * s : ℝ) * (2 * s - 1)! := by
      exact_mod_cast (Nat.mul_factorial_pred (n := 2 * s) (by omega)).symm
    have hf0 : ((2 * s - 1)! : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    simp only [g, smul_eq_mul, hpow, show -((2 * s - 1 : ℕ) + 1 : ℤ) = -(2 * s : ℤ) by omega,
      one_zpow, hfact]
    field_simp; ring
  have hrem : ∫ x in (1 : ℝ)..n,
        ((bernoulli (2 * m) - bernoulliFun (2 * m) (Int.fract x)) / (2 * m)!) • g (2 * m) x =
      ∫ x in (1 : ℝ)..n,
        ((bernoulli (2 * m) : ℝ) - bernoulliFun (2 * m) (Int.fract x)) *
          x ^ (-(2 * m + 1 : ℤ)) := by
    refine integral_congr fun x _ => ?_
    have hf0 : ((2 * m)! : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    simp only [g, smul_eq_mul, pow_mul, neg_one_sq, one_pow, one_mul, Nat.cast_mul, Nat.cast_ofNat]
    field_simp
  rw [Int.cast_one, Int.cast_natCast] at hEM
  rw [hsum, hEM, hint0, sum_congr rfl hmid, sum_sub_distrib, hrem]
  simp only [g, pow_zero, Nat.factorial_zero, Nat.cast_one, one_mul, Nat.cast_zero, zero_add,
    zpow_neg_one, inv_one, smul_eq_mul]
  ring

/-- **Euler–Maclaurin representation of Euler's constant** `γ`. For every `m ≥ 1`,
`γ = 1 / 2 + ∑_{s=1}^{m-1} B_{2s} / (2s) + ∫_1^∞ (B_{2m} - B_{2m}({x})) x^{-(2m+1)} dx`. -/
theorem eulerMascheroniConstant_eq_eulerMaclaurin {m : ℕ} (hm : 1 ≤ m) :
    Real.eulerMascheroniConstant = 1 / 2 + ∑ s ∈ Ico 1 m, (bernoulli (2 * s) : ℝ) / (2 * s) +
      ∫ x in Set.Ioi (1 : ℝ),
        ((bernoulli (2 * m) : ℝ) - bernoulliFun (2 * m) (Int.fract x)) *
          x ^ (-(2 * m + 1 : ℤ)) := by
  have hzpow0 : ∀ k : ℕ, 1 ≤ k → Tendsto (fun n : ℕ => (n : ℝ) ^ (-(k : ℤ))) atTop (𝓝 0) :=
    fun k _ => by
      refine (tendsto_rpow_neg_atTop (by positivity : (0 : ℝ) < k)).comp
        tendsto_natCast_atTop_atTop |>.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with n _
      simp [zpow_neg]
  have hinv0 : Tendsto (fun n : ℕ => 1 / (2 * (n : ℝ))) atTop (𝓝 0) := by
    simpa using (hzpow0 1 le_rfl).const_mul (1 / 2 : ℝ) |>.congr fun n => by simp; ring
  have hint := integrableOn_bernoulli_sub_mul_zpow_neg hm zero_lt_one
  have hRHS : Tendsto (fun n : ℕ =>
      1 / 2 + 1 / (2 * (n : ℝ)) + ∑ s ∈ Ico 1 m, (bernoulli (2 * s) : ℝ) / (2 * s) -
        ∑ s ∈ Ico 1 m, (bernoulli (2 * s) : ℝ) / (2 * s) * (n : ℝ) ^ (-(2 * s : ℤ)) +
        ∫ x in (1 : ℝ)..n,
          ((bernoulli (2 * m) : ℝ) - bernoulliFun (2 * m) (Int.fract x)) *
            x ^ (-(2 * m + 1 : ℤ))) atTop
      (𝓝 (1 / 2 + 0 + ∑ s ∈ Ico 1 m, (bernoulli (2 * s) : ℝ) / (2 * s) -
        ∑ _s ∈ Ico 1 m, 0 +
        ∫ x in Set.Ioi (1 : ℝ),
          ((bernoulli (2 * m) : ℝ) - bernoulliFun (2 * m) (Int.fract x)) *
            x ^ (-(2 * m + 1 : ℤ)))) :=
    (((tendsto_const_nhds.add hinv0).add tendsto_const_nhds).sub
      (tendsto_finsetSum _ fun s hs => by
        simpa using (hzpow0 (2 * s) (by linarith [(mem_Ico.mp hs).1])).const_mul _)).add
      (intervalIntegral_tendsto_integral_Ioi 1 hint tendsto_natCast_atTop_atTop)
  have heq := tendsto_nhds_unique Real.tendsto_harmonic_sub_log (hRHS.congr' (by
    filter_upwards [eventually_ge_atTop 1] with n hn
    linarith [harmonic_eq_finite_eulerMaclaurin hm hn]))
  simpa using heq

/-- **Euler–Maclaurin expansion of the harmonic numbers**. For `m ≥ 1` and `n ≥ 1`,
`H_n = log n + γ + 1 / (2n) - ∑_{s=1}^{m-1} (B_{2s} / (2s)) n^{-2s}
  - ∫_n^∞ (B_{2m} - B_{2m}({x})) x^{-(2m+1)} dx`. -/
theorem harmonic_eq_eulerMaclaurin {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    (harmonic n : ℝ) = Real.log n + Real.eulerMascheroniConstant + 1 / (2 * (n : ℝ)) -
      ∑ s ∈ Ico 1 m, (bernoulli (2 * s) : ℝ) / (2 * s) * (n : ℝ) ^ (-(2 * s : ℤ)) -
      ∫ x in Set.Ioi (n : ℝ),
        ((bernoulli (2 * m) : ℝ) - bernoulliFun (2 * m) (Int.fract x)) *
          x ^ (-(2 * m + 1 : ℤ)) := by
  have hsplit := intervalIntegral.integral_Ioi_sub_Ioi
    (integrableOn_bernoulli_sub_mul_zpow_neg hm zero_lt_one) (b := (n : ℝ)) (by exact_mod_cast hn)
  linarith [harmonic_eq_finite_eulerMaclaurin hm hn, eulerMascheroniConstant_eq_eulerMaclaurin hm,
    hsplit]

/-- **Euler–Maclaurin expansion of `∑_{j=1}^{n-1} j⁻¹`** (DLMF 2.10.8, integral-remainder form).
For `m ≥ 1` and `n ≥ 1`,
`∑_{j=1}^{n-1} j⁻¹ = log n + γ - 1 / (2n) - ∑_{s=1}^{m-1} (B_{2s} / (2s)) n^{-2s}
  - ∫_n^∞ (B_{2m} - B_{2m}({x})) x^{-(2m+1)} dx`. -/
theorem sum_Ico_inv_eq_eulerMaclaurin {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    ∑ j ∈ Ico 1 n, (j : ℝ)⁻¹ = Real.log n + Real.eulerMascheroniConstant - 1 / (2 * (n : ℝ)) -
      ∑ s ∈ Ico 1 m, (bernoulli (2 * s) : ℝ) / (2 * s) * (n : ℝ) ^ (-(2 * s : ℤ)) -
      ∫ x in Set.Ioi (n : ℝ),
        ((bernoulli (2 * m) : ℝ) - bernoulliFun (2 * m) (Int.fract x)) *
          x ^ (-(2 * m + 1 : ℤ)) := by
  have hsum : (harmonic n : ℝ) = ∑ j ∈ Ico 1 n, (j : ℝ)⁻¹ + (n : ℝ)⁻¹ := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    rw [harmonic_succ, Rat.cast_add, Rat.cast_inv, Nat.cast_succ]
    congr 1
    · rw [harmonic, Rat.cast_sum, Finset.sum_Ico_eq_sum_range, Nat.succ_sub_one]
      exact sum_congr rfl fun i _ => by push_cast; ring_nf
    · push_cast; rfl
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hinv : (n : ℝ)⁻¹ = 1 / (2 * (n : ℝ)) + 1 / (2 * (n : ℝ)) := by field_simp; ring
  linarith [harmonic_eq_eulerMaclaurin hm hn, hsum, hinv]

/-- **DLMF 2.10.8 remainder theorem for `harmonic n`**: for `m ≥ 1` and `n ≥ 1`, the remainder
after `m - 1` Bernoulli terms equals `θ` times the first neglected term
`-(B_{2m} / (2m)) n^{-2m}` for some `θ ∈ (0, 1)`. -/
theorem exists_Ioo_harmonic_sub_eulerMaclaurin {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    ∃ θ ∈ Set.Ioo (0 : ℝ) 1,
      (harmonic n : ℝ) - (Real.log n + Real.eulerMascheroniConstant + 1 / (2 * (n : ℝ)) -
        ∑ s ∈ Ico 1 m, (bernoulli (2 * s) : ℝ) / (2 * s) * (n : ℝ) ^ (-(2 * s : ℤ))) =
        θ * (-(bernoulli (2 * m) : ℝ) / (2 * m) * (n : ℝ) ^ (-(2 * m : ℤ))) := by
  set rem : ℕ → ℝ := fun k => -∫ x in Set.Ioi (n : ℝ),
    ((bernoulli (2 * k) : ℝ) - bernoulliFun (2 * k) (Int.fract x)) * x ^ (-(2 * k + 1 : ℤ))
  set term : ℝ := -(bernoulli (2 * m) : ℝ) / (2 * m) * (n : ℝ) ^ (-(2 * m : ℤ))
  have hm_eq := harmonic_eq_eulerMaclaurin hm hn
  have hm1_eq := harmonic_eq_eulerMaclaurin (m := m + 1) (by omega) hn
  rw [sum_Ico_succ_top hm] at hm1_eq
  have hterm : term = -((bernoulli (2 * m) : ℝ) / (2 * m) * (n : ℝ) ^ (-(2 * m : ℤ))) := by
    dsimp [term]; ring
  have hstep : rem m = term + rem (m + 1) := by linarith [hm_eq, hm1_eq, hterm]
  have hsign : ∀ k : ℕ, 1 ≤ k → 0 < (-1 : ℝ) ^ k * rem k := fun k hk => by
    have hn_pos : (0 : ℝ) < n := by positivity
    have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hw_int : IntegrableOn (fun x : ℝ => x ^ (-(2 * k + 1 : ℤ))) (Set.Ioi (n : ℝ)) :=
      (integrableOn_Ioi_rpow_of_lt (a := -(2 * (k : ℝ) + 1)) (by linarith) hn_pos).congr_fun
        (fun x _ => by rw [← Real.rpow_intCast]; push_cast; rfl) measurableSet_Ioi
    have hw_cont : ContinuousOn (fun x : ℝ => x ^ (-(2 * k + 1 : ℤ))) (Set.Ioi (n : ℝ)) :=
      fun x hx => ((hasDerivAt_zpow _ x (Or.inl (hn_pos.trans hx).ne')).continuousAt
        ).continuousWithinAt
    simpa [rem, pow_succ] using
      neg_one_pow_succ_mul_setIntegral_bernoulli_sub_bernoulliFun_fract_mul_pos
        (k := k) (by omega) hw_int hw_cont (fun x hx => zpow_pos (hn_pos.trans hx) _)
  have hr_pos : 0 < (-1 : ℝ) ^ m * rem m := hsign m hm
  have hr1_neg : (-1 : ℝ) ^ m * rem (m + 1) < 0 := by
    have h := hsign (m + 1) (by omega)
    rw [pow_succ, mul_assoc, neg_one_mul, mul_neg] at h; linarith
  have ht_pos : 0 < (-1 : ℝ) ^ m * term := by linarith [congrArg ((-1 : ℝ) ^ m * ·) hstep]
  have hrt_lt : (-1 : ℝ) ^ m * rem m < (-1 : ℝ) ^ m * term := by
    linarith [congrArg ((-1 : ℝ) ^ m * ·) hstep]
  have ht_ne : term ≠ 0 := fun h => by simp [h] at ht_pos
  have hθ_eq : rem m / term = ((-1 : ℝ) ^ m * rem m) / ((-1 : ℝ) ^ m * term) :=
    (mul_div_mul_left _ _ (pow_ne_zero m (by norm_num))).symm
  refine ⟨rem m / term, ⟨?_, ?_⟩, ?_⟩
  · rw [hθ_eq]; exact div_pos hr_pos ht_pos
  · rw [hθ_eq, div_lt_one ht_pos]; exact hrt_lt
  · have hrem_sub : (harmonic n : ℝ) -
        (Real.log n + Real.eulerMascheroniConstant + 1 / (2 * (n : ℝ)) -
          ∑ s ∈ Ico 1 m, (bernoulli (2 * s) : ℝ) / (2 * s) * (n : ℝ) ^ (-(2 * s : ℤ))) =
        rem m := by linarith [hm_eq]
    rw [hrem_sub, div_mul_cancel₀ _ ht_ne]

/-- **DLMF 2.10.8** for `∑_{j=1}^{n-1} j⁻¹`: for `m ≥ 1` and `n ≥ 1`, there exists `θ ∈ (0, 1)`
such that
`∑_{j=1}^{n-1} j⁻¹ = log n + γ - 1/(2n) - ∑_{s=1}^{m-1} (B_{2s}/(2s)) n^{-2s}
  - θ (B_{2m}/(2m)) n^{-2m}`. -/
theorem exists_Ioo_sum_Ico_inv_sub_eulerMaclaurin {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    ∃ θ ∈ Set.Ioo (0 : ℝ) 1,
      ∑ j ∈ Ico 1 n, (j : ℝ)⁻¹ -
        (Real.log n + Real.eulerMascheroniConstant - 1 / (2 * (n : ℝ)) -
          ∑ s ∈ Ico 1 m, (bernoulli (2 * s) : ℝ) / (2 * s) * (n : ℝ) ^ (-(2 * s : ℤ))) =
        θ * (-(bernoulli (2 * m) : ℝ) / (2 * m) * (n : ℝ) ^ (-(2 * m : ℤ))) := by
  obtain ⟨θ, hθ, heq⟩ := exists_Ioo_harmonic_sub_eulerMaclaurin hm hn
  refine ⟨θ, hθ, ?_⟩
  linarith [harmonic_eq_eulerMaclaurin hm hn, sum_Ico_inv_eq_eulerMaclaurin hm hn, heq]

/-- Strict error bound for the Euler–Maclaurin expansion of `harmonic n`: the remainder is strictly
smaller in absolute value than the first neglected term `|B_{2m}| / (2m) * n ^ (-2m)`. -/
theorem abs_harmonic_sub_eulerMaclaurin_lt {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    |(harmonic n : ℝ) - (Real.log n + Real.eulerMascheroniConstant + 1 / (2 * (n : ℝ)) -
      ∑ s ∈ Ico 1 m, (bernoulli (2 * s) : ℝ) / (2 * s) * (n : ℝ) ^ (-(2 * s : ℤ)))| <
      |(bernoulli (2 * m) : ℝ)| / (2 * m) * (n : ℝ) ^ (-(2 * m : ℤ)) := by
  obtain ⟨θ, hθ, heq⟩ := exists_Ioo_harmonic_sub_eulerMaclaurin hm hn
  have hB : |(bernoulli (2 * m) : ℝ)| ≠ 0 :=
    abs_ne_zero.mpr (Rat.cast_ne_zero.mpr (bernoulli_two_mul_ne_zero (by omega)))
  have hterm_pos : 0 < |(bernoulli (2 * m) : ℝ)| / (2 * m) * (n : ℝ) ^ (-(2 * m : ℤ)) :=
    mul_pos (div_pos (abs_pos.mpr (abs_ne_zero.mp hB)) (by positivity))
      (zpow_pos (by positivity) _)
  have hterm_abs : |-(bernoulli (2 * m) : ℝ) / (2 * m) * (n : ℝ) ^ (-(2 * m : ℤ))| =
      |(bernoulli (2 * m) : ℝ)| / (2 * m) * (n : ℝ) ^ (-(2 * m : ℤ)) := by
    rw [abs_mul, abs_div, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 2 * m),
      abs_of_pos (zpow_pos (by positivity : (0 : ℝ) < n) _)]
  rw [heq, abs_mul, hterm_abs, abs_of_pos hθ.1]
  exact mul_lt_of_lt_one_left hterm_pos hθ.2

/-- Asymptotic bound `O(n ^ (-2m))` for the order-`2m` Euler–Maclaurin expansion of `harmonic n`. -/
theorem harmonic_sub_eulerMaclaurin_isBigO {m : ℕ} (hm : 1 ≤ m) :
    (fun n : ℕ => (harmonic n : ℝ) -
      (Real.log n + Real.eulerMascheroniConstant + 1 / (2 * (n : ℝ)) -
        ∑ s ∈ Ico 1 m, (bernoulli (2 * s) : ℝ) / (2 * s) * (n : ℝ) ^ (-(2 * s : ℤ)))) =O[atTop]
      fun n : ℕ => (n : ℝ) ^ (-(2 * m : ℤ)) := by
  refine Asymptotics.IsBigO.of_bound (|(bernoulli (2 * m) : ℝ)| / (2 * m)) ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  simp only [Real.norm_eq_abs, abs_of_pos (zpow_pos (by positivity : (0 : ℝ) < n) _)]
  exact (abs_harmonic_sub_eulerMaclaurin_lt hm hn).le

/-- Asymptotic bound `O(n ^ (-2m))` for the order-`2m` Euler–Maclaurin expansion of
`∑_{j=1}^{n-1} j⁻¹` (DLMF 2.10.8). -/
theorem sum_Ico_inv_sub_eulerMaclaurin_isBigO {m : ℕ} (hm : 1 ≤ m) :
    (fun n : ℕ => ∑ j ∈ Ico 1 n, (j : ℝ)⁻¹ -
      (Real.log n + Real.eulerMascheroniConstant - 1 / (2 * (n : ℝ)) -
        ∑ s ∈ Ico 1 m, (bernoulli (2 * s) : ℝ) / (2 * s) * (n : ℝ) ^ (-(2 * s : ℤ)))) =O[atTop]
      fun n : ℕ => (n : ℝ) ^ (-(2 * m : ℤ)) := by
  refine (harmonic_sub_eulerMaclaurin_isBigO hm).congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_ge_atTop 1] with n hn
  linarith [harmonic_eq_eulerMaclaurin hm hn, sum_Ico_inv_eq_eulerMaclaurin hm hn]

end TauCeti

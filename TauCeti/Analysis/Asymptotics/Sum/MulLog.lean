/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.NumberTheory.ZetaValues
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import TauCeti.Analysis.Asymptotics.Sum.EulerMaclaurin
import TauCeti.NumberTheory.LSeries.RiemannZeta.EulerMaclaurin
import TauCeti.NumberTheory.ZetaValues

/-!
# Euler–Maclaurin expansion of `∑ j log j`

Applying the even-order Euler–Maclaurin summation formula on `[1, n]` at order `2(m + 1)` (`m ≥ 1`)
to `x ↦ x log x` expresses `∑_{j=1}^n j log j` and `∑_{j=1}^{n-1} j log j` in terms of
`(n^2 / 2 ± n / 2 + 1 / 12) log n - n^2 / 4`, Bernoulli numbers `B_{2k+2}`, and an integrable tail
on `(n, ∞)`. At `m = 1`, comparing the `n`-independent constant term with
`TauCeti.deriv_riemannZeta_neg_one_re` identifies the constant as `1 / 12 - Re ζ'(-1)` (the
logarithm of the Glaisher–Kinkelin constant, DLMF 2.10.3–2.10.6).

Comparing consecutive orders then yields the strict `θ ∈ (0, 1)` remainder representation
(DLMF 2.10.5), strict magnitude bound, and `O(n ^ (-2m))` asymptotic error as `n → ∞`.

## Main results

* `TauCeti.tendsto_sum_mul_log_sub` and `TauCeti.tendsto_sum_mul_log_sub'`:
  `∑_{j=1}^n j log j - (n^2 / 2 * log n - n^2 / 4 + n / 2 * log n + log n / 12)` converges as
  `n → ∞` to `1 / 12 - (deriv riemannZeta (-1)).re`, equivalently
  `(γ + log (2π)) / 12 - (deriv riemannZeta 2).re / (2π²)` (DLMF 2.10.3–2.10.6).
* `TauCeti.one_div_twelve_sub_deriv_riemannZeta_neg_one_re_eq_eulerMaclaurin`: order-`2(m + 1)`
  Euler–Maclaurin representation of `1 / 12 - (deriv riemannZeta (-1)).re`.
* `TauCeti.sum_Icc_mul_log_eq_eulerMaclaurin` and `TauCeti.sum_Ico_mul_log_eq_eulerMaclaurin`:
  exact Euler–Maclaurin expansions of `∑_{j=1}^n j log j` and `∑_{j=1}^{n-1} j log j`.
* `TauCeti.exists_Ioo_sum_Icc_mul_log_sub_eulerMaclaurin`,
  `TauCeti.exists_Ioo_sum_Ico_mul_log_sub_eulerMaclaurin`, and
  `TauCeti.abs_sum_Icc_mul_log_sub_eulerMaclaurin_lt`: the DLMF 2.10.5 remainder theorem with
  `θ ∈ (0, 1)` and strict error bound.
* `TauCeti.sum_Icc_mul_log_sub_eulerMaclaurin_isBigO` and
  `TauCeti.sum_Ico_mul_log_sub_eulerMaclaurin_isBigO`: `O(n ^ (-2m))` asymptotic bounds as `n → ∞`.

## References

* NIST *Digital Library of Mathematical Functions*, §2.10(i), formulas 2.10.3–2.10.6.
* F. W. J. Olver, *Asymptotics and Special Functions*, Chapter 8, §2.
-/

public section

open Filter Finset intervalIntegral MeasureTheory
open scoped Nat Real Topology

namespace TauCeti

/-- Explicit `i`-th derivative of `x ↦ x * log x` on `(0, ∞)`. -/
private noncomputable def mulLogIteratedDeriv : ℕ → ℝ → ℝ
  | 0 => fun x => x * Real.log x
  | 1 => fun x => Real.log x + 1
  | k + 2 => fun x => (-1 : ℝ) ^ k * k ! * x ^ (-(k + 1 : ℤ))

/-- `mulLogIteratedDeriv (i + 1)` is the derivative of `mulLogIteratedDeriv i` on `(0, ∞)`. -/
private theorem hasDerivAt_mulLogIteratedDeriv (i : ℕ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (mulLogIteratedDeriv i) (mulLogIteratedDeriv (i + 1) x) x := by
  match i with
  | 0 => exact Real.hasDerivAt_mul_log hx.ne'
  | 1 =>
    simpa [mulLogIteratedDeriv] using (Real.hasDerivAt_log hx.ne').add_const (1 : ℝ)
  | k + 2 =>
    have hd := (hasDerivAt_zpow (-(k + 1 : ℤ)) x (Or.inl hx.ne')).const_mul ((-1 : ℝ) ^ k * k !)
    refine hd.congr_deriv ?_
    simp only [mulLogIteratedDeriv, Nat.factorial_succ, pow_succ]
    rw [show (-(k + 1 : ℤ) - 1 : ℤ) = -((k + 1 : ℕ) + 1 : ℤ) by omega]
    push_cast; ring

/-- Continuity of `mulLogIteratedDeriv i` on `[1, n]`. -/
private theorem continuousOn_mulLogIteratedDeriv (i : ℕ) (n : ℕ) :
    ContinuousOn (mulLogIteratedDeriv i) (Set.Icc ((1 : ℤ) : ℝ) ((n : ℤ) : ℝ)) := by
  intro x hx
  have hx0 : 0 < x := zero_lt_one.trans_le (by simpa using hx.1)
  exact (hasDerivAt_mulLogIteratedDeriv i hx0).continuousAt.continuousWithinAt

/-- Definite integral `∫_1^b x * log x dx = b^2 / 2 * log b - b^2 / 4 + 1 / 4` for `b ≥ 1`. -/
private theorem integral_mul_log_one_to {b : ℝ} (hb : 1 ≤ b) :
    ∫ x in (1 : ℝ)..b, x * Real.log x = b ^ 2 / 2 * Real.log b - b ^ 2 / 4 + 1 / 4 := by
  set F : ℝ → ℝ := fun x => x ^ 2 / 2 * Real.log x - x ^ 2 / 4
  have hderiv : ∀ x ∈ Set.uIcc (1 : ℝ) b, HasDerivAt F (x * Real.log x) x := fun x hx => by
    rw [Set.uIcc_of_le hb] at hx
    have hx0 : (0 : ℝ) < x := zero_lt_one.trans_le hx.1
    have hd1 := (((hasDerivAt_id' x).pow 2).div_const 2).fun_mul (Real.hasDerivAt_log hx0.ne')
    have hd2 := ((hasDerivAt_id' x).pow 2).div_const 4
    refine (hd1.sub hd2).congr_deriv ?_
    simp only [Pi.pow_apply]
    have : x ≠ 0 := hx0.ne'
    field_simp; ring
  have hint : IntervalIntegrable (fun x : ℝ => x * Real.log x) volume 1 b := by
    refine ContinuousOn.intervalIntegrable (fun x hx => ?_)
    rw [Set.uIcc_of_le hb] at hx
    exact (Real.hasDerivAt_mul_log (zero_lt_one.trans_le hx.1).ne').continuousAt.continuousWithinAt
  rw [integral_eq_sub_of_hasDerivAt hderiv hint]
  simp only [F, one_pow, Real.log_one, mul_zero, zero_sub]
  ring

/-- Integrability of `(B_{2m+2} - B_{2m+2}({x})) * x ^ (-(2m + 1 : ℤ))` on `(a, ∞)` for `a > 0`,
`m ≥ 1`. -/
private theorem integrableOn_bernoulli_sub_mul_zpow_tail {m : ℕ} (hm : 1 ≤ m) {a : ℝ}
    (ha : 0 < a) :
    IntegrableOn
      (fun x : ℝ => ((bernoulli (2 * m + 2) : ℝ) - bernoulliFun (2 * m + 2) (Int.fract x)) *
        x ^ (-(2 * m + 1 : ℤ))) (Set.Ioi a) := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hrpow : IntegrableOn (fun x : ℝ => x ^ (-(2 * (m : ℝ) + 1))) (Set.Ioi a) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) ha
  have hzpow : IntegrableOn (fun x : ℝ => x ^ (-(2 * m + 1 : ℤ))) (Set.Ioi a) :=
    hrpow.congr_fun (fun x _ => by rw [← Real.rpow_intCast]; push_cast; rfl) measurableSet_Ioi
  exact hzpow.bernoulli_sub_bernoulliFun_fract_smul (2 * m + 2)

/-- Simplification of the boundary Bernoulli sum at order `2 * (m + 1)` for
`mulLogIteratedDeriv`. -/
private theorem mulLog_boundary_sum_eq {m n : ℕ} (hm : 1 ≤ m) :
    ∑ s ∈ Ico 1 (m + 1), ((bernoulli (2 * s) : ℝ) / (2 * s)!) •
        (mulLogIteratedDeriv (2 * s - 1) n - mulLogIteratedDeriv (2 * s - 1) 1) =
      Real.log n / 12 +
        ∑ k ∈ Ico 1 m, (bernoulli (2 * k + 2) : ℝ) / (2 * k * (2 * k + 1) * (2 * k + 2)) -
        ∑ k ∈ Ico 1 m, (bernoulli (2 * k + 2) : ℝ) / (2 * k * (2 * k + 1) * (2 * k + 2)) *
          (n : ℝ) ^ (-(2 * k : ℤ)) := by
  rw [sum_eq_sum_Ico_succ_bot (by omega : 1 < m + 1),
    ← Finset.sum_Ico_add' (f := fun s => ((bernoulli (2 * s) : ℝ) / (2 * s)!) •
      (mulLogIteratedDeriv (2 * s - 1) n - mulLogIteratedDeriv (2 * s - 1) 1)) 1 m 1]
  have h1 : ((bernoulli (2 * 1) : ℝ) / (2 * 1)!) •
      (mulLogIteratedDeriv (2 * 1 - 1) n - mulLogIteratedDeriv (2 * 1 - 1) 1) =
      Real.log n / 12 := by
    simp only [show 2 * 1 = 2 from rfl, show 2 - 1 = 1 from rfl, mulLogIteratedDeriv,
      Real.log_one, zero_add, add_sub_cancel_right, bernoulli_two, Nat.factorial_two, smul_eq_mul]
    norm_num; ring
  have hmid : ∀ k ∈ Ico 1 m, ((bernoulli (2 * (k + 1)) : ℝ) / (2 * (k + 1))!) •
        (mulLogIteratedDeriv (2 * (k + 1) - 1) n - mulLogIteratedDeriv (2 * (k + 1) - 1) 1) =
      (bernoulli (2 * k + 2) : ℝ) / (2 * k * (2 * k + 1) * (2 * k + 2)) -
        (bernoulli (2 * k + 2) : ℝ) / (2 * k * (2 * k + 1) * (2 * k + 2)) *
          (n : ℝ) ^ (-(2 * k : ℤ)) := fun k hk => by
    have hk1 : 1 ≤ k := (mem_Ico.mp hk).1
    have hidx : 2 * (k + 1) - 1 = (2 * k - 1) + 2 := by omega
    have hpow : (-1 : ℝ) ^ (2 * k - 1) = -1 := Odd.neg_one_pow ⟨k - 1, by omega⟩
    have hexp : -((2 * k - 1 : ℕ) + 1 : ℤ) = -(2 * k : ℤ) := by omega
    have hfact : ((2 * (k + 1))! : ℝ) =
        (2 * k : ℝ) * (2 * k + 1) * (2 * k + 2) * (2 * k - 1)! := by
      rw [show 2 * (k + 1) = (2 * k - 1) + 1 + 1 + 1 by omega, Nat.factorial_succ,
        Nat.factorial_succ, Nat.factorial_succ]
      have hk2 : 1 ≤ 2 * k := by omega
      push_cast [hk2]; ring
    have hf0 : ((2 * k - 1)! : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    rw [hidx, show 2 * (k + 1) = 2 * k + 2 by ring]
    simp only [mulLogIteratedDeriv, smul_eq_mul, hpow, hexp, one_zpow]
    rw [show ((2 * k + 2)! : ℝ) = (2 * k : ℝ) * (2 * k + 1) * (2 * k + 2) * (2 * k - 1)! from
      by simpa [show 2 * (k + 1) = 2 * k + 2 by ring] using hfact]
    field_simp; ring
  rw [h1, sum_congr rfl hmid, sum_sub_distrib, add_sub_assoc]

/-- Finite-interval Euler–Maclaurin identity on `[1, n]` at order `2 * (m + 1)` for
`∑_{j=1}^n j log j`. -/
private theorem sum_Icc_mul_log_eq_finite_eulerMaclaurin {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    ∑ j ∈ Icc 1 n, (j : ℝ) * Real.log j =
      (n : ℝ) ^ 2 / 2 * Real.log n - (n : ℝ) ^ 2 / 4 + n / 2 * Real.log n + Real.log n / 12 +
      (1 / 4 + ∑ k ∈ Ico 1 m, (bernoulli (2 * k + 2) : ℝ) / (2 * k * (2 * k + 1) * (2 * k + 2))) -
      ∑ k ∈ Ico 1 m, (bernoulli (2 * k + 2) : ℝ) / (2 * k * (2 * k + 1) * (2 * k + 2)) *
        (n : ℝ) ^ (-(2 * k : ℤ)) +
      1 / ((2 * m + 1 : ℝ) * (2 * m + 2)) *
        ∫ x in (1 : ℝ)..n,
          ((bernoulli (2 * m + 2) : ℝ) - bernoulliFun (2 * m + 2) (Int.fract x)) *
            x ^ (-(2 * m + 1 : ℤ)) := by
  have hEM := sum_Icc_eq_eulerMaclaurin_of_hasDerivAt_two_mul (g := mulLogIteratedDeriv)
    (a := 1) (n := (n : ℤ)) (m := m + 1) (by exact_mod_cast hn) (by omega)
    (fun i _ => continuousOn_mulLogIteratedDeriv i n)
    (fun i _ x hx => hasDerivAt_mulLogIteratedDeriv i (zero_lt_one.trans (by simpa using hx.1)))
    ((continuousOn_mulLogIteratedDeriv (2 * (m + 1)) n).intervalIntegrable_of_Icc
      (by exact_mod_cast hn))
  have hsum : ∑ j ∈ Icc 1 n, (j : ℝ) * Real.log j =
      ∑ j ∈ Icc (1 : ℤ) n, mulLogIteratedDeriv 0 j := by
    have himg : (Icc 1 n).image (Nat.cast : ℕ → ℤ) = Icc (1 : ℤ) n := by
      ext z; simp only [mem_image, mem_Icc]
      exact ⟨fun ⟨k, hk, hkz⟩ => hkz ▸ ⟨by exact_mod_cast hk.1, by exact_mod_cast hk.2⟩,
        fun hz => ⟨z.toNat, ⟨by omega, by omega⟩, by omega⟩⟩
    rw [← himg, Finset.sum_image (f := fun j : ℤ => mulLogIteratedDeriv 0 (j : ℝ))
      Nat.cast_injective.injOn]
    exact sum_congr rfl fun j _ => by simp [mulLogIteratedDeriv]
  have hrem : ∫ x in (1 : ℝ)..n,
        ((bernoulli (2 * (m + 1)) - bernoulliFun (2 * (m + 1)) (Int.fract x)) /
          (2 * (m + 1))!) • mulLogIteratedDeriv (2 * (m + 1)) x =
      1 / ((2 * m + 1 : ℝ) * (2 * m + 2)) * ∫ x in (1 : ℝ)..n,
        ((bernoulli (2 * m + 2) : ℝ) - bernoulliFun (2 * m + 2) (Int.fract x)) *
          x ^ (-(2 * m + 1 : ℤ)) := by
    rw [← intervalIntegral.integral_const_mul]
    refine integral_congr fun x _ => ?_
    have hf0 : ((2 * m)! : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    rw [show 2 * (m + 1) = 2 * m + 2 by ring]
    simp only [mulLogIteratedDeriv, smul_eq_mul, pow_mul, neg_one_sq, one_pow, one_mul]
    rw [show (2 * m + 2)! = (2 * m + 2) * ((2 * m + 1) * (2 * m)!) by
      rw [show 2 * m + 2 = (2 * m + 1) + 1 from rfl, Nat.factorial_succ, Nat.factorial_succ]]
    push_cast; field_simp
  rw [Int.cast_one, Int.cast_natCast] at hEM
  rw [hsum, hEM, mulLog_boundary_sum_eq hm, hrem]
  simp only [mulLogIteratedDeriv, Real.log_one, mul_zero, smul_eq_mul]
  rw [integral_mul_log_one_to (b := (n : ℝ)) (by exact_mod_cast hn)]
  ring

/-- For every `m ≥ 1`, the subtracted Euler–Maclaurin sequence of `∑_{j=1}^n j log j` converges to
the `m`-th Euler–Maclaurin constant expression. -/
private theorem tendsto_sum_mul_log_sub_eq_const {m : ℕ} (hm : 1 ≤ m) :
    Tendsto (fun n : ℕ => ∑ j ∈ Icc 1 n, (j : ℝ) * Real.log j -
        ((n : ℝ) ^ 2 / 2 * Real.log n - (n : ℝ) ^ 2 / 4 + n / 2 * Real.log n +
          Real.log n / 12))
      atTop (𝓝 (1 / 4 +
        ∑ k ∈ Ico 1 m, (bernoulli (2 * k + 2) : ℝ) / (2 * k * (2 * k + 1) * (2 * k + 2)) +
        1 / ((2 * m + 1 : ℝ) * (2 * m + 2)) *
          ∫ x in Set.Ioi (1 : ℝ),
            ((bernoulli (2 * m + 2) : ℝ) - bernoulliFun (2 * m + 2) (Int.fract x)) *
              x ^ (-(2 * m + 1 : ℤ)))) := by
  have hzpow0 : ∀ k ∈ Ico 1 m, Tendsto (fun n : ℕ =>
      (bernoulli (2 * k + 2) : ℝ) / (2 * k * (2 * k + 1) * (2 * k + 2)) *
        (n : ℝ) ^ (-(2 * k : ℤ))) atTop (𝓝 0) := fun k hk => by
    have hk1 : 1 ≤ k := (mem_Ico.mp hk).1
    have ht : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(2 * k : ℤ))) atTop (𝓝 0) := by
      refine ((tendsto_rpow_neg_atTop (by positivity : (0 : ℝ) < 2 * k)).comp
        tendsto_natCast_atTop_atTop).congr' ?_
      filter_upwards [eventually_gt_atTop 0] with n _
      rw [← Real.rpow_intCast]; push_cast; rfl
    simpa using ht.const_mul _
  have hint := integrableOn_bernoulli_sub_mul_zpow_tail hm zero_lt_one
  set C₀ : ℝ := 1 / 4 +
    ∑ k ∈ Ico 1 m, (bernoulli (2 * k + 2) : ℝ) / (2 * k * (2 * k + 1) * (2 * k + 2))
  have hRHS := ((tendsto_const_nhds (x := C₀)).sub (tendsto_finsetSum _ hzpow0)).add
    ((intervalIntegral_tendsto_integral_Ioi 1 hint tendsto_natCast_atTop_atTop).const_mul
      (1 / ((2 * m + 1 : ℝ) * (2 * m + 2))))
  simp only [sum_const_zero, sub_zero] at hRHS
  refine hRHS.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  dsimp only [C₀]
  linarith [sum_Icc_mul_log_eq_finite_eulerMaclaurin hm hn]

/-- **DLMF 2.10.3–2.10.4**: `∑_{j=1}^n j log j - (n^2 / 2 * log n - n^2 / 4 + n / 2 * log n +
log n / 12)` converges as `n → ∞` to `1 / 12 - Re ζ'(-1)` (the logarithm of the Glaisher–Kinkelin
constant). -/
theorem tendsto_sum_mul_log_sub :
    Tendsto (fun n : ℕ => ∑ j ∈ Icc 1 n, (j : ℝ) * Real.log j -
        ((n : ℝ) ^ 2 / 2 * Real.log n - (n : ℝ) ^ 2 / 4 + n / 2 * Real.log n +
          Real.log n / 12))
      atTop (𝓝 (1 / 12 - (deriv riemannZeta (-1)).re)) := by
  have h := tendsto_sum_mul_log_sub_eq_const (m := 1) le_rfl
  have hconst : 1 / 4 +
      ∑ k ∈ Ico 1 1, (bernoulli (2 * k + 2) : ℝ) / (2 * k * (2 * k + 1) * (2 * k + 2)) +
      1 / ((2 * (1 : ℕ) + 1 : ℝ) * (2 * (1 : ℕ) + 2)) *
        ∫ x in Set.Ioi (1 : ℝ),
          ((bernoulli (2 * 1 + 2) : ℝ) - bernoulliFun (2 * 1 + 2) (Int.fract x)) *
            x ^ (-(2 * (1 : ℕ) + 1 : ℤ)) =
      1 / 12 - (deriv riemannZeta (-1)).re := by
    simp only [Finset.Ico_self, sum_empty, add_zero, Nat.cast_one, show 2 * 1 + 2 = 4 from rfl]
    linarith [deriv_riemannZeta_neg_one_re]
  rwa [hconst] at h

/-- **DLMF 2.10.3 & 2.10.6**: limit of `∑_{j=1}^n j log j` with the constant expressed in terms of
Euler's constant `γ`, `log (2π)`, and `ζ'(2)`. -/
theorem tendsto_sum_mul_log_sub' :
    Tendsto (fun n : ℕ => ∑ j ∈ Icc 1 n, (j : ℝ) * Real.log j -
        ((n : ℝ) ^ 2 / 2 * Real.log n - (n : ℝ) ^ 2 / 4 + n / 2 * Real.log n +
          Real.log n / 12))
      atTop (𝓝 ((Real.eulerMascheroniConstant + Real.log (2 * π)) / 12 -
        (deriv riemannZeta 2).re / (2 * π ^ 2))) := by
  rw [← one_div_twelve_sub_deriv_riemannZeta_neg_one_re]
  exact tendsto_sum_mul_log_sub

/-- Order-`2(m + 1)` Euler–Maclaurin representation of `1 / 12 - Re ζ'(-1)`. -/
theorem one_div_twelve_sub_deriv_riemannZeta_neg_one_re_eq_eulerMaclaurin {m : ℕ} (hm : 1 ≤ m) :
    1 / 12 - (deriv riemannZeta (-1)).re = 1 / 4 +
      ∑ k ∈ Ico 1 m, (bernoulli (2 * k + 2) : ℝ) / (2 * k * (2 * k + 1) * (2 * k + 2)) +
      1 / ((2 * m + 1 : ℝ) * (2 * m + 2)) *
        ∫ x in Set.Ioi (1 : ℝ),
          ((bernoulli (2 * m + 2) : ℝ) - bernoulliFun (2 * m + 2) (Int.fract x)) *
            x ^ (-(2 * m + 1 : ℤ)) :=
  tendsto_nhds_unique tendsto_sum_mul_log_sub (tendsto_sum_mul_log_sub_eq_const hm)

/-- **Euler–Maclaurin expansion of `∑_{j=1}^n j log j`** (DLMF 2.10.4–2.10.5, integral-remainder
form). -/
theorem sum_Icc_mul_log_eq_eulerMaclaurin {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    ∑ j ∈ Icc 1 n, (j : ℝ) * Real.log j =
      (n : ℝ) ^ 2 / 2 * Real.log n - (n : ℝ) ^ 2 / 4 + n / 2 * Real.log n + Real.log n / 12 +
      (1 / 12 - (deriv riemannZeta (-1)).re) -
      ∑ k ∈ Ico 1 m, (bernoulli (2 * k + 2) : ℝ) / (2 * k * (2 * k + 1) * (2 * k + 2)) *
        (n : ℝ) ^ (-(2 * k : ℤ)) -
      1 / ((2 * m + 1 : ℝ) * (2 * m + 2)) *
        ∫ x in Set.Ioi (n : ℝ),
          ((bernoulli (2 * m + 2) : ℝ) - bernoulliFun (2 * m + 2) (Int.fract x)) *
            x ^ (-(2 * m + 1 : ℤ)) := by
  have hsplit := intervalIntegral.integral_Ioi_sub_Ioi
    (integrableOn_bernoulli_sub_mul_zpow_tail hm zero_lt_one) (b := (n : ℝ)) (by exact_mod_cast hn)
  have hfin := sum_Icc_mul_log_eq_finite_eulerMaclaurin hm hn
  rw [← hsplit, mul_sub] at hfin
  linarith [hfin, one_div_twelve_sub_deriv_riemannZeta_neg_one_re_eq_eulerMaclaurin hm]

/-- **Euler–Maclaurin expansion of `∑_{j=1}^{n-1} j log j`** (DLMF 2.10.4–2.10.5,
integral-remainder form). -/
theorem sum_Ico_mul_log_eq_eulerMaclaurin {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    ∑ j ∈ Ico 1 n, (j : ℝ) * Real.log j =
      (n : ℝ) ^ 2 / 2 * Real.log n - (n : ℝ) ^ 2 / 4 - n / 2 * Real.log n + Real.log n / 12 +
      (1 / 12 - (deriv riemannZeta (-1)).re) -
      ∑ k ∈ Ico 1 m, (bernoulli (2 * k + 2) : ℝ) / (2 * k * (2 * k + 1) * (2 * k + 2)) *
        (n : ℝ) ^ (-(2 * k : ℤ)) -
      1 / ((2 * m + 1 : ℝ) * (2 * m + 2)) *
        ∫ x in Set.Ioi (n : ℝ),
          ((bernoulli (2 * m + 2) : ℝ) - bernoulliFun (2 * m + 2) (Int.fract x)) *
            x ^ (-(2 * m + 1 : ℤ)) := by
  have hsum : ∑ j ∈ Ico 1 n, (j : ℝ) * Real.log j + (n : ℝ) * Real.log n =
      ∑ j ∈ Icc 1 n, (j : ℝ) * Real.log j := by
    rw [← sum_Ico_succ_top hn, Finset.Ico_add_one_right_eq_Icc]
  linarith [sum_Icc_mul_log_eq_eulerMaclaurin hm hn, hsum]

/-- Strict sign of the scaled tail integral in `sum_Icc_mul_log_eq_eulerMaclaurin`. -/
private theorem neg_one_pow_succ_mul_mulLog_rem_pos {k n : ℕ} (hk : 1 ≤ k) (hn : 1 ≤ n) :
    0 < (-1 : ℝ) ^ (k + 1) * (-1 / ((2 * k + 1 : ℝ) * (2 * k + 2)) *
      ∫ x in Set.Ioi (n : ℝ),
        ((bernoulli (2 * k + 2) : ℝ) - bernoulliFun (2 * k + 2) (Int.fract x)) *
          x ^ (-(2 * k + 1 : ℤ))) := by
  have hn_pos : (0 : ℝ) < n := by positivity
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hw_int : IntegrableOn (fun x : ℝ => x ^ (-(2 * k + 1 : ℤ))) (Set.Ioi (n : ℝ)) :=
    (integrableOn_Ioi_rpow_of_lt (a := -(2 * (k : ℝ) + 1)) (by linarith) hn_pos).congr_fun
      (fun x _ => by rw [← Real.rpow_intCast]; push_cast; rfl) measurableSet_Ioi
  have hw_cont : ContinuousOn (fun x : ℝ => x ^ (-(2 * k + 1 : ℤ))) (Set.Ioi (n : ℝ)) :=
    fun x hx => ((hasDerivAt_zpow _ x (Or.inl (hn_pos.trans hx).ne')).continuousAt
      ).continuousWithinAt
  have hI := neg_one_pow_succ_mul_setIntegral_bernoulli_sub_bernoulliFun_fract_mul_pos
    (k := k + 1) (by omega) hw_int hw_cont (fun x hx => zpow_pos (hn_pos.trans hx) _)
  have heq : (-1 : ℝ) ^ (k + 1) * (-1 / ((2 * k + 1 : ℝ) * (2 * k + 2)) *
      ∫ x in Set.Ioi (n : ℝ),
        ((bernoulli (2 * k + 2) : ℝ) - bernoulliFun (2 * k + 2) (Int.fract x)) *
          x ^ (-(2 * k + 1 : ℤ))) =
      1 / ((2 * k + 1 : ℝ) * (2 * k + 2)) *
        ((-1 : ℝ) ^ ((k + 1) + 1) * ∫ x in Set.Ioi (n : ℝ),
          ((bernoulli (2 * (k + 1)) : ℝ) - bernoulliFun (2 * (k + 1)) (Int.fract x)) *
            x ^ (-(2 * k + 1 : ℤ))) := by
    rw [show 2 * (k + 1) = 2 * k + 2 by ring, pow_succ]; ring
  rw [heq]
  exact mul_pos (by positivity) hI

/-- **DLMF 2.10.5 remainder theorem for `∑_{j=1}^n j log j`**: for `m ≥ 1` and `n ≥ 1`, there
exists `θ ∈ (0, 1)` such that the error after `m - 1` Bernoulli terms equals `θ` times the first
neglected term `-(B_{2m+2} / (2m(2m+1)(2m+2))) n ^ (-2m)`. -/
theorem exists_Ioo_sum_Icc_mul_log_sub_eulerMaclaurin {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    ∃ θ ∈ Set.Ioo (0 : ℝ) 1,
      ∑ j ∈ Icc 1 n, (j : ℝ) * Real.log j -
        ((n : ℝ) ^ 2 / 2 * Real.log n - (n : ℝ) ^ 2 / 4 + n / 2 * Real.log n + Real.log n / 12 +
          (1 / 12 - (deriv riemannZeta (-1)).re) -
          ∑ k ∈ Ico 1 m, (bernoulli (2 * k + 2) : ℝ) / (2 * k * (2 * k + 1) * (2 * k + 2)) *
            (n : ℝ) ^ (-(2 * k : ℤ))) =
        θ * (-(bernoulli (2 * m + 2) : ℝ) / (2 * m * (2 * m + 1) * (2 * m + 2)) *
          (n : ℝ) ^ (-(2 * m : ℤ))) := by
  set rem : ℕ → ℝ := fun k => -1 / ((2 * k + 1 : ℝ) * (2 * k + 2)) *
    ∫ x in Set.Ioi (n : ℝ),
      ((bernoulli (2 * k + 2) : ℝ) - bernoulliFun (2 * k + 2) (Int.fract x)) *
        x ^ (-(2 * k + 1 : ℤ))
  set term : ℝ := -(bernoulli (2 * m + 2) : ℝ) / (2 * m * (2 * m + 1) * (2 * m + 2)) *
    (n : ℝ) ^ (-(2 * m : ℤ))
  have hm_eq := sum_Icc_mul_log_eq_eulerMaclaurin hm hn
  have hm1_eq := sum_Icc_mul_log_eq_eulerMaclaurin (m := m + 1) (by omega) hn
  rw [sum_Ico_succ_top hm] at hm1_eq
  have hrem : ∀ k : ℕ, rem k = -(1 / ((2 * k + 1 : ℝ) * (2 * k + 2)) *
      ∫ x in Set.Ioi (n : ℝ),
        ((bernoulli (2 * k + 2) : ℝ) - bernoulliFun (2 * k + 2) (Int.fract x)) *
          x ^ (-(2 * k + 1 : ℤ))) := fun k => by dsimp only [rem]; ring
  have hstep : rem m = term + rem (m + 1) := by
    have hterm : term = -((bernoulli (2 * m + 2) : ℝ) / (2 * m * (2 * m + 1) * (2 * m + 2)) *
        (n : ℝ) ^ (-(2 * m : ℤ))) := by dsimp only [term]; ring
    rw [hrem m, hrem (m + 1), hterm]; linarith [hm_eq, hm1_eq]
  have hr_pos : 0 < (-1 : ℝ) ^ (m + 1) * rem m := neg_one_pow_succ_mul_mulLog_rem_pos hm hn
  have hr1_neg : (-1 : ℝ) ^ (m + 1) * rem (m + 1) < 0 := by
    have h : 0 < (-1 : ℝ) ^ ((m + 1) + 1) * rem (m + 1) :=
      neg_one_pow_succ_mul_mulLog_rem_pos (k := m + 1) (by omega) hn
    rw [pow_succ ((-1 : ℝ)) (m + 1), mul_assoc, neg_one_mul, mul_neg, neg_pos] at h; exact h
  have ht_pos : 0 < (-1 : ℝ) ^ (m + 1) * term := by
    linarith [congrArg ((-1 : ℝ) ^ (m + 1) * ·) hstep]
  have hrt_lt : (-1 : ℝ) ^ (m + 1) * rem m < (-1 : ℝ) ^ (m + 1) * term := by
    linarith [congrArg ((-1 : ℝ) ^ (m + 1) * ·) hstep]
  have hu_ne : (-1 : ℝ) ^ (m + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
  have ht_ne : term ≠ 0 := fun h => by simp [h] at ht_pos
  refine ⟨rem m / term, ⟨?_, ?_⟩, ?_⟩
  · rw [← mul_div_mul_left (rem m) term hu_ne]; exact div_pos hr_pos ht_pos
  · rw [← mul_div_mul_left (rem m) term hu_ne, div_lt_one ht_pos]; exact hrt_lt
  · have hsub : ∑ j ∈ Icc 1 n, (j : ℝ) * Real.log j -
        ((n : ℝ) ^ 2 / 2 * Real.log n - (n : ℝ) ^ 2 / 4 + n / 2 * Real.log n + Real.log n / 12 +
          (1 / 12 - (deriv riemannZeta (-1)).re) -
          ∑ k ∈ Ico 1 m, (bernoulli (2 * k + 2) : ℝ) / (2 * k * (2 * k + 1) * (2 * k + 2)) *
            (n : ℝ) ^ (-(2 * k : ℤ))) = rem m := by
      rw [hrem m]; linarith [hm_eq]
    rw [hsub, div_mul_cancel₀ _ ht_ne]

/-- **DLMF 2.10.5** for `∑_{j=1}^{n-1} j log j`: for `m ≥ 1` and `n ≥ 1`, there exists `θ ∈ (0, 1)`
such that the remainder equals `θ` times `-(B_{2m+2} / (2m(2m+1)(2m+2))) n ^ (-2m)`. -/
theorem exists_Ioo_sum_Ico_mul_log_sub_eulerMaclaurin {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    ∃ θ ∈ Set.Ioo (0 : ℝ) 1,
      ∑ j ∈ Ico 1 n, (j : ℝ) * Real.log j -
        ((n : ℝ) ^ 2 / 2 * Real.log n - (n : ℝ) ^ 2 / 4 - n / 2 * Real.log n + Real.log n / 12 +
          (1 / 12 - (deriv riemannZeta (-1)).re) -
          ∑ k ∈ Ico 1 m, (bernoulli (2 * k + 2) : ℝ) / (2 * k * (2 * k + 1) * (2 * k + 2)) *
            (n : ℝ) ^ (-(2 * k : ℤ))) =
        θ * (-(bernoulli (2 * m + 2) : ℝ) / (2 * m * (2 * m + 1) * (2 * m + 2)) *
          (n : ℝ) ^ (-(2 * m : ℤ))) := by
  obtain ⟨θ, hθ, heq⟩ := exists_Ioo_sum_Icc_mul_log_sub_eulerMaclaurin hm hn
  refine ⟨θ, hθ, ?_⟩
  linarith [sum_Icc_mul_log_eq_eulerMaclaurin hm hn, sum_Ico_mul_log_eq_eulerMaclaurin hm hn, heq]

/-- Strict error bound for the Euler–Maclaurin expansion of `∑_{j=1}^n j log j` (DLMF 2.10.5). -/
theorem abs_sum_Icc_mul_log_sub_eulerMaclaurin_lt {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    |∑ j ∈ Icc 1 n, (j : ℝ) * Real.log j -
      ((n : ℝ) ^ 2 / 2 * Real.log n - (n : ℝ) ^ 2 / 4 + n / 2 * Real.log n + Real.log n / 12 +
        (1 / 12 - (deriv riemannZeta (-1)).re) -
        ∑ k ∈ Ico 1 m, (bernoulli (2 * k + 2) : ℝ) / (2 * k * (2 * k + 1) * (2 * k + 2)) *
          (n : ℝ) ^ (-(2 * k : ℤ)))| <
      |(bernoulli (2 * m + 2) : ℝ)| / (2 * m * (2 * m + 1) * (2 * m + 2)) *
        (n : ℝ) ^ (-(2 * m : ℤ)) := by
  obtain ⟨θ, hθ, heq⟩ := exists_Ioo_sum_Icc_mul_log_sub_eulerMaclaurin hm hn
  have hB : 0 < |(bernoulli (2 * m + 2) : ℝ)| := by
    rw [show 2 * m + 2 = 2 * (m + 1) by ring]
    exact abs_pos.mpr (Rat.cast_ne_zero.mpr (bernoulli_two_mul_ne_zero (by omega)))
  have hden : (0 : ℝ) < 2 * m * (2 * m + 1) * (2 * m + 2) := by positivity
  have hn_pos : (0 : ℝ) < n := by positivity
  have hterm_pos : 0 < |(bernoulli (2 * m + 2) : ℝ)| / (2 * m * (2 * m + 1) * (2 * m + 2)) *
      (n : ℝ) ^ (-(2 * m : ℤ)) :=
    mul_pos (div_pos hB hden) (zpow_pos hn_pos _)
  have hterm_abs : |-(bernoulli (2 * m + 2) : ℝ) / (2 * m * (2 * m + 1) * (2 * m + 2)) *
      (n : ℝ) ^ (-(2 * m : ℤ))| =
      |(bernoulli (2 * m + 2) : ℝ)| / (2 * m * (2 * m + 1) * (2 * m + 2)) *
        (n : ℝ) ^ (-(2 * m : ℤ)) := by
    rw [abs_mul, abs_div, abs_neg, abs_of_pos hden, abs_of_pos (zpow_pos hn_pos _)]
  rw [heq, abs_mul, hterm_abs, abs_of_pos hθ.1]
  exact mul_lt_of_lt_one_left hterm_pos hθ.2

/-- Asymptotic bound `O(n ^ (-2m))` for the Euler–Maclaurin expansion of `∑_{j=1}^n j log j`
(DLMF 2.10.3 & 2.10.5). -/
theorem sum_Icc_mul_log_sub_eulerMaclaurin_isBigO {m : ℕ} (hm : 1 ≤ m) :
    (fun n : ℕ => ∑ j ∈ Icc 1 n, (j : ℝ) * Real.log j -
      ((n : ℝ) ^ 2 / 2 * Real.log n - (n : ℝ) ^ 2 / 4 + n / 2 * Real.log n + Real.log n / 12 +
        (1 / 12 - (deriv riemannZeta (-1)).re) -
        ∑ k ∈ Ico 1 m, (bernoulli (2 * k + 2) : ℝ) / (2 * k * (2 * k + 1) * (2 * k + 2)) *
          (n : ℝ) ^ (-(2 * k : ℤ)))) =O[atTop]
      fun n : ℕ => (n : ℝ) ^ (-(2 * m : ℤ)) := by
  refine Asymptotics.IsBigO.of_bound
    (|(bernoulli (2 * m + 2) : ℝ)| / (2 * m * (2 * m + 1) * (2 * m + 2))) ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  simp only [Real.norm_eq_abs, abs_of_pos (zpow_pos (by positivity : (0 : ℝ) < n) _)]
  exact (abs_sum_Icc_mul_log_sub_eulerMaclaurin_lt hm hn).le

/-- Asymptotic bound `O(n ^ (-2m))` for the Euler–Maclaurin expansion of `∑_{j=1}^{n-1} j log j`
(DLMF 2.10.3 & 2.10.5). -/
theorem sum_Ico_mul_log_sub_eulerMaclaurin_isBigO {m : ℕ} (hm : 1 ≤ m) :
    (fun n : ℕ => ∑ j ∈ Ico 1 n, (j : ℝ) * Real.log j -
      ((n : ℝ) ^ 2 / 2 * Real.log n - (n : ℝ) ^ 2 / 4 - n / 2 * Real.log n + Real.log n / 12 +
        (1 / 12 - (deriv riemannZeta (-1)).re) -
        ∑ k ∈ Ico 1 m, (bernoulli (2 * k + 2) : ℝ) / (2 * k * (2 * k + 1) * (2 * k + 2)) *
          (n : ℝ) ^ (-(2 * k : ℤ)))) =O[atTop]
      fun n : ℕ => (n : ℝ) ^ (-(2 * m : ℤ)) := by
  refine (sum_Icc_mul_log_sub_eulerMaclaurin_isBigO hm).congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_ge_atTop 1] with n hn
  linarith [sum_Icc_mul_log_eq_eulerMaclaurin hm hn, sum_Ico_mul_log_eq_eulerMaclaurin hm hn]

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.NumberTheory.ZetaValues
public import Mathlib.RingTheory.Binomial
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import TauCeti.Analysis.Asymptotics.Sum.EulerMaclaurin
import TauCeti.NumberTheory.LSeries.RiemannZeta.EulerMaclaurin
import TauCeti.NumberTheory.ZetaValues

/-!
# Euler–Maclaurin expansion of sums of real powers

Applying the even-order Euler–Maclaurin summation formula on `[1, n]` to `x ↦ x ^ α` (`α ≠ -1`) and
matching the `n`-independent terms against the analytic continuation
`TauCeti.riemannZeta_neg_ofReal_re_eq_eulerMaclaurin` of `ζ(-α)` yields the exact Euler–Maclaurin
identity for `∑_{j=1}^{n-1} j ^ α` (DLMF 2.10.7), written with generalized binomial coefficients
`Ring.choose (α + 1) s`.

When `(α + 1) / 2 ≤ m` (`m ≥ 1`, `n ≥ 1`), comparing consecutive orders shows that the remainder
after `2m` terms (`s = 0, …, 2m - 1`) equals `θ` times the `s = 2m` term for some `θ ∈ [0, 1]`
(with `θ = 0` when `α ∈ {0, …, 2m - 2}` and `θ = 1` at the boundary `α = 2m - 1`). Choosing `m`
large enough then gives the `O(n ^ (α + 1 - N))` asymptotic expansion to every truncation order
`N : ℕ`.

## Main results

* `TauCeti.sum_Ico_rpow_eq_eulerMaclaurin`: exact order-`2m` Euler–Maclaurin formula for
  `∑_{j=1}^{n-1} j ^ α` when `α ≠ -1`, `1 ≤ m`, `α < 2m - 1`, `1 ≤ n`.
* `TauCeti.exists_Icc_sum_Ico_rpow_sub_eulerMaclaurin` and
  `TauCeti.abs_sum_Ico_rpow_sub_eulerMaclaurin_le`: the DLMF 2.10.7 remainder representation with
  `θ ∈ [0, 1]` and magnitude bound when `α ≠ -1`, `1 ≤ m`, `α ≤ 2m - 1`, `1 ≤ n`.
* `TauCeti.sum_Ico_rpow_sub_eulerMaclaurin_isBigO`: for every `α ≠ -1` and `N : ℕ`, the error after
  `N` terms (`s < N`) is `O(n ^ (α + 1 - N))` as `n → ∞`.

## References

* NIST *Digital Library of Mathematical Functions*, §2.10(i), formula 2.10.7.
* F. W. J. Olver, *Asymptotics and Special Functions*, Chapter 8, §2.2.
-/

public section

open Filter Finset intervalIntegral MeasureTheory
open scoped Nat Real Topology

namespace TauCeti

/-- Derivative of `x ↦ (descPochhammer ℝ i).eval α * x ^ (α - i)` on `(0, ∞)`. -/
private theorem hasDerivAt_descPochhammer_mul_rpow (α : ℝ) (i : ℕ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => (descPochhammer ℝ i).eval α * y ^ (α - i))
      ((descPochhammer ℝ (i + 1)).eval α * x ^ (α - (i + 1 : ℕ))) x := by
  have hd := (Real.hasDerivAt_rpow_const (p := α - i) (Or.inl hx.ne')).const_mul
    ((descPochhammer ℝ i).eval α)
  refine hd.congr_deriv ?_
  rw [descPochhammer_succ_right, Polynomial.eval_mul, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_natCast, Nat.cast_add, Nat.cast_one]
  ring_nf

/-- Evaluation of `descPochhammer ℤ k` via `smeval` on `ℝ` agrees with `Polynomial.eval`. -/
private theorem descPochhammer_smeval_real (a : ℝ) (k : ℕ) :
    (descPochhammer ℤ k).smeval a = (descPochhammer ℝ k).eval a := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp [descPochhammer_succ_right, Polynomial.smeval_mul, Polynomial.smeval_sub,
      Polynomial.smeval_X, Polynomial.smeval_natCast, ih]

/-- Identity relating `Ring.choose (α + 1) (k + 1)` to `(descPochhammer ℝ k).eval α`. -/
private theorem ringChoose_add_one_succ (α : ℝ) (k : ℕ) :
    Ring.choose (α + 1) (k + 1) = (α + 1) / (k + 1)! * (descPochhammer ℝ k).eval α := by
  rw [Ring.choose_eq_smul, descPochhammer_smeval_real, smul_eq_mul,
    descPochhammer_eval_eq_prod_range, prod_range_succ', Nat.cast_zero, sub_zero,
    descPochhammer_eval_eq_prod_range]
  have hprod : ∏ i ∈ range k, (α + 1 - ((i + 1 : ℕ) : ℝ)) = ∏ i ∈ range k, (α - i) :=
    prod_congr rfl fun i _ => by push_cast; ring
  rw [hprod]
  ring

/-- Rewrite the Euler–Maclaurin boundary polynomial in `n` as the DLMF 2.10.7 sum over
`range (2 * m)` with `Ring.choose (α + 1) s`. -/
private theorem eulerMaclaurin_rpow_poly_eq_sum_range {α : ℝ} (hα : α ≠ -1) {m n : ℕ}
    (hm : 1 ≤ m) (hn : 1 ≤ n) :
    (n : ℝ) ^ (α + 1) / (α + 1) - (n : ℝ) ^ α / 2 +
      ∑ r ∈ Ico 1 m, (bernoulli (2 * r) : ℝ) / (2 * r)! *
        (descPochhammer ℝ (2 * r - 1)).eval α * (n : ℝ) ^ (α - (2 * r - 1 : ℕ)) =
      (n : ℝ) ^ (α + 1) / (α + 1) *
        ∑ s ∈ range (2 * m),
          Ring.choose (α + 1) s * (bernoulli s : ℝ) * (n : ℝ) ^ (-(s : ℤ)) := by
  have hn_pos : (0 : ℝ) < n := by positivity
  have hα1 : α + 1 ≠ 0 := fun h => hα (by linarith)
  induction m, hm using Nat.le_induction with
  | base =>
    simp only [Finset.Ico_self, sum_empty, add_zero, show 2 * 1 = 2 from rfl, sum_range_succ,
      sum_range_zero, zero_add, Ring.choose_zero_right, bernoulli_zero, Rat.cast_one, Nat.cast_zero,
      neg_zero, zpow_zero, mul_one, Ring.choose_one_right, bernoulli_one, Rat.cast_div,
      Rat.cast_neg, Rat.cast_ofNat, Nat.cast_one, zpow_neg_one]
    have hpow : (n : ℝ) ^ (α + 1) * (n : ℝ)⁻¹ = (n : ℝ) ^ α := by
      rw [← Real.rpow_neg_one, ← Real.rpow_add hn_pos]; ring_nf
    rw [← hpow]
    field_simp
    ring
  | succ m hm ih =>
    have hodd : bernoulli (2 * m + 1) = 0 := bernoulli_eq_zero_of_odd ⟨m, rfl⟩ (by omega)
    have hpow : (n : ℝ) ^ (α + 1) * (n : ℝ) ^ (-((2 * m : ℕ) : ℤ)) =
        (n : ℝ) ^ (α - (2 * m - 1 : ℕ)) := by
      rw [← Real.rpow_intCast, ← Real.rpow_add hn_pos]
      congr 1
      have hm1 : 1 ≤ 2 * m := by omega
      push_cast [hm1]; ring
    have hterm : (bernoulli (2 * m) : ℝ) / (2 * m)! *
          (descPochhammer ℝ (2 * m - 1)).eval α * (n : ℝ) ^ (α - (2 * m - 1 : ℕ)) =
        (n : ℝ) ^ (α + 1) / (α + 1) *
          (Ring.choose (α + 1) (2 * m) * (bernoulli (2 * m) : ℝ) *
            (n : ℝ) ^ (-((2 * m : ℕ) : ℤ))) := by
      have h2m : 2 * m = (2 * m - 1) + 1 := by omega
      conv_rhs => rw [h2m, ringChoose_add_one_succ, ← h2m]
      rw [← hpow]
      field_simp
    rw [sum_Ico_succ_top hm, ← add_assoc, ih, show 2 * (m + 1) = 2 * m + 1 + 1 by ring,
      sum_range_succ, sum_range_succ, hodd, Rat.cast_zero, mul_zero, zero_mul, add_zero,
      mul_add, hterm]

/-- **Euler–Maclaurin formula for sums of real powers** (DLMF 2.10.7, integral-remainder form).
For `α ≠ -1`, `m ≥ 1` with `α < 2 * m - 1`, and `n ≥ 1`,
`∑_{j=1}^{n-1} j ^ α = Re ζ(-α) + n^(α+1)/(α+1) ∑_{s=0}^{2m-1} C(α+1, s) B_s n^(-s)
  - (α)_{2m} ∫_n^∞ (B_{2m} - B_{2m}({x}))/(2m)! x^(α - 2m) dx`. -/
theorem sum_Ico_rpow_eq_eulerMaclaurin {α : ℝ} (hα : α ≠ -1) {m n : ℕ} (hm : 1 ≤ m)
    (hαm : α < 2 * (m : ℝ) - 1) (hn : 1 ≤ n) :
    ∑ j ∈ Ico 1 n, (j : ℝ) ^ α = (riemannZeta (-α : ℂ)).re +
      (n : ℝ) ^ (α + 1) / (α + 1) *
        ∑ s ∈ range (2 * m),
          Ring.choose (α + 1) s * (bernoulli s : ℝ) * (n : ℝ) ^ (-(s : ℤ)) -
      (descPochhammer ℝ (2 * m)).eval α *
        ∫ x in Set.Ioi (n : ℝ),
          ((bernoulli (2 * m) : ℝ) - bernoulliFun (2 * m) (Int.fract x)) / (2 * m)! *
            x ^ (α - 2 * m) := by
  set g : ℕ → ℝ → ℝ := fun i x => (descPochhammer ℝ i).eval α * x ^ (α - i)
  have h0not : (0 : ℝ) ∉ Set.uIcc (1 : ℝ) n := by
    rw [Set.uIcc_of_le (by exact_mod_cast hn), Set.mem_Icc]; intro h; linarith [h.1]
  have hcont : ∀ i, ContinuousOn (g i) (Set.Icc ((1 : ℤ) : ℝ) ((n : ℤ) : ℝ)) := fun i x hx =>
    (continuousAt_const.mul (Real.continuousAt_rpow_const x _
      (Or.inl (zero_lt_one.trans_le (by simpa using hx.1)).ne'))).continuousWithinAt
  have hEM := sum_Icc_eq_eulerMaclaurin_of_hasDerivAt_two_mul (g := g)
    (a := 1) (n := (n : ℤ)) (by exact_mod_cast hn) hm (fun i _ => hcont i)
    (fun i _ x hx => hasDerivAt_descPochhammer_mul_rpow α i
      (zero_lt_one.trans (by simpa using hx.1)))
    ((hcont (2 * m)).intervalIntegrable_of_Icc (by exact_mod_cast hn))
  have hsum : ∑ j ∈ Ico 1 n, (j : ℝ) ^ α + (n : ℝ) ^ α = ∑ j ∈ Icc (1 : ℤ) n, g 0 j := by
    rw [← sum_Ico_succ_top hn, Finset.Ico_add_one_right_eq_Icc]
    have himg : (Icc 1 n).image (Nat.cast : ℕ → ℤ) = Icc (1 : ℤ) n := by
      ext z; simp only [mem_image, mem_Icc]
      exact ⟨fun ⟨k, hk, hkz⟩ => hkz ▸ ⟨by exact_mod_cast hk.1, by exact_mod_cast hk.2⟩,
        fun hz => ⟨z.toNat, ⟨by omega, by omega⟩, by omega⟩⟩
    rw [← himg, Finset.sum_image (f := fun j : ℤ => g 0 (j : ℝ)) Nat.cast_injective.injOn]
    exact sum_congr rfl fun j _ => by simp [g]
  have hint0 : ∫ x in (1 : ℝ)..n, g 0 x = (n : ℝ) ^ (α + 1) / (α + 1) + -1 / (α + 1) := by
    rw [show (fun x : ℝ => g 0 x) = fun x : ℝ => x ^ α by ext x; simp [g],
      integral_rpow (Or.inr ⟨hα, h0not⟩), Real.one_rpow]; ring
  have hrem_fin : ∫ x in (1 : ℝ)..n,
        ((bernoulli (2 * m) - bernoulliFun (2 * m) (Int.fract x)) / (2 * m)!) • g (2 * m) x =
      (descPochhammer ℝ (2 * m)).eval α * ∫ x in (1 : ℝ)..n,
        ((bernoulli (2 * m) : ℝ) - bernoulliFun (2 * m) (Int.fract x)) / (2 * m)! *
          x ^ (α - 2 * m) := by
    rw [← intervalIntegral.integral_const_mul]
    exact integral_congr fun x _ => by simp only [g, smul_eq_mul]; push_cast; ring
  have hint_tail : IntegrableOn
      (fun x : ℝ => ((bernoulli (2 * m) : ℝ) - bernoulliFun (2 * m) (Int.fract x)) / (2 * m)! *
        x ^ (α - 2 * m)) (Set.Ioi 1) :=
    IntegrableOn.congr_fun (((integrableOn_Ioi_rpow_of_lt (a := α - 2 * (m : ℝ)) (by linarith)
      zero_lt_one).bernoulli_sub_bernoulliFun_fract_smul (2 * m)).smul ((2 * m)! : ℝ)⁻¹)
      (fun x _ => by simp only [Pi.smul_apply, smul_eq_mul]; ring) measurableSet_Ioi
  have hsplit :=
    intervalIntegral.integral_Ioi_sub_Ioi hint_tail (b := (n : ℝ)) (by exact_mod_cast hn)
  rw [Int.cast_one, Int.cast_natCast, ← hsum, hint0, hrem_fin, ← hsplit] at hEM
  simp only [g, descPochhammer_zero, Polynomial.eval_one, one_mul, mul_one, Nat.cast_zero, sub_zero,
    Real.one_rpow, smul_eq_mul, mul_sub, sum_sub_distrib, ← mul_assoc] at hEM
  linarith [hEM, riemannZeta_neg_ofReal_re_eq_eulerMaclaurin hα hm hαm,
    eulerMaclaurin_rpow_poly_eq_sum_range hα hm hn]

/-- Strict sign of the scaled tail integral in `sum_Ico_rpow_eq_eulerMaclaurin`. -/
private theorem neg_one_pow_succ_mul_setIntegral_rpow_tail_pos {α : ℝ} {k n : ℕ} (hk : 1 ≤ k)
    (hαk : α < 2 * (k : ℝ) - 1) (hn : 1 ≤ n) :
    0 < (-1 : ℝ) ^ (k + 1) * ∫ x in Set.Ioi (n : ℝ),
      ((bernoulli (2 * k) : ℝ) - bernoulliFun (2 * k) (Int.fract x)) / (2 * k)! *
        x ^ (α - 2 * k) := by
  have hn_pos : (0 : ℝ) < n := by positivity
  have hw_int : IntegrableOn (fun x : ℝ => x ^ (α - 2 * k) / (2 * k)!) (Set.Ioi (n : ℝ)) :=
    (integrableOn_Ioi_rpow_of_lt (a := α - 2 * (k : ℝ)) (by linarith) hn_pos).div_const _
  have hw_cont : ContinuousOn (fun x : ℝ => x ^ (α - 2 * k) / (2 * k)!) (Set.Ioi (n : ℝ)) :=
    fun x hx => ((Real.continuousAt_rpow_const x _
      (Or.inl (hn_pos.trans hx).ne')).div_const _).continuousWithinAt
  refine (neg_one_pow_succ_mul_setIntegral_bernoulli_sub_bernoulliFun_fract_mul_pos
    (k := k) (by omega) hw_int hw_cont fun x hx =>
      div_pos (Real.rpow_pos_of_pos (hn_pos.trans hx) _) (by positivity)).trans_eq ?_
  congr 1
  exact setIntegral_congr_fun measurableSet_Ioi fun x _ => by ring

/-- Factorizations of `-(descPochhammer ℝ (2 * m)).eval α` and
`-(descPochhammer ℝ (2 * (m + 1))).eval α` relative to `(descPochhammer ℝ (2 * m - 1)).eval α`. -/
private theorem neg_descPochhammer_two_mul_eval (α : ℝ) {m : ℕ} (hm : 1 ≤ m) :
    -(descPochhammer ℝ (2 * m)).eval α =
        (descPochhammer ℝ (2 * m - 1)).eval α * (2 * (m : ℝ) - 1 - α) ∧
      -(descPochhammer ℝ (2 * (m + 1))).eval α =
        (descPochhammer ℝ (2 * m - 1)).eval α *
          ((2 * (m : ℝ) - 1 - α) * (2 * (m : ℝ) - α) * (2 * (m : ℝ) + 1 - α)) := by
  have hm' : 1 ≤ 2 * m := by omega
  constructor
  · rw [show 2 * m = (2 * m - 1) + 1 by omega, descPochhammer_succ_right, Polynomial.eval_mul,
      Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_natCast]
    push_cast [hm']; ring
  · rw [show 2 * (m + 1) = (2 * m - 1) + 1 + 1 + 1 by omega]
    simp only [descPochhammer_succ_right, Polynomial.eval_mul, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_natCast]
    push_cast [hm']; ring

/-- Strict `θ ∈ (0, 1)` remainder bound in the non-terminating regime `α < 2 * m - 1` and
`(descPochhammer ℝ (2 * m - 1)).eval α ≠ 0`. -/
private theorem exists_Ioo_sum_Ico_rpow_sub_of_lt {α : ℝ} (hα : α ≠ -1) {m n : ℕ} (hm : 1 ≤ m)
    (hαm : α < 2 * (m : ℝ) - 1) (hQ : (descPochhammer ℝ (2 * m - 1)).eval α ≠ 0) (hn : 1 ≤ n) :
    ∃ θ ∈ Set.Ioo (0 : ℝ) 1,
      ∑ j ∈ Ico 1 n, (j : ℝ) ^ α - ((riemannZeta (-α : ℂ)).re +
        (n : ℝ) ^ (α + 1) / (α + 1) *
          ∑ s ∈ range (2 * m),
            Ring.choose (α + 1) s * (bernoulli s : ℝ) * (n : ℝ) ^ (-(s : ℤ))) =
        θ * ((n : ℝ) ^ (α + 1) / (α + 1) *
          (Ring.choose (α + 1) (2 * m) * (bernoulli (2 * m) : ℝ) *
            (n : ℝ) ^ (-((2 * m : ℕ) : ℤ)))) := by
  set Q : ℝ := (descPochhammer ℝ (2 * m - 1)).eval α
  set rem : ℕ → ℝ := fun k => -(descPochhammer ℝ (2 * k)).eval α *
    ∫ x in Set.Ioi (n : ℝ),
      ((bernoulli (2 * k) : ℝ) - bernoulliFun (2 * k) (Int.fract x)) / (2 * k)! * x ^ (α - 2 * k)
  set term : ℝ := (n : ℝ) ^ (α + 1) / (α + 1) *
    (Ring.choose (α + 1) (2 * m) * (bernoulli (2 * m) : ℝ) * (n : ℝ) ^ (-((2 * m : ℕ) : ℤ)))
  have hm_eq := sum_Ico_rpow_eq_eulerMaclaurin hα hm hαm hn
  have hm1_eq := sum_Ico_rpow_eq_eulerMaclaurin hα (m := m + 1) (by omega)
    (by push_cast; linarith) hn
  have hrange : ∑ s ∈ range (2 * (m + 1)),
        Ring.choose (α + 1) s * (bernoulli s : ℝ) * (n : ℝ) ^ (-(s : ℤ)) =
      ∑ s ∈ range (2 * m), Ring.choose (α + 1) s * (bernoulli s : ℝ) * (n : ℝ) ^ (-(s : ℤ)) +
        Ring.choose (α + 1) (2 * m) * (bernoulli (2 * m) : ℝ) * (n : ℝ) ^ (-((2 * m : ℕ) : ℤ)) := by
    have hodd : bernoulli (2 * m + 1) = 0 := bernoulli_eq_zero_of_odd ⟨m, rfl⟩ (by omega)
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, sum_range_succ, sum_range_succ, hodd,
      Rat.cast_zero, mul_zero, zero_mul, add_zero]
  rw [hrange, mul_add] at hm1_eq
  have hstep : rem m = term + rem (m + 1) := by dsimp only [rem, term]; linarith [hm_eq, hm1_eq]
  obtain ⟨hP1, hP2⟩ := neg_descPochhammer_two_mul_eval α hm
  set u : ℝ := (-1 : ℝ) ^ (m + 1) / Q
  have hcancel : ∀ c d : ℝ, (-1 : ℝ) ^ (m + 1) / Q * (Q * c * d) = c * ((-1 : ℝ) ^ (m + 1) * d) :=
    fun c d => by field_simp
  have hu_rem : 0 < u * rem m := by
    dsimp only [rem, u]
    rw [hP1, show (descPochhammer ℝ (2 * m - 1)).eval α = Q from rfl, hcancel]
    exact mul_pos (by linarith) (neg_one_pow_succ_mul_setIntegral_rpow_tail_pos hm hαm hn)
  have hu_rem1 : u * rem (m + 1) < 0 := by
    dsimp only [rem, u]
    rw [hP2, show (descPochhammer ℝ (2 * m - 1)).eval α = Q from rfl, hcancel]
    have h1 := neg_one_pow_succ_mul_setIntegral_rpow_tail_pos (α := α) (k := m + 1) (by omega)
      (by push_cast; linarith) hn
    rw [pow_succ, mul_assoc, neg_one_mul, mul_neg, neg_pos] at h1
    exact mul_neg_of_pos_of_neg
      (mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)) h1
  have hu_term : 0 < u * term := by linarith [congrArg (u * ·) hstep]
  have hu_lt : u * rem m < u * term := by linarith [congrArg (u * ·) hstep]
  have hu_ne : u ≠ 0 := div_ne_zero (pow_ne_zero _ (by norm_num)) hQ
  have ht_ne : term ≠ 0 := fun h => by simp [h] at hu_term
  refine ⟨rem m / term, ⟨?_, ?_⟩, ?_⟩
  · rw [← mul_div_mul_left (rem m) term hu_ne]; exact div_pos hu_rem hu_term
  · rw [← mul_div_mul_left (rem m) term hu_ne, div_lt_one hu_term]; exact hu_lt
  · have hsub : ∑ j ∈ Ico 1 n, (j : ℝ) ^ α - ((riemannZeta (-α : ℂ)).re +
        (n : ℝ) ^ (α + 1) / (α + 1) * ∑ s ∈ range (2 * m),
          Ring.choose (α + 1) s * (bernoulli s : ℝ) * (n : ℝ) ^ (-(s : ℤ))) = rem m := by
      dsimp only [rem]; linarith [hm_eq]
    rw [hsub, div_mul_cancel₀ _ ht_ne]

/-- **DLMF 2.10.7 remainder theorem**: for `α ≠ -1`, `m ≥ 1` with `α ≤ 2 * m - 1` (i.e.
`(α + 1) / 2 ≤ m`), and `n ≥ 1`, there exists `θ ∈ [0, 1]` such that the error after `2m` terms
equals `θ` times the `s = 2m` term. -/
theorem exists_Icc_sum_Ico_rpow_sub_eulerMaclaurin {α : ℝ} (hα : α ≠ -1) {m n : ℕ} (hm : 1 ≤ m)
    (hαm : α ≤ 2 * (m : ℝ) - 1) (hn : 1 ≤ n) :
    ∃ θ ∈ Set.Icc (0 : ℝ) 1,
      ∑ j ∈ Ico 1 n, (j : ℝ) ^ α - ((riemannZeta (-α : ℂ)).re +
        (n : ℝ) ^ (α + 1) / (α + 1) *
          ∑ s ∈ range (2 * m),
            Ring.choose (α + 1) s * (bernoulli s : ℝ) * (n : ℝ) ^ (-(s : ℤ))) =
        θ * ((n : ℝ) ^ (α + 1) / (α + 1) *
          (Ring.choose (α + 1) (2 * m) * (bernoulli (2 * m) : ℝ) *
            (n : ℝ) ^ (-((2 * m : ℕ) : ℤ)))) := by
  rcases hαm.lt_or_eq with hlt | rfl
  · by_cases hQ : (descPochhammer ℝ (2 * m - 1)).eval α = 0
    · refine ⟨0, ⟨le_rfl, zero_le_one⟩, ?_⟩
      have hm_eq := sum_Ico_rpow_eq_eulerMaclaurin hα hm hlt hn
      have hP : (descPochhammer ℝ (2 * m)).eval α = 0 := by
        have h2m : 2 * m = (2 * m - 1) + 1 := by omega
        rw [h2m, descPochhammer_succ_right, Polynomial.eval_mul, hQ, zero_mul]
      rw [hP, zero_mul, sub_zero] at hm_eq
      linarith [hm_eq]
    · obtain ⟨θ, hθ, heq⟩ := exists_Ioo_sum_Ico_rpow_sub_of_lt hα hm hlt hQ hn
      exact ⟨θ, Set.Ioo_subset_Icc_self hθ, heq⟩
  · -- Boundary case `α = 2 * m - 1`: the `(m + 1)`-st remainder vanishes identically, so `θ = 1`.
    refine ⟨1, ⟨zero_le_one, le_rfl⟩, ?_⟩
    have hm1_eq := sum_Ico_rpow_eq_eulerMaclaurin hα (m := m + 1) (by omega)
      (by push_cast; linarith) hn
    have hP : (descPochhammer ℝ (2 * (m + 1))).eval (2 * (m : ℝ) - 1) = 0 := by
      rw [descPochhammer_eval_eq_prod_range]
      refine prod_eq_zero (i := 2 * m - 1) (mem_range.mpr (by omega)) ?_
      have hm1 : 1 ≤ 2 * m := by omega
      push_cast [hm1]; ring
    have hodd : bernoulli (2 * m + 1) = 0 := bernoulli_eq_zero_of_odd ⟨m, rfl⟩ (by omega)
    rw [hP, zero_mul, sub_zero, show 2 * (m + 1) = 2 * m + 1 + 1 by ring,
      sum_range_succ, sum_range_succ, hodd, Rat.cast_zero, mul_zero, zero_mul, add_zero,
      mul_add] at hm1_eq
    linarith [hm1_eq]

/-- Magnitude bound for the order-`2m` Euler–Maclaurin expansion of `∑_{j=1}^{n-1} j ^ α`
(DLMF 2.10.7): when `α ≠ -1`, `1 ≤ m`, `α ≤ 2 * m - 1`, and `1 ≤ n`, the remainder does not
exceed the magnitude of the `s = 2m` term. -/
theorem abs_sum_Ico_rpow_sub_eulerMaclaurin_le {α : ℝ} (hα : α ≠ -1) {m n : ℕ} (hm : 1 ≤ m)
    (hαm : α ≤ 2 * (m : ℝ) - 1) (hn : 1 ≤ n) :
    |∑ j ∈ Ico 1 n, (j : ℝ) ^ α - ((riemannZeta (-α : ℂ)).re +
      (n : ℝ) ^ (α + 1) / (α + 1) *
        ∑ s ∈ range (2 * m),
          Ring.choose (α + 1) s * (bernoulli s : ℝ) * (n : ℝ) ^ (-(s : ℤ)))| ≤
      |Ring.choose (α + 1) (2 * m) * (bernoulli (2 * m) : ℝ) / (α + 1)| *
        (n : ℝ) ^ (α + 1 - 2 * (m : ℝ)) := by
  obtain ⟨θ, hθ, heq⟩ := exists_Icc_sum_Ico_rpow_sub_eulerMaclaurin hα hm hαm hn
  have hn_pos : (0 : ℝ) < n := by positivity
  have hpow : (n : ℝ) ^ (α + 1) * (n : ℝ) ^ (-((2 * m : ℕ) : ℤ)) =
      (n : ℝ) ^ (α + 1 - 2 * (m : ℝ)) := by
    rw [← Real.rpow_intCast, ← Real.rpow_add hn_pos]
    congr 1; push_cast; ring
  have hterm : (n : ℝ) ^ (α + 1) / (α + 1) *
      (Ring.choose (α + 1) (2 * m) * (bernoulli (2 * m) : ℝ) * (n : ℝ) ^ (-((2 * m : ℕ) : ℤ))) =
      (Ring.choose (α + 1) (2 * m) * (bernoulli (2 * m) : ℝ) / (α + 1)) *
        ((n : ℝ) ^ (α + 1) * (n : ℝ) ^ (-((2 * m : ℕ) : ℤ))) := by ring
  rw [heq, hterm, hpow, abs_mul, abs_mul, abs_of_nonneg hθ.1,
    abs_of_pos (Real.rpow_pos_of_pos hn_pos _)]
  exact mul_le_of_le_one_left (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg hn_pos.le _)) hθ.2

/-- Each individual Euler–Maclaurin term of index `s ≥ N` is `O(n ^ (α + 1 - N))` as `n → ∞`. -/
private theorem rpow_eulerMaclaurin_term_isBigO (α : ℝ) {N s : ℕ} (hs : N ≤ s) :
    (fun n : ℕ => (n : ℝ) ^ (α + 1) / (α + 1) *
      (Ring.choose (α + 1) s * (bernoulli s : ℝ) * (n : ℝ) ^ (-(s : ℤ)))) =O[atTop]
      fun n : ℕ => (n : ℝ) ^ (α + 1 - (N : ℝ)) := by
  refine Asymptotics.IsBigO.of_bound |Ring.choose (α + 1) s * (bernoulli s : ℝ) / (α + 1)| ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by positivity
  have hs' : (N : ℝ) ≤ s := by exact_mod_cast hs
  have hpow : (n : ℝ) ^ (α + 1) * (n : ℝ) ^ (-(s : ℤ)) = (n : ℝ) ^ (α + 1 - (s : ℝ)) := by
    rw [← Real.rpow_intCast, ← Real.rpow_add hn0]; push_cast; ring_nf
  have hrearr : (n : ℝ) ^ (α + 1) / (α + 1) *
      (Ring.choose (α + 1) s * (bernoulli s : ℝ) * (n : ℝ) ^ (-(s : ℤ))) =
      (Ring.choose (α + 1) s * (bernoulli s : ℝ) / (α + 1)) *
        ((n : ℝ) ^ (α + 1) * (n : ℝ) ^ (-(s : ℤ))) := by ring
  simp only [Real.norm_eq_abs, hrearr, hpow, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hn0 _)]
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith))
    (abs_nonneg _)

/-- **Generalized Euler–Maclaurin asymptotic expansion of `∑_{j=1}^{n-1} j ^ α`** (DLMF 2.10.7).
For every real `α ≠ -1` and every truncation order `N : ℕ`, subtracting `ζ(-α)` and the first `N`
Euler–Maclaurin terms leaves an `O(n ^ (α + 1 - N))` error as `n → ∞`. -/
theorem sum_Ico_rpow_sub_eulerMaclaurin_isBigO {α : ℝ} (hα : α ≠ -1) (N : ℕ) :
    (fun n : ℕ => ∑ j ∈ Ico 1 n, (j : ℝ) ^ α - ((riemannZeta (-α : ℂ)).re +
      (n : ℝ) ^ (α + 1) / (α + 1) *
        ∑ s ∈ range N,
          Ring.choose (α + 1) s * (bernoulli s : ℝ) * (n : ℝ) ^ (-(s : ℤ)))) =O[atTop]
      fun n : ℕ => (n : ℝ) ^ (α + 1 - (N : ℝ)) := by
  set m : ℕ := max 1 (max N (⌊(α + 1) / 2⌋₊ + 1))
  have hm1 : 1 ≤ m := le_max_left _ _
  have hNm : N ≤ 2 * m := by
    have : N ≤ m := (le_max_left _ _).trans (le_max_right _ _)
    omega
  have hαm : α ≤ 2 * (m : ℝ) - 1 := by
    have hlt : (α + 1) / 2 < (⌊(α + 1) / 2⌋₊ + 1 : ℕ) := by
      simpa using Nat.lt_floor_add_one ((α + 1) / 2)
    have hle : ((⌊(α + 1) / 2⌋₊ + 1 : ℕ) : ℝ) ≤ m := by
      exact_mod_cast (le_max_right _ _).trans (le_max_right _ _)
    linarith
  have hrem_bigO : (fun n : ℕ => ∑ j ∈ Ico 1 n, (j : ℝ) ^ α - ((riemannZeta (-α : ℂ)).re +
      (n : ℝ) ^ (α + 1) / (α + 1) *
        ∑ s ∈ range (2 * m),
          Ring.choose (α + 1) s * (bernoulli s : ℝ) * (n : ℝ) ^ (-(s : ℤ)))) =O[atTop]
      fun n : ℕ => (n : ℝ) ^ (α + 1 - (N : ℝ)) := by
    refine Asymptotics.IsBigO.of_bound
      |Ring.choose (α + 1) (2 * m) * (bernoulli (2 * m) : ℝ) / (α + 1)| ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hn0 : (0 : ℝ) < n := by positivity
    have hNm' : (N : ℝ) ≤ 2 * (m : ℝ) := by exact_mod_cast hNm
    simp only [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hn0 _)]
    exact (abs_sum_Ico_rpow_sub_eulerMaclaurin_le hα hm1 hαm hn).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith))
        (abs_nonneg _))
  have hmid_bigO := Asymptotics.IsBigO.sum (s := Ico N (2 * m)) fun s hs =>
    rpow_eulerMaclaurin_term_isBigO α (mem_Ico.mp hs).1
  refine (hmid_bigO.add hrem_bigO).congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_ge_atTop 1] with n _
  have hsplit : ∑ s ∈ range (2 * m),
        Ring.choose (α + 1) s * (bernoulli s : ℝ) * (n : ℝ) ^ (-(s : ℤ)) =
      ∑ s ∈ range N, Ring.choose (α + 1) s * (bernoulli s : ℝ) * (n : ℝ) ^ (-(s : ℤ)) +
        ∑ s ∈ Ico N (2 * m), Ring.choose (α + 1) s * (bernoulli s : ℝ) * (n : ℝ) ^ (-(s : ℤ)) :=
    (sum_range_add_sum_Ico _ hNm).symm
  rw [Finset.sum_apply, hsplit, mul_add, ← Finset.mul_sum]
  ring

end TauCeti

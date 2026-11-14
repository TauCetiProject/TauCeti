/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.RademacherSum.Moment
public import TauCeti.Analysis.Normed.Module.RademacherSum.TypeCotype

import TauCeti.Analysis.Normed.Module.RademacherSum.Levy

/-!
# Kahane's inequality for Rademacher sums

In any real normed space `E`, **Kahane's inequality** states that all `p`-th moments (`0 < p < ∞`)
of finite Rademacher sums are comparable up to universal constants depending only on the exponents:
`K_q(x) ≤ kahaneConst p q * K_p(x)`.

When `q ≤ p` this holds with constant `1` by power-mean monotonicity. When `p < q`, Markov's
inequality at `t₀ = (8 * 3 ^ q) ^ (1 / p) * K_p(x)` makes `4 P(t₀ < ‖S‖) ≤ (2 * 3 ^ q)⁻¹`; feeding
this into the iterated Rademacher tail bound `4 P(3 ^ k * t₀ < ‖S‖) ≤ (4 P(t₀ < ‖S‖)) ^ (2 ^ k)`
and summing over a finite triadic ladder cancels the `3 ^ (q (k + 1))` growth against a geometric
series in `1 / 2`, yielding the explicit constant `2 ^ (1 / q) * (8 * 3 ^ q) ^ (1 / p)`.

As immediate consequences:

* every moment `K_q(x)` (`0 < q < ∞`) is equivalent to the Rademacher second moment `R₂(x)`;
* Rademacher type `p` and cotype `q` of a real normed space may be tested using any `r`-th moment
  (`0 < r < ∞`) in place of `R₂`;
* for an arbitrary family `x : α → E`, boundedness of the finite truncations `s ↦ K_p(x|_s)` is
  independent of `p ∈ (0, ∞)` and their suprema satisfy Kahane's bound.

## Main declarations

* `TauCeti.kahaneConst`: explicit constant in Kahane's inequality.
* `TauCeti.rademacherMoment_le_kahaneConst_mul`: **Kahane's inequality**
  `K_q(x) ≤ kahaneConst p q * K_p(x)` for `0 < p` and `0 < q`.
* `TauCeti.rademacherMoment_le_kahaneConst_mul_secondMoment`,
  `TauCeti.rademacherSecondMoment_le_kahaneConst_mul_moment`: comparison between `K_p` and `R₂`.
* `TauCeti.HasType.rademacherMoment_le`, `TauCeti.hasType_of_rademacherMoment_le`,
  `TauCeti.HasCotype.norm_toLp_le_rademacherMoment`, `TauCeti.hasCotype_of_rademacherMoment_le`:
  equivalence of type and cotype across Rademacher moments.
* `TauCeti.bddAbove_range_rademacherMoment_subtype_iff`,
  `TauCeti.ciSup_rademacherMoment_subtype_le`: infinite-family truncation consequences.

## References

* J.-P. Kahane, *Some Random Series of Functions*, 2nd ed., Cambridge Univ. Press, 1985, §2.5.
* M. Ledoux and M. Talagrand, *Probability in Banach Spaces*, Theorem 4.7.
* G. Pisier and Q. Xu, *Non-commutative martingale inequalities*, Comm. Math. Phys. 189 (1997),
  667–698, §2.
-/

public section

noncomputable section

open Finset
open scoped BigOperators ENNReal NNReal

namespace TauCeti

/-! ### Explicit Kahane constant -/

/-- Explicit universal constant in Kahane's inequality `K_q(x) ≤ kahaneConst p q * K_p(x)`: equal to
`1` when `q ≤ p`, and to `2 ^ (1 / q) * (8 * 3 ^ q) ^ (1 / p)` when `p < q`. -/
def kahaneConst (p q : ℝ) : ℝ≥0 :=
  if q ≤ p then 1 else Real.toNNReal (2 ^ (1 / q) * (8 * 3 ^ q) ^ (1 / p))

/-- Unfolding lemma for `kahaneConst` across module boundaries. -/
theorem kahaneConst_def (p q : ℝ) :
    kahaneConst p q = if q ≤ p then 1 else Real.toNNReal (2 ^ (1 / q) * (8 * 3 ^ q) ^ (1 / p)) :=
  (rfl)

/-- For `q ≤ p`, `kahaneConst p q = 1`. -/
theorem kahaneConst_of_le {p q : ℝ} (h : q ≤ p) : kahaneConst p q = 1 := by
  simp [kahaneConst, h]

/-- For `p < q`, `kahaneConst p q = 2 ^ (1 / q) * (8 * 3 ^ q) ^ (1 / p)`. -/
theorem coe_kahaneConst_of_lt {p q : ℝ} (h : p < q) :
    (kahaneConst p q : ℝ) = 2 ^ (1 / q) * (8 * 3 ^ q) ^ (1 / p) := by
  rw [kahaneConst, ite_eq_right_iff.2 fun hqp ↦ absurd h (not_lt.2 hqp),
    Real.coe_toNNReal _ (by positivity)]

/-- At equal exponents, `kahaneConst p p = 1`. -/
@[simp]
theorem kahaneConst_self (p : ℝ) : kahaneConst p p = 1 := by
  simp [kahaneConst]

/-- `kahaneConst p q` is strictly positive for all real `p` and `q`. -/
theorem kahaneConst_pos (p q : ℝ) : 0 < kahaneConst p q := by
  by_cases h : q ≤ p
  · simp [kahaneConst, h]
  · rw [← NNReal.coe_pos, coe_kahaneConst_of_lt (not_le.1 h)]
    positivity

/-- For `0 < p` and `0 < q`, `1 ≤ kahaneConst p q`. -/
theorem one_le_kahaneConst {p q : ℝ} (hp : 0 < p) (hq : 0 < q) : 1 ≤ kahaneConst p q := by
  by_cases h : q ≤ p
  · simp [kahaneConst, h]
  · rw [← NNReal.coe_le_coe, NNReal.coe_one, coe_kahaneConst_of_lt (not_le.1 h)]
    have h2 : (1 : ℝ) ≤ 2 ^ (1 / q) := Real.one_le_rpow (by norm_num) (by positivity)
    have h3 : (1 : ℝ) ≤ 8 * 3 ^ q := by
      have : (1 : ℝ) ≤ 3 ^ q := Real.one_le_rpow (by norm_num) hq.le
      linarith
    have h8 : (1 : ℝ) ≤ (8 * 3 ^ q) ^ (1 / p) := Real.one_le_rpow h3 (by positivity)
    nlinarith

/-! ### Proof of Kahane's inequality -/

section Finite

variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [SeminormedAddCommGroup E]

/-- Expectation of an exceedance indicator over the sign cube equals the normalized `Set.ncard`
probability. -/
private theorem expect_ite_lt_norm_sum (x : ι → E) (r : ℝ) :
    (𝔼 ε : ι → ℤˣ, if r < ‖∑ i, ε i • x i‖ then (1 : ℝ) else 0) =
      ({ε : ι → ℤˣ | r < ‖∑ i, ε i • x i‖}.ncard : ℝ) / 2 ^ Fintype.card ι := by
  classical
  rw [expect_eq_sum_div_card, card_univ, Fintype.card_fun, Fintype.card_units_int, Nat.cast_pow,
    Nat.cast_ofNat, sum_boole, Set.ncard_eq_toFinset_card']
  congr 3
  ext ε
  simp

/-- Markov's inequality on the sign cube for `0 < p` and `0 < t`. -/
private theorem rademacher_tail_le_div_rpow {p : ℝ} (hp : 0 < p) {t : ℝ} (ht : 0 < t)
    (x : ι → E) :
    ({ε : ι → ℤˣ | t < ‖∑ i, ε i • x i‖}.ncard : ℝ) / 2 ^ Fintype.card ι ≤
      rademacherMoment p x ^ p / t ^ p := by
  rw [le_div_iff₀ (by positivity), ← expect_ite_lt_norm_sum, expect_mul, rademacherMoment_rpow]
  refine expect_le_expect fun ε _ ↦ ?_
  split_ifs with hε
  · rw [one_mul]
    exact Real.rpow_le_rpow ht.le hε.le hp.le
  · rw [zero_mul]
    exact Real.rpow_nonneg (norm_nonneg _) _

omit [DecidableEq ι] in
/-- Pointwise finite triadic bound for a signed sum: when `‖S(ε)‖ ≤ 3 ^ M * t₀`, `‖S(ε)‖ ^ q` is
dominated by `t₀ ^ q` plus the finite sum of `(3 ^ (k + 1) * t₀) ^ q` over levels `k < M` with
`3 ^ k * t₀ < ‖S(ε)‖`. -/
private theorem norm_sum_rpow_le_add_sum_three_pow_ite {q t₀ : ℝ} (hq : 0 < q) (ht₀ : 0 < t₀)
    (x : ι → E) (ε : ι → ℤˣ) {M : ℕ} (huM : ‖∑ i, ε i • x i‖ ≤ 3 ^ M * t₀) :
    ‖∑ i, ε i • x i‖ ^ q ≤
      t₀ ^ q + ∑ k ∈ range M,
        (3 ^ (k + 1) * t₀) ^ q * (if 3 ^ k * t₀ < ‖∑ i, ε i • x i‖ then 1 else 0) := by
  set u := ‖∑ i, ε i • x i‖
  have hu : 0 ≤ u := norm_nonneg _
  have hterm_nonneg (k : ℕ) :
      0 ≤ ((3 : ℝ) ^ (k + 1) * t₀) ^ q * (if (3 : ℝ) ^ k * t₀ < u then 1 else 0) := by
    split_ifs <;> positivity
  rcases le_or_gt u t₀ with hle | hgt
  · exact (Real.rpow_le_rpow hu hle hq.le).trans
      (le_add_of_nonneg_right (sum_nonneg fun k _ ↦ hterm_nonneg k))
  · have hMpos : 0 < M := by
      by_contra hM0
      obtain rfl : M = 0 := Nat.eq_zero_of_not_pos hM0
      rw [pow_zero, one_mul] at huM
      linarith
    let K := (range M).filter fun k : ℕ ↦ (3 : ℝ) ^ k * t₀ < u
    have h0K : 0 ∈ K := mem_filter.2 ⟨mem_range.2 hMpos, by simpa using hgt⟩
    let km := K.max' ⟨0, h0K⟩
    have hkm_mem : km ∈ K := max'_mem K ⟨0, h0K⟩
    have hkm_lt : km < M := mem_range.1 (mem_filter.1 hkm_mem).1
    have hu_le : u ≤ (3 : ℝ) ^ (km + 1) * t₀ := by
      by_contra hlt
      push Not at hlt
      rcases lt_or_eq_of_le (Nat.add_one_le_iff.2 hkm_lt) with hltM | heqM
      · have hsucc : km + 1 ∈ K := mem_filter.2 ⟨mem_range.2 hltM, hlt⟩
        exact absurd (le_max' K (km + 1) hsucc) (by omega)
      · rw [heqM] at hlt
        linarith
    have hle_km : u ^ q ≤ ((3 : ℝ) ^ (km + 1) * t₀) ^ q *
        (if (3 : ℝ) ^ km * t₀ < u then 1 else 0) := by
      have hcond : (3 : ℝ) ^ km * t₀ < u := (mem_filter.1 hkm_mem).2
      simp only [hcond, ↓reduceIte, mul_one]
      exact Real.rpow_le_rpow hu hu_le hq.le
    exact (hle_km.trans (single_le_sum (fun k _ ↦ hterm_nonneg k) (mem_range.2 hkm_lt))).trans
      (le_add_of_nonneg_left (by positivity))

omit [DecidableEq ι] in
/-- Single-shell estimate in the triadic ladder: once `4 P(t₀ < ‖S‖) ≤ (2 * 3 ^ q)⁻¹`, the `k`-th
shell contribution is at most `t₀ ^ q * (1 / 2) ^ (k + 1)`. -/
private theorem mul_rademacher_tail_three_pow_le [NormedSpace ℝ E] {q t₀ : ℝ} (hq : 0 < q)
    (ht₀ : 0 < t₀) {x : ι → E}
    (hbase : 4 * (({ε : ι → ℤˣ | t₀ < ‖∑ i, ε i • x i‖}.ncard : ℝ) / 2 ^ Fintype.card ι) ≤
      ((2 : ℝ) * 3 ^ q)⁻¹)
    (k : ℕ) :
    ((3 : ℝ) ^ (k + 1) * t₀) ^ q *
        (({ε : ι → ℤˣ | (3 : ℝ) ^ k * t₀ < ‖∑ i, ε i • x i‖}.ncard : ℝ) / 2 ^ Fintype.card ι) ≤
      t₀ ^ q * (1 / 2 : ℝ) ^ (k + 1) := by
  have h3pos : (1 : ℝ) ≤ 2 * 3 ^ q := by
    have : (1 : ℝ) ≤ 3 ^ q := Real.one_le_rpow (by norm_num) hq.le
    linarith
  have htail : ({ε : ι → ℤˣ | (3 : ℝ) ^ k * t₀ < ‖∑ i, ε i • x i‖}.ncard : ℝ) /
      2 ^ Fintype.card ι ≤ (((2 : ℝ) * 3 ^ q)⁻¹) ^ (k + 1) := by
    have hiter := ncard_lt_norm_sum_three_pow_mul_div_le x t₀ k
    have hpow1 : (4 * (({ε : ι → ℤˣ | t₀ < ‖∑ i, ε i • x i‖}.ncard : ℝ) /
        2 ^ Fintype.card ι)) ^ (2 ^ k) ≤ (((2 : ℝ) * 3 ^ q)⁻¹) ^ (2 ^ k) :=
      pow_le_pow_left₀ (by positivity) hbase _
    have hpow2 : (((2 : ℝ) * 3 ^ q)⁻¹) ^ (2 ^ k) ≤ (((2 : ℝ) * 3 ^ q)⁻¹) ^ (k + 1) :=
      pow_le_pow_of_le_one (by positivity) (inv_le_one_of_one_le₀ h3pos)
        (Nat.succ_le_of_lt k.lt_two_pow_self)
    have hnn : 0 ≤ ({ε : ι → ℤˣ | (3 : ℝ) ^ k * t₀ < ‖∑ i, ε i • x i‖}.ncard : ℝ) /
        2 ^ Fintype.card ι := by positivity
    have h4 : ({ε : ι → ℤˣ | (3 : ℝ) ^ k * t₀ < ‖∑ i, ε i • x i‖}.ncard : ℝ) /
        2 ^ Fintype.card ι ≤
          4 * (({ε : ι → ℤˣ | (3 : ℝ) ^ k * t₀ < ‖∑ i, ε i • x i‖}.ncard : ℝ) /
            2 ^ Fintype.card ι) := by linarith
    exact h4.trans (hiter.trans (hpow1.trans hpow2))
  have hrpow : ((3 : ℝ) ^ (k + 1) * t₀) ^ q = t₀ ^ q * (3 ^ q) ^ (k + 1) := by
    rw [Real.mul_rpow (by positivity) ht₀.le, mul_comm, ← Real.rpow_natCast 3 (k + 1),
      ← Real.rpow_mul (by norm_num), mul_comm ((k + 1 : ℕ) : ℝ) q, Real.rpow_mul (by norm_num),
      Real.rpow_natCast]
  have ha : (3 : ℝ) ^ q * ((2 : ℝ) * 3 ^ q)⁻¹ = 1 / 2 := by
    rw [mul_inv, mul_left_comm, mul_inv_cancel₀ (by positivity), mul_one, one_div]
  calc ((3 : ℝ) ^ (k + 1) * t₀) ^ q *
          (({ε : ι → ℤˣ | (3 : ℝ) ^ k * t₀ < ‖∑ i, ε i • x i‖}.ncard : ℝ) / 2 ^ Fintype.card ι)
      ≤ (t₀ ^ q * (3 ^ q) ^ (k + 1)) * (((2 : ℝ) * 3 ^ q)⁻¹) ^ (k + 1) := by
        rw [hrpow]; gcongr
    _ = t₀ ^ q * (1 / 2 : ℝ) ^ (k + 1) := by
        rw [mul_assoc, ← mul_pow, ha]

/-- Core moment estimate behind Kahane's inequality when `0 < rademacherMoment p x`: for
`t₀ = (8 * 3 ^ q) ^ (1 / p) * K_p(x)`, the `q`-th power average is at most `2 * t₀ ^ q`. -/
private theorem expect_norm_sum_rpow_le_two_mul_rpow [NormedSpace ℝ E] {p q : ℝ} (hp : 0 < p)
    (hq : 0 < q) {x : ι → E} (hKp : 0 < rademacherMoment p x) :
    𝔼 ε : ι → ℤˣ, ‖∑ i, ε i • x i‖ ^ q ≤
      2 * ((8 * 3 ^ q) ^ (1 / p) * rademacherMoment p x) ^ q := by
  let t₀ : ℝ := (8 * 3 ^ q) ^ (1 / p) * rademacherMoment p x
  have ht₀ : 0 < t₀ := by positivity
  have hbase : 4 * (({ε : ι → ℤˣ | t₀ < ‖∑ i, ε i • x i‖}.ncard : ℝ) / 2 ^ Fintype.card ι) ≤
      ((2 : ℝ) * 3 ^ q)⁻¹ := by
    have ht₀p : t₀ ^ p = 8 * 3 ^ q * rademacherMoment p x ^ p := by
      dsimp [t₀]
      rw [Real.mul_rpow (by positivity) hKp.le, ← Real.rpow_mul (by positivity),
        one_div_mul_cancel hp.ne', Real.rpow_one]
    have hmarkov := rademacher_tail_le_div_rpow hp ht₀ x
    rw [ht₀p] at hmarkov
    nth_rw 1 [← one_mul (rademacherMoment p x ^ p)] at hmarkov
    rw [mul_div_mul_right _ _ (by positivity)] at hmarkov
    calc 4 * (({ε : ι → ℤˣ | t₀ < ‖∑ i, ε i • x i‖}.ncard : ℝ) / 2 ^ Fintype.card ι)
        ≤ 4 * (1 / (8 * 3 ^ q)) := by gcongr
      _ = ((2 : ℝ) * 3 ^ q)⁻¹ := by ring
  obtain ⟨M, hM⟩ := exists_nat_gt ((∑ i, ‖x i‖) / t₀)
  have huM (ε : ι → ℤˣ) : ‖∑ i, ε i • x i‖ ≤ 3 ^ M * t₀ := by
    have hsum : ‖∑ i, ε i • x i‖ ≤ ∑ i, ‖x i‖ :=
      (norm_sum_le _ _).trans_eq (sum_congr rfl fun i _ ↦ norm_units_zsmul _ _)
    have hM3 : (M : ℝ) ≤ (3 : ℝ) ^ M := by
      exact_mod_cast M.lt_two_pow_self.le.trans (Nat.pow_le_pow_left (by norm_num) M)
    exact hsum.trans (((div_lt_iff₀ ht₀).1 (hM.trans_le hM3)).le)
  have hgeom : ∑ k ∈ range M, (1 / 2 : ℝ) ^ (k + 1) ≤ 1 := by
    have hval : (1 / 2 : ℝ) * (((1 / 2 : ℝ) ^ M - 1) / (1 / 2 - 1)) = 1 - (1 / 2 : ℝ) ^ M := by
      ring
    rw [sum_congr rfl fun k _ ↦ pow_succ' (1 / 2 : ℝ) k, ← mul_sum,
      geom_sum_eq (by norm_num : (1 / 2 : ℝ) ≠ 1), hval]
    linarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) M]
  calc 𝔼 ε : ι → ℤˣ, ‖∑ i, ε i • x i‖ ^ q
      ≤ 𝔼 ε : ι → ℤˣ, (t₀ ^ q + ∑ k ∈ range M, ((3 : ℝ) ^ (k + 1) * t₀) ^ q *
          (if (3 : ℝ) ^ k * t₀ < ‖∑ i, ε i • x i‖ then 1 else 0)) :=
        expect_le_expect fun ε _ ↦ norm_sum_rpow_le_add_sum_three_pow_ite hq ht₀ x ε (huM ε)
    _ = t₀ ^ q + ∑ k ∈ range M, ((3 : ℝ) ^ (k + 1) * t₀) ^ q *
          (({ε : ι → ℤˣ | (3 : ℝ) ^ k * t₀ < ‖∑ i, ε i • x i‖}.ncard : ℝ) /
            2 ^ Fintype.card ι) := by
        rw [expect_add_distrib, expect_const univ_nonempty, expect_sum_comm]
        congr 1
        refine sum_congr rfl fun k _ ↦ ?_
        rw [← mul_expect, expect_ite_lt_norm_sum]
    _ ≤ t₀ ^ q + ∑ k ∈ range M, t₀ ^ q * (1 / 2 : ℝ) ^ (k + 1) :=
        add_le_add le_rfl (sum_le_sum fun k _ ↦ mul_rademacher_tail_three_pow_le hq ht₀ hbase k)
    _ ≤ 2 * t₀ ^ q := by
        rw [← mul_sum]
        nlinarith [Real.rpow_pos_of_pos ht₀ q]

/-- **Kahane's inequality**: in any real normed space and for all `0 < p` and `0 < q`,
`rademacherMoment q x ≤ kahaneConst p q * rademacherMoment p x`. -/
theorem rademacherMoment_le_kahaneConst_mul [NormedSpace ℝ E] {p q : ℝ} (hp : 0 < p) (hq : 0 < q)
    (x : ι → E) :
    rademacherMoment q x ≤ kahaneConst p q * rademacherMoment p x := by
  by_cases hqp : q ≤ p
  · rw [kahaneConst_of_le hqp, NNReal.coe_one, one_mul]
    exact rademacherMoment_mono_exponent hq hqp x
  have hpq : p < q := not_le.1 hqp
  rcases eq_or_lt_of_le (rademacherMoment_nonneg p x) with hzero | hKp
  · have hsum0 : ∑ ε ∈ (univ : Finset (ι → ℤˣ)), ‖∑ i, ε i • x i‖ ^ p = 0 := by
      have h := (rademacherMoment_rpow p x).symm
      rw [← hzero, Real.zero_rpow hp.ne', expect_eq_sum_div_card, div_eq_zero_iff] at h
      exact h.resolve_right (Nat.cast_ne_zero.2 univ_nonempty.card_ne_zero)
    have hnorm0 (ε : ι → ℤˣ) : ‖∑ i, ε i • x i‖ = 0 := by
      have h0 := (sum_eq_zero_iff_of_nonneg
        (fun δ _ ↦ Real.rpow_nonneg (norm_nonneg (∑ i, δ i • x i)) p)).1 hsum0 ε (mem_univ ε)
      by_contra hne
      exact absurd h0 (Real.rpow_pos_of_pos (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)) p).ne'
    rw [rademacherMoment_def]
    simp [hnorm0, Real.zero_rpow hq.ne', Real.zero_rpow (inv_ne_zero hq.ne'), ← hzero]
  · rw [coe_kahaneConst_of_lt hpq, mul_assoc]
    refine rademacherMoment_le_of_rpow_le hq (by positivity) ?_
    refine (expect_norm_sum_rpow_le_two_mul_rpow hp hq hKp).trans_eq ?_
    symm
    rw [Real.mul_rpow (by positivity) (by positivity),
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), one_div_mul_cancel hq.ne', Real.rpow_one]

/-- Comparison of the `q`-th Rademacher moment (`0 < q`) against `rademacherSecondMoment`. -/
theorem rademacherMoment_le_kahaneConst_mul_secondMoment [NormedSpace ℝ E] {q : ℝ} (hq : 0 < q)
    (x : ι → E) :
    rademacherMoment q x ≤ kahaneConst 2 q * rademacherSecondMoment x := by
  simpa [rademacherMoment_two] using rademacherMoment_le_kahaneConst_mul two_pos hq x

/-- Comparison of `rademacherSecondMoment` against the `p`-th Rademacher moment (`0 < p`). -/
theorem rademacherSecondMoment_le_kahaneConst_mul_moment [NormedSpace ℝ E] {p : ℝ} (hp : 0 < p)
    (x : ι → E) :
    rademacherSecondMoment x ≤ kahaneConst p 2 * rademacherMoment p x := by
  simpa [rademacherMoment_two] using rademacherMoment_le_kahaneConst_mul hp two_pos x

/-! ### Equivalence of Rademacher type and cotype across moments -/

/-- If a real normed space `E` has Rademacher type `p` with constant `C`, then its `r`-th
Rademacher moments (`0 < r`) satisfy the type `p` bound with constant `kahaneConst 2 r * C`. -/
theorem HasType.rademacherMoment_le [NormedSpace ℝ E] {p : ℝ≥0∞} {C : ℝ≥0} (h : HasType E p C)
    {r : ℝ} (hr : 0 < r) (y : ι → E) :
    rademacherMoment r y ≤ (kahaneConst 2 r * C : ℝ≥0) * ‖WithLp.toLp p y‖ := calc
  rademacherMoment r y
      ≤ kahaneConst 2 r * rademacherSecondMoment y :=
        rademacherMoment_le_kahaneConst_mul_secondMoment hr y
  _ ≤ kahaneConst 2 r * (C * ‖WithLp.toLp p y‖) := by
        gcongr; exact h.rademacherSecondMoment_le y
  _ = (kahaneConst 2 r * C : ℝ≥0) * ‖WithLp.toLp p y‖ := by push_cast; ring

/-- If a real normed space `E` has Rademacher cotype `q` with constant `C`, then its `r`-th
Rademacher moments (`0 < r`) satisfy the cotype `q` bound with constant `C * kahaneConst r 2`. -/
theorem HasCotype.norm_toLp_le_rademacherMoment [NormedSpace ℝ E] {q : ℝ≥0∞} {C : ℝ≥0}
    (h : HasCotype E q C) {r : ℝ} (hr : 0 < r) (y : ι → E) :
    ‖WithLp.toLp q y‖ ≤ (C * kahaneConst r 2 : ℝ≥0) * rademacherMoment r y := calc
  ‖WithLp.toLp q y‖
      ≤ C * rademacherSecondMoment y := h.norm_toLp_le y
  _ ≤ C * (kahaneConst r 2 * rademacherMoment r y) := by
        gcongr; exact rademacherSecondMoment_le_kahaneConst_mul_moment hr y
  _ = (C * kahaneConst r 2 : ℝ≥0) * rademacherMoment r y := by push_cast; ring

end Finite

section TypeCotype

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

/-- A real normed space has Rademacher type `p` as soon as the type `p` bound holds for some
`r`-th Rademacher moment (`0 < r`). -/
theorem hasType_of_rademacherMoment_le {p : ℝ≥0∞} {C : ℝ≥0} {r : ℝ} (hr : 0 < r)
    (h : ∀ (n : ℕ) (y : Fin n → E), rademacherMoment r y ≤ C * ‖WithLp.toLp p y‖) :
    HasType E p (kahaneConst r 2 * C) :=
  hasType_iff.2 fun n y ↦ calc
    rademacherSecondMoment y
        ≤ kahaneConst r 2 * rademacherMoment r y :=
          rademacherSecondMoment_le_kahaneConst_mul_moment hr y
    _ ≤ kahaneConst r 2 * (C * ‖WithLp.toLp p y‖) := by gcongr; exact h n y
    _ = (kahaneConst r 2 * C : ℝ≥0) * ‖WithLp.toLp p y‖ := by push_cast; ring

/-- A real normed space has Rademacher cotype `q` as soon as the cotype `q` bound holds for some
`r`-th Rademacher moment (`0 < r`). -/
theorem hasCotype_of_rademacherMoment_le {q : ℝ≥0∞} {C : ℝ≥0} {r : ℝ} (hr : 0 < r)
    (h : ∀ (n : ℕ) (y : Fin n → E), ‖WithLp.toLp q y‖ ≤ C * rademacherMoment r y) :
    HasCotype E q (C * kahaneConst 2 r) :=
  hasCotype_iff.2 fun n y ↦ calc
    ‖WithLp.toLp q y‖
        ≤ C * rademacherMoment r y := h n y
    _ ≤ C * (kahaneConst 2 r * rademacherSecondMoment y) := by
          gcongr; exact rademacherMoment_le_kahaneConst_mul_secondMoment hr y
    _ = (C * kahaneConst 2 r : ℝ≥0) * rademacherSecondMoment y := by push_cast; ring

end TypeCotype

/-! ### Finite truncations of an arbitrary indexed family -/

section Truncation

variable {α E : Type*} [DecidableEq α] [SeminormedAddCommGroup E] [NormedSpace ℝ E]

/-- Boundedness of the finite Rademacher moments `s ↦ K_p(x|_s)` is independent of the exponent
`p ∈ (0, ∞)`. -/
theorem bddAbove_range_rademacherMoment_subtype_iff {p q : ℝ} (hp : 0 < p) (hq : 0 < q)
    (x : α → E) :
    BddAbove (Set.range fun s : Finset α ↦ rademacherMoment p (fun i : s ↦ x i)) ↔
      BddAbove (Set.range fun s : Finset α ↦ rademacherMoment q (fun i : s ↦ x i)) := by
  have hdir {u v : ℝ} (hu : 0 < u) (hv : 0 < v)
      (hb : BddAbove (Set.range fun s : Finset α ↦ rademacherMoment u (fun i : s ↦ x i))) :
      BddAbove (Set.range fun s : Finset α ↦ rademacherMoment v (fun i : s ↦ x i)) := by
    obtain ⟨B, hB⟩ := hb
    refine ⟨kahaneConst u v * B, ?_⟩
    rintro _ ⟨s, rfl⟩
    exact (rademacherMoment_le_kahaneConst_mul hu hv _).trans
      (mul_le_mul_of_nonneg_left (hB ⟨s, rfl⟩) (kahaneConst u v).2)
  exact ⟨hdir hp hq, hdir hq hp⟩

/-- Kahane's inequality for the supremum of finite truncations of an arbitrary family `x : α → E`
and exponents `0 < p` and `0 < q`. -/
theorem ciSup_rademacherMoment_subtype_le {p q : ℝ} (hp : 0 < p) (hq : 0 < q) (x : α → E) :
    (⨆ s : Finset α, rademacherMoment q (fun i : s ↦ x i)) ≤
      kahaneConst p q * ⨆ s : Finset α, rademacherMoment p (fun i : s ↦ x i) := by
  by_cases hbdd : BddAbove (Set.range fun s : Finset α ↦ rademacherMoment p (fun i : s ↦ x i))
  · refine ciSup_le fun s ↦ ?_
    exact (rademacherMoment_le_kahaneConst_mul hp hq _).trans
      (mul_le_mul_of_nonneg_left (le_ciSup hbdd s) (kahaneConst p q).2)
  · have hbdd_q : ¬ BddAbove (Set.range fun s : Finset α ↦ rademacherMoment q (fun i : s ↦ x i)) :=
      mt (bddAbove_range_rademacherMoment_subtype_iff hp hq x).2 hbdd
    rw [Real.iSup_of_not_bddAbove hbdd, Real.iSup_of_not_bddAbove hbdd_q, mul_zero]

end Truncation

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.LevelOne.TraceFormula.ExplicitElement.Trace
public import TauCeti.NumberTheory.HurwitzClassNumber
import Mathlib.Data.Int.Order.Lemmas
import TauCeti.NumberTheory.Divisors
import TauCeti.NumberTheory.ModularForms.LevelOne.PeriodPolynomial.Finrank
import TauCeti.NumberTheory.ModularForms.LevelOne.TraceFormula.ExplicitElement.Hyperbolic
import TauCeti.NumberTheory.ModularForms.LevelOne.TraceFormula.ExplicitElement.Parabolic
import TauCeti.NumberTheory.ModularForms.LevelOne.TraceFormula.ExplicitElement.PeriodRelation

/-!
# The class-number trace formula for Popa–Zagier's explicit element

This file assembles the trace of Popa–Zagier's explicit element `Tₙ` on the space `V_w` of
even-degree binary forms and, for `w ≠ 0`, on the full period-polynomial space `W_w`. For even `w`
and `n > 0` over a field of characteristic zero, the trace is

`σ_{w+1}(n) - ∑_{ad=n} min(a,d)^{w+1} - ∑_{t²≤4n} H(4n-t²) P_{w+2}(t,n)`.

Here Popa–Zagier's `P_{w+2}(t,n)` is `(dickson 2 n w).eval t`, the degree-`w`
second-kind Dickson polynomial evaluated at `t`. The convention `H(0) = -1/12` absorbs the
repeated-root contribution: when `n = a²` is a square (`a > 0`), the parabolic weights `2` at
`t = 2a` and `0` at `t = -2a` divide by `12` to give `(1/6) P_{w+2}(2a, n)`, matching
`-H(0) P_{w+2}(2a, n) - H(0) P_{w+2}(-2a, n)` by even parity of `P_{w+2}`. For `w > 0`, the trace
is on `W_w`, not on cusp forms: the latter requires the Hecke-equivariant Eichler–Shimura
comparison and subtraction of the Eisenstein eigenvalue `σ_{w+1}(n)`, followed by division by two.

The inputs are the fixed-trace assembly in `ExplicitElement.Trace` and the elliptic,
hyperbolic and repeated-root fibre evaluations. Pairing the fibres of traces `t` and `-t`
removes the sign asymmetry of the explicit representative. Split hyperbolic traces correspond
to unordered positive factorizations `n = ad`; the Dickson root formula changes their
contribution into `d^{w+1} - a^{w+1}`.

In degree `w = 0`, every matrix acts trivially on constant binary forms, so `tr(Tₙ | V_0)` is also
the sum of the coefficients of `Tₙ`, namely `-σ₁(n)` since `ℳₙ` decomposes into `σ₁(n)` right
cosets of `PSL(2, ℤ)` and each right coset sum is `-1`. Comparing the two evaluations of
`tr(Tₙ | V_0)` gives the **Kronecker–Hurwitz class number relation**

`(∑_{|t| ≤ √(4 n)} H(4 n - t²)) + ∑_{a d = n} min(a, d) = 2 ∑_{d ∣ n} d`.

At `n = 1` and positive even `w`, the trace formula on `W_w` simplifies to `dim W_w`; at `n = 2`
and `w = 10` (weight `12`), it evaluates to `2001 = σ₁₁(2) + 2 · (-24)`.

## Main results

* `trace_periodAction_popaZagierElement_eq_sigma_sub_min_sub_hurwitzClassNumber` and
  `trace_periodActionRestrict_popaZagierElement_eq_sigma_sub_min_sub_hurwitzClassNumber`
  (in `TauCeti.TraceFormulaMatrixModule`): the class-number trace formula on `V_w` (for even `w`)
  and on `W_w` (for positive even `w`).
* `TauCeti.TraceFormulaMatrixModule.trace_periodAction_popaZagierElement_zero`: in degree `0`,
  `tr(Tₙ | V_0) = -∑_{d ∣ n} d`.
* `TauCeti.sum_Icc_hurwitzClassNumber_add_sum_divisorsAntidiagonal_min`: the Kronecker–Hurwitz
  class number relation.
* `TauCeti.TraceFormulaMatrixModule.trace_periodActionRestrict_popaZagierElement_one` and
  `TauCeti.TraceFormulaMatrixModule.trace_periodActionRestrict_popaZagierElement_two_ten`: the
  specialisations `n = 1` (`tr(T₁ | W_w) = dim W_w`) and `n = 2, w = 10` (`tr(T₂ | W₁₀) = 2001`).

## References

* A. Popa and D. Zagier, *An elementary proof of the Eichler–Selberg trace formula*,
  J. Reine Angew. Math. **762** (2020), 105–122, arXiv:1711.00327, §§1, 2, 4, eqs. (2) and (15),
  Theorem 4.
* D. Zagier, *Nombres de classes et formes modulaires de poids 3/2*, C. R. Acad. Sci. Paris
  Sér. A-B **281** (1975), 883–886.
* D. Zagier, *The Eichler–Selberg trace formula on `SL₂(ℤ)`*, appendix to S. Lang,
  *Introduction to Modular Forms*, Springer, 1976, for the convention `H(0) = -1/12`.
-/

public section

open Matrix MvPolynomial Polynomial
open scoped ArithmeticFunction.sigma

namespace TauCeti

namespace TraceFormulaMatrixModule

private noncomputable def fibreWeight (t n : ℤ) : ℚ :=
  ∑ᶠ A : traceDetFiber (Fin 2) t n, (PopaZagier.weight A.1 : ℚ)

private lemma fibreWeight_cast (t n : ℤ) :
    fibreWeight t n = (∑ᶠ A : traceDetFiber (Fin 2) t n, PopaZagier.weight A.1 : ℤ) := by
  exact (map_finsum (Int.castAddHom ℚ) (PopaZagier.finite_support_weight_traceDetFiber t n)).symm

private lemma fibreWeight_pair_of_sq_le (n : ℕ) (hn : 0 < n) (t : ℤ)
    (hD : t ^ 2 ≤ 4 * n) :
    fibreWeight t n + fibreWeight (-t) n =
      -24 * hurwitzClassNumber (4 * n - t ^ 2).toNat := by
  rcases hD.lt_or_eq with hD | hD
  · have : NeZero (4 * (n : ℤ) - t ^ 2).toNat := ⟨by omega⟩
    have heq : t ^ 2 - 4 * (n : ℤ) = -((4 * (n : ℤ) - t ^ 2).toNat : ℤ) := by omega
    rw [fibreWeight, fibreWeight,
      PopaZagier.finsum_weight_traceDetFiber_eq_neg_twelve_mul_hurwitzClassNumber heq,
      PopaZagier.finsum_weight_traceDetFiber_eq_neg_twelve_mul_hurwitzClassNumber
        (t := -t) (by nlinarith : (-t) ^ 2 - 4 * (n : ℤ) =
          -((4 * (n : ℤ) - t ^ 2).toNat : ℤ))]
    ring
  · -- At the boundary the two fibre weights sum to 2 = -24 H(0).
    have hnp : (0 : ℤ) < n := by exact_mod_cast hn
    have ht : t ≠ 0 := by rintro rfl; omega
    have hzero : 4 * (n : ℤ) - t ^ 2 = 0 := by omega
    rw [fibreWeight_cast, fibreWeight_cast,
      PopaZagier.finsum_weight_traceDetFiber_of_discrim_eq_zero hnp (by omega),
      PopaZagier.finsum_weight_traceDetFiber_of_discrim_eq_zero hnp (by nlinarith), hzero]
    by_cases htpos : 0 < t
    · simp only [htpos, ite_true, Int.toNat_zero, hurwitzClassNumber_zero,
        ite_eq_right (by omega : ¬0 < -t)]
      norm_num
    · simp only [htpos, ite_false, Int.toNat_zero, hurwitzClassNumber_zero,
        ite_eq_left (by omega : 0 < -t)]
      norm_num

private lemma fibreWeight_pair_of_factorPair (n : ℕ) (hn : 0 < n) (p : ℕ × ℕ)
    (hp : p ∈ n.divisorsAntidiagonal) (hlt : p.1 < p.2) :
    fibreWeight ((p.1 : ℤ) + p.2) n + fibreWeight (-((p.1 : ℤ) + p.2)) n =
      12 * ((p.2 : ℚ) - p.1) := by
  have hnp : (0 : ℤ) < n := by exact_mod_cast hn
  have ha := Nat.pos_of_mem_divisors (Nat.fst_mem_divisors_of_mem_antidiagonal hp)
  have hmul : (p.1 : ℤ) * p.2 = n := by
    exact_mod_cast (Nat.mem_divisorsAntidiagonal.mp hp).1
  have hspos : (0 : ℤ) < (p.1 : ℤ) + p.2 := by omega
  have hdisc : ((p.1 : ℤ) + p.2) ^ 2 - 4 * n = ((p.2 : ℤ) - p.1) ^ 2 := by nlinarith
  rw [fibreWeight_cast, fibreWeight_cast,
    PopaZagier.finsum_weight_traceDetFiber_of_discrim_eq_sq hnp (by omega) hdisc,
    PopaZagier.finsum_weight_traceDetFiber_of_discrim_eq_sq hnp (by omega)
      (u := (p.2 : ℤ) - p.1) (t := -((p.1 : ℤ) + p.2)) (by nlinarith)]
  simp [hspos]

private lemma fibreWeight_pair_of_not_isSquare (n : ℕ) (t : ℤ)
    (hD : 4 * (n : ℤ) < t ^ 2) (hnsq : ¬IsSquare (t ^ 2 - 4 * (n : ℤ))) :
    fibreWeight t n + fibreWeight (-t) n = 0 := by
  rw [fibreWeight_cast, fibreWeight_cast,
    PopaZagier.finsum_weight_traceDetFiber_of_not_isSquare (by omega) hnsq,
    PopaZagier.finsum_weight_traceDetFiber_of_not_isSquare (by nlinarith)
      (by simpa using hnsq)]
  norm_num

private lemma fibreWeight_pair_eq_sum_of_factorPair (n : ℕ) (hn : 0 < n) (t : ℤ)
    (p : ℕ × ℕ) (hp : p ∈ n.divisorsAntidiagonal.filter (fun p ↦ p.1 < p.2))
    (ht : t = (p.1 : ℤ) + p.2 ∨ -t = (p.1 : ℤ) + p.2) :
    fibreWeight t n + fibreWeight (-t) n =
      12 * ∑ q ∈ n.divisorsAntidiagonal with q.1 < q.2,
        if t = (q.1 : ℤ) + q.2 ∨ -t = (q.1 : ℤ) + q.2 then (q.2 : ℚ) - q.1 else 0 := by
  classical
  -- The increasing factor pair with this absolute trace is unique.
  rw [Finset.sum_eq_single p]
  · rw [ite_eq_left ht]
    obtain ⟨hpmem, hlt⟩ := Finset.mem_filter.mp hp
    have heval := fibreWeight_pair_of_factorPair n hn p hpmem hlt
    rcases ht with ht | ht
    · simpa only [ht] using heval
    · have ht' : t = -((p.1 : ℤ) + p.2) := by omega
      simpa only [ht', neg_neg, add_comm] using heval
  · intro q hq hqp
    apply ite_eq_right
    intro hqt
    have hplt := (Finset.mem_filter.mp hp).2
    have hqlt := (Finset.mem_filter.mp hq).2
    apply hqp
    apply Nat.injOn_add_divisorsAntidiagonal_filter_lt n hq hp
    dsimp only
    rcases ht with ht | ht <;> rcases hqt with hqt | hqt <;> omega
  · exact fun h ↦ (h hp).elim

private lemma fibreWeight_pair (n : ℕ) (hn : 0 < n) (t : ℤ) :
    fibreWeight t n + fibreWeight (-t) n =
      -24 * (if t ^ 2 ≤ 4 * n then hurwitzClassNumber (4 * n - t ^ 2).toNat else 0) +
      12 * ∑ p ∈ n.divisorsAntidiagonal with p.1 < p.2,
        if t = (p.1 : ℤ) + p.2 ∨ -t = (p.1 : ℤ) + p.2 then (p.2 : ℚ) - p.1 else 0 := by
  classical
  set s := n.divisorsAntidiagonal.filter (fun p ↦ p.1 < p.2) with hs
  -- In the elliptic range no increasing factor pair can have trace ±t.
  by_cases hD : t ^ 2 ≤ 4 * n
  · have hz : ∑ p ∈ s,
        (if t = (p.1 : ℤ) + p.2 ∨ -t = (p.1 : ℤ) + p.2 then (p.2 : ℚ) - p.1 else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro p hp
      obtain ⟨hpmem, hlt⟩ := Finset.mem_filter.mp hp
      have hmul : (p.1 : ℤ) * p.2 = n := by
        exact_mod_cast (Nat.mem_divisorsAntidiagonal.mp hpmem).1
      apply ite_eq_right
      intro ht
      have hdiff : (0 : ℤ) < (p.2 : ℤ) - p.1 := by omega
      rcases ht with ht | ht <;> nlinarith [sq_pos_of_pos hdiff]
    rw [hz, ite_eq_left hD, mul_zero, add_zero]
    exact fibreWeight_pair_of_sq_le n hn t hD
  · rw [ite_eq_right hD, mul_zero, zero_add]
    -- Split traces have one increasing factor pair; nonsplit traces have none.
    by_cases hex : ∃ p ∈ s, t = (p.1 : ℤ) + p.2 ∨ -t = (p.1 : ℤ) + p.2
    · obtain ⟨p, hp, ht⟩ := hex
      exact fibreWeight_pair_eq_sum_of_factorPair n hn t p hp ht
    · have hsum : ∑ p ∈ s,
          (if t = (p.1 : ℤ) + p.2 ∨ -t = (p.1 : ℤ) + p.2 then (p.2 : ℚ) - p.1 else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro p hp
        exact ite_eq_right (fun ht ↦ hex ⟨p, hp, ht⟩)
      rw [hsum, mul_zero]
      apply fibreWeight_pair_of_not_isSquare n t (by omega)
      intro hsquare
      obtain ⟨p, hp, hlt, ht⟩ :=
        (Int.isSquare_sq_sub_four_mul_iff_exists_mem_divisorsAntidiagonal n hn t
          (by omega)).mp hsquare
      apply hex
      refine ⟨p, Finset.mem_filter.mpr ⟨hp, hlt⟩, ?_⟩
      rcases le_or_gt 0 t with ht0 | ht0
      · left; simpa only [abs_of_nonneg ht0] using ht
      · right; simpa only [abs_of_neg ht0] using ht

-- This is the split contribution in the paired-fibre formula, summed over its trace window.
private lemma sum_split_trace_mul_dickson (n w : ℕ) (hw : Even w) (p : ℕ × ℕ)
    (hp : p ∈ n.divisorsAntidiagonal.filter (fun p ↦ p.1 < p.2)) :
    ∑ t ∈ Finset.Icc (-4 * (n : ℤ)) (4 * n),
      (if t = (p.1 : ℤ) + p.2 ∨ -t = (p.1 : ℤ) + p.2 then (p.2 : ℚ) - p.1 else 0) *
        (dickson 2 (n : ℚ) w).eval (t : ℚ) =
      2 * ((p.2 : ℚ) ^ (w + 1) - (p.1 : ℚ) ^ (w + 1)) := by
  classical
  set I := Finset.Icc (-4 * (n : ℤ)) (4 * n)
  let P (t : ℤ) : ℚ := (dickson 2 (n : ℚ) w).eval t
  obtain ⟨hp, hlt⟩ := Finset.mem_filter.mp hp
  have ha := Nat.pos_of_mem_divisors (Nat.fst_mem_divisors_of_mem_antidiagonal hp)
  have hm := (Nat.mem_divisorsAntidiagonal.mp hp).1
  have hs : (0 : ℤ) < (p.1 : ℤ) + p.2 := by omega
  have ha_le := Nat.divisor_le (Nat.fst_mem_divisors_of_mem_antidiagonal hp)
  have hd_le := Nat.divisor_le (Nat.snd_mem_divisors_of_mem_antidiagonal hp)
  have hmem : (p.1 : ℤ) + p.2 ∈ I := by simp only [I, Finset.mem_Icc]; omega
  have hmem' : -((p.1 : ℤ) + p.2) ∈ I := by simp only [I, Finset.mem_Icc]; omega
  -- The two traces are distinct, so the indicator splits without a trace-zero correction.
  have hind (t : ℤ) :
      (if t = (p.1 : ℤ) + p.2 ∨ -t = (p.1 : ℤ) + p.2 then (p.2 : ℚ) - p.1 else 0) * P t =
        (if t = (p.1 : ℤ) + p.2 then ((p.2 : ℚ) - p.1) * P t else 0) +
        (if t = -((p.1 : ℤ) + p.2) then ((p.2 : ℚ) - p.1) * P t else 0) := by
    by_cases ht : t = (p.1 : ℤ) + p.2
    · have hneg : t ≠ -((p.1 : ℤ) + p.2) := by omega
      rw [ite_eq_left (Or.inl ht), ite_eq_left ht, ite_eq_right hneg, add_zero]
    · by_cases htneg : t = -((p.1 : ℤ) + p.2)
      · have heq : -t = (p.1 : ℤ) + p.2 := by omega
        rw [ite_eq_left (Or.inr heq), ite_eq_right ht, ite_eq_left htneg, zero_add]
      · have hne : -t ≠ (p.1 : ℤ) + p.2 := by omega
        simp only [ht, htneg, hne, or_self, ite_false, zero_mul, add_zero]
  rw [Finset.sum_congr rfl (fun t _ ↦ hind t), Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', hmem, hmem', ite_true]
  have hPneg (t : ℤ) : P (-t) = P t := by
    simpa only [P, Int.cast_neg] using dickson_eval_neg_of_even 2 (n : ℚ) (t : ℚ) hw
  rw [hPneg]
  have hm' : (p.2 : ℚ) * p.1 = n := by exact_mod_cast (mul_comm _ _).trans hm
  have hroot := dickson_two_eval_add_mul_sub hm' w
  have heval : P ((p.1 : ℤ) + p.2) = (dickson 2 (n : ℚ) w).eval ((p.2 : ℚ) + p.1) := by
    simp [P, add_comm]
  rw [heval]
  linarith

private lemma sum_fibreWeight (n : ℕ) (hn : 0 < n) (w : ℕ) (hw : Even w) :
    (12 : ℚ)⁻¹ * ∑ t ∈ Finset.Icc (-4 * (n : ℤ)) (4 * n),
      fibreWeight t n * (dickson 2 (n : ℚ) w).eval (t : ℚ) =
      (ArithmeticFunction.sigma (w + 1) n : ℚ) -
        (∑ p ∈ n.divisorsAntidiagonal, ((min p.1 p.2 : ℕ) : ℚ) ^ (w + 1)) -
        ∑ t ∈ (Finset.Icc (-4 * (n : ℤ)) (4 * n)).filter (fun t ↦ t ^ 2 ≤ 4 * (n : ℤ)),
          hurwitzClassNumber (4 * (n : ℤ) - t ^ 2).toNat * (dickson 2 (n : ℚ) w).eval (t : ℚ) := by
  classical
  let I := Finset.Icc (-4 * (n : ℤ)) (4 * n)
  let P (t : ℤ) : ℚ := (dickson 2 (n : ℚ) w).eval t
  have hPneg (t : ℤ) : P (-t) = P t := by
    simpa only [P, Int.cast_neg] using dickson_eval_neg_of_even 2 (n : ℚ) (t : ℚ) hw
  let s := n.divisorsAntidiagonal.filter (fun p ↦ p.1 < p.2)
  have hneg : ∑ t ∈ I, fibreWeight (-t) n * P t = ∑ t ∈ I, fibreWeight t n * P t := by
    apply Finset.sum_bij (fun t _ ↦ -t)
    · intro t ht; simp only [I, Finset.mem_Icc] at ht ⊢; omega
    · intro t _ u _ h; omega
    · intro t ht; exact ⟨-t, by simp only [I, Finset.mem_Icc] at ht ⊢; omega, neg_neg t⟩
    · intro t _; rw [hPneg]
  -- Sum the paired-fibre identity and exchange the two finite sums in the split part.
  have hsym := Finset.sum_congr rfl fun t (_ : t ∈ I) ↦
    congrArg (fun x : ℚ ↦ x * P t) (fibreWeight_pair n hn t)
  simp only [add_mul, Finset.sum_add_distrib, hneg, Finset.sum_mul, mul_assoc,
    ← Finset.mul_sum] at hsym
  have hswap : (∑ t ∈ I, ∑ p ∈ s,
      (if t = (p.1 : ℤ) + p.2 ∨ -t = (p.1 : ℤ) + p.2 then (p.2 : ℚ) - p.1 else 0) * P t) =
      2 * ∑ p ∈ s, ((p.2 : ℚ) ^ (w + 1) - (p.1 : ℚ) ^ (w + 1)) := by
    rw [Finset.sum_comm, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun p hp ↦ sum_split_trace_mul_dickson n w hw p hp)
  have hclass : (∑ t ∈ I, (if t ^ 2 ≤ 4 * n then
      hurwitzClassNumber (4 * (n : ℤ) - t ^ 2).toNat else 0) * P t) =
      ∑ t ∈ I.filter (fun t ↦ t ^ 2 ≤ 4 * (n : ℤ)),
        hurwitzClassNumber (4 * (n : ℤ) - t ^ 2).toNat * P t := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro t _
    split_ifs <;> simp
  -- Symmetrization counts each matrix trace twice, including trace zero.
  have hsym' : 2 * (∑ t ∈ I, fibreWeight t n * P t) =
      -24 * (∑ t ∈ I.filter (fun t ↦ t ^ 2 ≤ 4 * (n : ℤ)),
        hurwitzClassNumber (4 * (n : ℤ) - t ^ 2).toNat * P t) +
      24 * (∑ p ∈ s, ((p.2 : ℚ) ^ (w + 1) - (p.1 : ℚ) ^ (w + 1))) := by
    rw [hswap, hclass] at hsym
    linear_combination hsym
  dsimp only [s] at hsym'
  rw [Nat.sum_divisorsAntidiagonal_filter_sub n (fun d ↦ (d : ℚ) ^ (w + 1))] at hsym'
  have hsigma : (∑ d ∈ n.divisors, (d : ℚ) ^ (w + 1)) =
      (ArithmeticFunction.sigma (w + 1) n : ℚ) := by
    simp [ArithmeticFunction.sigma_apply, Nat.cast_sum, Nat.cast_pow]
  rw [hsigma] at hsym'
  dsimp only [I, P] at hsym'
  linarith

/-- **The class-number trace formula on binary forms.** Over a characteristic-zero field `K`, for
every even degree `w` (including `w = 0`) and `n > 0`, Popa–Zagier's explicit element `Tₙ` has
trace `σ_{w+1}(n)` minus the divisor-minimum sum and the Hurwitz-class-number sum on the space
`V_w` of degree-`w` binary forms, with `H(0) = -1/12` at discriminant zero. -/
theorem trace_periodAction_popaZagierElement_eq_sigma_sub_min_sub_hurwitzClassNumber
    {K : Type*} [Field K] [CharZero K] (n : ℕ) (hn : 0 < n)
    (w : ℕ) (hw : Even w) :
    LinearMap.trace K (homogeneousSubmodule (Fin 2) K w)
        (periodAction hw (popaZagierElement K (n : ℤ))) =
      (ArithmeticFunction.sigma (w + 1) n : K) -
        (∑ p ∈ n.divisorsAntidiagonal, ((min p.1 p.2 : ℕ) : K) ^ (w + 1)) -
        ∑ t ∈ (Finset.Icc (-4 * (n : ℤ)) (4 * n)).filter (fun t ↦ t ^ 2 ≤ 4 * (n : ℤ)),
          (hurwitzClassNumber (4 * (n : ℤ) - t ^ 2).toNat : K) *
            (dickson 2 (n : K) w).eval (t : K) := by
  classical
  have hP (t : ℤ) : (Rat.castHom K) ((dickson 2 (n : ℚ) w).eval (t : ℚ)) =
      (dickson 2 (n : K) w).eval (t : K) := by
    simpa only [map_dickson, map_natCast, map_intCast] using
      (eval_map_apply (Rat.castHom K) (p := dickson 2 (n : ℚ) w) (t : ℚ)).symm
  have h := congrArg (Rat.castHom K) (sum_fibreWeight n hn w hw)
  simp only [map_mul, map_inv₀, map_ofNat, map_sum, map_sub, map_natCast, map_pow,
    fibreWeight_cast, map_intCast, hP] at h
  rw [trace_periodAction_popaZagierElement_eq_sum_trace_fibres (by exact_mod_cast hn.ne') w hw]
  simpa only [Rat.coe_castHom, Rat.cast_natCast, Int.cast_natCast] using h

/-- **The class-number trace formula on period polynomials.** For positive even degree `w`,
Popa–Zagier's explicit Hecke element has trace `σ_{w+1}(n)` minus the divisor-minimum sum and
the Hurwitz-class-number sum, whose weight `P_{w+2}(t,n)` in Popa–Zagier's indexing is
`(dickson 2 n w).eval t`. The discriminant-zero terms use `H(0) = -1/12`. This is the trace
on the full space `W_w`, before the Eichler–Shimura transfer to cusp forms. -/
theorem trace_periodActionRestrict_popaZagierElement_eq_sigma_sub_min_sub_hurwitzClassNumber
    {K : Type*} [Field K] [CharZero K] (n : ℕ) (hn : 0 < n)
    (w : ℕ) (hw : Even w) (hw₀ : w ≠ 0) :
    LinearMap.trace K (periodPolynomials K w)
        ((exchangeRelations_popaZagierElement K (n : ℤ)).periodActionRestrict hw) =
      (ArithmeticFunction.sigma (w + 1) n : K) -
        (∑ p ∈ n.divisorsAntidiagonal, ((min p.1 p.2 : ℕ) : K) ^ (w + 1)) -
        ∑ t ∈ (Finset.Icc (-4 * (n : ℤ)) (4 * n)).filter (fun t ↦ t ^ 2 ≤ 4 * (n : ℤ)),
          (hurwitzClassNumber (4 * (n : ℤ) - t ^ 2).toNat : K) *
            (dickson 2 (n : K) w).eval (t : K) := by
  rw [(exchangeRelations_popaZagierElement K (n : ℤ)).trace_periodActionRestrict_eq_trace hw hw₀,
    trace_periodAction_popaZagierElement_eq_sigma_sub_min_sub_hurwitzClassNumber n hn w hw]

private lemma filter_sq_le_four_mul_eq_Icc_sqrt (n : ℕ) :
    (Finset.Icc (-4 * (n : ℤ)) (4 * n)).filter (fun t ↦ t ^ 2 ≤ 4 * (n : ℤ)) =
      Finset.Icc (-(Nat.sqrt (4 * n) : ℤ)) (Nat.sqrt (4 * n)) := by
  have hs (t : ℤ) : t ∈ Finset.Icc (-(Nat.sqrt (4 * n) : ℤ)) (Nat.sqrt (4 * n)) ↔
      t ^ 2 ≤ 4 * (n : ℤ) := by
    rw [Finset.mem_Icc, ← abs_le, ← Int.sqrt_natCast,
      Int.abs_le_sqrt_iff_sq_le (Nat.cast_nonneg (4 * n)), Nat.cast_mul, Nat.cast_ofNat]
  have hle : (Nat.sqrt (4 * n) : ℤ) ≤ 4 * (n : ℤ) := by
    exact_mod_cast Nat.sqrt_le_self (4 * n)
  ext t
  simp only [Finset.mem_filter, Finset.mem_Icc, hs]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨by have := Finset.mem_Icc.mp ((hs t).mpr h); omega, h⟩⟩

/-- In degree `0`, every matrix acts trivially on `V_0`, so the trace of Popa–Zagier's explicit
element `Tₙ` on `V_0` is the sum of its coefficients, `-∑_{d ∣ n} d`. -/
theorem trace_periodAction_popaZagierElement_zero {K : Type*} [Field K] (h12 : (12 : K) ≠ 0)
    {n : ℕ} (hn : n ≠ 0) :
    LinearMap.trace K (homogeneousSubmodule (Fin 2) K 0)
        (periodAction .zero (popaZagierElement K n)) =
      - ∑ d ∈ n.divisors, (d : K) := by
  have hn' : (0 : ℤ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  rw [trace_periodAction_zero, sum_coeff_popaZagierElement h12 hn', Int.natAbs_natCast,
    ArithmeticFunction.sigma_one_apply, Nat.cast_sum]

end TraceFormulaMatrixModule

open TraceFormulaMatrixModule in
/-- **The Kronecker–Hurwitz class number relation.** For every nonzero natural number `n`,

`(∑_{|t| ≤ √(4 n)} H(4 n - t²)) + ∑_{a d = n} min(a, d) = 2 ∑_{d ∣ n} d`,

where `H` is the Hurwitz class number (`H 0 = -1/12`). It follows from equating the closed-form
trace of Popa–Zagier's explicit element on constant binary forms (`w = 0`, where `P_2(t, n) = 1`)
with its coefficient sum `-σ₁(n)`. -/
theorem sum_Icc_hurwitzClassNumber_add_sum_divisorsAntidiagonal_min {n : ℕ} (hn : n ≠ 0) :
    (∑ t ∈ Finset.Icc (-(Nat.sqrt (4 * n) : ℤ)) (Nat.sqrt (4 * n)),
        hurwitzClassNumber (4 * (n : ℤ) - t ^ 2).toNat) +
      (∑ p ∈ n.divisorsAntidiagonal, (↑(min p.1 p.2) : ℚ)) =
    2 * ∑ d ∈ n.divisors, (d : ℚ) := by
  have h :=
    trace_periodAction_popaZagierElement_eq_sigma_sub_min_sub_hurwitzClassNumber
      (K := ℚ) n (Nat.pos_of_ne_zero hn) 0 .zero
  rw [trace_periodAction_popaZagierElement_zero (by norm_num) hn,
    filter_sq_le_four_mul_eq_Icc_sqrt] at h
  have hd0 (t : ℤ) : (dickson 2 (n : ℚ) 0).eval (t : ℚ) = 1 := by norm_num
  simp only [zero_add, pow_one, hd0, mul_one, Rat.cast_id,
    ArithmeticFunction.sigma_one_apply, Nat.cast_sum] at h
  linear_combination h

namespace TraceFormulaMatrixModule

/-- **At `n = 1`, the trace of Popa–Zagier's explicit element on `W_w` equals `dim W_w`** for
positive even `w` over a field of characteristic zero: the `t = ±2`, `0`, `±1` terms evaluate via
`H 0 = -1/12`, `H 4 = 1/2`, `H 3 = 1/3` and the periodic values `P_{w+2}(0, 1)` and
`P_{w+2}(±1, 1)` to `2 ⌈w / 4⌉ + 2 ⌈w / 3⌉ - (w + 1)`. -/
theorem trace_periodActionRestrict_popaZagierElement_one {K : Type*} [Field K] [CharZero K]
    {w : ℕ} (hw : Even w) (hw₀ : w ≠ 0) :
    LinearMap.trace K (periodPolynomials K w)
        ((exchangeRelations_popaZagierElement K 1).periodActionRestrict hw) =
      (Module.finrank K (periodPolynomials K w) : K) := by
  have hsqrt : (4 * 1).sqrt = 2 := (Nat.eq_sqrt.mpr (by decide)).symm
  have hIcc : Finset.Icc (-2 : ℤ) 2 = {-2, -1, 0, 1, 2} := by decide
  have hp2 : (dickson 2 (1 : K) w).eval 2 = w + 1 := by
    simpa using dickson_two_sq_eval_two_mul (1 : K) w
  have htr :=
    trace_periodActionRestrict_popaZagierElement_eq_sigma_sub_min_sub_hurwitzClassNumber
      (K := K) 1 one_pos w hw hw₀
  rw [filter_sq_le_four_mul_eq_Icc_sqrt, Nat.cast_one] at htr
  rw [htr, hsqrt, Nat.cast_ofNat, hIcc,
    ArithmeticFunction.sigma_apply, Nat.divisors_one, Nat.divisorsAntidiagonal_one]
  norm_num [hurwitzClassNumber_zero, hurwitzClassNumber_three, hurwitzClassNumber_four, hw, hp2]
  have hW := congrArg (Nat.cast : ℕ → K) (finrank_periodPolynomials_add_eq (K := K) hw hw₀)
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r,
      (r = 0 ∨ r = 2 ∨ r = 4 ∨ r = 6 ∨ r = 8 ∨ r = 10) ∧ w = 12 * q + r :=
    ⟨w / 12, w % 12, by obtain ⟨m, rfl⟩ := hw; omega, (Nat.div_add_mod w 12).symm⟩
  have h12q : 12 * q + r = 6 * (2 * q) + r := by ring
  have h1 : (dickson 2 (1 : K) (12 * q + r)).eval 1 =
      (dickson 2 (1 : K) r).eval 1 := by
    rw [h12q, dickson_two_one_eval_one_six_mul_add]
  rw [h1]
  have h4 : (12 * q + r + 3) / 4 = 3 * q + (r + 3) / 4 := by omega
  have h3 : (12 * q + r + 2) / 3 = 4 * q + (r + 2) / 3 := by omega
  have hev : 12 * q + r = 2 * (6 * q + r / 2) := by
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  have h0 : (dickson 2 (1 : K) (12 * q + r)).eval 0 =
      (-1 : K) ^ (6 * q + r / 2) := by
    rw [hev, dickson_two_eval_zero_two_mul]
  rw [h4, h3] at hW
  rw [h0, pow_add, Even.neg_one_pow ⟨3 * q, by ring⟩, one_mul]
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
  · norm_num [dickson_two, dickson_add_two]
    push_cast at hW ⊢
    linear_combination -hW

/-- **At `n = 2` and `w = 10` (weight `12`), the trace of Popa–Zagier's explicit element on `W₁₀`
equals `2001`** (`= σ₁₁(2) + 2 · (-24)`, matching Ramanujan's `τ(2) = -24` on `S₁₂ = ℂ Δ`). -/
theorem trace_periodActionRestrict_popaZagierElement_two_ten {K : Type*} [Field K] [CharZero K] :
    LinearMap.trace K (periodPolynomials K 10)
        ((exchangeRelations_popaZagierElement K 2).periodActionRestrict ⟨5, rfl⟩) = 2001 := by
  have hsqrt : (4 * 2).sqrt = 2 := (Nat.eq_sqrt.mpr (by decide)).symm
  have hIcc : Finset.Icc (-2 : ℤ) 2 = {-2, -1, 0, 1, 2} := by decide
  have hdiv : (2 : ℕ).divisors = {1, 2} := by decide
  have hanti : (2 : ℕ).divisorsAntidiagonal = {(1, 2), (2, 1)} := by decide
  have htr :=
    trace_periodActionRestrict_popaZagierElement_eq_sigma_sub_min_sub_hurwitzClassNumber
      (K := K) 2 (by decide) 10 ⟨5, rfl⟩ (by decide)
  rw [filter_sq_le_four_mul_eq_Icc_sqrt, Nat.cast_ofNat] at htr
  rw [htr, hsqrt, Nat.cast_ofNat, hIcc,
    ArithmeticFunction.sigma_apply, hdiv, hanti]
  norm_num [hurwitzClassNumber_four, hurwitzClassNumber_seven, hurwitzClassNumber_eight,
    dickson_add_two, dickson_two]

end TraceFormulaMatrixModule

end TauCeti

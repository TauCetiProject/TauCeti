/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.LevelOne.TraceFormula.ExplicitElement.Trace
public import TauCeti.NumberTheory.HurwitzClassNumber
import TauCeti.NumberTheory.ModularForms.LevelOne.TraceFormula.ExplicitElement.Hyperbolic
import TauCeti.NumberTheory.ModularForms.LevelOne.TraceFormula.ExplicitElement.Parabolic
import TauCeti.NumberTheory.Divisors

/-!
# The class-number trace formula on period polynomials

This file assembles the trace of Popa–Zagier's explicit element on the full period-polynomial
space `W_w`. For positive even `w` and `n > 0`, it is

`σ_{w+1}(n) - ∑_{ad=n} min(a,d)^{w+1} - ∑_{t²≤4n} H(4n-t²) P_{w+2}(t,n)`.

Here Popa–Zagier's `P_{w+2}(t,n)` is `(dickson 2 n w).eval t`, the degree-`w`
second-kind Dickson polynomial evaluated at `t`. The convention `H(0) = -1/12` absorbs the
repeated-root contribution. The trace is on `W_w`, not on cusp forms: the latter requires the
Hecke-equivariant Eichler–Shimura comparison and subtraction of the Eisenstein eigenvalue,
followed by division by two.

The inputs are the fixed-trace assembly in `ExplicitElement.Trace` and the elliptic,
hyperbolic and repeated-root fibre evaluations. Pairing the fibres of traces `t` and `-t`
removes the sign asymmetry of the explicit representative. Split hyperbolic traces correspond
to unordered positive factorizations `n = ad`; the Dickson root formula changes their
contribution into `d^{w+1} - a^{w+1}`.

## References

* A. Popa and D. Zagier, *An elementary proof of the Eichler–Selberg trace formula*,
  J. Reine Angew. Math. **762** (2020), 105–122, arXiv:1711.00327, §§2, 4.
* D. Zagier, *The Eichler–Selberg trace formula on SL₂(ℤ)*, appendix to S. Lang,
  *Introduction to Modular Forms*, for the convention `H(0) = -1/12`.
-/

public section

open Matrix Polynomial
open scoped ArithmeticFunction.sigma

namespace TauCeti.TraceFormulaMatrixModule

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
  classical
  have hP (t : ℤ) : (Rat.castHom K) ((dickson 2 (n : ℚ) w).eval (t : ℚ)) =
      (dickson 2 (n : K) w).eval (t : K) := by
    simpa only [map_dickson, map_natCast, map_intCast] using
      (eval_map_apply (Rat.castHom K) (p := dickson 2 (n : ℚ) w) (t : ℚ)).symm
  have h := congrArg (Rat.castHom K) (sum_fibreWeight n hn w hw)
  simp only [map_mul, map_inv₀, map_ofNat, map_sum, map_sub, map_natCast, map_pow,
    fibreWeight_cast, map_intCast, hP] at h
  rw [trace_periodActionRestrict_popaZagierElement_eq_sum_trace_fibres
    (by exact_mod_cast hn.ne') w hw hw₀]
  simpa only [Rat.coe_castHom, Rat.cast_natCast, Int.cast_natCast] using h

end TauCeti.TraceFormulaMatrixModule

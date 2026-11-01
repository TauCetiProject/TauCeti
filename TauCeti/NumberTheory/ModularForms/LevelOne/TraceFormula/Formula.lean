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

Here `P` is Mathlib's second-kind Dickson polynomial, and `H(0) = -1/12` absorbs the
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

private lemma fibreWeight_pair (n : ℕ) (hn : 0 < n) (t : ℤ) :
    fibreWeight t n + fibreWeight (-t) n =
      -24 * (if t ^ 2 ≤ 4 * n then hurwitzClassNumber (4 * n - t ^ 2).toNat else 0) +
      12 * ∑ p ∈ n.divisorsAntidiagonal with p.1 < p.2,
        if t = (p.1 : ℤ) + p.2 ∨ -t = (p.1 : ℤ) + p.2 then (p.2 : ℚ) - p.1 else 0 := by
  classical
  have hnp : (0 : ℤ) < n := by exact_mod_cast hn
  let s := n.divisorsAntidiagonal.filter (fun p ↦ p.1 < p.2)
  have hpair (p : ℕ × ℕ) (hp : p ∈ s) :
      4 * (n : ℤ) < ((p.1 : ℤ) + p.2) ^ 2 := by
    obtain ⟨hp, hlt⟩ := Finset.mem_filter.mp hp
    have hmul : (p.1 : ℤ) * p.2 = n := by
      exact_mod_cast (Nat.mem_divisorsAntidiagonal.mp hp).1
    nlinarith [sq_pos_of_pos (show (0 : ℤ) < (p.2 : ℤ) - p.1 by omega)]
  -- In the elliptic range no positive unequal factor pair can have trace ±t.
  by_cases hD : t ^ 2 ≤ 4 * n
  · have hz : ∑ p ∈ s,
        (if t = (p.1 : ℤ) + p.2 ∨ -t = (p.1 : ℤ) + p.2 then (p.2 : ℚ) - p.1 else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro p hp
      have := hpair p hp
      split_ifs with ht
      · rcases ht with ht | ht <;> nlinarith
      · rfl
    rw [show (n.divisorsAntidiagonal.filter (fun p ↦ p.1 < p.2)) = s from rfl, hz,
      ite_eq_left hD, mul_zero, add_zero]
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
      have ht : t ≠ 0 := by rintro rfl; omega
      rw [fibreWeight_cast, fibreWeight_cast,
        PopaZagier.finsum_weight_traceDetFiber_of_discrim_eq_zero hnp (by omega),
        PopaZagier.finsum_weight_traceDetFiber_of_discrim_eq_zero hnp (by nlinarith)]
      rw [show 4 * (n : ℤ) - t ^ 2 = 0 by omega]
      simp only [Int.toNat_zero, hurwitzClassNumber_zero]
      split_ifs <;> norm_num at * <;> omega
  · rw [ite_eq_right hD, mul_zero, zero_add]
    -- A split hyperbolic pair is unique; its weight is twelve times the root difference.
    by_cases hex : ∃ p ∈ s, t = (p.1 : ℤ) + p.2 ∨ -t = (p.1 : ℤ) + p.2
    · obtain ⟨p, hp, ht⟩ := hex
      obtain ⟨hpmem, hlt⟩ := Finset.mem_filter.mp hp
      obtain ⟨hmul, _⟩ := Nat.mem_divisorsAntidiagonal.mp hpmem
      have ha : 0 < p.1 := Nat.pos_of_ne_zero (by intro h; simp [h] at hmul; omega)
      have hd : 0 < p.2 := by omega
      have hsum : ∑ q ∈ s,
          (if t = (q.1 : ℤ) + q.2 ∨ -t = (q.1 : ℤ) + q.2 then (q.2 : ℚ) - q.1 else 0) =
            (p.2 : ℚ) - p.1 := by
        rw [Finset.sum_eq_single p]
        · exact ite_eq_left ht
        · intro q hq hqp
          apply ite_eq_right
          intro hqt
          obtain ⟨hqmem, hq'⟩ := Finset.mem_filter.mp hq
          have hp0 : (0 : ℤ) < (p.1 : ℤ) + p.2 := by positivity
          have hq0 : (0 : ℤ) < (q.1 : ℤ) + q.2 := by omega
          rcases ht with ht | ht <;> rcases hqt with hqt | hqt
          · exact hqp (Nat.injOn_add_divisorsAntidiagonal n ⟨hqmem, hq'⟩ ⟨hpmem, hlt⟩
              (by dsimp only; omega))
          · omega
          · omega
          · exact hqp (Nat.injOn_add_divisorsAntidiagonal n ⟨hqmem, hq'⟩ ⟨hpmem, hlt⟩
              (by dsimp only; omega))
        · exact fun h ↦ (h hp).elim
      rw [show (n.divisorsAntidiagonal.filter (fun p ↦ p.1 < p.2)) = s from rfl, hsum]
      have hspos : (0 : ℤ) < (p.1 : ℤ) + p.2 := by positivity
      have hdisc : ((p.1 : ℤ) + p.2) ^ 2 - 4 * n = ((p.2 : ℤ) - p.1) ^ 2 := by
        have : (p.1 : ℤ) * p.2 = n := by exact_mod_cast hmul
        nlinarith
      have heval : fibreWeight ((p.1 : ℤ) + p.2) n +
          fibreWeight (-((p.1 : ℤ) + p.2)) n = 12 * ((p.2 : ℚ) - p.1) := by
        rw [fibreWeight_cast, fibreWeight_cast,
          PopaZagier.finsum_weight_traceDetFiber_of_discrim_eq_sq hnp (by omega) hdisc,
          PopaZagier.finsum_weight_traceDetFiber_of_discrim_eq_sq hnp (by omega)
            (u := (p.2 : ℤ) - p.1) (t := -((p.1 : ℤ) + p.2)) (by nlinarith)]
        simp [hspos]
      rcases ht with ht | ht
      · simpa [ht] using heval
      · have ht' : t = -((p.1 : ℤ) + p.2) := by omega
        simpa [ht', add_comm] using heval
    · have hsum : ∑ p ∈ s,
          (if t = (p.1 : ℤ) + p.2 ∨ -t = (p.1 : ℤ) + p.2 then (p.2 : ℚ) - p.1 else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro p hp
        exact ite_eq_right (fun ht ↦ hex ⟨p, hp, ht⟩)
      rw [show (n.divisorsAntidiagonal.filter (fun p ↦ p.1 < p.2)) = s from rfl, hsum, mul_zero]
      -- With no factor pair the discriminant is nonsquare, so both fibres vanish.
      have hnsq : ¬IsSquare (t ^ 2 - 4 * (n : ℤ)) := by
        intro hsquare
        obtain ⟨p, hp, hlt, ht⟩ :=
          (Int.isSquare_sq_sub_four_mul_iff_exists_mem_divisorsAntidiagonal n hn t
            (by omega)).mp hsquare
        apply hex
        refine ⟨p, Finset.mem_filter.mpr ⟨hp, hlt⟩, ?_⟩
        rcases le_or_gt 0 t with ht0 | ht0
        · left; simpa only [abs_of_nonneg ht0] using ht
        · right; simpa only [abs_of_neg ht0] using ht
      rw [fibreWeight_cast, fibreWeight_cast,
        PopaZagier.finsum_weight_traceDetFiber_of_not_isSquare (by omega) hnsq,
        PopaZagier.finsum_weight_traceDetFiber_of_not_isSquare (by nlinarith)
          (by simpa using hnsq)]
      norm_num

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
    have h := dickson_sq_mul_eval_mul 2 (-1 : ℚ) (t : ℚ) n w
    simpa [P, hw.neg_one_pow] using h
  let s := n.divisorsAntidiagonal.filter (fun p ↦ p.1 < p.2)
  have hneg : ∑ t ∈ I, fibreWeight (-t) n * P t = ∑ t ∈ I, fibreWeight t n * P t := by
    apply Finset.sum_bij (fun t _ ↦ -t)
    · intro t ht; simp only [I, Finset.mem_Icc] at ht ⊢; omega
    · intro t _ u _ h; omega
    · intro t ht; exact ⟨-t, by simp only [I, Finset.mem_Icc] at ht ⊢; omega, neg_neg t⟩
    · intro t _; rw [hPneg]
  -- Summing one factor pair over the two traces turns its Dickson value into a power difference.
  have hp (p : ℕ × ℕ) (hp : p ∈ s) :
      ∑ t ∈ I,
        (if t = (p.1 : ℤ) + p.2 ∨ -t = (p.1 : ℤ) + p.2 then (p.2 : ℚ) - p.1 else 0) * P t =
        2 * ((p.2 : ℚ) ^ (w + 1) - (p.1 : ℚ) ^ (w + 1)) := by
    obtain ⟨hp, hlt⟩ := Finset.mem_filter.mp hp
    have hm : p.1 * p.2 = n := (Nat.mem_divisorsAntidiagonal.mp hp).1
    have ha : 0 < p.1 := Nat.pos_of_ne_zero (by intro h; simp [h] at hm; omega)
    have hd : 0 < p.2 := by omega
    have hs : (0 : ℤ) < (p.1 : ℤ) + p.2 := by positivity
    have hbd : (p.1 : ℤ) + p.2 ≤ 4 * n := by
      have hm' : (p.1 : ℤ) * p.2 = n := by exact_mod_cast hm
      nlinarith [mul_nonneg (show (0 : ℤ) ≤ (p.1 : ℤ) - 1 by omega)
        (show (0 : ℤ) ≤ (p.2 : ℤ) - 1 by omega)]
    have hmem : (p.1 : ℤ) + p.2 ∈ I := by simp only [I, Finset.mem_Icc]; omega
    have hmem' : -((p.1 : ℤ) + p.2) ∈ I := by simp only [I, Finset.mem_Icc]; omega
    have hind (t : ℤ) :
        (if t = (p.1 : ℤ) + p.2 ∨ -t = (p.1 : ℤ) + p.2 then (p.2 : ℚ) - p.1 else 0) * P t =
          (if t = (p.1 : ℤ) + p.2 then ((p.2 : ℚ) - p.1) * P t else 0) +
          (if t = -((p.1 : ℤ) + p.2) then ((p.2 : ℚ) - p.1) * P t else 0) := by
      split_ifs <;> simp_all <;> omega
    rw [Finset.sum_congr rfl (fun t _ ↦ hind t), Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq', hmem, hmem', ite_true]
    rw [hPneg]
    have hroot := dickson_two_eval_add_mul_sub
      (show (p.2 : ℚ) * p.1 = n by exact_mod_cast (mul_comm p.2 p.1).trans hm) w
    have heval : P ((p.1 : ℤ) + p.2) = (dickson 2 (n : ℚ) w).eval ((p.2 : ℚ) + p.1) := by
      simp [P, add_comm]
    rw [heval]
    linarith
  -- Sum the paired-fibre identity and exchange the two finite sums in the split part.
  have hsym := Finset.sum_congr rfl fun t (_ : t ∈ I) ↦
    congrArg (fun x : ℚ ↦ x * P t) (fibreWeight_pair n hn t)
  simp only [add_mul, Finset.sum_add_distrib, hneg, mul_assoc, Finset.mul_sum,
    Finset.sum_mul] at hsym
  have hswap : (∑ t ∈ I, ∑ p ∈ s,
      (if t = (p.1 : ℤ) + p.2 ∨ -t = (p.1 : ℤ) + p.2 then (p.2 : ℚ) - p.1 else 0) * P t) =
      2 * ∑ p ∈ s, ((p.2 : ℚ) ^ (w + 1) - (p.1 : ℚ) ^ (w + 1)) := by
    rw [Finset.sum_comm, Finset.mul_sum]
    exact Finset.sum_congr rfl hp
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
    rw [← Finset.mul_sum] at hsym
    simp only [← Finset.mul_sum] at hsym
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
the Hurwitz-class-number sum. The discriminant-zero terms use `H(0) = -1/12`. This is the trace
on the full space `W_w`, before the Eichler–Shimura transfer to cusp forms. -/
theorem trace_periodActionRestrict_popaZagierElement_eq_classNumber_sum
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

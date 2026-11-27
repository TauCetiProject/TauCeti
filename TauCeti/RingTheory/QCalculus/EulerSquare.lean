/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.QCalculus.Series
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.Tactic.Ring
import TauCeti.RingTheory.PowerSeries.Order

/-!
# Euler's square-exponent product identity

This file defines the two sides of Euler's raw square-exponent product identity in `R⟦X⟧` and
proves that they agree over any commutative ring `R`, without unit hypotheses:

* `TauCeti.eulerOddProd R`: `∏_{i ≥ 0} (1 + r ^ (2 i + 1))` over any commutative semiring `R`,
  defined as an infinite product in `R⟦X⟧` under `PowerSeries.WithPiTopology`.
* `TauCeti.eulerSqSeries R`: `∑_{n ≥ 0} r ^ (n ^ 2) / (r ^ 2; r ^ 2)_n` over any commutative
  ring `R`, defined by coefficient stabilization.
* `TauCeti.eulerSqSeries_eq_eulerOddProd`: `eulerSqSeries R = eulerOddProd R`.

## References

* W. J. G. Ong, notes of P. Scholze's course *V5A2 – The Habiro Ring of a Number Field*, Bonn,
  winter 2024/25 (6 March 2025 version,
  https://wgabrielong.github.io/academic-writing/notes/bonn-winter-24-25/V5A2-Habiro-Rings/Habiro_Rings_Notes.pdf),
  Proposition 2.7.
* S. Garoufalidis, P. Scholze, C. Wheeler, D. Zagier, *The Habiro ring of a number field*,
  arXiv:2412.04241v2, Section 2.1, (46).
-/

public section

open Finset PowerSeries
open scoped Polynomial PowerSeries PowerSeries.WithPiTopology

namespace TauCeti

section EulerOddProd

variable {R : Type*} [CommSemiring R]

variable (R) in
/-- The right-hand side `∏_{i ≥ 0} (1 + r ^ (2 i + 1))` of Euler's raw identity in `R⟦X⟧`,
defined as the infinite product `∏' i, (1 + r ^ (2 i + 1))` for the product topology on `R⟦X⟧`
induced by the discrete topology on `R`. -/
noncomputable def eulerOddProd : R⟦X⟧ :=
  letI : TopologicalSpace R := ⊥
  ∏' i : ℕ, (1 + (X : R⟦X⟧) ^ (2 * i + 1))

/-- Under the discrete topology on `R`, `eulerOddProd R` equals the infinite product
`∏' i, (1 + X ^ (2 * i + 1))`. -/
theorem eulerOddProd_eq_tprod [TopologicalSpace R] [DiscreteTopology R] :
    eulerOddProd R = ∏' i : ℕ, (1 + (X : R⟦X⟧) ^ (2 * i + 1)) := by
  obtain rfl := DiscreteTopology.eq_bot (α := R)
  rfl

/-- Multiplying by factors `1 + X ^ (2 * i + 1)` with `k < 2 * i + 1` does not change the
`k`-th coefficient. -/
private theorem coeff_mul_prod_one_add_X_pow_eq (k : ℕ) (t : Finset ℕ)
    (ht : ∀ i ∈ t, k < 2 * i + 1) (f : R⟦X⟧) :
    coeff k (f * ∏ i ∈ t, (1 + (X : R⟦X⟧) ^ (2 * i + 1))) = coeff k f := by
  classical
  induction t using Finset.induction_on generalizing f with
  | empty => simp
  | insert a t ha ih =>
    rw [Finset.prod_insert ha, ← mul_assoc, ih (fun i hi ↦ ht i (Finset.mem_insert_of_mem hi)),
      mul_add, mul_one, map_add, coeff_mul_X_pow',
      ite_eq_right (Nat.not_le.mpr (ht a (Finset.mem_insert_self a t))), add_zero]

/-- **Stabilization of `eulerOddProd`**: the `k`-th coefficient equals that of the finite product
over `i < N` whenever `k < 2 * N + 1`. -/
theorem coeff_eulerOddProd_eq_prod_of_lt (k : ℕ) {N : ℕ} (hN : k < 2 * N + 1) :
    coeff k (eulerOddProd R) =
      coeff k (∏ i ∈ range N, (1 + (X : R⟦X⟧) ^ (2 * i + 1))) := by
  nontriviality R
  let : TopologicalSpace R := ⊥
  have : DiscreteTopology R := ⟨rfl⟩
  have hm : Multipliable fun i : ℕ ↦ (1 + (X : R⟦X⟧) ^ (2 * i + 1)) := by
    apply WithPiTopology.multipliable_one_add_of_tendsto_order_atTop_nhds_top
    refine ENat.tendsto_nhds_top_iff_natCast_lt.mpr fun n ↦ Filter.eventually_atTop.mpr ⟨n, ?_⟩
    intro m hm
    rw [order_X_pow]
    norm_cast
    omega
  have hprod := hm.hasProd
  rw [HasProd, WithPiTopology.tendsto_iff_coeff_tendsto] at hprod
  have ht := hprod k
  rw [nhds_discrete, Filter.tendsto_pure] at ht
  obtain ⟨s₀, hs₀⟩ := Filter.eventually_atTop.mp ht
  have hs := hs₀ (s₀ ∪ range N) Finset.subset_union_left
  rw [← eulerOddProd_eq_tprod] at hs
  rw [← hs, ← Finset.prod_sdiff (Finset.subset_union_right (s₁ := s₀) (s₂ := range N)), mul_comm]
  exact coeff_mul_prod_one_add_X_pow_eq k ((s₀ ∪ range N) \ range N)
    (fun i hi ↦ by
      simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_range, not_lt] at hi
      omega) _

/-- Constant coefficient of `eulerOddProd R` is `1`. -/
@[simp] theorem constantCoeff_eulerOddProd : constantCoeff (eulerOddProd R) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_eulerOddProd_eq_prod_of_lt 0 (N := 0) (by omega)]
  simp

/-- The degree-`1` coefficient of `eulerOddProd R` is `1`. -/
theorem coeff_one_eulerOddProd : coeff 1 (eulerOddProd R) = 1 := by
  rw [coeff_eulerOddProd_eq_prod_of_lt 1 (N := 1) (by omega)]; simp

/-- The degree-`2` coefficient of `eulerOddProd R` is `0`. -/
theorem coeff_two_eulerOddProd : coeff 2 (eulerOddProd R) = 0 := by
  rw [coeff_eulerOddProd_eq_prod_of_lt 2 (N := 1) (by omega)]; simp [coeff_X]

/-- The degree-`3` coefficient of `eulerOddProd R` is `1`. -/
theorem coeff_three_eulerOddProd : coeff 3 (eulerOddProd R) = 1 := by
  rw [coeff_eulerOddProd_eq_prod_of_lt 3 (N := 2) (by omega)]
  have hpoly : (∏ i ∈ range 2, (1 + (X : R⟦X⟧) ^ (2 * i + 1))) =
      (((1 + Polynomial.X) * (1 + Polynomial.X ^ 3) : R[X]) : R⟦X⟧) := by simp [prod_range_succ]
  rw [hpoly, Polynomial.coeff_coe]
  simp [add_mul, mul_add, Polynomial.coeff_X_pow, Polynomial.coeff_one, Polynomial.coeff_X]

/-- The degree-`8` coefficient of `eulerOddProd R` is `2`. -/
theorem coeff_eight_eulerOddProd : coeff 8 (eulerOddProd R) = 2 := by
  rw [coeff_eulerOddProd_eq_prod_of_lt 8 (N := 4) (by omega)]
  have hpoly : (∏ i ∈ range 4, (1 + (X : R⟦X⟧) ^ (2 * i + 1))) =
      (((1 + Polynomial.X) * (1 + Polynomial.X ^ 3) * (1 + Polynomial.X ^ 5) *
        (1 + Polynomial.X ^ 7) : R[X]) : R⟦X⟧) := by simp [prod_range_succ]
  rw [hpoly, Polynomial.coeff_coe]
  simp only [add_mul, mul_add, one_mul, mul_one, ← pow_add, ← pow_succ']
  simp [Polynomial.coeff_X_pow, Polynomial.coeff_one, Polynomial.coeff_X, one_add_one_eq_two]

end EulerOddProd

section EulerSquareIdentity

variable {R : Type*} [CommRing R]

variable (R) in
/-- The left-hand side `∑_{n ≥ 0} r ^ (n ^ 2) / (r ^ 2; r ^ 2)_n` of Euler's raw identity in
`R⟦X⟧`, defined by coefficient stabilization. -/
noncomputable def eulerSqSeries : R⟦X⟧ :=
  PowerSeries.mk fun k ↦
    coeff k (∑ n ∈ range (k + 1),
      (X : R⟦X⟧) ^ (n ^ 2) * Ring.inverse (qPochhammer (X ^ 2 : R⟦X⟧) (X ^ 2 : R⟦X⟧) n))

/-- **Stabilization of `eulerSqSeries`**: the `k`-th coefficient equals that of the partial sum
over `n < N` whenever `k < N ^ 2`. -/
theorem coeff_eulerSqSeries_eq_sum_of_lt (k : ℕ) {N : ℕ} (hN : k < N ^ 2) :
    coeff k (eulerSqSeries R) =
      coeff k (∑ n ∈ range N,
        (X : R⟦X⟧) ^ (n ^ 2) * Ring.inverse (qPochhammer (X ^ 2 : R⟦X⟧) (X ^ 2 : R⟦X⟧) n)) := by
  have hzero : ∀ n, k < n ^ 2 →
      coeff k ((X : R⟦X⟧) ^ (n ^ 2) *
        Ring.inverse (qPochhammer (X ^ 2 : R⟦X⟧) (X ^ 2 : R⟦X⟧) n)) = 0 := fun n hlt ↦ by
    rw [coeff_X_pow_mul']; simp [Nat.not_le.mpr hlt]
  rw [eulerSqSeries, coeff_mk, map_sum, map_sum]
  refine Finset.sum_congr_of_eq_on_inter (fun n _ hn ↦ hzero n ?_) (fun n _ hn ↦ hzero n ?_)
    (fun _ _ _ ↦ rfl)
  · exact lt_of_lt_of_le hN (Nat.pow_le_pow_left (Nat.le_of_not_lt (by simpa using hn)) 2)
  · have : k + 1 ≤ n := Nat.le_of_not_lt (by simpa using hn); nlinarith

/-- Each summand `r ^ (n ^ 2) / (r ^ 2; r ^ 2)_n` equals `(-r) ^ n` times the `n`-th coefficient
of `qPochhammerSeries (r ^ 2)`. -/
private theorem neg_X_pow_mul_coeff_qPochhammerSeries_sq (n : ℕ) :
    (-X : R⟦X⟧) ^ n * coeff n (qPochhammerSeries (X ^ 2 : R⟦X⟧)) =
      (X : R⟦X⟧) ^ (n ^ 2) * Ring.inverse (qPochhammer (X ^ 2 : R⟦X⟧) (X ^ 2 : R⟦X⟧) n) := by
  rw [coeff_qPochhammerSeries, neg_eq_neg_one_mul, mul_pow, ← pow_mul]
  have hexp : n + 2 * (n * (n - 1) / 2) = n ^ 2 := by
    rw [Nat.mul_div_cancel' (Nat.two_dvd_mul_sub_one n)]
    rcases n with _ | m <;> [rfl; (rw [Nat.add_sub_cancel]; ring)]
  have hsign : (-1 : R⟦X⟧) ^ n * (-1 : R⟦X⟧) ^ n = 1 := by rw [← mul_pow]; simp
  rw [← hexp, pow_add]
  linear_combination
    (X : R⟦X⟧) ^ n * (X : R⟦X⟧) ^ (2 * (n * (n - 1) / 2)) *
      Ring.inverse (qPochhammer (X ^ 2 : R⟦X⟧) (X ^ 2 : R⟦X⟧) n) * hsign

/-- Below `r`-degree `k + 1`, the coefficients of `qPochhammerSeries (r ^ 2)` agree with those of
the finite polynomial product `qPochhammer t (r ^ 2) (k + 1)`. -/
private theorem coeff_coeff_qPochhammerSeries_sq_eq (k n j : ℕ) (hj : j ≤ k) :
    coeff j (coeff n (qPochhammerSeries (X ^ 2 : R⟦X⟧))) =
      coeff j ((qPochhammer Polynomial.X (Polynomial.C (X ^ 2 : R⟦X⟧)) (k + 1)).coeff n) := by
  let φ : R⟦X⟧ →+* R⟦X⟧ := (expand 2 two_ne_zero).toRingHom
  have hF : map φ (integralQPochhammer R) = qPochhammerSeries (X ^ 2 : R⟦X⟧) := by
    rw [integralQPochhammer_eq_qPochhammerSeries,
      map_qPochhammerSeries _ (isUnit_one_sub_X_pow_succ (R := R))]
    ext m
    simp [φ, expand_X]
  have hp_map :
      qPochhammer Polynomial.X (Polynomial.C (X ^ 2 : R⟦X⟧)) (k + 1) =
        (qPochhammer (Polynomial.X : (R⟦X⟧)[X]) (Polynomial.C (X : R⟦X⟧)) (k + 1)).map φ := by
    rw [Polynomial.map_qPochhammer]; simp [φ, expand_X]
  rw [← hF, hp_map, Polynomial.coeff_map, coeff_map]
  dsimp [φ]
  rw [coeff_expand, coeff_expand]
  split_ifs with hd
  · exact coeff_coeff_integralQPochhammer_eq_of_lt (j / 2) n (by omega)
  · rfl

/-- Coefficient of `(-X) ^ n * f` at degree `k`. -/
private theorem coeff_neg_X_pow_mul (k n : ℕ) (f : R⟦X⟧) :
    coeff k ((-X : R⟦X⟧) ^ n * f) = (-1) ^ n * if n ≤ k then coeff (k - n) f else 0 := by
  rw [neg_eq_neg_one_mul, mul_pow, mul_assoc, ← map_one C, ← map_neg, ← map_pow, coeff_C_mul,
    coeff_X_pow_mul']

/-- **Euler's raw identity** in `R⟦X⟧`:
`∑_{n ≥ 0} r ^ (n ^ 2) / (r ^ 2; r ^ 2)_n = ∏_{i ≥ 0} (1 + r ^ (2 i + 1))`. -/
theorem eulerSqSeries_eq_eulerOddProd : eulerSqSeries R = eulerOddProd R := by
  ext k
  let p : (R⟦X⟧)[X] := qPochhammer Polynomial.X (Polynomial.C (X ^ 2 : R⟦X⟧)) (k + 1)
  have hp_eval : p.eval (-X : R⟦X⟧) = ∏ i ∈ range (k + 1), (1 + (X : R⟦X⟧) ^ (2 * i + 1)) := by
    rw [Polynomial.eval_qPochhammer, Polynomial.eval_X, Polynomial.eval_C, qPochhammer_def]
    refine prod_congr rfl fun i _ ↦ ?_
    rw [← pow_mul, neg_mul, sub_neg_eq_add, ← pow_succ']
  rw [eulerSqSeries, coeff_mk, coeff_eulerOddProd_eq_prod_of_lt k (N := k + 1) (by omega),
    ← hp_eval, map_sum, coeff_eval_eq_sum_range p (by simp)]
  refine sum_congr rfl fun n _ ↦ ?_
  rw [← neg_X_pow_mul_coeff_qPochhammerSeries_sq n, mul_comm (p.coeff n),
    coeff_neg_X_pow_mul, coeff_neg_X_pow_mul]
  split_ifs with hnk
  · rw [coeff_coeff_qPochhammerSeries_sq_eq k n (k - n) (by omega)]
  · rfl

end EulerSquareIdentity

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.AbsoluteValue.Nonarchimedean
public import TauCeti.RingTheory.MvPolynomial.Abv.Eval
public import TauCeti.RingTheory.MvPolynomial.WeightedIndex

import TauCeti.Algebra.MvPolynomial.Degrees

/-!
# The value of a polynomial at one absolute value

Let `P` be a polynomial over a commutative ring `R` with partial degrees `degreeOf i P ≤ L i`
and coefficients of absolute value at most `B` under an absolute value `v : AbsoluteValue R ℝ`.
This file bounds `v(P(x))` at a point `x`, in two ways.

* **Trivially.** `P(x)` is a sum of at most `∏ i, (L i + 1)` terms, each at most
  `B ∏ i, max(v(x_i), 1) ^ L i`. At a nonarchimedean `v` the count disappears. These bounds,
  `AbsoluteValue.apply_eval_le` and `IsNonarchimedean.apply_eval_le`, are in
  `TauCeti.RingTheory.MvPolynomial.Abv.Eval`; here they give the trivial bound for the jets.
* **Through the Taylor expansion at a point `a` where `P` has weighted index at least `t`** with
  respect to the weights `L`. Then `P(x) = ∑_d (∂^d P)(a) (x - a)^d` involves only multi-indices
  `d ≤ L` of weight `∑ i, d i / L i ≥ t`. If every such `d` has `∏ i, v(x_i - a_i) ^ d i ≤ E`,
  then `v(P(x)) ≤ B (∏ i, (L i + 1))² ∏ i, (2 max(v(a_i), 1)) ^ L i · E`, and at a
  nonarchimedean `v` simply `v(P(x)) ≤ B ∏ i, max(v(a_i), 1) ^ L i · E`.

In the proof of Roth's theorem over a number field `K` an auxiliary polynomial `P` over `K`
vanishes to a high index at a point `a` with coordinates in a finite extension `F`, and is
evaluated at a point `x ∈ Kⁿ` close to `a` at the places of a finite set `S`. The Taylor bound
is the upper estimate for `P(x)` at a place of `S`; the trivial bound is the upper estimate at
every other place, where the nonarchimedean form is needed because there are infinitely many of
them. The comparison of the product of these bounds with the product formula is the
contradiction that proves the theorem. The forms
`AbsoluteValue.LiesOver.apply_eval_le_of_le_weightedIndex` and
`AbsoluteValue.LiesOver.apply_eval_le_of_le_weightedIndex_of_isNonarchimedean` state the Taylor
bound for `P` over `K` at an absolute value `w` of `F` lying over an absolute value `v` of `K`, so
that the targets `a` need not lie in `K`.

## Main results

* `AbsoluteValue.apply_eval_hasseDeriv_le`: the trivial bound for the jets `(∂^d P)(a)`, whose
  coefficients carry an extra factor `2 ^ ∑ i, L i`.
* `AbsoluteValue.apply_eval_le_of_le_weightedIndex`,
  `IsNonarchimedean.apply_eval_le_of_le_weightedIndex`: the bounds through the Taylor expansion
  at a point of weighted index at least `t`.
* `AbsoluteValue.LiesOver.apply_eval_le_of_le_weightedIndex`,
  `AbsoluteValue.LiesOver.apply_eval_le_of_le_weightedIndex_of_isNonarchimedean`: the same for
  a polynomial over `K` and a point `a` over an extension `F`.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press
  (2006), §6.4, the proof of Theorem 6.4.1.
* L. Pottmeyer, *Diophantine Approximation*, lecture notes (2022), §3.5.3.
-/

public section

open Finset MvPolynomial

variable {ι R : Type*} [Fintype ι] [CommRing R]

/-- The Taylor coefficients of a polynomial with partial degrees `degreeOf i P ≤ L i` and
weighted index at least `t` at `a` are supported on multi-indices `d ≤ L` of weight at least
`t`, and `P(x)` is the sum of the terms `(∂^d P)(a) (x - a)^d` over them. -/
private theorem eval_eq_sum_taylor {P : MvPolynomial ι R} {L : ι → ℕ}
    (hL : ∀ i, P.degreeOf i ≤ L i) {a : ι → R} {t : ℝ}
    (ht : ENNReal.ofReal t ≤ weightedIndex L a P) (x : ι → R) :
    (eval x P = ∑ d ∈ (taylor a P).support,
      eval a (hasseDeriv d P) * ∏ i, (x i - a i) ^ d i) ∧
    ∀ d ∈ (taylor a P).support, (∀ i, d i ≤ L i) ∧ t ≤ ∑ i, (d i : ℝ) / L i := by
  refine ⟨?_, fun d hd ↦ ?_⟩
  · have hx : x = (fun i ↦ x i - a i) + a := by
      ext i
      simp
    conv_lhs => rw [hx, ← eval_taylor, eval_eq']
    simp only [coeff_taylor]
  · rw [mem_support_iff, coeff_taylor] at hd
    exact le_sum_div_of_le_weightedIndex hL ht hd

variable [Nontrivial R]

namespace AbsoluteValue

/-- **The jets of a polynomial.** If `P` has partial degrees `degreeOf i P ≤ L i` and
coefficients of absolute value at most `B`, then every Hasse derivative of `P` satisfies
`v((∂^d P)(a)) ≤ B ∏ i, (L i + 1) ∏ i, (2 max(v(a_i), 1)) ^ L i`. -/
theorem apply_eval_hasseDeriv_le (v : AbsoluteValue R ℝ) {P : MvPolynomial ι R}
    {L : ι → ℕ} (hL : ∀ i, P.degreeOf i ≤ L i) {B : ℝ} (hB : ∀ s, v (P.coeff s) ≤ B)
    (a : ι → R) (d : ι →₀ ℕ) :
    v (eval a (hasseDeriv d P)) ≤
      B * (∏ i, ((L i : ℝ) + 1)) * ∏ i, (2 * max (v (a i)) 1) ^ L i := by
  refine (v.apply_eval_le (degreeOf_hasseDeriv_le_of_le hL d)
    (abv_coeff_hasseDeriv_le_two_pow_mul v hL hB d) a).trans_eq ?_
  simp only [mul_pow, prod_mul_distrib, prod_pow_eq_pow_sum]
  ring

/-- **The value of a polynomial near a point of high index.** Let `P` have partial degrees
`degreeOf i P ≤ L i`, coefficients of absolute value at most `B`, and weighted index at least `t`
at `a` with respect to the weights `L`. If `0 ≤ E` and `∏ i, v(x_i - a_i) ^ d i ≤ E` for every
multi-index `d ≤ L` of weight `∑ i, d i / L i ≥ t`, then
`v(P(x)) ≤ B (∏ i, (L i + 1))² ∏ i, (2 max(v(a_i), 1)) ^ L i · E`. -/
theorem apply_eval_le_of_le_weightedIndex (v : AbsoluteValue R ℝ) {P : MvPolynomial ι R}
    {L : ι → ℕ} (hL : ∀ i, P.degreeOf i ≤ L i) {B : ℝ} (hB : ∀ s, v (P.coeff s) ≤ B)
    {a : ι → R} {t : ℝ} (ht : ENNReal.ofReal t ≤ weightedIndex L a P) (x : ι → R) {E : ℝ}
    (hE0 : 0 ≤ E)
    (hE : ∀ d : ι →₀ ℕ, (∀ i, d i ≤ L i) → t ≤ ∑ i, (d i : ℝ) / L i →
      ∏ i, v (x i - a i) ^ d i ≤ E) :
    v (eval x P) ≤
      B * (∏ i, ((L i : ℝ) + 1)) ^ 2 * (∏ i, (2 * max (v (a i)) 1) ^ L i) * E := by
  have hB0 : 0 ≤ B := (v.nonneg _).trans (hB 0)
  obtain ⟨heval, hT⟩ := eval_eq_sum_taylor hL ht x
  rw [heval]
  refine (v.sum_le _ _).trans <| (Finsupp.sum_le_prod_mul_of_forall_le (fun d hd ↦ (hT d hd).1)
    (C := B * (∏ i, ((L i : ℝ) + 1)) * (∏ i, (2 * max (v (a i)) 1) ^ L i) * E) (fun d hd ↦ ?_)
    (by positivity)).trans_eq (by ring)
  rw [v.map_mul, map_prod]
  simp only [v.map_pow]
  exact mul_le_mul (v.apply_eval_hasseDeriv_le hL hB a d) (hE d (hT d hd).1 (hT d hd).2)
    (by positivity) (by positivity)

omit [Fintype ι] in
/-- Along an absolute value `w` of `F` lying over `v`, the value `v(P(x))` of a polynomial over
`K` is the `w`-value of its image over `F` at the image of `x`, and that image keeps the partial
degree bounds and coefficient bounds of `P`. -/
private theorem LiesOver.apply_eval_eq_map {K F : Type*} [CommRing K] [CommRing F]
    [Algebra K F] [FaithfulSMul K F] (w : AbsoluteValue F ℝ)
    (v : AbsoluteValue K ℝ) [w.LiesOver v] {P : MvPolynomial ι K} {L : ι → ℕ}
    (hL : ∀ i, P.degreeOf i ≤ L i) {B : ℝ} (hB : ∀ s, v (P.coeff s) ≤ B) (x : ι → K) :
    v (eval x P) = w (eval (algebraMap K F ∘ x) (P.map (algebraMap K F))) ∧
      (∀ i, (P.map (algebraMap K F)).degreeOf i ≤ L i) ∧
      ∀ s, w ((P.map (algebraMap K F)).coeff s) ≤ B := by
  refine ⟨?_, fun i ↦ (degreeOf_map_le _ P i).trans (hL i), fun s ↦ ?_⟩
  · rw [← LiesOver.apply_algebraMap (w := w) v, eval₂_comp, ← eval_map]
  · rw [coeff_map, LiesOver.apply_algebraMap v]
    exact hB s

/-- **The value of a polynomial over `K` near a point over an extension `F`.** Let `w` be an
absolute value of `F` lying over the absolute value `v` of `K`, and let `P` over `K` have partial
degrees `degreeOf i P ≤ L i` and coefficients with `v`-value at most `B`. If the image of `P` in
`F` has weighted index at least `t` at `a : ι → F`, and `∏ i, w(x_i - a_i) ^ d i ≤ E` with
`0 ≤ E` for every multi-index `d ≤ L` of weight at least `t`, then
`v(P(x)) ≤ B (∏ i, (L i + 1))² ∏ i, (2 max(w(a_i), 1)) ^ L i · E` for `x : ι → K`. -/
theorem LiesOver.apply_eval_le_of_le_weightedIndex {K F : Type*} [CommRing K] [CommRing F]
    [Nontrivial F] [Algebra K F] [FaithfulSMul K F] (w : AbsoluteValue F ℝ)
    (v : AbsoluteValue K ℝ) [w.LiesOver v] {P : MvPolynomial ι K} {L : ι → ℕ}
    (hL : ∀ i, P.degreeOf i ≤ L i) {B : ℝ} (hB : ∀ s, v (P.coeff s) ≤ B) {a : ι → F} {t : ℝ}
    (ht : ENNReal.ofReal t ≤ weightedIndex L a (P.map (algebraMap K F))) (x : ι → K) {E : ℝ}
    (hE0 : 0 ≤ E)
    (hE : ∀ d : ι →₀ ℕ, (∀ i, d i ≤ L i) → t ≤ ∑ i, (d i : ℝ) / L i →
      ∏ i, w (algebraMap K F (x i) - a i) ^ d i ≤ E) :
    v (eval x P) ≤
      B * (∏ i, ((L i : ℝ) + 1)) ^ 2 * (∏ i, (2 * max (w (a i)) 1) ^ L i) * E := by
  obtain ⟨heval, hL', hB'⟩ := LiesOver.apply_eval_eq_map w v hL hB x
  rw [heval]
  exact w.apply_eval_le_of_le_weightedIndex hL' hB' ht _ hE0 hE

end AbsoluteValue

namespace IsNonarchimedean

/-- **The value of a polynomial near a point of high index, at a nonarchimedean absolute value.**
Let `P` have partial degrees `degreeOf i P ≤ L i`, coefficients of absolute value at most `B`,
and weighted index at least `t` at `a` with respect to the weights `L`. If `0 ≤ E` and
`∏ i, v(x_i - a_i) ^ d i ≤ E` for every multi-index `d ≤ L` of weight `∑ i, d i / L i ≥ t`, then
`v(P(x)) ≤ B ∏ i, max(v(a_i), 1) ^ L i · E`. -/
theorem apply_eval_le_of_le_weightedIndex {v : AbsoluteValue R ℝ} (hv : IsNonarchimedean v)
    {P : MvPolynomial ι R} {L : ι → ℕ} (hL : ∀ i, P.degreeOf i ≤ L i) {B : ℝ}
    (hB : ∀ s, v (P.coeff s) ≤ B) {a : ι → R} {t : ℝ}
    (ht : ENNReal.ofReal t ≤ weightedIndex L a P) (x : ι → R) {E : ℝ} (hE0 : 0 ≤ E)
    (hE : ∀ d : ι →₀ ℕ, (∀ i, d i ≤ L i) → t ≤ ∑ i, (d i : ℝ) / L i →
      ∏ i, v (x i - a i) ^ d i ≤ E) :
    v (eval x P) ≤ B * (∏ i, max (v (a i)) 1 ^ L i) * E := by
  have hB0 : 0 ≤ B := (v.nonneg _).trans (hB 0)
  obtain ⟨heval, hT⟩ := eval_eq_sum_taylor hL ht x
  rw [heval]
  rcases (taylor a P).support.eq_empty_or_nonempty with hP | hP
  · rw [hP, sum_empty, v.map_zero]
    positivity
  refine (hv.apply_sum_le_sup hP).trans <| sup'_le _ _ fun d hd ↦ ?_
  rw [v.map_mul, map_prod]
  simp only [v.map_pow]
  refine mul_le_mul ?_ (hE d (hT d hd).1 (hT d hd).2) (by positivity) (by positivity)
  exact hv.apply_eval_le (degreeOf_hasseDeriv_le_of_le hL d)
    (fun s ↦ (abv_coeff_hasseDeriv_le_of_isNonarchimedean hv d s P).trans (hB _)) a

end IsNonarchimedean

namespace AbsoluteValue

/-- **The value of a polynomial over `K` near a point over an extension `F`, at a nonarchimedean
absolute value.** Let `w` be a nonarchimedean absolute value of `F` lying over the absolute value
`v` of `K`, and let `P` over `K` have partial degrees `degreeOf i P ≤ L i` and coefficients with
`v`-value at most `B`. If the image of `P` in `F` has weighted index at least `t` at
`a : ι → F`, and `∏ i, w(x_i - a_i) ^ d i ≤ E` with `0 ≤ E` for every multi-index `d ≤ L` of
weight at least `t`, then `v(P(x)) ≤ B ∏ i, max(w(a_i), 1) ^ L i · E` for `x : ι → K`. -/
theorem LiesOver.apply_eval_le_of_le_weightedIndex_of_isNonarchimedean {K F : Type*} [CommRing K]
    [CommRing F] [Nontrivial F] [Algebra K F] [FaithfulSMul K F] {w : AbsoluteValue F ℝ}
    (hw : IsNonarchimedean w) (v : AbsoluteValue K ℝ) [w.LiesOver v] {P : MvPolynomial ι K}
    {L : ι → ℕ} (hL : ∀ i, P.degreeOf i ≤ L i) {B : ℝ} (hB : ∀ s, v (P.coeff s) ≤ B)
    {a : ι → F} {t : ℝ} (ht : ENNReal.ofReal t ≤ weightedIndex L a (P.map (algebraMap K F)))
    (x : ι → K) {E : ℝ} (hE0 : 0 ≤ E)
    (hE : ∀ d : ι →₀ ℕ, (∀ i, d i ≤ L i) → t ≤ ∑ i, (d i : ℝ) / L i →
      ∏ i, w (algebraMap K F (x i) - a i) ^ d i ≤ E) :
    v (eval x P) ≤ B * (∏ i, max (w (a i)) 1 ^ L i) * E := by
  obtain ⟨heval, hL', hB'⟩ := LiesOver.apply_eval_eq_map w v hL hB x
  rw [heval]
  exact hw.apply_eval_le_of_le_weightedIndex hL' hB' ht _ hE0 hE

end AbsoluteValue

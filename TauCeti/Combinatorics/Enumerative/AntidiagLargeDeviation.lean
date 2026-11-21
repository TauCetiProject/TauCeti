/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Order.Antidiag.Moments
public import TauCeti.Analysis.SpecialFunctions.Exp.QuadraticBound
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# Exponential tails for monomials of fixed multidegree

Count a degree-`N` monomial uniformly among the exponent vectors supported on a nonempty finite
set `s`. Its exponent at a fixed variable, divided by `N`, has mean `1 / #s`. The exact first
two binomial moments give an exponential-moment bound with an explicit error of order `1 / N`.
Products of these bounds count multidegree monomials for which the sum of these normalized
exponents is smaller than its mean. No passage to a continuous distribution is necessary.

`Finset.card_filter_piFinset_finsuppAntidiag_sum_apply_div_le_le_mul_exp` is the finite-degree
Chernoff bound. `Finset.card_filter_piFinset_finsuppAntidiag_sum_apply_div_le_div_sub_mul_le`
evaluates it at `l = #s * (#s + 1) * η / 2`, the minimizer of the leading,
degree-independent quadratic term. The block degrees may differ, and their error is measured
by the sum of their reciprocals.
`Finset.exists_bound_card_filter_piFinset_finsuppAntidiag_sum_apply_div_le_div_sub_mul_le`
absorbs that error into any positive slack in the per-block exponent (rate) of the upper bound.
Such bounds count the linear vanishing conditions in the construction of multihomogeneous
auxiliary polynomials.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry* (2006), §7.5.14 and Lemma 7.5.15.
  The proof uses the exact binomial moments from `TauCeti.Algebra.Order.Antidiag.Moments` in
  place of a limiting volume computation.
-/

public section

open scoped BigOperators

namespace Finset

variable {ι κ : Type*} [DecidableEq ι]

/-- The exponential moment of a normalized exponent of a uniformly counted degree-`N`
monomial. The last term is a finite-degree correction; there is no upper bound on `l`. -/
theorem sum_finsuppAntidiag_exp_neg_mul_div_le (s : Finset ι) {i : ι} (hi : i ∈ s)
    {N : ℕ} (hN : 0 < N) {l : ℝ} (hl : 0 ≤ l) :
    ∑ f ∈ finsuppAntidiag s N, Real.exp (-l * (f i : ℝ) / N) ≤
      (finsuppAntidiag s N).card *
        Real.exp (-l / s.card + l ^ 2 / (s.card * (s.card + 1)) +
          l ^ 2 / (2 * N * s.card)) := by
  let A := finsuppAntidiag s N
  let q : ℝ := s.card
  let M : ℝ := A.card
  have hq : 0 < q := Nat.cast_pos.mpr (card_pos.mpr ⟨i, hi⟩)
  have hN' : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  -- Evaluate the first and second raw moments exactly.
  have hfirst : (∑ f ∈ A, (f i : ℝ)) = N * M / q := by
    apply (eq_div_iff hq.ne').mpr
    simpa only [q, M, A, Nat.cast_mul, Nat.cast_sum, mul_comm] using
      congrArg (Nat.cast : ℕ → ℝ) (card_mul_sum_finsuppAntidiag_apply hi N)
  have hsecond : (∑ f ∈ A, (f i : ℝ) ^ 2) =
      N * (2 * N + q - 1) * M / (q * (q + 1)) := by
    apply (eq_div_iff (by positivity)).mpr
    rw [mul_comm]
    have hsub : 1 ≤ 2 * N + s.card := by omega
    simpa only [q, M, A, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_sum,
      Nat.cast_sub hsub, Nat.cast_pow, Nat.cast_ofNat] using
      congrArg (Nat.cast : ℕ → ℝ) (card_mul_card_add_one_mul_sum_finsuppAntidiag_sq hi N)
  have hfrac : l ^ 2 * (2 * N + q - 1) / (2 * N * q * (q + 1)) ≤
      l ^ 2 / (q * (q + 1)) + l ^ 2 / (2 * N * q) := by
    calc
      _ ≤ l ^ 2 * (2 * N + q + 1) / (2 * N * q * (q + 1)) :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg l)) (by positivity)
      _ = _ := by field_simp; ring
  -- Sum the quadratic exponential bound, then absorb the finite-degree correction.
  calc
    _ ≤ ∑ f ∈ A, (1 - l / N * (f i : ℝ) +
        l ^ 2 / (2 * (N : ℝ) ^ 2) * (f i : ℝ) ^ 2) := by
      apply sum_le_sum
      intro f _
      have h := Real.exp_le_one_add_add_sq_div_two_of_nonpos
        (div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg
          (neg_nonpos.mpr hl) (Nat.cast_nonneg (f i))) (Nat.cast_nonneg N))
      convert h using 1
      ring
    _ = M * (1 - l / q + l ^ 2 * (2 * N + q - 1) / (2 * N * q * (q + 1))) := by
      simp only [sum_add_distrib, sum_sub_distrib, ← mul_sum, sum_const, nsmul_eq_mul,
        hfirst, hsecond]
      dsimp [M]
      field_simp
    _ ≤ M * (1 + (-l / q + l ^ 2 / (q * (q + 1)) + l ^ 2 / (2 * N * q))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ M)
      simp only [neg_div]
      linarith only [hfrac]
    _ ≤ M * Real.exp (-l / q + l ^ 2 / (q * (q + 1)) + l ^ 2 / (2 * N * q)) :=
      mul_le_mul_of_nonneg_left
        (by simpa only [add_comm] using
          Real.add_one_le_exp (-l / q + l ^ 2 / (q * (q + 1)) + l ^ 2 / (2 * N * q)))
        (by positivity)

/-- The exponential moment of the sum of normalized exponents in independent blocks factors
into the one-block bounds. The blocks can have different positive degrees. -/
theorem sum_piFinset_finsuppAntidiag_exp_neg_mul_sum_div_le [Fintype κ] [DecidableEq κ]
    (s : Finset ι) {i : ι} (hi : i ∈ s) (d : κ → ℕ) (hd : ∀ h, 0 < d h)
    {l : ℝ} (hl : 0 ≤ l) :
    ∑ f ∈ Fintype.piFinset (fun h ↦ finsuppAntidiag s (d h)),
        Real.exp (-l * ∑ h, (f h i : ℝ) / d h) ≤
      (∏ h, (finsuppAntidiag s (d h)).card : ℝ) *
        Real.exp ((Fintype.card κ : ℝ) *
          (-l / s.card + l ^ 2 / (s.card * (s.card + 1))) +
          l ^ 2 / (2 * s.card) * ∑ h, (d h : ℝ)⁻¹) := by
  classical
  have hfactor : ∑ f ∈ Fintype.piFinset (fun h ↦ finsuppAntidiag s (d h)),
      Real.exp (-l * ∑ h, (f h i : ℝ) / d h) =
      ∏ h, ∑ g ∈ finsuppAntidiag s (d h), Real.exp (-l * (g i : ℝ) / d h) := by
    simp_rw [mul_sum, Real.exp_sum, mul_div_assoc]
    exact (prod_univ_sum (fun h ↦ finsuppAntidiag s (d h))
      (fun h g ↦ Real.exp (-l * ((g i : ℝ) / d h)))).symm
  rw [hfactor]
  refine (prod_le_prod₀ (fun _ _ ↦ sum_nonneg fun _ _ ↦ (Real.exp_pos _).le)
    (fun h _ ↦ sum_finsuppAntidiag_exp_neg_mul_div_le s hi (hd h) hl)).trans_eq ?_
  rw [prod_mul_distrib, ← Real.exp_sum]
  congr 2
  have hcorr (h : κ) : l ^ 2 / (2 * (d h : ℝ) * s.card) =
      l ^ 2 / (2 * s.card) * (d h : ℝ)⁻¹ := by ring
  simp_rw [hcorr]
  simp only [sum_add_distrib, sum_const, nsmul_eq_mul, card_univ, ← mul_sum]
  ring

/-- A finite-degree lower-tail bound for multidegree monomials. At a fixed variable `i`,
count the block exponent families with normalized sum at most `t`, by exponential Markov.
The estimate is valid for every nonnegative exponential parameter `l`. -/
theorem card_filter_piFinset_finsuppAntidiag_sum_apply_div_le_le_mul_exp
    [Fintype κ] [DecidableEq κ]
    (s : Finset ι) {i : ι} (hi : i ∈ s) (d : κ → ℕ) (hd : ∀ h, 0 < d h)
    {l : ℝ} (hl : 0 ≤ l) (t : ℝ) :
    ((Fintype.piFinset (fun h ↦ finsuppAntidiag s (d h))).filter
      (fun f ↦ ∑ h, (f h i : ℝ) / d h ≤ t)).card ≤
      (∏ h, (finsuppAntidiag s (d h)).card : ℝ) *
        Real.exp (l * (t - Fintype.card κ / s.card) +
          Fintype.card κ * l ^ 2 / (s.card * (s.card + 1)) +
          l ^ 2 / (2 * s.card) * ∑ h, (d h : ℝ)⁻¹) := by
  classical
  let A := Fintype.piFinset (fun h ↦ finsuppAntidiag s (d h))
  have hmarkov : ((A.filter (fun f ↦ ∑ h, (f h i : ℝ) / d h ≤ t)).card : ℝ) *
      Real.exp (-l * t) ≤ ∑ f ∈ A, Real.exp (-l * ∑ h, (f h i : ℝ) / d h) := by
    calc
      _ = ∑ _f ∈ A.filter (fun f ↦ ∑ h, (f h i : ℝ) / d h ≤ t),
          Real.exp (-l * t) := by simp
      _ ≤ ∑ f ∈ A.filter (fun f ↦ ∑ h, (f h i : ℝ) / d h ≤ t),
          Real.exp (-l * ∑ h, (f h i : ℝ) / d h) := by
        apply sum_le_sum
        intro f hf
        exact Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left (mem_filter.mp hf).2 (by linarith))
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
        (fun _ _ _ ↦ (Real.exp_pos _).le)
  have h := hmarkov.trans (sum_piFinset_finsuppAntidiag_exp_neg_mul_sum_div_le s hi d hd hl)
  apply (mul_le_mul_iff_left₀ (Real.exp_pos (-l * t))).mp
  convert h using 1
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- The lower-tail estimate with `l = #s * (#s + 1) * η / 2`, the optimum of the leading,
degree-independent quadratic, not of the full finite-degree bound. Writing `q = #s` and
`m = card κ`, the leading exponent is `-q * (q + 1) * η² * m / 4`; the displayed
reciprocal-degree term is the finite-degree correction. -/
theorem card_filter_piFinset_finsuppAntidiag_sum_apply_div_le_div_sub_mul_le
    [Fintype κ] [DecidableEq κ]
    (s : Finset ι) {i : ι} (hi : i ∈ s) (d : κ → ℕ) (hd : ∀ h, 0 < d h)
    {η : ℝ} (hη : 0 ≤ η) :
    ((Fintype.piFinset (fun h ↦ finsuppAntidiag s (d h))).filter
      (fun f ↦ ∑ h, (f h i : ℝ) / d h ≤ Fintype.card κ / s.card - Fintype.card κ * η)).card ≤
      (∏ h, (finsuppAntidiag s (d h)).card : ℝ) *
        Real.exp (-(s.card * (s.card + 1) * η ^ 2 * Fintype.card κ / 4) +
          s.card * (s.card + 1) ^ 2 * η ^ 2 / 8 * ∑ h, (d h : ℝ)⁻¹) := by
  have hq : (0 : ℝ) < s.card := Nat.cast_pos.mpr (card_pos.mpr ⟨i, hi⟩)
  convert card_filter_piFinset_finsuppAntidiag_sum_apply_div_le_le_mul_exp s hi d hd
    (l := s.card * (s.card + 1) * η / 2) (by positivity)
    (Fintype.card κ / s.card - Fintype.card κ * η) using 1
  congr 2
  field_simp
  ring

/-- A lower bound `D` on every block degree makes the per-block reciprocal-degree error at most
`ε`, bounding the total correction by `ε * Fintype.card κ`, uniformly in `i ∈ s` and `κ`.
The exponent per block approaches `-s.card * (s.card + 1) * η ^ 2 / 4`, the large-degree
exponent of the quadratic upper bound, without requiring all blocks to have the same degree. -/
theorem exists_bound_card_filter_piFinset_finsuppAntidiag_sum_apply_div_le_div_sub_mul_le
    (s : Finset ι) {η ε : ℝ} (hη : 0 ≤ η) (hε : 0 < ε) :
    ∃ D : ℕ, 0 < D ∧ ∀ {κ : Type*} [Fintype κ] [DecidableEq κ] (d : κ → ℕ),
      (∀ h, D ≤ d h) → ∀ ⦃i : ι⦄, i ∈ s →
      ((Fintype.piFinset (fun h ↦ finsuppAntidiag s (d h))).filter
        (fun f ↦ ∑ h, (f h i : ℝ) / d h ≤ Fintype.card κ / s.card - Fintype.card κ * η)).card ≤
        (∏ h, (finsuppAntidiag s (d h)).card : ℝ) *
          Real.exp ((-s.card * (s.card + 1) * η ^ 2 / 4 + ε) * Fintype.card κ) := by
  let C : ℝ := s.card * (s.card + 1) ^ 2 * η ^ 2 / 8
  obtain ⟨D, hD⟩ := exists_nat_gt (max 1 (C / ε))
  have hDpos : 0 < D := by
    have : (1 : ℝ) < D := (le_max_left _ _).trans_lt hD
    exact_mod_cast (lt_trans zero_lt_one this)
  have hC : C ≤ ε * D := by
    have := (div_lt_iff₀ hε).mp ((le_max_right _ _).trans_lt hD)
    simpa only [mul_comm] using this.le
  refine ⟨D, hDpos, ?_⟩
  intro κ _ _ d hd i hi
  have hdpos (h : κ) : 0 < d h := hDpos.trans_le (hd h)
  have herror : C * ∑ h, (d h : ℝ)⁻¹ ≤ ε * Fintype.card κ := by
    calc
      _ = ∑ h, C / (d h : ℝ) := by simp only [mul_sum, div_eq_mul_inv]
      _ ≤ ∑ _h : κ, ε := by
        apply sum_le_sum
        intro h _
        apply (div_le_iff₀ (Nat.cast_pos.mpr (hdpos h))).mpr
        exact hC.trans (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (hd h)) hε.le)
      _ = _ := by rw [sum_const, nsmul_eq_mul, card_univ, mul_comm]
  refine (card_filter_piFinset_finsuppAntidiag_sum_apply_div_le_div_sub_mul_le
    s hi d hdpos hη).trans ?_
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_)
    (prod_nonneg fun _ _ ↦ Nat.cast_nonneg _)
  dsimp [C] at herror
  nlinarith only [herror]

/-- The empty block family has exactly one monomial; its tail at the mean has probability one.
For `i ∈ s`, the lower-tail estimates still apply with non-strict thresholds: their exponents
vanish when `Fintype.card κ = 0`. -/
example (s : Finset ι) (i : ι) :
    ((Fintype.piFinset (fun _h : Fin 0 ↦ finsuppAntidiag s (1 : ℕ))).filter
      (fun f ↦ ∑ h, (f h i : ℝ) ≤ 0)).card = 1 := by
  simp

/-- Three blocks of binary monomials: the normalized exponent sum has mean `3 / 2`, and
this bounds the number lying at or below half that mean. -/
example (d : Fin 3 → ℕ) (hd : ∀ h, 0 < d h) :
    ((Fintype.piFinset (fun h ↦ finsuppAntidiag (univ : Finset (Fin 2)) (d h))).filter
      (fun f ↦ ∑ h, (f h 0 : ℝ) / d h ≤ 3 / 4)).card ≤
      (∏ h, (finsuppAntidiag (univ : Finset (Fin 2)) (d h)).card : ℝ) *
        Real.exp (-9 / 32 + 9 / 64 * ∑ h, (d h : ℝ)⁻¹) := by
  have h := card_filter_piFinset_finsuppAntidiag_sum_apply_div_le_div_sub_mul_le
    (univ : Finset (Fin 2)) (mem_univ 0) d hd (η := 1 / 4) (by norm_num)
  norm_num only [card_univ, Fintype.card_fin] at h
  simpa only [neg_div] using h

end Finset

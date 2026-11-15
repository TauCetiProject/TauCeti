/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Height.MvPolynomial
public import TauCeti.RingTheory.MvPolynomial.FormIndex

import TauCeti.NumberTheory.DiophantineApproximation.Roth.IndexEstimate
import TauCeti.NumberTheory.Height.Basic

/-!
# Generalized Roth lemma for the index along linear forms

This file bounds the form index `MvPolynomial.formIndex d M P` of a nonzero multihomogeneous
polynomial `P` along a tuple of linear forms `M : Fin m → ι → K` over a number field `K` when the
block degree bounds `d h` decay geometrically (`d (h + 1) ≤ σ * d h` for `0 < σ ≤ 1 / 2`) and the
heights of the forms are large compared to `h(P)` and `m * d 0 * [K : ℚ]`
(Bombieri–Gubler, Lemma 7.5.19). Combined with
`MvPolynomial.exists_eval_hasseDeriv_ne_zero_eq_formIndex`, an upper bound on `formIndex d M P`
produces a low-order Hasse derivative of the auxiliary polynomial `P` that does not vanish on the
intersection of hyperplane kernels `∏ h, ker (M h)` in Schmidt's proof of the Subspace Theorem.

The proof reduces the multivariable linear-form statement to Roth's lemma
(`TauCeti.weightedIndex_le_of_logHeight_le`):
1. The height lower bound forces each form `M h` to be nonzero, and in each block `h`,
   `Height.exists_logHeight_le_mul_logHeight₁_div` finds distinct coordinates `i₀ h ≠ i₁ h` with
   `M h (i₁ h) ≠ 0` such that `h(M h) ≤ (card ι - 1) * h(-M h (i₀ h) / M h (i₁ h))`.
2. Iterated elimination (`MvPolynomial.exists_elimination`) removes every coordinate outside
   `{i₀ h, i₁ h}` by first dividing out each eliminated variable's lowest power and then
   specializing that variable to `0`, without vanishing, without increasing the multidegrees or
   the coefficient height (`MvPolynomial.logHeight_le_of_coeff_mem_range`), and without lowering
   `formIndex` along the truncated forms.
3. Embedding the surviving two coordinates per block (`MvPolynomial.formIndex_rename`) and
   dehomogenizing (`MvPolynomial.formIndex_eq_weightedIndex_dehomogenize_of_ne_zero`, packaged in
   `MvPolynomial.exists_le_weightedIndex_of_isMultiHomogeneous`) yields a nonzero polynomial in
   `m` variables of no larger height to which Roth's lemma applies.

Heights are relative logarithmic heights: `h(P)` is `MvPolynomial.logHeight` and `h(M h)` is
`Height.logHeight` (differing from Bombieri–Gubler's absolute logarithmic heights by `[K : ℚ]`).

## Main results

* `MvPolynomial.formIndex_le_of_degree_ratio`: the generalized Roth lemma for
  `MvPolynomial.formIndex`.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
  Definitions 7.5.17–7.5.18 and Lemma 7.5.19.
-/

public section

open Module

namespace MvPolynomial

section GeneralizedRoth

/-- **Generalized Roth lemma for the index along linear forms** (Bombieri–Gubler, Lemma 7.5.19).
Let `P ≠ 0` be a multihomogeneous polynomial in `m ≥ 1` blocks of `card ι ≥ 2` variables over a
number field `K`, with multidegree `e h ≤ d h` for positive weights `d h` satisfying
`d (h + 1) ≤ σ * d h` where `0 < σ ≤ 1 / 2`, and let `M : Fin m → ι → K` be a tuple of linear
forms. If `(card ι - 1) * σ⁻¹ * (h(P) + 4 * m * d 0 * [K : ℚ]) ≤ d h * h(M h)` for every block
`h`, then `formIndex d M P ≤ 2 * m * σ ^ (1 / 2 ^ (m - 1))`. Heights `h(P)` and `h(M h)` are
relative logarithmic heights. -/
theorem formIndex_le_of_degree_ratio {K : Type*} [Field K] [NumberField K]
    {m : ℕ} [NeZero m] {ι : Type*} [Fintype ι] [Nontrivial ι]
    {P : MvPolynomial (Fin m × ι) K} (hP : P ≠ 0) {e d : Fin m → ℕ}
    (hPe : P.IsMultiHomogeneous e) (hed : ∀ h, e h ≤ d h) (hd : ∀ h, 0 < d h)
    {σ : ℝ} (hσ₀ : 0 < σ) (hσ : σ ≤ 1 / 2)
    (hratio : ∀ h j : Fin m, (j : ℕ) = h + 1 → (d j : ℝ) ≤ σ * d h)
    {M : Fin m → ι → K}
    (hMh : ∀ h, ((Fintype.card ι - 1 : ℕ) : ℝ) *
        (σ⁻¹ * (P.logHeight + 4 * m * d 0 * finrank ℚ K)) ≤ d h * Height.logHeight (M h)) :
    formIndex d M P ≤ ENNReal.ofReal (2 * m * σ ^ ((1 : ℝ) / 2 ^ (m - 1))) := by
  have hcard_pos : (0 : ℝ) < ((Fintype.card ι - 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.sub_pos_of_lt Fintype.one_lt_card
  have hM (h : Fin m) : M h ≠ 0 := by
    intro h0
    have hrhs : (d h : ℝ) * Height.logHeight (M h) = 0 := by simp [h0]
    have hpos_sum : 0 < P.logHeight + 4 * (m : ℝ) * d 0 * finrank ℚ K := by
      have : (0 : ℝ) < 4 * (m : ℝ) * d 0 * finrank ℚ K := by
        have := NeZero.pos m
        have := hd 0
        have := Module.finrank_pos (R := ℚ) (M := K)
        positivity
      linarith [P.logHeight_nonneg]
    have hlhs : 0 < ((Fintype.card ι - 1 : ℕ) : ℝ) *
        (σ⁻¹ * (P.logHeight + 4 * m * d 0 * finrank ℚ K)) :=
      mul_pos hcard_pos (mul_pos (inv_pos.mpr hσ₀) hpos_sum)
    linarith [hMh h]
  -- Step 1: in each block, choose distinct coordinates `i₀ h ≠ i₁ h` capturing `h(M h)`.
  have hchoice : ∀ h : Fin m, ∃ i₀ i₁ : ι, i₀ ≠ i₁ ∧ M h i₁ ≠ 0 ∧
      Height.logHeight (M h) ≤
        ((Fintype.card ι - 1 : ℕ) : ℝ) * Height.logHeight₁ (-M h i₀ / M h i₁) := by
    intro h
    obtain ⟨i₀, i₁, hne, hne0, hlog⟩ :=
      Height.exists_logHeight_le_mul_logHeight₁_div (hM h)
    refine ⟨i₀, i₁, hne, hne0, ?_⟩
    rw [Nat.card_eq_fintype_card] at hlog
    rwa [neg_div, Height.logHeight₁_neg]
  choose i₀ i₁ hdiff hM₁ hlog_M using hchoice
  -- Steps 2–3: eliminate all other coordinates and dehomogenize to `Fin m` variables.
  obtain ⟨R, hR0, hRdeg_e, hRcoeff, hind⟩ :=
    exists_le_weightedIndex_of_isMultiHomogeneous (d := d) hdiff hM₁ hP hPe
  have hRdeg (h : Fin m) : R.degreeOf h ≤ d h := (hRdeg_e h).trans (hed h)
  have hRlog : R.logHeight ≤ P.logHeight := logHeight_le_of_coeff_mem_range hRcoeff
  -- Step 4: verify the height hypothesis of Roth's lemma and conclude.
  let α : Fin m → K := fun h ↦ -M h (i₀ h) / M h (i₁ h)
  have hα : ∀ h : Fin m,
      σ⁻¹ * (R.logHeight + 4 * m * d 0 * finrank ℚ K) ≤
        d h * Height.logHeight₁ (α h) := by
    intro h
    have h1 : ((Fintype.card ι - 1 : ℕ) : ℝ) *
        (σ⁻¹ * (R.logHeight + 4 * m * d 0 * finrank ℚ K)) ≤
        ((Fintype.card ι - 1 : ℕ) : ℝ) *
          (σ⁻¹ * (P.logHeight + 4 * m * d 0 * finrank ℚ K)) := by
      gcongr
    have h2 : d h * Height.logHeight (M h) ≤
        ((Fintype.card ι - 1 : ℕ) : ℝ) * (d h * Height.logHeight₁ (α h)) := by
      calc (d h : ℝ) * Height.logHeight (M h)
          ≤ d h * (((Fintype.card ι - 1 : ℕ) : ℝ) * Height.logHeight₁ (α h)) := by
            gcongr; exact hlog_M h
        _ = ((Fintype.card ι - 1 : ℕ) : ℝ) * (d h * Height.logHeight₁ (α h)) := by ring
    exact le_of_mul_le_mul_left (h1.trans ((hMh h).trans h2)) hcard_pos
  exact hind.trans
    (TauCeti.weightedIndex_le_of_logHeight_le hR0 hd hRdeg hσ₀ hσ hratio α hα)

/-- Acceptance check: over `ℚ` with two variables per block and one block (`m = 1`),
`P = X (0, 1) - X (0, 0)` and `M 0 = ![1, 3 ^ 10]` satisfy the hypotheses of
`MvPolynomial.formIndex_le_of_degree_ratio` at `σ = 1 / 2`, giving `formIndex d M P ≤ 1`. -/
example :
    let P : MvPolynomial (Fin 1 × Fin 2) ℚ := X (0, 1) - X (0, 0)
    let d : Fin 1 → ℕ := fun _ ↦ 1
    let M : Fin 1 → Fin 2 → ℚ := fun _ ↦ ![1, 3 ^ 10]
    formIndex d M P ≤
      ENNReal.ofReal (2 * (1 : ℕ) * (1 / 2 : ℝ) ^ ((1 : ℝ) / 2 ^ (1 - 1))) := by
  intro P d M
  have hP0 : P ≠ 0 := fun h ↦ by
    have := congrArg (eval fun p : Fin 1 × Fin 2 ↦ (p.2 : ℚ)) h
    simp [P] at this
  have hPe : P.IsMultiHomogeneous d := by
    have hpi : (Pi.single 0 1 : Fin 1 → ℕ) = d := by
      ext h
      fin_cases h
      simp [d]
    rw [← hpi]
    exact (isMultiHomogeneous_X (R := ℚ) 0 1).sub (isMultiHomogeneous_X 0 0)
  have hlogP : P.logHeight ≤ 0 := by
    rw [← logHeight_blockDehomogenize_of_isMultiHomogeneous hPe]
    have hdehom : blockDehomogenize P = X 0 - C 1 := by simp [P]
    rw [hdehom, logHeight_X_sub_C]
    simp
  have hlogM : (10 : ℝ) * Real.log 3 ≤ Height.logHeight (M 0) := by
    have hm : ((3 : ℝ) ^ 10 : ℝ) ≤ Height.mulHeight (M 0) := by
      have hratio_le : Height.mulHeight₁ (M 0 1 / M 0 0) ≤ Height.mulHeight (M 0) :=
        Height.mulHeight₁_div_le_mulHeight (M 0) 1 0
      have hm1 : Height.mulHeight₁ (M 0 1 / M 0 0) = 3 ^ 10 := by
        have hval : M 0 1 / M 0 0 = (3 : ℚ) ^ 10 := by simp [M]
        rw [hval, Rat.mulHeight₁_eq_max]
        norm_num
      exact hm1.symm.trans_le hratio_le
    rw [Height.logHeight_eq_log_mulHeight]
    have h10 : (10 : ℝ) * Real.log 3 = Real.log ((3 : ℝ) ^ 10) := by
      rw [Real.log_pow]
      norm_num
    exact h10.trans_le (Real.log_le_log (by positivity) hm)
  have hlog3 : 1 < Real.log 3 := by
    have hexp : Real.exp 1 < 3 := Real.exp_one_lt_d9.trans (by norm_num)
    simpa [Real.log_exp] using Real.log_lt_log (Real.exp_pos 1) hexp
  refine formIndex_le_of_degree_ratio hP0 hPe (fun _ ↦ le_rfl) (fun _ ↦ Nat.zero_lt_one)
    (by norm_num) (by norm_num) (fun h j hhj ↦ by omega) fun h ↦ ?_
  fin_cases h
  have hfin : (finrank ℚ ℚ : ℝ) = 1 := by simp
  rw [hfin]
  norm_num
  linarith

/-- Rejection check for `[Nontrivial ι]`: with `ι = Fin 1` (single variable per block),
`card ι - 1 = 0`, so the height hypothesis holds vacuously for `P = X (0, 0)`, `d = 1`, `M = 1`,
`σ = 1 / 4`, yet `formIndex d M P = 1 > 2 * 1 * (1 / 4)`. -/
example :
    let P : MvPolynomial (Fin 1 × Fin 1) ℚ := X (0, 0)
    let d : Fin 1 → ℕ := fun _ ↦ 1
    let M : Fin 1 → Fin 1 → ℚ := fun _ _ ↦ 1
    let σ : ℝ := 1 / 4
    (∀ h, ((Fintype.card (Fin 1) - 1 : ℕ) : ℝ) *
        (σ⁻¹ * (P.logHeight + 4 * (1 : ℕ) * d 0 * finrank ℚ ℚ)) ≤
          d h * Height.logHeight (M h)) ∧
      ENNReal.ofReal (2 * (1 : ℕ) * σ ^ ((1 : ℝ) / 2 ^ (1 - 1))) < formIndex d M P := by
  intro P d M σ
  constructor
  · intro h
    simp
  · have hP : formIndex d M P = 1 := by
      have hM : ∀ h, M h 0 ≠ 0 := fun _ ↦ one_ne_zero
      rw [formIndex_eq_iInf hM]
      have hsub : substFormInv M (fun _ ↦ 0) P = X (0, 0) := by
        simp [P, substFormInv_X_self, M]
      rw [hsub, support_X, Finset.iInf_singleton]
      simp [d]
    rw [hP]
    norm_num [σ]

end GeneralizedRoth

end MvPolynomial

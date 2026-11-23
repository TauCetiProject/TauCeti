/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.Polynomial.Vieta
import TauCeti.Analysis.Calculus.ContDiff.Matrix
import TauCeti.RingTheory.Polynomial.Resultant.Discriminant

/-!
# Regularity of the Sylvester matrix and of the discriminant

The entries of the Sylvester matrix of two polynomials are coefficients of those polynomials or
zero, and the discriminant of a monic polynomial is, up to sign, the determinant of the Sylvester
matrix of the polynomial and its derivative. So for polynomials whose coefficients depend `C^n` on
a parameter, the Sylvester matrix and the discriminant depend `C^n` on it as well.

## Main results

* `TauCeti.contDiffOn_sylvester_apply`: an entry of the Sylvester matrix of two families of
  polynomials with `C^n` coefficients is `C^n`.
* `TauCeti.contDiffOn_discr_of_monic`: the discriminant of a family of monic polynomials of fixed
  degree with `C^n` coefficients is `C^n`.
* `TauCeti.contDiffOn_discr_prod_X_sub_C`: if `b_j(y) = e_j(R(y))` are `C^n`, then the discriminant
  of `∏_{w ∈ R(y)} (X - w)` is `C^n`.
-/

public section

open Finset Polynomial

namespace TauCeti

variable {𝕜 E 𝔸 : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedCommRing 𝔸] [NormedAlgebra 𝕜 𝔸] {n : WithTop ℕ∞} {s : Set E}

/-- An entry of the Sylvester matrix of two families of polynomials whose coefficients are `C^n`
on a set is `C^n` there. -/
theorem contDiffOn_sylvester_apply {f g : E → 𝔸[X]}
    (hf : ∀ k, ContDiffOn 𝕜 n (fun y ↦ (f y).coeff k) s)
    (hg : ∀ k, ContDiffOn 𝕜 n (fun y ↦ (g y).coeff k) s) (p q : ℕ) (i j : Fin (p + q)) :
    ContDiffOn 𝕜 n (fun y ↦ sylvester (f y) (g y) p q i j) s := by
  induction j using Fin.addCases with
  | left j =>
    by_cases h : (i : ℕ) ∈ Set.Icc (j : ℕ) (j + q)
    · simpa only [sylvester, Matrix.of_apply, Fin.addCases_left, h, ↓reduceIte] using hg _
    · simpa only [sylvester, Matrix.of_apply, Fin.addCases_left, h, ↓reduceIte] using
        contDiffOn_const
  | right j =>
    by_cases h : (i : ℕ) ∈ Set.Icc (j : ℕ) (j + p)
    · simpa only [sylvester, Matrix.of_apply, Fin.addCases_right, h, ↓reduceIte] using hf _
    · simpa only [sylvester, Matrix.of_apply, Fin.addCases_right, h, ↓reduceIte] using
        contDiffOn_const

/-- **Regularity of the discriminant.** If `P y` is monic of degree `m` for `y ∈ s` and its
coefficients are `C^n` on `s`, then its discriminant is `C^n` on `s`: up to sign, it is the
determinant of the Sylvester matrix of `P y` and its derivative. -/
theorem contDiffOn_discr_of_monic {m : ℕ} {P : E → 𝔸[X]} (hmon : ∀ y ∈ s, (P y).Monic)
    (hdeg : ∀ y ∈ s, (P y).natDegree = m) (hc : ∀ k, ContDiffOn 𝕜 n (fun y ↦ (P y).coeff k) s) :
    ContDiffOn 𝕜 n (fun y ↦ (P y).discr) s := by
  have hc' : ∀ k, ContDiffOn 𝕜 n (fun y ↦ (P y).derivative.coeff k) s := fun k ↦ by
    simpa only [coeff_derivative] using (hc (k + 1)).mul contDiffOn_const
  refine ((contDiffOn_const (c := (-1 : 𝔸) ^ (m * (m - 1) / 2))).mul
    (ContDiffOn.matrix_det fun i j ↦ contDiffOn_sylvester_apply hc hc' m (m - 1) i j)).congr
    fun y hy ↦ ?_
  rw [(hmon y hy).discr_eq_neg_one_pow_mul_resultant_deriv, hdeg y hy, resultant]

/-- **Regularity of the discriminant in the roots.** If `b₁, …, b_m` are `C^n` on `s` and
`b_j(y) = e_j(R(y))` for a multiset `R(y)` of `m` points, then the discriminant of
`∏_{w ∈ R(y)} (X - w)` is `C^n` on `s`. By Vieta's formulas the coefficients of that product are
`±b_j` and `1`. -/
theorem contDiffOn_discr_prod_X_sub_C [Nontrivial 𝔸] {m : ℕ} {b : ℕ → E → 𝔸}
    {R : E → Multiset 𝔸} (hb : ∀ j ∈ Icc 1 m, ContDiffOn 𝕜 n (b j) s)
    (hR : ∀ y ∈ s, Multiset.card (R y) = m ∧ ∀ j ∈ Icc 1 m, b j y = (R y).esymm j) :
    ContDiffOn 𝕜 n (fun y ↦ ((R y).map fun w ↦ X - C w).prod.discr) s := by
  set P : E → 𝔸[X] := fun y ↦ ((R y).map fun w ↦ X - C w).prod with hP
  -- The coefficients of `P y`, read off Vieta's formulas.
  set c : ℕ → E → 𝔸 := fun k y ↦
    if k < m then (-1) ^ (m - k) * b (m - k) y else if k = m then 1 else 0 with hc
  have hcd : ∀ k, ContDiffOn 𝕜 n (c k) s := by
    intro k
    by_cases hk : k < m
    · simpa only [hc, hk, ↓reduceIte] using
        contDiffOn_const.mul (hb (m - k) (mem_Icc.2 ⟨by omega, by omega⟩))
    · by_cases hk' : k = m
      · simpa only [hc, hk, hk', ↓reduceIte, lt_irrefl] using contDiffOn_const
      · simpa only [hc, hk, hk', ↓reduceIte] using contDiffOn_const
  have hPc : ∀ y ∈ s, ∀ k, (P y).coeff k = c k y := by
    intro y hy k
    obtain ⟨hcard, hbR⟩ := hR y hy
    by_cases hk : k ≤ m
    · rw [hP, Multiset.prod_X_sub_C_coeff _ (hcard ▸ hk), hcard]
      rcases hk.lt_or_eq with hk | rfl
      · simp only [hc, hk, ↓reduceIte, hbR (m - k) (mem_Icc.2 ⟨by omega, by omega⟩)]
      · simp [hc]
    · rw [coeff_eq_zero_of_natDegree_lt (by
        rw [hP, natDegree_multiset_prod_X_sub_C_eq_card, hcard]; omega)]
      simp [hc, show ¬k < m by omega, show k ≠ m by omega]
  exact contDiffOn_discr_of_monic (fun y _ ↦ monic_multisetProd_X_sub_C (R y))
    (fun y hy ↦ by rw [natDegree_multiset_prod_X_sub_C_eq_card, (hR y hy).1])
    fun k ↦ (hcd k).congr fun y hy ↦ hPc y hy k

end TauCeti

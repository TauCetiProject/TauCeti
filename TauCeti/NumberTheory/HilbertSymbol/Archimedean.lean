/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Real.Sqrt
public import TauCeti.LinearAlgebra.QuadraticForm.Real
public import TauCeti.NumberTheory.HilbertSymbol.Basic

/-!
# The Hilbert symbol over `ℝ`

This file computes the norm-equation Hilbert symbol `TauCeti.hilbertSymbol` over `ℝ`.

Over `ℝ` the equation `b = x² - a y²` is solvable unless both `a` and `b` are negative, because
`x² - a y²` is then positive for every nonzero `(x, y)`. Hence `(a, b) = -1` exactly when
`a < 0` and `b < 0`. Bimultiplicativity over `ℝ` is read off this formula, and so is the value of
the product `∏_{i<j} (a_i, a_j)` attached to a diagonal real form: it is `(-1)^(q(q-1)/2)`,
where `q` is the number of negative coefficients.

By Sylvester's law of inertia that count is the negative index of the form the family
diagonalizes, so the product is an invariant of the isometry class and is the archimedean
counterpart of the Hasse invariant of a form over a nonarchimedean local field.  Evaluating it on
the normal form `p⟨1⟩ ⊥ q⟨-1⟩` gives the archimedean Hasse sign `(-1)^(q(q-1)/2)` of that form.

## Main results

* `TauCeti.hilbertSymbol_real`: the closed formula for the real symbol.
* `TauCeti.hilbertSymbol_real_mul_left`, `TauCeti.hilbertSymbol_real_mul_right`:
  bimultiplicativity over `ℝ`.
* `TauCeti.exists_hilbertSymbol_real_eq_neg_one`: every real nonsquare has a partner with symbol
  `-1`.
* `TauCeti.prod_hilbertSymbol_real`: the product of the symbols over ordered pairs of a finite
  family of real units.
* `TauCeti.prod_hilbertSymbol_real_of_equiv_weightedSumSquares`: that product is `(-1)^(q(q-1)/2)`
  for the negative index `q` of any real form the family diagonalizes, so it depends only on the
  isometry class.
* `TauCeti.prod_hilbertSymbol_realSignatureForm`: the archimedean Hasse sign of the normal form
  `QuadraticForm.realSignatureForm p q` is `(-1)^(q(q-1)/2)`.

## References

* J.-P. Serre, *A Course in Arithmetic*, Chapter III, §1.1.
* O. T. O'Meara, *Introduction to Quadratic Forms*, 71:18.
-/

public section

namespace TauCeti

open Finset

section Real

/-- The real Hilbert symbol is `-1` exactly when both parameters are negative. -/
theorem hilbertSymbol_real (a b : ℝˣ) :
    hilbertSymbol a b = if (a : ℝ) < 0 ∧ (b : ℝ) < 0 then -1 else 1 := by
  classical
  rw [hilbertSymbol_def]
  split_ifs with h hab hab
  · -- `x² - a y²` is nonnegative when `a < 0`, so it never equals `b < 0`.
    obtain ⟨x, y, h⟩ := h
    nlinarith [sq_nonneg x, sq_nonneg y, hab.1, hab.2]
  · rfl
  · rfl
  · refine absurd ?_ h
    rcases (b.ne_zero).lt_or_gt with hb | hb
    · -- Here `a > 0`, and `b = 0² - a (√(-b/a))²`.
      have ha : 0 < (a : ℝ) := (a.ne_zero).lt_or_gt.resolve_left fun ha => hab ⟨ha, hb⟩
      refine ⟨0, √(-b / a), ?_⟩
      rw [Real.sq_sqrt (div_nonneg (neg_nonneg.mpr hb.le) ha.le)]
      field_simp
      ring
    · exact ⟨√b, 0, by rw [Real.sq_sqrt hb.le]; ring⟩

/-- The real Hilbert symbol is `-1` exactly when both parameters are negative. -/
theorem hilbertSymbol_real_eq_neg_one_iff (a b : ℝˣ) :
    hilbertSymbol a b = -1 ↔ (a : ℝ) < 0 ∧ (b : ℝ) < 0 := by
  rw [hilbertSymbol_real]
  split_ifs with h <;> simp [h]

/-- The real Hilbert symbol is `1` exactly when one of the parameters is positive. -/
theorem hilbertSymbol_real_eq_one_iff (a b : ℝˣ) :
    hilbertSymbol a b = 1 ↔ 0 < (a : ℝ) ∨ 0 < (b : ℝ) := by
  have ha := a.ne_zero
  have hb := b.ne_zero
  rw [hilbertSymbol_real]
  split_ifs with h
  · exact ⟨fun h' => absurd h' (by decide), fun h' => by grind⟩
  · simp only [true_iff]
    grind

/-- The real Hilbert symbol is multiplicative in its first parameter. -/
theorem hilbertSymbol_real_mul_left (a a' b : ℝˣ) :
    hilbertSymbol (a * a') b = hilbertSymbol a b * hilbertSymbol a' b := by
  simp only [hilbertSymbol_real, Units.val_mul, mul_neg_iff]
  have := a.ne_zero
  have := a'.ne_zero
  split_ifs <;> (try simp) <;> grind

/-- The real Hilbert symbol is multiplicative in its second parameter. -/
theorem hilbertSymbol_real_mul_right (a b b' : ℝˣ) :
    hilbertSymbol a (b * b') = hilbertSymbol a b * hilbertSymbol a b' := by
  let _ : Invertible (2 : ℝ) := invertibleOfNonzero two_ne_zero
  calc
    hilbertSymbol a (b * b') = hilbertSymbol (b * b') a := hilbertSymbol_comm _ _
    _ = hilbertSymbol b a * hilbertSymbol b' a := hilbertSymbol_real_mul_left _ _ _
    _ = hilbertSymbol a b * hilbertSymbol a b' := by
      rw [hilbertSymbol_comm b a, hilbertSymbol_comm b' a]

/-- Every real nonsquare `b` has a partner `a` with `(a, b) = -1`; one may take `a = -1`. -/
theorem exists_hilbertSymbol_real_eq_neg_one {b : ℝˣ} (hb : ¬IsSquare b) :
    ∃ a : ℝˣ, hilbertSymbol a b = -1 := by
  refine ⟨-1, (hilbertSymbol_real_eq_neg_one_iff _ _).mpr ⟨by simp, ?_⟩⟩
  refine (b.ne_zero).lt_or_gt.resolve_right fun hpos => hb ?_
  have hs : √(b : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
  exact ⟨Units.mk0 _ hs, Units.ext <| by simp [Real.mul_self_sqrt hpos.le]⟩

/-- The product of the real Hilbert symbols `(a_i, a_j)` over the pairs `i < j` of a finite
family is `(-1)^(q(q-1)/2)`, where `q` is the number of negative members of the family. -/
theorem prod_hilbertSymbol_real {ι : Type*} [Fintype ι] [LinearOrder ι] (a : ι → ℝˣ) :
    ∏ ij ∈ univ.filter (fun ij : ι × ι => ij.1 < ij.2), hilbertSymbol (a ij.1) (a ij.2) =
      (-1) ^ (#{i | (a i : ℝ) < 0}).choose 2 := by
  classical
  simp_rw [hilbertSymbol_real]
  rw [prod_ite, prod_const_one, mul_one, prod_const, filter_filter,
    ← card_product_filter_lt]
  congr 2
  ext ij
  simp only [mem_filter, mem_univ, mem_product, true_and]
  tauto

/-- The product of the real Hilbert symbols over the ordered pairs of a diagonalization of a
real quadratic form is `(-1)^(q(q-1)/2)`, where `q = sigNeg Q` is the negative index of the
form.  In particular the product depends only on the isometry class of `Q` and not on the chosen
diagonalization. -/
theorem prod_hilbertSymbol_real_of_equiv_weightedSumSquares {M : Type*} [AddCommGroup M]
    [Module ℝ M] {ι : Type*} [Fintype ι] [LinearOrder ι] {Q : _root_.QuadraticForm ℝ M}
    {a : ι → ℝˣ}
    (h : Q.Equivalent (QuadraticMap.weightedSumSquares ℝ fun i ↦ (a i : ℝ))) :
    ∏ ij ∈ univ.filter (fun ij : ι × ι => ij.1 < ij.2), hilbertSymbol (a ij.1) (a ij.2) =
      (-1) ^ (sigNeg Q).choose 2 := by
  classical
  rw [prod_hilbertSymbol_real, _root_.QuadraticForm.sigNeg_of_equiv_weightedSumSquares h,
    Set.ncard_eq_toFinset_card', Set.toFinset_ofPred]

/-- **The archimedean Hasse sign of the normal form.**  Listing the weights of
`QuadraticForm.realSignatureForm p q` as `fun i : Fin (p + q) ↦ if i < p then 1 else -1`, the
product of the real Hilbert symbols over the ordered pairs `i < j` is `(-1)^(q(q-1)/2)`. -/
theorem prod_hilbertSymbol_realSignatureForm (p q : ℕ) :
    ∏ ij ∈ univ.filter (fun ij : Fin (p + q) × Fin (p + q) => ij.1 < ij.2),
        hilbertSymbol (if (ij.1 : ℕ) < p then (1 : ℝˣ) else -1)
          (if (ij.2 : ℕ) < p then (1 : ℝˣ) else -1) =
      (-1) ^ q.choose 2 := by
  have hweight : (fun i : Fin (p + q) ↦ ((if (i : ℕ) < p then (1 : ℝˣ) else -1 : ℝˣ) : ℝ)) ∘
      finSumFinEquiv = Sum.elim (fun _ ↦ (1 : ℝ)) fun _ ↦ -1 := by
    funext x
    cases x <;> simp
  have hdiag : (_root_.QuadraticForm.realSignatureForm p q).Equivalent
      (QuadraticMap.weightedSumSquares ℝ fun i : Fin (p + q) ↦
        ((if (i : ℕ) < p then (1 : ℝˣ) else -1 : ℝˣ) : ℝ)) := by
    rw [_root_.QuadraticForm.realSignatureForm_def]
    exact ⟨((_root_.QuadraticForm.isometryEquivWeightedSumSquaresReindex (R := ℝ) _
      finSumFinEquiv).trans (_root_.QuadraticForm.weightedSumSquaresCongr hweight)).symm⟩
  rw [prod_hilbertSymbol_real_of_equiv_weightedSumSquares hdiag,
    _root_.QuadraticForm.sigNeg_realSignatureForm]

end Real

end TauCeti

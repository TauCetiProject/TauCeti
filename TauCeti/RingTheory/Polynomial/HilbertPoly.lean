/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Binomial
public import Mathlib.RingTheory.Polynomial.HilbertPoly

/-!
# Degree bounds and integrality for Hilbert polynomials

This file extends Mathlib's `Polynomial.hilbertPoly` API with two ingredients needed when turning
the rational Hilbert–Serre series of a `ℤ`-graded module into its eventual Hilbert polynomial:

* **Degree bounds.** Over any ring `R`, `(ascPochhammer R d).comp (X - C c + 1)` has degree at
  most `d`. Over any field `F` (with no characteristic assumption), `preHilbertPoly F d k`
  therefore has degree at most `d`, and `hilbertPoly p d` has degree strictly less than `d` in
  `WithBot ℕ`. In particular, for `d = 0` it has degree `⊥ < 0`.
* **Integer values and integrality of `(e - 1)! • hilbertPoly`.** Whenever `d! ≠ 0` in `F`,
  evaluating `preHilbertPoly F d k` at an integer `z` yields the generalized multichoose number
  `Ring.multichoose (z - k + 1) d` cast to `F`. Consequently, for every integer polynomial
  `h : ℤ[X]` and every field `F`, `hilbertPoly (h.map (Int.castRingHom F)) d` takes integer values
  at every integer `z : ℤ`, and multiplying `hilbertPoly (h.map (Int.castRingHom ℚ)) e` by
  `(e - 1)!` produces a polynomial with integer coefficients.

## Main results

* `Polynomial.degree_ascPochhammer_comp_X_sub_C_add_one_le`:
  `((ascPochhammer R d).comp (X - C c + 1)).degree ≤ d`.
* `Polynomial.degree_preHilbertPoly_le`: `(preHilbertPoly F d k).degree ≤ d`.
* `Polynomial.degree_hilbertPoly_lt`: `(hilbertPoly p d).degree < (d : WithBot ℕ)`.
* `Polynomial.preHilbertPoly_eval_intCast`: evaluating `preHilbertPoly F d k` at an integer gives
  `Ring.multichoose (z - k + 1) d` when `d! ≠ 0` in `F`.
* `Polynomial.exists_int_eval_hilbertPoly_map_intCast`: for `h : ℤ[X]`, `hilbertPoly` of the image
  of `h` takes integer values at every integer.
* `Polynomial.exists_map_eq_factorial_nsmul_hilbertPoly`: for `h : ℤ[X]`,
  `(e - 1)! • hilbertPoly (h.map (Int.castRingHom ℚ)) e` has integer coefficients and degree `< e`.
-/

public section

namespace Polynomial

section Degree

/-- Composing `ascPochhammer R d` with `X - C c + 1` has degree at most `d` over any ring. -/
theorem degree_ascPochhammer_comp_X_sub_C_add_one_le {R : Type*} [Ring R] (d : ℕ) (c : R) :
    ((ascPochhammer R d).comp (X - C c + 1)).degree ≤ d := by
  have hdeg : (ascPochhammer R d).natDegree ≤ d := by
    rw [← ascPochhammer_map (Nat.castRingHom R) d]
    exact natDegree_map_le.trans (by rw [ascPochhammer_natDegree])
  have hlin : (X - C c + 1 : R[X]).natDegree ≤ 1 :=
    (natDegree_add_le _ _).trans
      (max_le ((natDegree_sub_le _ _).trans (max_le natDegree_X_le (by simp))) (by simp))
  exact degree_le_natDegree.trans
    (WithBot.coe_le_coe.mpr (natDegree_comp_le.trans (by simpa using Nat.mul_le_mul hdeg hlin)))

variable (F : Type*) [Field F]

/-- The basic Hilbert polynomial `preHilbertPoly F d k` has degree at most `d`, over any field
(without assuming characteristic zero). -/
theorem degree_preHilbertPoly_le (d k : ℕ) : (preHilbertPoly F d k).degree ≤ d :=
  (degree_smul_le _ _).trans (degree_ascPochhammer_comp_X_sub_C_add_one_le d (k : F))

variable {F}

/-- The Hilbert polynomial `hilbertPoly p d` has degree strictly less than `d` in `WithBot ℕ`,
over any field. -/
theorem degree_hilbertPoly_lt (p : F[X]) (d : ℕ) :
    (hilbertPoly p d).degree < (d : WithBot ℕ) := by
  cases d with
  | zero =>
    rw [hilbertPoly_zero_right, degree_zero]
    exact WithBot.bot_lt_coe 0
  | succ d =>
    rw [hilbertPoly_succ]
    refine (degree_sum_le p.support _).trans_lt ?_
    refine (Finset.sup_lt_iff (WithBot.bot_lt_coe (d + 1))).2 fun i _ ↦ ?_
    exact ((degree_smul_le _ _).trans (degree_preHilbertPoly_le F d i)).trans_lt
      (WithBot.coe_lt_coe.mpr (Nat.lt_succ_self d))

end Degree

section IntEval

variable (F : Type*) [Field F]

/-- Evaluating `preHilbertPoly F d k` at an integer `z` yields the generalized multichoose number
`Ring.multichoose (z - k + 1) d`, provided `d!` is nonzero in `F`. -/
theorem preHilbertPoly_eval_intCast {d : ℕ} (hfac : (d.factorial : F) ≠ 0) (k : ℕ) (z : ℤ) :
    (preHilbertPoly F d k).eval (z : F) = ((Ring.multichoose (z - k + 1 : ℤ) d : ℤ) : F) := by
  rw [preHilbertPoly, eval_smul, smul_eq_mul, eval_comp]
  have harg : eval (z : F) (X - C (k : F) + 1) = ((z - k + 1 : ℤ) : F) := by
    simp
  rw [harg, ← ascPochhammer_smeval_eq_eval]
  have hpoch : (ascPochhammer ℕ d).smeval ((z - k + 1 : ℤ) : F) =
      (((ascPochhammer ℕ d).smeval (z - k + 1 : ℤ) : ℤ) : F) := by
    rw [← eval₂_smulOneHom_eq_smeval, ← eval₂_smulOneHom_eq_smeval]
    symm
    refine (hom_eval₂ (ascPochhammer ℕ d) _ (Int.castRingHom F) _).trans ?_
    congr 1
    exact Subsingleton.elim _ _
  rw [hpoch, ← Ring.factorial_nsmul_multichoose_eq_ascPochhammer, nsmul_eq_mul, Int.cast_mul,
    Int.cast_natCast, inv_mul_cancel_left₀ hfac]

variable {F}

/-- For any integer polynomial `h : ℤ[X]`, `hilbertPoly (h.map (Int.castRingHom F)) d` takes
integer values at every integer `z : ℤ`, over any field `F`. -/
theorem exists_int_eval_hilbertPoly_map_intCast (h : ℤ[X]) (d : ℕ) (z : ℤ) :
    ∃ m : ℤ, (hilbertPoly (h.map (Int.castRingHom F)) d).eval (z : F) = (m : F) := by
  cases d with
  | zero => exact ⟨0, by simp [hilbertPoly_zero_right]⟩
  | succ d =>
    by_cases hfac : (d.factorial : F) = 0
    · refine ⟨0, ?_⟩
      simp [hilbertPoly_succ, preHilbertPoly, hfac]
    · refine ⟨∑ i ∈ (h.map (Int.castRingHom F)).support,
        h.coeff i * Ring.multichoose (z - i + 1 : ℤ) d, ?_⟩
      rw [hilbertPoly_succ, eval_finsetSum, Int.cast_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [eval_smul, smul_eq_mul, coeff_map, eq_intCast, preHilbertPoly_eval_intCast F hfac,
        Int.cast_mul]

/-- Multiplying `hilbertPoly (h.map (Int.castRingHom ℚ)) e` by `(e - 1)!` yields a polynomial with
integer coefficients and degree strictly less than `e`. -/
theorem exists_map_eq_factorial_nsmul_hilbertPoly (h : ℤ[X]) (e : ℕ) :
    ∃ Q : ℤ[X], Q.degree < (e : WithBot ℕ) ∧
      Q.map (Int.castRingHom ℚ) =
        (e - 1).factorial • hilbertPoly (h.map (Int.castRingHom ℚ)) e := by
  cases e with
  | zero =>
    exact ⟨0, by simp, by simp [hilbertPoly_zero_right]⟩
  | succ d =>
    let Q : ℤ[X] := ∑ i ∈ h.support,
      C (h.coeff i) * (ascPochhammer ℤ d).comp (X - C (i : ℤ) + 1)
    refine ⟨Q, ?_, ?_⟩
    · refine (degree_sum_le h.support _).trans_lt ?_
      refine (Finset.sup_lt_iff (WithBot.bot_lt_coe (d + 1))).2 fun i _ ↦ ?_
      rw [← smul_eq_C_mul]
      exact ((degree_smul_le _ _).trans
        (degree_ascPochhammer_comp_X_sub_C_add_one_le d (i : ℤ))).trans_lt
        (WithBot.coe_lt_coe.mpr (Nat.lt_succ_self d))
    · have hsupp : (h.map (Int.castRingHom ℚ)).support = h.support :=
        support_map_of_injective h Int.cast_injective
      rw [Nat.add_sub_cancel, hilbertPoly_succ, hsupp, Finset.smul_sum, Polynomial.map_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      have hpoch : ((ascPochhammer ℤ d).comp (X - C (i : ℤ) + 1)).map (Int.castRingHom ℚ) =
          (ascPochhammer ℚ d).comp (X - C (i : ℚ) + 1) := by
        simp [map_comp, ascPochhammer_map]
      have hfac : (d.factorial : ℚ) * (d.factorial : ℚ)⁻¹ = 1 :=
        mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero d))
      rw [Polynomial.map_mul, map_C, hpoch, preHilbertPoly, smul_comm, ← Nat.cast_smul_eq_nsmul ℚ,
        smul_smul, smul_smul, mul_assoc, hfac, mul_one, coeff_map, smul_eq_C_mul]

end IntEval

end Polynomial

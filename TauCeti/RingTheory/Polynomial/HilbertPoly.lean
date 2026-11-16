/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Binomial
public import Mathlib.RingTheory.Polynomial.HilbertPoly
import Mathlib.Algebra.Polynomial.Degree.Operations

/-!
# Degree bounds, integrality, and shifts for Hilbert polynomials

This file extends Mathlib's `Polynomial.hilbertPoly` API with three ingredients needed when
turning the rational Hilbert–Serre series of a `ℤ`-graded module into its eventual Hilbert
polynomial:

* **Degree bounds.** Over any field `F` (with no characteristic assumption), `preHilbertPoly F d k`
  has degree at most `d`, and therefore `hilbertPoly p d` has degree strictly less than `d` in
  `WithBot ℕ`. In particular, for `d = 0` it has degree `⊥ < 0`.
* **Integer values and integrality of `(e - 1)! • hilbertPoly`.** Whenever `d! ≠ 0` in `F`,
  evaluating `preHilbertPoly F d k` at an integer `z` yields the generalized multichoose number
  `Ring.multichoose (z - k + 1) d` cast to `F`. Consequently, for every integer polynomial
  `h : ℤ[X]` and every field `F`, `hilbertPoly (h.map (Int.castRingHom F)) d` takes integer values
  at every integer `z : ℤ`, and multiplying `hilbertPoly (h.map (Int.castRingHom ℚ)) e` by
  `(e - 1)!` produces a polynomial with integer coefficients.
* **Shifted series and polynomial uniqueness.** Given a sequence `f : ℤ → F` whose shifted
  generating series satisfies `(∑ n, f (d₀ + n) Xⁿ) * (1 - X)^e = h` in `F⟦X⟧` over a field `F`
  with `(e - 1)! ≠ 0`, the shifted Hilbert polynomial `(hilbertPoly h e).comp (X - C (d₀ : F))` has
  degree `< e` and agrees with `f d` for all `d ≥ d₀ + h.natDegree + 1`. Over any ring `R` with
  unique additive division (`HasUniqueDiv R`), two polynomials agreeing on all sufficiently large
  integers are equal.

## Main results

* `Polynomial.degree_preHilbertPoly_le`: `(preHilbertPoly F d k).degree ≤ d`.
* `Polynomial.degree_hilbertPoly_lt`: `(hilbertPoly p d).degree < (d : WithBot ℕ)`.
* `Polynomial.preHilbertPoly_eval_intCast`: evaluating `preHilbertPoly F d k` at an integer gives
  `Ring.multichoose (z - k + 1) d` when `d! ≠ 0` in `F`.
* `Polynomial.exists_int_eval_hilbertPoly_map_intCast`: for `h : ℤ[X]`, `hilbertPoly` of the image
  of `h` takes integer values at every integer.
* `Polynomial.exists_map_eq_factorial_nsmul_hilbertPoly`: for `h : ℤ[X]`,
  `(e - 1)! • hilbertPoly (h.map (Int.castRingHom ℚ)) e` has integer coefficients and degree `< e`.
* `Polynomial.eq_of_forall_ge_intCast_eval_eq`: two polynomials over a ring with `HasUniqueDiv`
  that agree on all integers from some point onward are equal.
* `Polynomial.eval_hilbertPoly_comp_sub_eq_of_mul_one_sub_pow_eq`: eventual evaluation of the
  shifted Hilbert polynomial associated to a rational series `h / (1 - X)^e`.
-/

public section

open PowerSeries

namespace Polynomial

section Degree

variable (F : Type*) [Field F]

/-- The basic Hilbert polynomial `preHilbertPoly F d k` has degree at most `d`, over any field
(without assuming characteristic zero). -/
theorem degree_preHilbertPoly_le (d k : ℕ) : (preHilbertPoly F d k).degree ≤ d := by
  rw [preHilbertPoly]
  refine (degree_smul_le _ _).trans ?_
  have hlin : (X - C (k : F) + 1 : F[X]).degree = 1 := by
    rw [sub_add, ← C_1, ← map_sub]
    exact degree_X_sub_C _
  rw [degree_comp, hlin, mul_one]
  · exact degree_le_natDegree.trans (by rw [ascPochhammer_natDegree])
  · rw [hlin]
    exact zero_lt_one

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
      have hlin : (X - C (i : ℤ) + 1 : ℤ[X]).degree = 1 := by
        rw [sub_add, ← C_1, ← map_sub]
        exact degree_X_sub_C _
      have hcomp : ((ascPochhammer ℤ d).comp (X - C (i : ℤ) + 1)).degree ≤ d := by
        rw [degree_comp, hlin, mul_one]
        · exact degree_le_natDegree.trans (by rw [ascPochhammer_natDegree])
        · rw [hlin]; exact zero_lt_one
      rw [← smul_eq_C_mul]
      exact ((degree_smul_le _ _).trans hcomp).trans_lt
        (WithBot.coe_lt_coe.mpr (Nat.lt_succ_self d))
    · have hsupp : (h.map (Int.castRingHom ℚ)).support = h.support :=
        support_map_of_injective h Int.cast_injective
      rw [Nat.add_sub_cancel, hilbertPoly_succ, hsupp, Finset.smul_sum, Polynomial.map_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [Polynomial.map_mul, map_C, eq_intCast, map_comp, ascPochhammer_map,
        Polynomial.map_add, Polynomial.map_sub, map_X, map_C, Polynomial.map_one, eq_intCast,
        Int.cast_natCast, coeff_map, eq_intCast, preHilbertPoly, smul_comm,
        ← Nat.cast_smul_eq_nsmul ℚ, smul_smul, smul_smul, mul_assoc,
        mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero d)), mul_one,
        smul_eq_C_mul]

end IntEval

section Eventual

/-- Evaluating `p.comp q` at an integer cast `(d : R)` equals `p.eval (q.eval (d : R))` over any
ring `R` (not necessarily commutative), because integer casts are central. -/
private theorem eval_comp_intCast {R : Type*} [Ring R] (p q : R[X]) (d : ℤ) :
    (p.comp q).eval (d : R) = p.eval (q.eval (d : R)) := by
  have hmul (u v : R[X]) : (u * v).eval (d : R) = u.eval (d : R) * v.eval (d : R) :=
    eval₂_mul_noncomm (RingHom.id R) (d : R) fun _ ↦ (Int.cast_commute d _).symm
  have hpow (m : ℕ) : (q ^ m).eval (d : R) = (q.eval (d : R)) ^ m := by
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ, hmul, ih, pow_succ]
  induction p using Polynomial.induction_on' with
  | add p₁ p₂ h₁ h₂ => simp [add_comp, h₁, h₂]
  | monomial k r => rw [monomial_comp, eval_C_mul, hpow, eval_monomial]

/-- Coefficient formula for `p.comp (X + 1)` over any ring `R`. -/
private theorem coeff_comp_X_add_one {R : Type*} [Ring R] (p : R[X]) (m k : ℕ)
    (hm : p.natDegree < m) :
    (p.comp (X + 1)).coeff k = ∑ i ∈ Finset.range m, p.coeff i * (i.choose k : R) := by
  have hpow (i : ℕ) : ((X + 1 : R[X]) ^ i).coeff k = (i.choose k : R) := by
    rw [(Commute.one_right (X : R[X])).add_pow, finsetSum_coeff]
    have hterm (j : ℕ) :
        ((X : R[X]) ^ j * 1 ^ (i - j) * (i.choose j : R[X])).coeff k =
          if k = j then (i.choose j : R) else 0 := by
      rw [one_pow, mul_one, ← C_eq_natCast, coeff_mul_C, coeff_X_pow]
      split_ifs <;> simp
    simp_rw [hterm]
    by_cases hki : k ≤ i
    · rw [Finset.sum_ite_eq _ k (fun j ↦ (i.choose j : R)),
        ite_eq_left (Finset.mem_range.mpr (Nat.lt_succ_of_le hki))]
    · rw [Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hki), Nat.cast_zero]
      refine Finset.sum_eq_zero fun j hj ↦ ?_
      have hne : k ≠ j := by have := Finset.mem_range.mp hj; omega
      simp [hne]
  conv_lhs => rw [as_sum_range' p m hm]
  rw [sum_comp, finsetSum_coeff]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [monomial_comp, coeff_C_mul, hpow]

/-- Two polynomials over a ring with unique additive division (`HasUniqueDiv`) that agree on every
integer greater than or equal to some bound `N` are equal. -/
theorem eq_of_forall_ge_intCast_eval_eq {R : Type*} [Ring R] [HasUniqueDiv R]
    {P Q : R[X]} {N : ℤ} (h : ∀ d : ℤ, N ≤ d → P.eval (d : R) = Q.eval (d : R)) : P = Q := by
  suffices hzero : ∀ (n : ℕ) (D : R[X]), D.natDegree ≤ n →
      (∀ d : ℤ, N ≤ d → D.eval (d : R) = 0) → D = 0 from
    sub_eq_zero.mp (hzero (P - Q).natDegree (P - Q) le_rfl fun d hd ↦ by
      rw [eval_sub, h d hd, sub_self])
  intro n
  induction n with
  | zero =>
    intro D hdeg hD
    rw [eq_C_of_natDegree_eq_zero (Nat.eq_zero_of_le_zero hdeg)] at hD ⊢
    simpa using hD N le_rfl
  | succ n ih =>
    intro D hdeg hD
    let Δ : R[X] := D.comp (X + 1) - D
    have hΔ_eval (d : ℤ) (hd : N ≤ d) : Δ.eval (d : R) = 0 := by
      rw [eval_sub, eval_comp_intCast, eval_add, eval_X, eval_one, ← Int.cast_one,
        ← Int.cast_add, hD (d + 1) (by omega), hD d hd, sub_self]
    have hΔ_deg : Δ.natDegree ≤ n := natDegree_le_iff_coeff_eq_zero.mpr fun k hk ↦ by
      rw [coeff_sub, coeff_comp_X_add_one D (n + 2) k (by omega)]
      by_cases hkn : k = n + 1
      · subst hkn
        rw [Finset.sum_eq_single (n + 1)
          (fun i hi hne ↦ by
            rw [Nat.choose_eq_zero_of_lt (by have := Finset.mem_range.mp hi; omega),
              Nat.cast_zero, mul_zero])
          (fun hnot ↦ absurd (Finset.mem_range.mpr (Nat.lt_succ_self _)) hnot)]
        simp
      · rw [coeff_eq_zero_of_natDegree_lt (by omega), sub_zero]
        exact Finset.sum_eq_zero fun i hi ↦ by
          rw [Nat.choose_eq_zero_of_lt (by have := Finset.mem_range.mp hi; omega),
            Nat.cast_zero, mul_zero]
    have hΔ_zero : Δ = 0 := ih Δ hΔ_deg hΔ_eval
    have hlead : D.coeff (n + 1) = 0 := by
      have h0 : Δ.coeff n = (n + 1) • D.coeff (n + 1) := by
        rw [coeff_sub, coeff_comp_X_add_one D (n + 2) n (by omega),
          Finset.sum_range_succ, Finset.sum_range_succ,
          Finset.sum_eq_zero fun i hi ↦ by
            rw [Nat.choose_eq_zero_of_lt (Finset.mem_range.mp hi), Nat.cast_zero, mul_zero],
          zero_add, Nat.choose_self, Nat.cast_one, mul_one, Nat.choose_succ_self_right,
          add_sub_cancel_left, ← nsmul_eq_mul']
      exact HasUniqueDiv.nsmul_right_injective (Nat.succ_ne_zero n)
        (by dsimp only; rw [nsmul_zero, ← h0, hΔ_zero, coeff_zero])
    exact ih D (natDegree_le_iff_coeff_eq_zero.mpr fun k hk ↦ by
      rcases eq_or_lt_of_le (Nat.succ_le_of_lt hk) with rfl | hgt
      · exact hlead
      · exact coeff_eq_zero_of_natDegree_lt (by omega)) hD

/-- Translating `hilbertPoly p d` by `X - C c` preserves the strict degree bound `< d`. -/
theorem degree_hilbertPoly_comp_X_sub_C_lt {F : Type*} [Field F] (p : F[X]) (d : ℕ) (c : F) :
    ((hilbertPoly p d).comp (X - C c)).degree < (d : WithBot ℕ) := by
  rw [degree_comp, degree_X_sub_C, mul_one]
  · exact degree_hilbertPoly_lt p d
  · rw [degree_X_sub_C]
    exact zero_lt_one

/-- Given a sequence `f : ℤ → F` whose shifted generating series satisfies
`(∑ n, f (d₀ + n) Xⁿ) * (1 - X)^e = h` in `F⟦X⟧` over a field `F` with `(e - 1)! ≠ 0`, the shifted
Hilbert polynomial agrees with `f d` for every integer `d ≥ d₀ + h.natDegree + 1`. -/
theorem eval_hilbertPoly_comp_sub_eq_of_mul_one_sub_pow_eq {F : Type*} [Field F]
    {f : ℤ → F} {d₀ : ℤ} {h : F[X]} {e : ℕ} (hfac : ((e - 1).factorial : F) ≠ 0)
    (hser : (PowerSeries.mk fun n : ℕ ↦ f (d₀ + n)) * (1 - PowerSeries.X) ^ e = (h : F⟦X⟧))
    {d : ℤ} (hd : d₀ + (h.natDegree : ℤ) + 1 ≤ d) :
    ((hilbertPoly h e).comp (X - C (d₀ : F))).eval (d : F) = f d := by
  have hinv : (PowerSeries.mk fun n : ℕ ↦ f (d₀ + n)) =
      (h : F⟦X⟧) * (PowerSeries.invOneSubPow F e : F⟦X⟧) := by
    rw [← hser, mul_assoc, ← PowerSeries.invOneSubPow_inv_eq_one_sub_pow, Units.inv_val, mul_one]
  set n : ℕ := (d - d₀).toNat
  have hdn : d₀ + (n : ℤ) = d := by omega
  have hn : h.natDegree < n := by omega
  have harg : (d : F) - (d₀ : F) = (n : F) := by
    rw [← Int.cast_sub, ← Int.cast_natCast]
    congr 1
    omega
  rw [eval_comp, eval_sub, eval_X, eval_C, harg]
  have hfn : f d = ((h : F⟦X⟧) * (PowerSeries.invOneSubPow F e : F⟦X⟧)).coeff n := by
    rw [← hinv, PowerSeries.coeff_mk, hdn]
  rw [hfn]
  cases e with
  | zero =>
    rw [hilbertPoly_zero_right, eval_zero, invOneSubPow_zero, Units.val_one, mul_one, coeff_coe]
    exact (coeff_eq_zero_of_natDegree_lt hn).symm
  | succ k =>
    rw [Nat.add_sub_cancel] at hfac
    rw [hilbertPoly_succ, eval_finsetSum, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      invOneSubPow_val_eq_mk_sub_one_add_choose_of_pos F (k + 1) (Nat.succ_pos k)]
    simp only [coeff_coe, coeff_mk, eval_smul, smul_eq_mul, Nat.add_sub_cancel]
    refine Finset.sum_subset_zero_on_sdiff (fun i hi ↦ ?_) (fun i hi ↦ ?_) (fun i hi ↦ ?_)
    · exact Finset.mem_range_succ_iff.mpr
        ((le_natDegree_of_ne_zero (mem_support_iff.mp hi)).trans hn.le)
    · simp only [Finset.mem_sdiff, mem_support_iff, not_not] at hi
      rw [hi.2, zero_mul]
    · have hik : i ≤ n := (le_natDegree_of_ne_zero (mem_support_iff.mp hi)).trans hn.le
      rw [← Int.cast_natCast n, preHilbertPoly_eval_intCast F hfac i (n : ℤ)]
      congr 1
      have hsub : ((n : ℤ) - (i : ℤ) + 1) = ((n - i + 1 : ℕ) : ℤ) := by omega
      rw [hsub]
      change ((Nat.choose (n - i + 1 + k - 1) k : ℤ) : F) = _
      rw [show n - i + 1 + k - 1 = k + (n - i) by omega, Int.cast_natCast]

end Eventual

end Polynomial

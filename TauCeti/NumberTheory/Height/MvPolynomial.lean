/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Height.Polynomial.Basic
public import TauCeti.Algebra.Polynomial.Coeff.ToMvPolynomial
public import TauCeti.Algebra.MvPolynomial.Rename
public import Mathlib.NumberTheory.Height.NumberField
public import TauCeti.RingTheory.MvPolynomial.AbvCoeff
import TauCeti.NumberTheory.Height.Basic

/-!
# Projective coefficient heights of multivariate polynomials

The height of a multivariate polynomial is the native projective height of its finitely
supported coefficient vector. The variables may form an infinite type: only the finitely
many nonzero coefficients contribute. Nonzero scalar multiplication, injective variable
renaming, and placement of a univariate polynomial in one coordinate preserve the height.
These comparisons allow auxiliary polynomials to be handled in their natural variable types.

The normalization is relative to the admissible family of absolute values of the field.
In particular, constant polynomials and the zero polynomial have multiplicative height one.
For nonzero polynomials over number fields, `logHeight_eq_of_numberField` expresses the height
as a sum of local logarithmic sup norms, with complex-place multiplicity two.

There is no bound for the height of a sum of polynomials in terms of the heights of its terms,
so the height of a determinant of a matrix of polynomials is bounded place by place.
`Matrix.mulHeight_det_le` and `Matrix.logHeight_det_le` do this for an `n × n` matrix whose
entries have partial degrees at most `d j` and coefficients dominated by those of one polynomial
`P`, up to a factor `C` at the archimedean absolute values:
`h(det A) ≤ n h(P) + totalWeight K * (log n! + n (∑ j, d j * log 2 + log C))`.
This applies to the generalized Wronskians of Hasse derivatives of `P` in Roth's lemma.

## References

* Lukas Pottmeyer, *Diophantine Approximation*, §3.2, Definition 3.2.1 and Lemma 3.2.2
  (17 January 2022). The absolute heights in those notes correspond to degree-root
  normalizations of the relative heights defined here. The determinant bound is the
  estimate of §3.4.6.
* The determinant bound follows `DiophantineApproximation/PolynomialDeterminantHeight.lean` in
  Ralf Stephan's `rwst/Subspace-Theorems`, snapshot `c26d909dc48cf7fe` (Apache 2.0).
-/

public section

namespace MvPolynomial

variable {K σ τ : Type*} [Field K] [Height.AdmissibleAbsValues K]

/-- The relative projective multiplicative height of a multivariate coefficient vector. -/
noncomputable def mulHeight (p : MvPolynomial σ K) : ℝ :=
  (AddMonoidAlgebra.coeff p).mulHeight

/-- The relative projective logarithmic height of a multivariate coefficient vector. -/
noncomputable def logHeight (p : MvPolynomial σ K) : ℝ := Real.log p.mulHeight

theorem mulHeight_eq_finsupp (p : MvPolynomial σ K) :
    p.mulHeight = (AddMonoidAlgebra.coeff p).mulHeight := (rfl)

theorem logHeight_eq_log_mulHeight (p : MvPolynomial σ K) :
    p.logHeight = Real.log p.mulHeight := (rfl)

/-- Multivariate logarithmic height agrees with the native finitely supported height. -/
theorem logHeight_eq_finsupp (p : MvPolynomial σ K) :
    p.logHeight = (AddMonoidAlgebra.coeff p).logHeight := by
  rw [logHeight_eq_log_mulHeight, mulHeight_eq_finsupp,
    Finsupp.logHeight_eq_log_mulHeight_support]

/-- Multivariate height is the height of the tuple indexed by its nonzero coefficients. -/
theorem mulHeight_eq_support (p : MvPolynomial σ K) :
    p.mulHeight = Height.mulHeight (fun i : p.support ↦ p.coeff i) := by
  -- The native coefficient vector has definitionally the same support and evaluations.
  rfl

/-- Padding a finite coefficient tuple with zeroes does not change multivariate height. -/
theorem mulHeight_eq_coeff (p : MvPolynomial σ K) (s : Finset (σ →₀ ℕ))
    (hs : p.support ⊆ s) :
    p.mulHeight = Height.mulHeight (fun i : s ↦ p.coeff i) :=
  Finsupp.mulHeight_eq_of_support_subset _ s hs

/-- The logarithmic height of any finite coefficient tuple containing the support. -/
theorem logHeight_eq_coeff (p : MvPolynomial σ K) (s : Finset (σ →₀ ℕ))
    (hs : p.support ⊆ s) :
    p.logHeight = Height.logHeight (fun i : s ↦ p.coeff i) := by
  rw [logHeight_eq_log_mulHeight, mulHeight_eq_coeff p s hs,
    Height.logHeight_eq_log_mulHeight]

theorem one_le_mulHeight (p : MvPolynomial σ K) : 1 ≤ p.mulHeight :=
  Finsupp.one_le_mulHeight _

theorem mulHeight_pos (p : MvPolynomial σ K) : 0 < p.mulHeight :=
  Finsupp.mulHeight_pos _

theorem logHeight_nonneg (p : MvPolynomial σ K) : 0 ≤ p.logHeight := by
  rw [logHeight_eq_log_mulHeight]
  exact Real.log_nonneg (one_le_mulHeight p)

@[simp]
theorem mulHeight_zero : (0 : MvPolynomial σ K).mulHeight = 1 := by
  simp [mulHeight_eq_finsupp]

@[simp]
theorem logHeight_zero : (0 : MvPolynomial σ K).logHeight = 0 := by
  simp [logHeight_eq_log_mulHeight]

@[simp]
theorem mulHeight_monomial (n : σ →₀ ℕ) (c : K) : (monomial n c).mulHeight = 1 := by
  rw [mulHeight_eq_finsupp, ← single_eq_monomial, AddMonoidAlgebra.coeff_single]
  exact Finsupp.mulHeight_single n c

@[simp]
theorem logHeight_monomial (n : σ →₀ ℕ) (c : K) : (monomial n c).logHeight = 0 := by
  simp [logHeight_eq_log_mulHeight]

@[simp]
theorem mulHeight_C (c : K) : (C c : MvPolynomial σ K).mulHeight = 1 := by
  rw [C_apply, mulHeight_monomial]

@[simp]
theorem logHeight_C (c : K) : (C c : MvPolynomial σ K).logHeight = 0 := by
  simp [logHeight_eq_log_mulHeight]

@[simp]
theorem mulHeight_one : (1 : MvPolynomial σ K).mulHeight = 1 := by
  rw [← C_1, mulHeight_C]

@[simp]
theorem logHeight_one : (1 : MvPolynomial σ K).logHeight = 0 := by
  simp [logHeight_eq_log_mulHeight]

@[simp]
theorem mulHeight_X_pow (i : σ) (n : ℕ) : (X i ^ n : MvPolynomial σ K).mulHeight = 1 := by
  rw [X_pow_eq_monomial, mulHeight_monomial]

@[simp]
theorem logHeight_X_pow (i : σ) (n : ℕ) : (X i ^ n : MvPolynomial σ K).logHeight = 0 := by
  simp [logHeight_eq_log_mulHeight]

@[simp]
theorem mulHeight_X (i : σ) : (X i : MvPolynomial σ K).mulHeight = 1 := by
  simpa only [pow_one] using mulHeight_X_pow (K := K) i 1

@[simp]
theorem logHeight_X (i : σ) : (X i : MvPolynomial σ K).logHeight = 0 := by
  simp [logHeight_eq_log_mulHeight]

/-- Nonzero scalar multiplication does not change multivariate coefficient height. -/
@[simp]
theorem mulHeight_smul (p : MvPolynomial σ K) {c : K} (hc : c ≠ 0) :
    (c • p).mulHeight = p.mulHeight := by
  simpa only [mulHeight_eq_finsupp, AddMonoidAlgebra.coeff_smul] using
    Finsupp.mulHeight_smul (AddMonoidAlgebra.coeff p) hc

@[simp]
theorem mulHeight_C_mul (p : MvPolynomial σ K) {c : K} (hc : c ≠ 0) :
    (C c * p).mulHeight = p.mulHeight := by
  rw [← smul_eq_C_mul, mulHeight_smul p hc]

@[simp]
theorem logHeight_smul (p : MvPolynomial σ K) {c : K} (hc : c ≠ 0) :
    (c • p).logHeight = p.logHeight := by
  simpa only [logHeight_eq_finsupp, AddMonoidAlgebra.coeff_smul] using
    Finsupp.logHeight_smul (AddMonoidAlgebra.coeff p) hc

@[simp]
theorem mulHeight_neg (p : MvPolynomial σ K) : (-p).mulHeight = p.mulHeight := by
  simpa only [neg_one_smul] using mulHeight_smul p (neg_ne_zero.mpr one_ne_zero)

@[simp]
theorem logHeight_neg (p : MvPolynomial σ K) : (-p).logHeight = p.logHeight := by
  simpa only [neg_one_smul] using logHeight_smul p (neg_ne_zero.mpr one_ne_zero)

@[simp]
theorem logHeight_C_mul (p : MvPolynomial σ K) {c : K} (hc : c ≠ 0) :
    (C c * p).logHeight = p.logHeight := by
  rw [logHeight_eq_log_mulHeight, mulHeight_C_mul p hc, logHeight_eq_log_mulHeight]

/-- Injective renaming of variables preserves projective coefficient height. -/
@[simp]
theorem mulHeight_rename (p : MvPolynomial σ K) {f : σ → τ} (hf : Function.Injective f) :
    (rename f p).mulHeight = p.mulHeight := by
  rw [mulHeight_eq_finsupp, coeff_rename_eq_embDomain p hf, Finsupp.mulHeight_embDomain,
    mulHeight_eq_finsupp]

@[simp]
theorem logHeight_rename (p : MvPolynomial σ K) {f : σ → τ} (hf : Function.Injective f) :
    (rename f p).logHeight = p.logHeight := by
  rw [logHeight_eq_log_mulHeight, mulHeight_rename p hf, logHeight_eq_log_mulHeight]

end MvPolynomial

namespace Polynomial

variable {K σ : Type*} [Field K] [Height.AdmissibleAbsValues K]

/-- Placement in a multivariate coordinate preserves projective coefficient height. -/
@[simp]
theorem mulHeight_toMvPolynomial (p : K[X]) (i : σ) :
    (p.toMvPolynomial i).mulHeight = p.mulHeight := by
  rw [MvPolynomial.mulHeight_eq_finsupp, coeff_toMvPolynomial_eq_embDomain,
    Finsupp.mulHeight_embDomain, mulHeight_eq_finsupp]

@[simp]
theorem logHeight_toMvPolynomial (p : K[X]) (i : σ) :
    (p.toMvPolynomial i).logHeight = p.logHeight := by
  rw [MvPolynomial.logHeight_eq_log_mulHeight, mulHeight_toMvPolynomial,
    logHeight_eq_log_mulHeight]

end Polynomial

namespace MvPolynomial

variable {K σ : Type*} [Field K] [Height.AdmissibleAbsValues K]

/-- The coefficient height of `X i - C a` is the scalar multiplicative height of `a`. -/
@[simp↓]
theorem mulHeight_X_sub_C (i : σ) (a : K) :
    (X i - C a).mulHeight = Height.mulHeight₁ a := by
  rw [← Polynomial.toMvPolynomial_X i, ← Polynomial.toMvPolynomial_C i,
    ← map_sub, Polynomial.mulHeight_toMvPolynomial, Polynomial.mulHeight_X_sub_C]

/-- The coefficient height of `X i - C a` is the scalar logarithmic height of `a`. -/
@[simp↓]
theorem logHeight_X_sub_C (i : σ) (a : K) :
    (X i - C a).logHeight = Height.logHeight₁ a := by
  rw [logHeight_eq_log_mulHeight, mulHeight_X_sub_C, Height.logHeight₁_eq_log_mulHeight₁]

end MvPolynomial

namespace MvPolynomial

variable {K σ : Type*} [Field K] [NumberField K]

/-- Over a number field, the relative logarithmic coefficient height is the sum of local
logarithmic sup norms. Infinite places occur with their real or complex multiplicity; divide
by `[K : ℚ]` for the absolute normalization. The variables may form an infinite type. -/
theorem logHeight_eq_of_numberField {p : MvPolynomial σ K} (hp : p ≠ 0) :
    p.logHeight =
      (∑ v : NumberField.InfinitePlace K,
        v.mult * Real.log (⨆ d, v (p.coeff d))) +
      ∑ᶠ v : NumberField.FinitePlace K, Real.log (⨆ d, v (p.coeff d)) := by
  classical
  have hx : (fun d ↦ p.coeff d) ≠ 0 := by
    intro h
    apply hp
    ext d
    simpa using congrFun h d
  obtain ⟨d, hd⟩ := Function.ne_iff.mp hx
  have hv (v : AbsoluteValue K ℝ) : 0 < ⨆ d, v (p.coeff d) := by
    have hb : BddAbove (Set.range (fun d ↦ v (p.coeff d))) := by
      simpa only [Set.range_comp'] using
        ((AddMonoidAlgebra.coeff p).finite_range.image v).bddAbove
    exact (v.pos hd).trans_le (le_ciSup hb d)
  have hi (v : NumberField.InfinitePlace K) : 0 < ⨆ d, v (p.coeff d) := by
    simpa only [NumberField.InfinitePlace.coe_apply] using hv v.val
  have hf (v : NumberField.FinitePlace K) : 0 < ⨆ d, v (p.coeff d) := by
    simpa only [NumberField.FinitePlace.coe_apply] using hv v.val
  rw [logHeight_eq_log_mulHeight, mulHeight_eq_finsupp,
    Finsupp.mulHeight_eq_mulHeight_coe, NumberField.mulHeight_eq hx,
    Real.log_mul (Finset.prod_pos (fun v _ ↦ pow_pos (hi v) v.mult)).ne'
      (finprod_ne_zero (fun v ↦ (hf v).ne')),
    Real.log_prod (fun v _ ↦ (pow_pos (hi v) v.mult).ne'),
    Real.log_finprod hf]
  simp only [Real.log_pow]

end MvPolynomial

namespace Matrix

open Finset Height AdmissibleAbsValues MvPolynomial
open scoped Nat

variable {K σ : Type*} [Field K] [AdmissibleAbsValues K] [Fintype σ]
  {n : Type*} [Fintype n] [DecidableEq n]

/-- **The height of a determinant of polynomials.** Let `A` be an `n × n` matrix of polynomials
whose entries have partial degrees at most `d j`, and let `P ≠ 0`. Suppose that, at every
archimedean absolute value `v`, each coefficient of each entry is bounded by `C` times `v` of
some coefficient of `P`, and at every nonarchimedean `v` by `v` of some coefficient of `P`. Then
`H(det A) ≤ (n! (2 ^ (∑ j, d j) * C) ^ n) ^ totalWeight K * H(P) ^ n`. -/
theorem mulHeight_det_le (A : Matrix n n (MvPolynomial σ K)) {P : MvPolynomial σ K} (hP : P ≠ 0)
    {d : σ → ℕ} (hd : ∀ i j k, (A i j).degreeOf k ≤ d k) {C : ℝ} (hC : 1 ≤ C)
    (harch : ∀ v ∈ archAbsVal (K := K), ∀ i j a, ∃ b, v ((A i j).coeff a) ≤ C * v (P.coeff b))
    (hnon : ∀ v ∈ nonarchAbsVal (K := K), ∀ i j a, ∃ b, v ((A i j).coeff a) ≤ v (P.coeff b)) :
    A.det.mulHeight ≤ ((Fintype.card n)! * (2 ^ (∑ k, d k) * C) ^ Fintype.card n) ^ totalWeight K *
      P.mulHeight ^ Fintype.card n := by
  classical
  have hx : (fun b : P.support ↦ P.coeff b) ≠ 0 := by
    obtain ⟨b, hb⟩ := support_nonempty.mpr hP
    exact Function.ne_iff.mpr ⟨⟨b, hb⟩, mem_support_iff.mp hb⟩
  -- Every coefficient of `P` is bounded by the local factor of its nonzero coefficients.
  have hM (v : AbsoluteValue K ℝ) (b : σ →₀ ℕ) :
      v (P.coeff b) ≤ ⨆ c : P.support, v (P.coeff c) := by
    by_cases hb : b ∈ P.support
    · exact Finite.le_ciSup_of_le ⟨b, hb⟩ le_rfl
    · rw [notMem_support_iff.mp hb, map_zero]
      exact Real.iSup_nonneg fun _ ↦ v.nonneg _
  have hB (i j : n) : #(A i j).support ≤ 2 ^ ∑ k, d k :=
    (card_support_le_two_pow _).trans
      (Nat.pow_le_pow_right two_pos (Finset.sum_le_sum fun k _ ↦ hd i j k))
  have hK : (1 : ℝ) ≤ (Fintype.card n)! * (2 ^ (∑ k, d k) * C) ^ Fintype.card n :=
    one_le_mul_of_one_le_of_one_le (by exact_mod_cast (Fintype.card n).factorial_pos)
      (one_le_pow₀ (one_le_mul_of_one_le_of_one_le (one_le_pow₀ one_le_two) hC))
  have hM0 (v : AbsoluteValue K ℝ) : 0 ≤ (⨆ c : P.support, v (P.coeff c)) ^ Fintype.card n :=
    pow_nonneg (Real.iSup_nonneg fun _ ↦ v.nonneg _) _
  rw [mulHeight_eq_support, mulHeight_eq_support]
  refine mulHeight_le_of_forall_iSup_le hx _ hK
    (fun v hv ↦ Real.iSup_le (fun t ↦ ?_) (mul_nonneg (zero_le_one.trans hK) (hM0 v)))
    fun v hv ↦ Real.iSup_le (fun t ↦ ?_) (hM0 v)
  · refine (abv_coeff_det_le A (C := C * ⨆ c : P.support, v (P.coeff c)) hB
      (fun i j a ↦ ?_) t).trans_eq ?_
    · obtain ⟨b, hb⟩ := harch v hv i j a
      exact hb.trans (mul_le_mul_of_nonneg_left (hM v b) (zero_le_one.trans hC))
    · rw [nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat, ← mul_assoc, mul_pow, mul_assoc]
  · refine abv_coeff_det_le_of_isNonarchimedean A (isNonarchimedean v hv) (fun i j a ↦ ?_) t
    obtain ⟨b, hb⟩ := hnon v hv i j a
    exact hb.trans (hM v b)

/-- **The logarithmic height of a determinant of polynomials.** Under the hypotheses of
`Matrix.mulHeight_det_le`,
`h(det A) ≤ n h(P) + totalWeight K * (log n! + n (∑ j, d j * log 2 + log C))`. -/
theorem logHeight_det_le (A : Matrix n n (MvPolynomial σ K)) {P : MvPolynomial σ K} (hP : P ≠ 0)
    {d : σ → ℕ} (hd : ∀ i j k, (A i j).degreeOf k ≤ d k) {C : ℝ} (hC : 1 ≤ C)
    (harch : ∀ v ∈ archAbsVal (K := K), ∀ i j a, ∃ b, v ((A i j).coeff a) ≤ C * v (P.coeff b))
    (hnon : ∀ v ∈ nonarchAbsVal (K := K), ∀ i j a, ∃ b, v ((A i j).coeff a) ≤ v (P.coeff b)) :
    A.det.logHeight ≤ Fintype.card n * P.logHeight + totalWeight K *
      (Real.log (Fintype.card n)! + Fintype.card n * (∑ k, d k * Real.log 2 + Real.log C)) := by
  have hfact : (0 : ℝ) < (Fintype.card n)! := by exact_mod_cast (Fintype.card n).factorial_pos
  have hC0 : 0 < C := zero_lt_one.trans_le hC
  have h := Real.log_le_log (MvPolynomial.mulHeight_pos _) (mulHeight_det_le A hP hd hC harch hnon)
  -- Expand the logarithm of the bound of `Matrix.mulHeight_det_le` into its terms.
  rw [Real.log_mul (by positivity) (pow_pos (MvPolynomial.mulHeight_pos P) _).ne', Real.log_pow,
    Real.log_pow, Real.log_mul hfact.ne' (by positivity), Real.log_pow,
    Real.log_mul (by positivity) hC0.ne', Real.log_pow, Nat.cast_sum, Finset.sum_mul] at h
  rw [MvPolynomial.logHeight_eq_log_mulHeight, MvPolynomial.logHeight_eq_log_mulHeight]
  linarith

end Matrix

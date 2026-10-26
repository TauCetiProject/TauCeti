/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti
-/
module

public import TauCeti.NumberTheory.Height.Finsupp
public import Mathlib.NumberTheory.Height.MvPolynomial
public import Mathlib.Algebra.Polynomial.Degree.Support

/-!
# Projective coefficient heights of univariate polynomials

The height of a polynomial is the native projective height of its coefficient vector.
It is unchanged by nonzero scalar multiplication; constants and the zero polynomial
have multiplicative height one. The normalization is relative to the admissible family
of absolute values on the coefficient field, rather than its degree-root normalization.

The product estimate uses Mathlib's `Height.mulHeight_linearMap_apply_le` on coefficient
convolution. Its archimedean factor counts the coefficients of the smaller-degree factor;
the nonarchimedean estimate has no such factor. These estimates are used to control
coefficients of auxiliary polynomials in Diophantine approximation.

## References

* Lukas Pottmeyer, *Diophantine Approximation*, §3.2, Definition 3.2.1 and Lemma 3.2.2
  (17 January 2022). Those notes use absolute heights; here we use the relative height
  supplied by `Height.AdmissibleAbsValues`.
-/

public section

namespace Polynomial

variable {K : Type*} [Field K] [Height.AdmissibleAbsValues K]

/-- The relative projective multiplicative height of the coefficients of a polynomial. -/
noncomputable def mulHeight (p : K[X]) : ℝ := p.toFinsupp.coeff.mulHeight

/-- The relative projective logarithmic height of the coefficients of a polynomial. -/
noncomputable def logHeight (p : K[X]) : ℝ := Real.log p.mulHeight

theorem mulHeight_eq_finsupp (p : K[X]) : p.mulHeight = p.toFinsupp.coeff.mulHeight := (rfl)

theorem logHeight_eq_log_mulHeight (p : K[X]) : p.logHeight = Real.log p.mulHeight := (rfl)

/-- Polynomial logarithmic height agrees with the native finitely supported height. -/
theorem logHeight_eq_finsupp (p : K[X]) : p.logHeight = p.toFinsupp.coeff.logHeight := by
  rw [logHeight_eq_log_mulHeight, mulHeight_eq_finsupp,
    Finsupp.logHeight_eq_log_mulHeight_support]

/-- Polynomial height is the height of the tuple indexed by its nonzero coefficients. -/
theorem mulHeight_eq_support (p : K[X]) :
    p.mulHeight = Height.mulHeight (fun i : p.support ↦ p.coeff i) := by
  -- The native coefficient vector has definitionally the same support and evaluations.
  rfl

/-- Any finite coefficient tuple containing the support gives the polynomial height. -/
theorem mulHeight_eq_coeff (p : K[X]) {n : ℕ} (hn : p.support ⊆ Finset.range n) :
    p.mulHeight = Height.mulHeight (fun i : Fin n ↦ p.coeff i) := by
  classical
  let e : Fin n ≃ Finset.range n := Fin.equivSubtype.trans
    (Equiv.subtypeEquivProp (by ext; simp))
  rw [mulHeight_eq_finsupp, Finsupp.mulHeight_eq_of_support_subset _ (Finset.range n)
    (by rwa [support_toFinsupp]), ← Height.mulHeight_comp_equiv e]
  -- Reindexing along `e` is definitionally the usual finite coefficient tuple.
  rfl

/-- The finite coefficient-tuple description of logarithmic polynomial height. -/
theorem logHeight_eq_coeff (p : K[X]) {n : ℕ} (hn : p.support ⊆ Finset.range n) :
    p.logHeight = Height.logHeight (fun i : Fin n ↦ p.coeff i) := by
  rw [logHeight_eq_log_mulHeight, mulHeight_eq_coeff p hn,
    Height.logHeight_eq_log_mulHeight]

/-- Any finite coefficient tuple extending past the degree gives the polynomial height. -/
theorem mulHeight_eq_coeff_of_natDegree_lt (p : K[X]) {n : ℕ} (hn : p.natDegree < n) :
    p.mulHeight = Height.mulHeight (fun i : Fin n ↦ p.coeff i) :=
  mulHeight_eq_coeff p (p.supp_subset_range hn)

/-- The logarithmic coefficient-tuple description when the tuple extends past the degree. -/
theorem logHeight_eq_coeff_of_natDegree_lt (p : K[X]) {n : ℕ} (hn : p.natDegree < n) :
    p.logHeight = Height.logHeight (fun i : Fin n ↦ p.coeff i) :=
  logHeight_eq_coeff p (p.supp_subset_range hn)

theorem one_le_mulHeight (p : K[X]) : 1 ≤ p.mulHeight :=
  Finsupp.one_le_mulHeight _

theorem mulHeight_pos (p : K[X]) : 0 < p.mulHeight :=
  Finsupp.mulHeight_pos _

theorem logHeight_nonneg (p : K[X]) : 0 ≤ p.logHeight := by
  rw [logHeight_eq_log_mulHeight]
  exact Real.log_nonneg (one_le_mulHeight p)

@[simp]
theorem mulHeight_zero : (0 : K[X]).mulHeight = 1 := by
  simp [mulHeight_eq_finsupp]

@[simp]
theorem logHeight_zero : (0 : K[X]).logHeight = 0 := by
  simp [logHeight_eq_log_mulHeight]

@[simp]
theorem mulHeight_monomial (n : ℕ) (c : K) : (monomial n c).mulHeight = 1 := by
  simp [mulHeight_eq_finsupp, toFinsupp_monomial]

@[simp]
theorem logHeight_monomial (n : ℕ) (c : K) : (monomial n c).logHeight = 0 := by
  simp [logHeight_eq_log_mulHeight]

@[simp]
theorem mulHeight_C (c : K) : (C c).mulHeight = 1 := by
  simp [mulHeight_eq_finsupp, toFinsupp_C]

@[simp]
theorem logHeight_C (c : K) : (C c).logHeight = 0 := by
  simp [logHeight_eq_log_mulHeight]

@[simp]
theorem mulHeight_one : (1 : K[X]).mulHeight = 1 := by
  rw [← C_1, mulHeight_C]

@[simp]
theorem logHeight_one : (1 : K[X]).logHeight = 0 := by
  simp [logHeight_eq_log_mulHeight]

@[simp]
theorem mulHeight_X_pow (n : ℕ) : (X ^ n : K[X]).mulHeight = 1 := by
  rw [X_pow_eq_monomial, mulHeight_monomial]

@[simp]
theorem logHeight_X_pow (n : ℕ) : (X ^ n : K[X]).logHeight = 0 := by
  simp [logHeight_eq_log_mulHeight]

@[simp]
theorem mulHeight_X : (X : K[X]).mulHeight = 1 := by
  simpa only [pow_one] using mulHeight_X_pow (K := K) 1

@[simp]
theorem logHeight_X : (X : K[X]).logHeight = 0 := by
  simp [logHeight_eq_log_mulHeight]

/-- Nonzero scalar multiplication does not change projective coefficient height. -/
@[simp]
theorem mulHeight_smul (p : K[X]) {c : K} (hc : c ≠ 0) :
    (c • p).mulHeight = p.mulHeight := by
  simpa [mulHeight_eq_finsupp, toFinsupp_smul] using Finsupp.mulHeight_smul p.toFinsupp.coeff hc

@[simp]
theorem mulHeight_C_mul (p : K[X]) {c : K} (hc : c ≠ 0) :
    (C c * p).mulHeight = p.mulHeight := by
  rw [← smul_eq_C_mul, mulHeight_smul p hc]

@[simp]
theorem logHeight_smul (p : K[X]) {c : K} (hc : c ≠ 0) :
    (c • p).logHeight = p.logHeight := by
  simpa [logHeight_eq_finsupp, toFinsupp_smul] using
    Finsupp.logHeight_smul p.toFinsupp.coeff hc

@[simp]
theorem mulHeight_neg (p : K[X]) : (-p).mulHeight = p.mulHeight := by
  simpa only [neg_one_smul] using mulHeight_smul p (neg_ne_zero.mpr one_ne_zero)

@[simp]
theorem logHeight_neg (p : K[X]) : (-p).logHeight = p.logHeight := by
  simpa only [neg_one_smul] using logHeight_smul p (neg_ne_zero.mpr one_ne_zero)

@[simp]
theorem logHeight_C_mul (p : K[X]) {c : K} (hc : c ≠ 0) :
    (C c * p).logHeight = p.logHeight := by
  rw [logHeight_eq_log_mulHeight, mulHeight_C_mul p hc, logHeight_eq_log_mulHeight]

/-- The coefficient height of the linear polynomial with root `a` is the scalar height of `a`.
-/
@[simp↓]
theorem mulHeight_X_sub_C (a : K) : (X - C a).mulHeight = Height.mulHeight₁ a := by
  rw [mulHeight_eq_coeff_of_natDegree_lt _ (n := 2) (by simp)]
  have hc : (fun i : Fin 2 ↦ (X - C a).coeff i) = ![-a, 1] := by
    ext i
    fin_cases i <;> simp
  rw [hc, ← Height.mulHeight₁_eq_mulHeight, Height.mulHeight₁_neg]

/-- The logarithmic coefficient height of the linear polynomial with root `a` is the
scalar logarithmic height of `a`. -/
@[simp↓]
theorem logHeight_X_sub_C (a : K) : (X - C a).logHeight = Height.logHeight₁ a := by
  rw [logHeight_eq_log_mulHeight, mulHeight_X_sub_C, Height.logHeight₁_eq_log_mulHeight₁]

/-- The coefficient matrix for multiplication by `g`, with columns indexed by the
coefficients of `f`; entries outside the convolution range are padded by zeroes. -/
private def convolutionMatrix (f g : K[X]) :
    Fin (f.natDegree + g.natDegree + 1) × Fin (f.natDegree + 1) → K :=
  fun ji ↦ if ji.2.val ≤ ji.1.val then g.coeff (ji.1.val - ji.2.val) else 0

omit [Height.AdmissibleAbsValues K] in
private theorem coeff_mul_eq_convolution (f g : K[X]) :
    (fun j : Fin (f.natDegree + g.natDegree + 1) ↦ (f * g).coeff j) =
      (fun j ↦ ∑ i : Fin (f.natDegree + 1), convolutionMatrix f g (j, i) * f.coeff i) := by
  classical
  ext j
  rw [congrArg (fun p : K[X] ↦ (p * g).coeff j.val) f.as_sum_range_C_mul_X_pow]
  simp only [Finset.sum_mul, finsetSum_coeff, mul_assoc, coeff_C_mul,
    coeff_X_pow_mul', convolutionMatrix]
  rw [Fin.sum_univ_eq_sum_range (fun i ↦
    (if i ≤ j.val then g.coeff (j.val - i) else 0) * f.coeff i)]
  apply Finset.sum_congr rfl
  intro i hi
  split_ifs <;> ring

private theorem mulHeight_convolutionMatrix_le (f g : K[X]) :
    Height.mulHeight (convolutionMatrix f g) ≤ g.mulHeight := by
  classical
  let x : Fin (g.natDegree + 1) ⊕ Unit → K :=
    Sum.elim (fun i ↦ g.coeff i) 0
  let r : Fin (f.natDegree + g.natDegree + 1) × Fin (f.natDegree + 1) →
      Fin (g.natDegree + 1) ⊕ Unit := fun ji ↦
    if h : ji.2.val ≤ ji.1.val ∧ ji.1.val - ji.2.val < g.natDegree + 1 then
      .inl ⟨ji.1.val - ji.2.val, h.2⟩ else .inr ()
  have hr : convolutionMatrix f g = x ∘ r := by
    ext ji
    simp only [convolutionMatrix, x, r, Function.comp_apply]
    split_ifs with h₁ h₂ h₂
    · rfl
    · exact coeff_eq_zero_of_natDegree_lt (by omega)
    · simp_all
    · rfl
  rw [hr, mulHeight_eq_coeff_of_natDegree_lt g (Nat.lt_succ_self _)]
  simpa [x, Height.mulHeight_sumElim_zero_eq] using Height.mulHeight_comp_le r x

/-- The height of a product is bounded by the product of coefficient heights,
with the archimedean convolution factor given by the smaller degree plus one. -/
theorem mulHeight_mul_le (f g : K[X]) :
    (f * g).mulHeight ≤
      ((min f.natDegree g.natDegree + 1 : ℕ) : ℝ) ^ Height.totalWeight K *
        f.mulHeight * g.mulHeight := by
  classical
  wlog hfg : f.natDegree ≤ g.natDegree generalizing f g
  · simpa [mul_comm, mul_left_comm, mul_assoc, min_comm] using this g f (le_of_not_ge hfg)
  calc
    (f * g).mulHeight = Height.mulHeight
        (fun j : Fin (f.natDegree + g.natDegree + 1) ↦ (f * g).coeff j) :=
      mulHeight_eq_coeff_of_natDegree_lt _
        (lt_of_le_of_lt (natDegree_mul_le ..) (Nat.lt_succ_self _))
    _ ≤ ((f.natDegree + 1 : ℕ) : ℝ) ^ Height.totalWeight K *
        Height.mulHeight (convolutionMatrix f g) *
          Height.mulHeight (fun i : Fin (f.natDegree + 1) ↦ f.coeff i) := by
      rw [coeff_mul_eq_convolution]
      simpa only [Nat.card_fin] using
        Height.mulHeight_linearMap_apply_le (convolutionMatrix f g) (fun i ↦ f.coeff i)
    _ ≤ ((f.natDegree + 1 : ℕ) : ℝ) ^ Height.totalWeight K * g.mulHeight * f.mulHeight := by
      rw [← mulHeight_eq_coeff_of_natDegree_lt f (Nat.lt_succ_self _)]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (mulHeight_convolutionMatrix_le f g) (by positivity))
        (le_of_lt (mulHeight_pos f))
    _ = ((min f.natDegree g.natDegree + 1 : ℕ) : ℝ) ^ Height.totalWeight K *
        f.mulHeight * g.mulHeight := by
      rw [min_eq_left hfg]
      ring

open Real in
/-- The logarithmic form of the coefficient convolution estimate. -/
theorem logHeight_mul_le (f g : K[X]) :
    (f * g).logHeight ≤
      Height.totalWeight K * Real.log (min f.natDegree g.natDegree + 1 : ℕ) +
        f.logHeight + g.logHeight := by
  have h := Real.log_le_log (mulHeight_pos (f * g)) (mulHeight_mul_le f g)
  have hf := mulHeight_pos f
  have hg := mulHeight_pos g
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_pow] at h
  simpa [logHeight_eq_log_mulHeight, add_assoc] using h

end Polynomial

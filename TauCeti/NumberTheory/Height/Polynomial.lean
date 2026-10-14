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
    p.mulHeight = Height.mulHeight (fun i : p.support ↦ p.coeff i) := (rfl)

/-- Any finite coefficient tuple extending past the degree gives the polynomial height. -/
theorem mulHeight_eq_coeff (p : K[X]) {n : ℕ} (hn : p.natDegree < n) :
    p.mulHeight = Height.mulHeight (fun i : Fin n ↦ p.coeff i) := by
  classical
  let e : Fin n ≃ Finset.range n := Fin.equivSubtype.trans
    (Equiv.subtypeEquivProp (by ext; simp))
  rw [mulHeight_eq_finsupp, Finsupp.mulHeight_eq_of_support_subset _ (Finset.range n)
    (by rw [support_toFinsupp]; exact p.supp_subset_range hn), ← Height.mulHeight_comp_equiv e]
  rfl

/-- The finite coefficient-tuple description of logarithmic polynomial height. -/
theorem logHeight_eq_coeff (p : K[X]) {n : ℕ} (hn : p.natDegree < n) :
    p.logHeight = Height.logHeight (fun i : Fin n ↦ p.coeff i) := by
  rw [logHeight_eq_log_mulHeight, mulHeight_eq_coeff p hn,
    Height.logHeight_eq_log_mulHeight]

theorem one_le_mulHeight (p : K[X]) : 1 ≤ p.mulHeight :=
  Finsupp.one_le_mulHeight _

theorem mulHeight_pos (p : K[X]) : 0 < p.mulHeight :=
  lt_of_lt_of_le zero_lt_one (one_le_mulHeight p)

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
  rw [logHeight_eq_log_mulHeight, mulHeight_smul p hc, logHeight_eq_log_mulHeight]

@[simp]
theorem logHeight_C_mul (p : K[X]) {c : K} (hc : c ≠ 0) :
    (C c * p).logHeight = p.logHeight := by
  rw [logHeight_eq_log_mulHeight, mulHeight_C_mul p hc, logHeight_eq_log_mulHeight]

/-- The coefficient height of the linear polynomial with root `a` is the scalar height of `a`.
-/
@[simp↓]
theorem mulHeight_X_sub_C (a : K) : (X - C a).mulHeight = Height.mulHeight₁ a := by
  rw [mulHeight_eq_coeff _ (n := 2) (by simp)]
  have hc : (fun i : Fin 2 ↦ (X - C a).coeff i) = ![-a, 1] := by
    ext i
    fin_cases i <;> simp
  rw [hc, ← Height.mulHeight₁_eq_mulHeight, Height.mulHeight₁_neg]

@[simp↓]
theorem logHeight_X_sub_C (a : K) : (X - C a).logHeight = Height.logHeight₁ a := by
  rw [logHeight_eq_log_mulHeight, mulHeight_X_sub_C, Height.logHeight₁_eq_log_mulHeight₁]

/-- The height of a product is bounded by the product of coefficient heights,
with the archimedean convolution factor given by the smaller degree plus one. -/
theorem mulHeight_mul_le (f g : K[X]) :
    (f * g).mulHeight ≤
      ((min f.natDegree g.natDegree + 1 : ℕ) : ℝ) ^ Height.totalWeight K *
        f.mulHeight * g.mulHeight := by
  classical
  wlog hfg : f.natDegree ≤ g.natDegree generalizing f g
  · simpa [mul_comm, mul_left_comm, mul_assoc, min_comm] using this g f (le_of_not_ge hfg)
  let A : Fin (f.natDegree + g.natDegree + 1) × Fin (f.natDegree + 1) → K :=
    fun ji ↦ if ji.2.val ≤ ji.1.val then g.coeff (ji.1.val - ji.2.val) else 0
  have hc : (fun j : Fin (f.natDegree + g.natDegree + 1) ↦ (f * g).coeff j) =
      (fun j ↦ ∑ i : Fin (f.natDegree + 1), A (j, i) * f.coeff i) := by
    ext j
    rw [congrArg (fun p : K[X] ↦ (p * g).coeff j.val) f.as_sum_range_C_mul_X_pow]
    simp only [Finset.sum_mul, finsetSum_coeff, mul_assoc, coeff_C_mul,
      coeff_X_pow_mul', A]
    rw [Fin.sum_univ_eq_sum_range (fun i ↦
      (if i ≤ j.val then g.coeff (j.val - i) else 0) * f.coeff i)]
    apply Finset.sum_congr rfl
    intro i hi
    split_ifs <;> ring
  let x : Fin (g.natDegree + 1) ⊕ Unit → K :=
    Sum.elim (fun i ↦ g.coeff i) 0
  let r : Fin (f.natDegree + g.natDegree + 1) × Fin (f.natDegree + 1) →
      Fin (g.natDegree + 1) ⊕ Unit := fun ji ↦
    if h : ji.2.val ≤ ji.1.val ∧ ji.1.val - ji.2.val < g.natDegree + 1 then
      .inl ⟨ji.1.val - ji.2.val, h.2⟩ else .inr ()
  have hr : A = x ∘ r := by
    ext ji
    simp only [A, x, r, Function.comp_apply]
    split_ifs with h₁ h₂ h₂
    · rfl
    · exact coeff_eq_zero_of_natDegree_lt (by omega)
    · simp_all
    · rfl
  have hA : Height.mulHeight A ≤ g.mulHeight := by
    rw [hr, mulHeight_eq_coeff g (Nat.lt_succ_self _)]
    simpa [x, Height.mulHeight_sumElim_zero_eq] using Height.mulHeight_comp_le r x
  rw [mulHeight_eq_coeff _ (lt_of_le_of_lt (natDegree_mul_le ..) (Nat.lt_succ_self _)), hc,
    min_eq_left hfg, mul_assoc _ f.mulHeight g.mulHeight,
    mul_comm f.mulHeight g.mulHeight, ← mul_assoc,
    mulHeight_eq_coeff f (Nat.lt_succ_self _)]
  exact (Height.mulHeight_linearMap_apply_le A (fun i ↦ f.coeff i)).trans <| by
    simp only [Nat.card_fin]
    gcongr

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

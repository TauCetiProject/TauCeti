/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Height.Polynomial
public import TauCeti.Algebra.Polynomial.Coeff.ToMvPolynomial

/-!
# Projective coefficient heights of multivariate polynomials

The height of a multivariate polynomial is the native projective height of its finitely
supported coefficient vector. The variables may form an infinite type: only the finitely
many nonzero coefficients contribute. Nonzero scalar multiplication, injective variable
renaming, and placement of a univariate polynomial in one coordinate preserve the height.
These comparisons allow auxiliary polynomials to be handled in their natural variable types.

The normalization is relative to the admissible family of absolute values of the field.
In particular, constant polynomials and the zero polynomial have multiplicative height one.

## References

* Lukas Pottmeyer, *Diophantine Approximation*, §3.2, Definition 3.2.1 and Lemma 3.2.2
  (17 January 2022). The absolute heights in those notes correspond to degree-root
  normalizations of the relative heights defined here.
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
  rw [MvPolynomial.mulHeight_eq_finsupp, MvPolynomial.coeff_toMvPolynomial_eq_embDomain,
    Finsupp.mulHeight_embDomain, mulHeight_eq_finsupp]

@[simp]
theorem logHeight_toMvPolynomial (p : K[X]) (i : σ) :
    (p.toMvPolynomial i).logHeight = p.logHeight := by
  rw [MvPolynomial.logHeight_eq_log_mulHeight, mulHeight_toMvPolynomial,
    logHeight_eq_log_mulHeight]

end Polynomial

namespace MvPolynomial

variable {K σ : Type*} [Field K] [Height.AdmissibleAbsValues K]

@[simp↓]
theorem mulHeight_X_sub_C (i : σ) (a : K) :
    (X i - C a).mulHeight = Height.mulHeight₁ a := by
  rw [← Polynomial.toMvPolynomial_X i, ← Polynomial.toMvPolynomial_C i,
    ← map_sub, Polynomial.mulHeight_toMvPolynomial, Polynomial.mulHeight_X_sub_C]

@[simp↓]
theorem logHeight_X_sub_C (i : σ) (a : K) :
    (X i - C a).logHeight = Height.logHeight₁ a := by
  rw [logHeight_eq_log_mulHeight, mulHeight_X_sub_C, Height.logHeight₁_eq_log_mulHeight₁]

end MvPolynomial

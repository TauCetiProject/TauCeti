/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.MvPolynomial.EulerIdentity

/-!
# Dehomogenization and the affine gradient criterion

Setting the `i`-th coordinate to one turns a polynomial in `n + 1` variables into a
polynomial in `n` variables. The remaining coordinates are indexed by `i.succAbove`.
We compute evaluation and partial derivatives of this substitution, and prove that at
a zero of a homogeneous equation its full gradient vanishes exactly when the gradient
of the affine equation vanishes. Thus the usual nonsingularity test can be checked in
any standard affine chart of a projective hypersurface; for a plane curve, take `n = 2`.

Euler's identity recovers the omitted partial derivative. No invertibility of the
degree is needed, so the criterion also applies when the characteristic divides the degree.

## References

* W. Fulton, *Algebraic Curves*, Chapter 5, Section 1.
-/

public section

namespace TauCeti

open MvPolynomial

variable {n : ℕ}

section CommSemiring

variable {R : Type*} [CommSemiring R]

/-- The substitution setting coordinate `i` to one and keeping the other coordinates,
indexed in increasing order by `i.succAbove`. -/
noncomputable def dehomogenize (i : Fin (n + 1)) :
    MvPolynomial (Fin (n + 1)) R →ₐ[R] MvPolynomial (Fin n) R :=
  aeval (i.insertNth 1 X)

/-- Variables are substituted by inserting one at the chosen coordinate. -/
@[simp]
theorem dehomogenize_X (i j : Fin (n + 1)) :
    dehomogenize (R := R) i (X j) =
      Fin.insertNth (α := fun _ ↦ MvPolynomial (Fin n) R) i 1 X j := by
  simp [dehomogenize]

/-- Dehomogenizing a monomial drops the exponent of the chosen coordinate and keeps the others,
indexed by `i.succAbove`. -/
theorem dehomogenize_monomial (i : Fin (n + 1)) (s : Fin (n + 1) →₀ ℕ) (c : R) :
    dehomogenize i (monomial s c) =
      monomial (Finsupp.equivFunOnFinite.symm (s ∘ i.succAbove)) c := by
  rw [monomial_eq, monomial_eq, map_mul, dehomogenize, algHom_C,
    Finsupp.prod_fintype _ _ (by simp), Finsupp.prod_fintype _ _ (by simp), map_prod,
    Fin.prod_univ_succAbove _ i]
  simp

/-- Substituting after adjoining the omitted variable recovers the original polynomial.
In particular, every affine polynomial is the dehomogenization of a polynomial. -/
@[simp]
theorem dehomogenize_rename_succAbove (i : Fin (n + 1)) (p : MvPolynomial (Fin n) R) :
    dehomogenize i (rename i.succAbove p) = p := by
  rw [dehomogenize, aeval_rename, Fin.insertNth_comp_succAbove, aeval_X_left_apply]

/-- Evaluation in an affine chart is evaluation of the homogeneous coordinates with
the chosen coordinate equal to one. -/
@[simp]
theorem eval_dehomogenize (i : Fin (n + 1)) (p : MvPolynomial (Fin (n + 1)) R)
    (a : Fin n → R) :
    eval a (dehomogenize i p) = eval (i.insertNth 1 a) p := by
  have h : (aeval a).comp (dehomogenize (R := R) i) = aeval (i.insertNth 1 a) := by
    ext j
    refine Fin.succAboveCases i ?_ (fun l ↦ ?_) j <;> simp
  exact AlgHom.congr_fun h p

/-- Changing coefficients commutes with dehomogenization. -/
@[simp]
theorem map_dehomogenize {S : Type*} [CommSemiring S] (f : R →+* S)
    (i : Fin (n + 1)) (p : MvPolynomial (Fin (n + 1)) R) :
    map f (dehomogenize i p) = dehomogenize i (map f p) := by
  simp only [dehomogenize, aeval_def, algebraMap_eq]
  rw [map_eval₂]
  congr 1
  ext l
  refine Fin.succAboveCases i ?_ (fun j ↦ ?_) l <;> simp

/-- Partial differentiation in a retained coordinate commutes with dehomogenization. -/
@[simp]
theorem pderiv_dehomogenize (i : Fin (n + 1)) (j : Fin n)
    (p : MvPolynomial (Fin (n + 1)) R) :
    pderiv j (dehomogenize i p) = dehomogenize i (pderiv (i.succAbove j) p) := by
  -- Follow the polynomial induction of Mathlib's `MvPolynomial.aeval_sumElim_pderiv_inl`,
  -- here over a commutative semiring and with the omitted coordinate indexed by `i`.
  classical
  induction p using MvPolynomial.induction_on with
  | C a => simp [dehomogenize]
  | add p q hp hq => simp [hp, hq]
  | mul_X p l h =>
    refine Fin.succAboveCases i ?_ (fun k ↦ ?_) l
    · simp [h, dehomogenize_X]
    · simp [h, dehomogenize_X, Pi.single_apply, apply_ite,
        Fin.succAbove_right_injective.eq_iff]

/-- Euler's identity at a zero in an affine chart: the omitted partial derivative plus
the coordinate-weighted sum of the retained partial derivatives is zero. -/
theorem eval_pderiv_add_sum_dehomogenize (i : Fin (n + 1))
    {p : MvPolynomial (Fin (n + 1)) R} {d : ℕ} (hp : p.IsHomogeneous d)
    (a : Fin n → R) (ha : eval a (dehomogenize i p) = 0) :
    eval (i.insertNth 1 a) (pderiv i p) +
      ∑ j : Fin n, a j * eval a (pderiv j (dehomogenize i p)) = 0 := by
  have he := congrArg (eval (i.insertNth 1 a)) hp.sum_X_mul_pderiv
  rw [map_sum, Fin.sum_univ_succAbove _ i] at he
  simp only [map_mul, eval_X, Fin.insertNth_apply_same, one_mul,
    Fin.insertNth_apply_succAbove, map_nsmul] at he
  rw [← eval_dehomogenize i p a, ha, nsmul_zero] at he
  simpa only [pderiv_dehomogenize, eval_dehomogenize] using he

/-- At a zero of a homogeneous equation, the homogeneous gradient vanishes if and only
if the gradient of the equation in any chosen affine chart vanishes. -/
theorem forall_eval_pderiv_eq_zero_iff_dehomogenize (i : Fin (n + 1))
    {p : MvPolynomial (Fin (n + 1)) R} {d : ℕ} (hp : p.IsHomogeneous d)
    (a : Fin n → R) (ha : eval a (dehomogenize i p) = 0) :
    (∀ l, eval (i.insertNth 1 a) (pderiv l p) = 0) ↔
      ∀ j, eval a (pderiv j (dehomogenize i p)) = 0 := by
  constructor
  · intro h j
    rw [pderiv_dehomogenize, eval_dehomogenize]
    exact h _
  · intro h l
    refine Fin.succAboveCases i ?_ (fun j ↦ ?_) l
    · simpa only [h, mul_zero, Finset.sum_const_zero, add_zero] using
        eval_pderiv_add_sum_dehomogenize i hp a ha
    · rw [← eval_dehomogenize, ← pderiv_dehomogenize]
      exact h j

/-- A homogeneous gradient is nonzero at a zero of the equation exactly when the
affine gradient is nonzero. Over a field, this is the nonsingularity criterion. -/
theorem exists_eval_pderiv_ne_zero_iff_dehomogenize (i : Fin (n + 1))
    {p : MvPolynomial (Fin (n + 1)) R} {d : ℕ} (hp : p.IsHomogeneous d)
    (a : Fin n → R) (ha : eval a (dehomogenize i p) = 0) :
    (∃ l, eval (i.insertNth 1 a) (pderiv l p) ≠ 0) ↔
      ∃ j, eval a (pderiv j (dehomogenize i p)) ≠ 0 := by
  simpa only [not_forall] using not_congr
    (forall_eval_pderiv_eq_zero_iff_dehomogenize i hp a ha)

end CommSemiring

section CommRing

variable {R : Type*} [CommRing R]

/-- At a zero of a homogeneous equation, the omitted partial derivative is determined
by the retained partial derivatives. -/
theorem eval_pderiv_eq_neg_sum_dehomogenize (i : Fin (n + 1))
    {p : MvPolynomial (Fin (n + 1)) R} {d : ℕ} (hp : p.IsHomogeneous d)
    (a : Fin n → R) (ha : eval a (dehomogenize i p) = 0) :
    eval (i.insertNth 1 a) (pderiv i p) =
      -∑ j : Fin n, a j * eval a (pderiv j (dehomogenize i p)) := by
  exact eq_neg_of_add_eq_zero_left (eval_pderiv_add_sum_dehomogenize i hp a ha)

end CommRing

section Semifield

variable {k : Type*} [Semifield k]

/-- At a homogeneous point whose `i`-th coordinate is nonzero, evaluation in the
standard affine chart differs by the inverse `d`-th power of that coordinate. -/
theorem eval_dehomogenize_div (i : Fin (n + 1))
    {p : MvPolynomial (Fin (n + 1)) k} {d : ℕ} (hp : p.IsHomogeneous d)
    (b : Fin (n + 1) → k) (hi : b i ≠ 0) :
    eval (fun j ↦ b (i.succAbove j) / b i) (dehomogenize i p) =
      (b i)⁻¹ ^ d * eval b p := by
  rw [eval_dehomogenize]
  have h : i.insertNth 1 (fun j ↦ b (i.succAbove j) / b i) = (b i)⁻¹ • b := by
    ext l
    refine Fin.succAboveCases i ?_ (fun j ↦ ?_) l <;> simp [hi, div_eq_mul_inv, mul_comm]
  rw [h, hp.eval_smul, smul_eq_mul]

/-- Over a semifield, a nonzero homogeneous coordinate can be normalized to one without
changing whether the gradient vanishes. The derivatives of the affine equation are
evaluated at the coordinate ratios. -/
theorem forall_eval_pderiv_eq_zero_iff_dehomogenize_div (i : Fin (n + 1))
    {p : MvPolynomial (Fin (n + 1)) k} {d : ℕ} (hp : p.IsHomogeneous d)
    (b : Fin (n + 1) → k) (hi : b i ≠ 0) (hb : eval b p = 0) :
    (∀ l, eval b (pderiv l p) = 0) ↔
      ∀ j, eval (fun j ↦ b (i.succAbove j) / b i) (pderiv j (dehomogenize i p)) = 0 := by
  let a : Fin n → k := fun j ↦ b (i.succAbove j) / b i
  have ha : eval a (dehomogenize i p) = 0 := by
    rw [eval_dehomogenize_div i hp b hi, hb, mul_zero]
  rw [← forall_eval_pderiv_eq_zero_iff_dehomogenize i hp a ha]
  refine forall_congr' fun l ↦ ?_
  rw [← eval_dehomogenize, eval_dehomogenize_div i hp.pderiv b hi]
  simp [hi]

/-- Over a field, nonsingularity of a point of a homogeneous hypersurface is equivalent
to a nonzero partial derivative of the equation in any affine chart containing it.
For a plane equation this applies uniformly to all three standard charts. -/
theorem exists_eval_pderiv_ne_zero_iff_dehomogenize_div (i : Fin (n + 1))
    {p : MvPolynomial (Fin (n + 1)) k} {d : ℕ} (hp : p.IsHomogeneous d)
    (b : Fin (n + 1) → k) (hi : b i ≠ 0) (hb : eval b p = 0) :
    (∃ l, eval b (pderiv l p) ≠ 0) ↔
      ∃ j, eval (fun j ↦ b (i.succAbove j) / b i) (pderiv j (dehomogenize i p)) ≠ 0 := by
  simpa only [not_forall] using not_congr
    (forall_eval_pderiv_eq_zero_iff_dehomogenize_div i hp b hi hb)

end Semifield

end TauCeti

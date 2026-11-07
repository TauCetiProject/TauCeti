/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.RingTheory.Ideal.Maps

/-!
# Rescaling the variables of a multivariate polynomial

For `a : σ → R`, `MvPolynomial.rescale a` is the `R`-algebra endomorphism of `MvPolynomial σ R`
sending each variable `X i` to `a i * X i`. It multiplies the coefficient of the monomial `X^n`
by `∏ i, a i ^ n i`, so supports can only shrink, and it is the polynomial counterpart of
Mathlib's `MvPowerSeries.rescale`. When every `a i` is a unit, rescaling by `a` is an algebra
automorphism with inverse the rescaling by the inverses, `MvPolynomial.rescaleEquiv`; then
contracting an ideal along `rescale a` is the same as extending it along the inverse rescaling.

Such diagonal changes of variables relate algebra maps `X i ↦ f i` and `X i ↦ a i * f i`
(`MvPolynomial.aeval_rescale`), for instance a presentation of a subalgebra by generators to the
presentation by rescaled generators.

## Main declarations

* `MvPolynomial.rescale`: the endomorphism `X i ↦ a i * X i`.
* `MvPolynomial.coeff_rescale`: the coefficient of `X^n` is multiplied by `∏ i, a i ^ n i`.
* `MvPolynomial.aeval_rescale`: evaluating a rescaled polynomial at `x` is evaluating it at
  `a i • x i`.
* `MvPolynomial.rescale_mul`: rescalings compose multiplicatively.
* `MvPolynomial.rescaleEquiv`: for units `u`, rescaling by `u` as an algebra automorphism, with
  inverse `MvPolynomial.rescaleEquiv u⁻¹`.
* `MvPolynomial.comap_rescale`: contraction along the rescaling by `a` is extension along the
  rescaling by an inverse family `b`.
-/

public section

namespace MvPolynomial

variable {σ R : Type*} [CommSemiring R]

/-- The `R`-algebra endomorphism of `MvPolynomial σ R` rescaling the variables, `X i ↦ a i * X i`.
It sends `p(X)` to `p(a X)`. -/
noncomputable def rescale (a : σ → R) : MvPolynomial σ R →ₐ[R] MvPolynomial σ R :=
  aeval fun i ↦ C (a i) * X i

theorem rescale_eq_aeval (a : σ → R) : rescale a = aeval fun i ↦ C (a i) * X i :=
  (rfl)

@[simp]
theorem rescale_X (a : σ → R) (i : σ) : rescale a (X i) = C (a i) * X i :=
  aeval_X _ _

/-- Evaluating a rescaled polynomial at `x` is evaluating the polynomial at `a i • x i`. -/
theorem aeval_rescale {S : Type*} [CommSemiring S] [Algebra R S] (a : σ → R) (x : σ → S)
    (p : MvPolynomial σ R) : aeval x (rescale a p) = aeval (fun i ↦ a i • x i) p := by
  rw [← AlgHom.comp_apply]
  congr 1
  refine algHom_ext fun i ↦ ?_
  simp [Algebra.smul_def]

/-- Rescaling the monomial `r X^n` multiplies its coefficient by `∏ i, a i ^ n i`. -/
@[simp]
theorem rescale_monomial (a : σ → R) (n : σ →₀ ℕ) (r : R) :
    rescale a (monomial n r) = monomial n ((n.prod fun i k ↦ a i ^ k) * r) := by
  simp only [rescale_eq_aeval, monomial_eq, map_mul, aeval_C, algebraMap_eq, Finsupp.prod,
    map_prod, map_pow, aeval_X, mul_pow, Finset.prod_mul_distrib]
  ring

/-- Rescaling multiplies the coefficient of `X^n` by `∏ i, a i ^ n i`. -/
@[simp]
theorem coeff_rescale (a : σ → R) (p : MvPolynomial σ R) (n : σ →₀ ℕ) :
    (rescale a p).coeff n = (n.prod fun i k ↦ a i ^ k) * p.coeff n := by
  induction p using MvPolynomial.induction_on' with
  | monomial d r =>
    classical
    rw [rescale_monomial, coeff_monomial, coeff_monomial]
    split_ifs with h
    · rw [h]
    · rw [mul_zero]
  | add p q hp hq => simp [hp, hq, mul_add]

theorem support_rescale_subset (a : σ → R) (p : MvPolynomial σ R) :
    (rescale a p).support ⊆ p.support := by
  intro n hn
  rw [mem_support_iff, coeff_rescale] at hn
  exact mem_support_iff.2 (right_ne_zero_of_mul hn)

@[simp]
theorem rescale_one : rescale (1 : σ → R) = AlgHom.id R (MvPolynomial σ R) :=
  algHom_ext fun i ↦ by simp

theorem rescale_rescale (a b : σ → R) (p : MvPolynomial σ R) :
    rescale b (rescale a p) = rescale (a * b) p := by
  ext n
  simp only [coeff_rescale, Pi.mul_apply, mul_pow, Finsupp.prod, Finset.prod_mul_distrib]
  ring

theorem rescale_mul (a b : σ → R) : rescale (a * b) = (rescale b).comp (rescale a) :=
  AlgHom.ext fun p ↦ (rescale_rescale a b p).symm

/-- Rescaling by `a` and then by `b` is the identity when `a i * b i = 1` for every `i`. -/
theorem rescale_rescale_of_mul_eq_one {a b : σ → R} (h : ∀ i, a i * b i = 1)
    (p : MvPolynomial σ R) : rescale b (rescale a p) = p := by
  have hab : a * b = 1 := funext fun i ↦ by rw [Pi.mul_apply, Pi.one_apply, h]
  rw [rescale_rescale, hab, rescale_one, AlgHom.id_apply]

/-- Rescaling by a family of units is an algebra automorphism, whose inverse rescales by the
inverse units. -/
noncomputable def rescaleEquiv (u : σ → Rˣ) : MvPolynomial σ R ≃ₐ[R] MvPolynomial σ R :=
  AlgEquiv.ofAlgHom (rescale fun i ↦ (u i : R)) (rescale fun i ↦ ((u i)⁻¹ : Rˣ))
    (AlgHom.ext <| rescale_rescale_of_mul_eq_one fun i ↦ (u i).inv_mul)
    (AlgHom.ext <| rescale_rescale_of_mul_eq_one fun i ↦ (u i).mul_inv)

@[simp]
theorem rescaleEquiv_apply (u : σ → Rˣ) (p : MvPolynomial σ R) :
    rescaleEquiv u p = rescale (fun i ↦ (u i : R)) p :=
  (rfl)

@[simp]
theorem toAlgHom_rescaleEquiv (u : σ → Rˣ) :
    (rescaleEquiv u : MvPolynomial σ R →ₐ[R] MvPolynomial σ R) = rescale fun i ↦ (u i : R) :=
  (rfl)

@[simp]
theorem rescaleEquiv_symm (u : σ → Rˣ) :
    (rescaleEquiv u).symm = rescaleEquiv (R := R) u⁻¹ :=
  (rfl)

/-- If `a i * b i = 1` for every `i`, then the contraction of an ideal along the rescaling by `a`
is its extension along the rescaling by `b`. -/
theorem comap_rescale {a b : σ → R} (h : ∀ i, a i * b i = 1) (I : Ideal (MvPolynomial σ R)) :
    I.comap (rescale a) = I.map (rescale b) := by
  have h' (i : σ) : b i * a i = 1 := by rw [mul_comm, h]
  exact le_antisymm (Ideal.comap_le_map_of_inverse _ _ _ (rescale_rescale_of_mul_eq_one h))
    (Ideal.map_le_comap_of_inverse _ _ _ (rescale_rescale_of_mul_eq_one h'))

end MvPolynomial

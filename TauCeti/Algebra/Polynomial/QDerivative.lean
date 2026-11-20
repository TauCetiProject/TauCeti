/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Expand
public import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Tactic.LinearCombination
import TauCeti.Algebra.Polynomial.Eval.Degree
import TauCeti.Algebra.Ring.GeomSum

/-!
# The `q`-derivative of a polynomial

For an element `q` of a commutative semiring `R`, the `q`-derivative (Jackson derivative) of a
polynomial `f = ∑ aₙ Xⁿ` is

`∇_q f = ∑ aₙ [n]_q X ^ (n - 1)`,

where `[n]_q = ∑_{i < n} q ^ i` is the `q`-integer, with the constant term sent to zero. This is a
finite sum, so it is defined for every `q`, including `q = 1` and values for which `q - 1` is a
zero divisor; it is not defined as the difference quotient `(f(qX) - f(X)) / ((q - 1) X)`.

The `q`-derivative is the polynomial model of the `q`-derivatives of a framed algebra in
`q`-de Rham cohomology: over the coefficient ring `R`, the coordinate scaling `X ↦ q X` plays the
role of the automorphism `γ`, and `∇_q` satisfies the laws of a `q`-derivative before any
completion:

* the defining identity `f(qX) - f(X) = (q - 1) X ∇_q f`, which determines `∇_q f` when `q - 1`
  is a nonzerodivisor (`Polynomial.C_sub_one_mul_X_mul_qDerivative`,
  `Polynomial.eq_qDerivative_iff`);
* the twisted Leibniz rule `∇_q (f g) = ∇_q f · g + f(qX) · ∇_q g` (`Polynomial.qDerivative_mul`);
* `∇_q (Xⁿ) = [n]_q X ^ (n - 1)` (`Polynomial.qDerivative_X_pow`);
* the specialisations `∇_1 = Polynomial.derivative` and `∇_0 = Polynomial.divX`;
* naturality under coefficient maps (`Polynomial.qDerivative_map`), and the chain rule for
  `X ↦ X ^ m`, `∇_q (f(X ^ m)) = [m]_q X ^ (m - 1) (∇_{q ^ m} f)(X ^ m)`
  (`Polynomial.qDerivative_expand`). Combining the last two gives the Frobenius identity
  `∇_q φ = [p]_q X ^ (p - 1) φ ∇_q` for `φ (X) = X ^ p` on coordinates and a coefficient map
  with `φ (q) = q ^ p`.

## Main definitions

* `Polynomial.qDerivative q`: the `q`-derivative, an `R`-linear endomorphism of `R[X]`.

The definition and its linearity proof follow Mathlib's `Polynomial.derivative`, with the factor
`n` replaced by the `q`-integer `[n]_q`.

## References

* B. Bhatt and P. Scholze, *Prisms and prismatic cohomology*, Ann. of Math. 196 (2022),
  Construction 16.19.
* P. Scholze, *Canonical q-deformations in arithmetic geometry*, Ann. Fac. Sci. Toulouse Math.
  26 (2017), §3.
* F. H. Jackson, *On q-functions and a certain difference operator*, Trans. Roy. Soc. Edinburgh
  46 (1908).
-/

public section

noncomputable section

open Finset

namespace Polynomial

variable {R S : Type*}

section Semiring

variable [Semiring R] [Semiring S] (q : R)

/-- The `q`-derivative `∇_q f = ∑ aₙ [n]_q X ^ (n - 1)` of `f = ∑ aₙ Xⁿ`, where
`[n]_q = ∑_{i < n} q ^ i` is the `q`-integer. It is the finite-sum form of the difference
quotient `(f(qX) - f(X)) / ((q - 1) X)`, defined for every `q`; for `q = 1` it is
`Polynomial.derivative`. -/
def qDerivative : R[X] →ₗ[R] R[X] where
  toFun f := f.sum fun n a ↦ C (a * ∑ i ∈ range n, q ^ i) * X ^ (n - 1)
  map_add' f g := by
    rw [sum_add_index _ _ _ (fun n ↦ by rw [zero_mul, map_zero, zero_mul])
      (fun n a b ↦ by rw [add_mul, map_add, add_mul])]
  map_smul' a f := by
    rw [RingHom.id_apply, sum_smul_index _ _ _ (fun n ↦ by rw [zero_mul, map_zero, zero_mul]),
      smul_eq_C_mul, sum, sum, mul_sum]
    simp only [mul_assoc, map_mul]

theorem qDerivative_apply (f : R[X]) :
    qDerivative q f = f.sum fun n a ↦ C (a * ∑ i ∈ range n, q ^ i) * X ^ (n - 1) :=
  (rfl)

/-- The `q`-derivative of a monomial: `∇_q (a Xⁿ) = a [n]_q X ^ (n - 1)`. -/
theorem qDerivative_monomial (a : R) (n : ℕ) :
    qDerivative q (monomial n a) = monomial (n - 1) (a * ∑ i ∈ range n, q ^ i) := by
  rw [qDerivative_apply, sum_monomial_index _ _ (by simp), C_mul_X_pow_eq_monomial]

@[simp]
theorem qDerivative_monomial_succ (a : R) (n : ℕ) :
    qDerivative q (monomial (n + 1) a) = monomial n (a * ∑ i ∈ range (n + 1), q ^ i) := by
  rw [qDerivative_monomial, Nat.add_sub_cancel]

/-- The coefficients of the `q`-derivative: the coefficient of `Xⁿ` in `∇_q f` is
`[n + 1]_q` times the coefficient of `X ^ (n + 1)` in `f`. -/
theorem coeff_qDerivative (f : R[X]) (n : ℕ) :
    (qDerivative q f).coeff n = f.coeff (n + 1) * ∑ i ∈ range (n + 1), q ^ i := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg => rw [map_add, coeff_add, hf, hg, coeff_add, add_mul]
  | monomial m a =>
    rcases m with _ | m
    · simp [-monomial_zero_left, qDerivative_monomial]
    · simp only [qDerivative_monomial_succ, coeff_monomial, Finsupp.single_apply,
        Nat.add_right_cancel_iff]
      split_ifs with h
      · rw [h]
      · rw [zero_mul]

theorem qDerivative_C_mul_X_pow (a : R) (n : ℕ) :
    qDerivative q (C a * X ^ n) = C (a * ∑ i ∈ range n, q ^ i) * X ^ (n - 1) := by
  rw [C_mul_X_pow_eq_monomial, C_mul_X_pow_eq_monomial, qDerivative_monomial]

/-- The `q`-derivative of a power of `X`: `∇_q (Xⁿ) = [n]_q X ^ (n - 1)`. -/
theorem qDerivative_X_pow (n : ℕ) :
    qDerivative q (X ^ n : R[X]) = C (∑ i ∈ range n, q ^ i) * X ^ (n - 1) := by
  simpa using qDerivative_C_mul_X_pow q 1 n

@[simp]
theorem qDerivative_X_pow_succ (n : ℕ) :
    qDerivative q (X ^ (n + 1) : R[X]) = C (∑ i ∈ range (n + 1), q ^ i) * X ^ n := by
  rw [qDerivative_X_pow, Nat.add_sub_cancel]

@[simp]
theorem qDerivative_C (a : R) : qDerivative q (C a) = 0 := by
  simp [← monomial_zero_left, qDerivative_monomial]

@[simp]
theorem qDerivative_X : qDerivative q (X : R[X]) = 1 := by
  simpa using qDerivative_X_pow_succ q 0

@[simp]
theorem qDerivative_one : qDerivative q (1 : R[X]) = 0 := by
  simpa using qDerivative_C q 1

/-- The `q`-derivative is linear over the constants. -/
theorem qDerivative_C_mul (a : R) (f : R[X]) :
    qDerivative q (C a * f) = C a * qDerivative q f := by
  rw [C_mul', map_smul, C_mul']

/-- At `q = 1` the `q`-derivative is the ordinary derivative. -/
@[simp]
theorem qDerivative_one_eq_derivative : qDerivative (1 : R) = derivative := by
  ext f n
  simp [coeff_qDerivative, coeff_derivative]

/-- At `q = 0` the `q`-derivative is division by `X` after removing the constant term:
`∇_0 f = (f - f(0)) / X`. -/
theorem qDerivative_zero_eq_divX (f : R[X]) : qDerivative 0 f = divX f := by
  ext n
  simp [coeff_qDerivative, coeff_divX]

/-- The `q`-derivative commutes with coefficient maps: `σ (∇_q f) = ∇_{σ q} (σ f)`. -/
@[simp]
theorem qDerivative_map (σ : R →+* S) (f : R[X]) :
    qDerivative (σ q) (f.map σ) = (qDerivative q f).map σ := by
  ext n
  simp [coeff_qDerivative, coeff_map]

end Semiring

section CommSemiring

variable [CommSemiring R] (q : R)

/-- The twisted Leibniz rule `∇_q (f g) = ∇_q f · g + f(qX) · ∇_q g`. At `q = 1` it is the
ordinary Leibniz rule. -/
theorem qDerivative_mul (f g : R[X]) :
    qDerivative q (f * g) = qDerivative q f * g + f.comp (C q * X) * qDerivative q g := by
  induction f using Polynomial.induction_on' with
  | add f₁ f₂ hf₁ hf₂ => rw [add_mul, map_add, hf₁, hf₂, map_add, add_comp]; ring
  | monomial m a =>
    induction g using Polynomial.induction_on' with
    | add g₁ g₂ hg₁ hg₂ => rw [mul_add, map_add, hg₁, hg₂, map_add]; ring
    | monomial n b =>
      simp only [monomial_comp_C_mul_X, monomial_mul_monomial, qDerivative_monomial]
      rcases m with _ | m
      · simp [mul_assoc]
      rcases n with _ | n
      · simp [mul_right_comm]
      -- `[m + n + 2]_q = [m + 1]_q + q ^ (m + 1) [n + 1]_q`
      have hsum : ∑ i ∈ range (m + 1 + (n + 1)), q ^ i =
          ∑ i ∈ range (m + 1), q ^ i + q ^ (m + 1) * ∑ i ∈ range (n + 1), q ^ i := by
        rw [sum_range_add, mul_sum]
        simp only [pow_add]
      ext k
      simp only [coeff_add, coeff_monomial, Finsupp.single_apply, hsum]
      split_ifs <;> first | omega | ring

/-- The chain rule for `X ↦ X ^ m`: `∇_q (f(X ^ m)) = (∇_{q ^ m} f)(X ^ m) · [m]_q X ^ (m - 1)`.
It is the `q`-analogue of `Polynomial.derivative_expand`. -/
theorem qDerivative_expand (m : ℕ) (f : R[X]) :
    qDerivative q (expand R m f) =
      expand R m (qDerivative (q ^ m) f) * (C (∑ i ∈ range m, q ^ i) * X ^ (m - 1)) := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg => rw [map_add, map_add, hf, hg, map_add, map_add, add_mul]
  | monomial n a =>
    rw [expand_monomial, qDerivative_monomial, qDerivative_monomial, expand_monomial,
      C_mul_X_pow_eq_monomial, monomial_mul_monomial]
    rcases n with _ | n
    · simp
    rcases m with _ | m
    · simp
    rw [show (n + 1) * (m + 1) - 1 = (n + 1 - 1) * (m + 1) + (m + 1 - 1) by
        simp only [Nat.add_sub_cancel, add_mul, one_mul]; omega,
      mul_comm (n + 1), TauCeti.geom_sum_range_mul]
    congr 1
    ring

end CommSemiring

section CommRing

variable [CommRing R] (q : R)

/-- The defining identity of the `q`-derivative: `f(qX) - f(X) = (q - 1) X ∇_q f`. -/
theorem C_sub_one_mul_X_mul_qDerivative (f : R[X]) :
    C (q - 1) * X * qDerivative q f = f.comp (C q * X) - f := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg => rw [map_add, mul_add, hf, hg, add_comp]; ring
  | monomial n a =>
    rw [monomial_comp_C_mul_X, ← map_sub]
    rcases n with _ | n
    · simp
    · rw [qDerivative_monomial_succ, mul_assoc, X_mul_monomial, C_mul_monomial]
      congr 1
      linear_combination a * mul_geom_sum q (n + 1)

/-- When `q - 1` is a nonzerodivisor, the defining identity `f(qX) - f(X) = (q - 1) X g`
characterizes the `q`-derivative `g = ∇_q f`. -/
theorem eq_qDerivative_iff (hq : IsLeftRegular (q - 1)) {f g : R[X]} :
    g = qDerivative q f ↔ C (q - 1) * X * g = f.comp (C q * X) - f := by
  refine ⟨fun h ↦ h ▸ C_sub_one_mul_X_mul_qDerivative q f, fun h ↦ ?_⟩
  rw [← C_sub_one_mul_X_mul_qDerivative] at h
  ext n
  have hn := congrArg (fun p : R[X] ↦ p.coeff (n + 1)) h
  simp only [mul_assoc, coeff_C_mul, coeff_X_mul] at hn
  exact hq hn

end CommRing

end Polynomial

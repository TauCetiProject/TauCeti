/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Derivative
public import TauCeti.RingTheory.MvPolynomial.Symmetric.Complete.Basic
import TauCeti.RingTheory.PowerSeries.Derivative
import TauCeti.RingTheory.PowerSeries.Geometric

/-!
# Newton's identities for the complete homogeneous symmetric polynomials

The generating function `H(t) = ∑ₙ hₙ tⁿ` of the complete homogeneous symmetric polynomials in the
variables `xᵢ` is the product `∏ᵢ (1 - xᵢ t)⁻¹`. Its logarithmic derivative is therefore
`H'(t) / H(t) = ∑ᵢ xᵢ / (1 - xᵢ t) = ∑_{n ≥ 1} pₙ tⁿ⁻¹`. Multiplying by `t` gives
`t H'(t) = H(t) P(t)`, where `P(t) = ∑_{n ≥ 1} pₙ tⁿ = ∑ᵢ xᵢ t / (1 - xᵢ t)` is the generating
function of the power sums. Comparing coefficients gives **Newton's identities for the complete
homogeneous symmetric polynomials**, `k hₖ = ∑_{i = 1}^{k} h_{k - i} pᵢ`. They are the counterpart
of Mathlib's `MvPolynomial.mul_esymm_eq_sum` for the elementary symmetric polynomials, but have no
signs.

## Main results

* `TauCeti.X_mul_derivative_mk_hsymm`: `t H'(t) = H(t) P(t)`, as power series over
  `MvPolynomial σ R`.
* `TauCeti.mul_hsymm_eq_sum`: `k hₖ = ∑_{i + j = k, i < k} hᵢ pⱼ`.

## References

* [I. G. Macdonald, *Symmetric Functions and Hall Polynomials*][macdonald1995], Chapter I,
  Section 2: the generating function of the power sums as the logarithmic derivative of `H(t)`,
  and Newton's identities for the `hₙ`.
-/

public section

namespace TauCeti

open PowerSeries Finset

/-- **The logarithmic derivative of the generating function of the complete homogeneous symmetric
polynomials**: `t H'(t) = H(t) P(t)`, where `H(t) = ∑ₙ hₙ tⁿ` and `P(t) = ∑_{n ≥ 1} pₙ tⁿ` is the
generating function of the power sums. -/
theorem X_mul_derivative_mk_hsymm (σ : Type*) [Fintype σ] [DecidableEq σ] (R : Type*)
    [CommSemiring R] :
    X * d⁄dX (mk fun n => MvPolynomial.hsymm σ R n) =
      (mk fun n => MvPolynomial.hsymm σ R n) *
        mk fun n => if n = 0 then 0 else MvPolynomial.psum σ R n := by
  set g : σ → (MvPolynomial σ R)⟦X⟧ := fun i => mk fun n => MvPolynomial.X i ^ n
  have hprod : ∀ s : Finset σ,
      X * d⁄dX (∏ i ∈ s, g i) = (∏ i ∈ s, g i) * ∑ i ∈ s, C (MvPolynomial.X i) * X * g i := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert j s hj ih =>
      rw [prod_insert hj, sum_insert hj, Derivation.leibniz, smul_eq_mul, smul_eq_mul, mul_add,
        mul_left_comm X (g j), ih, mul_left_comm X (∏ i ∈ s, g i),
        powerSeries_X_mul_derivative_mk_pow]
      ring
  have hP : ∑ i, C (MvPolynomial.X i) * X * g i =
      mk fun n => if n = 0 then 0 else MvPolynomial.psum σ R n := by
    ext n
    rw [map_sum, coeff_mk]
    cases n with
    | zero => simp
    | succ m => simp [g, mul_assoc, MvPolynomial.psum, pow_succ']
  rw [mk_hsymm_eq_prod_mk_pow, hprod, hP]

/-- **Newton's identities for the complete homogeneous symmetric polynomials**:
`k hₖ = ∑_{i + j = k, i < k} hᵢ pⱼ`, that is `k hₖ = ∑_{j = 1}^{k} h_{k - j} pⱼ`. -/
theorem mul_hsymm_eq_sum (σ : Type*) [Fintype σ] [DecidableEq σ] (R : Type*) [CommSemiring R]
    (k : ℕ) :
    k * MvPolynomial.hsymm σ R k =
      ∑ a ∈ antidiagonal k with a.1 < k,
        MvPolynomial.hsymm σ R a.1 * MvPolynomial.psum σ R a.2 := by
  have h := congrArg (coeff k) (X_mul_derivative_mk_hsymm σ R)
  have hk := coeff_X_pow_mul_iterate_derivative (mk fun n => MvPolynomial.hsymm σ R n) 1 k
  rw [pow_one, Function.iterate_one, Nat.descFactorial_one, coeff_mk] at hk
  rw [hk, coeff_mul] at h
  rw [h, sum_filter]
  refine sum_congr rfl fun a ha => ?_
  rw [mem_antidiagonal] at ha
  simp only [coeff_mk]
  split_ifs <;> first | omega | rfl | simp

end TauCeti

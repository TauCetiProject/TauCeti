/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Derivation
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import TauCeti.Data.Finsupp.Multiset

/-!
# Derivations that shift the weighted degree

A derivation of `MvPolynomial σ R` is determined by its values on the variables. If it sends each
variable `X i` to a weighted homogeneous polynomial of weight `w i + k` for one fixed shift `k`,
then it sends every weighted homogeneous polynomial of weight `m` to one of weight `m + k`
(`MvPolynomial.IsWeightedHomogeneous.derivation`).

The degree derivation, sending each variable `X i` to `w i • X i`, acts on a weighted homogeneous
polynomial of weight `m` as multiplication by `m`
(`MvPolynomial.IsWeightedHomogeneous.derivation_eq_nsmul`). This is Euler's identity for weighted
homogeneous polynomials in any number of variables; Mathlib's
`MvPolynomial.IsWeightedHomogeneous.sum_weight_X_mul_pderiv` states it as a sum over finitely many
variables.

Partial derivatives, whose shift depends on the variable, are treated in Mathlib by
`MvPolynomial.IsWeightedHomogeneous.pderiv`.
-/

public section

namespace MvPolynomial

variable {R σ M : Type*} [CommSemiring R] [AddCommMonoid M] {w : σ → M}

/-- A derivation sending each variable `X i` to a weighted homogeneous polynomial of weight
`w i + k` sends weighted homogeneous polynomials of weight `m` to weighted homogeneous
polynomials of weight `m + k`. -/
theorem IsWeightedHomogeneous.derivation {φ : MvPolynomial σ R} {m : M} (k : M)
    (D : Derivation R (MvPolynomial σ R) (MvPolynomial σ R))
    (hD : ∀ i, (D (X i)).IsWeightedHomogeneous w (w i + k))
    (hφ : φ.IsWeightedHomogeneous w m) : (D φ).IsWeightedHomogeneous w (m + k) := by
  induction hφ using IsWeightedHomogeneous.induction_on with
  | zero => simpa using isWeightedHomogeneous_zero R w (m + k)
  | add p q _ _ hp hq => simpa using hp.add hq
  | monomial d r hr =>
    subst hr
    induction d using Finsupp.induction_add_single_one with
    | zero => simpa using isWeightedHomogeneous_zero R w _
    | add_single_one i d ih =>
      -- `monomial (d + eᵢ) r = monomial d r * X i`, and both Leibniz terms have weight
      -- `weight d + w i + k`
      rw [monomial_add_single, Derivation.leibniz]
      refine .add ?_ ?_
      · convert (isWeightedHomogeneous_monomial w d r rfl).mul (hD i) using 1 <;>
          simp [Finsupp.weight_single, add_assoc]
      · convert (isWeightedHomogeneous_X R w i).mul ih using 1 <;>
          simp [Finsupp.weight_single, add_assoc, add_left_comm]

/-- **Euler's identity for weighted homogeneous polynomials.** A derivation sending each variable
`X i` to `w i • X i` multiplies a weighted homogeneous polynomial of weight `m` by `m`. -/
theorem IsWeightedHomogeneous.derivation_eq_nsmul {w : σ → ℕ} {φ : MvPolynomial σ R} {m : ℕ}
    (D : Derivation R (MvPolynomial σ R) (MvPolynomial σ R)) (hD : ∀ i, D (X i) = w i • X i)
    (hφ : φ.IsWeightedHomogeneous w m) : D φ = m • φ := by
  induction hφ using IsWeightedHomogeneous.induction_on with
  | zero => simp
  | add p q _ _ hp hq => simp [hp, hq]
  | monomial d r hr =>
    subst hr
    induction d using Finsupp.induction_add_single_one with
    | zero => simp
    | add_single_one i d ih =>
      -- `monomial (d + eᵢ) r = monomial d r * X i`, and both Leibniz terms are multiples of it
      rw [monomial_add_single, pow_one, Derivation.leibniz, ih, hD, map_add,
        Finsupp.weight_single]
      simp only [smul_eq_mul, nsmul_eq_mul, one_mul, Nat.cast_add]
      ring

end MvPolynomial

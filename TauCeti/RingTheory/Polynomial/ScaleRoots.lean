/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.Polynomial.ScaleRoots

/-!
# Root scaling of finite products, derivatives and separability

Scaling roots commutes with finite products over a commutative semiring without zero
divisors, and with finite products of monic polynomials over any commutative semiring.
This transports factorizations into linear factors through integral normalization.
Over any semiring, scaling the roots by `s` also multiplies the subleading coefficient by `s`
on the right, so it preserves the vanishing of that coefficient.

The derivative of `p.scaleRoots s` is `(derivative p).scaleRoots s` up to the factor
`s ^ (natDegree p - 1 - natDegree p')`, so scaling the roots by a unit preserves separability.
This is how a separable polynomial over a valued field is given integral coefficients without
losing separability.
-/

public section

namespace Polynomial

variable {R ι : Type*}

/-- Scaling the roots by `s` multiplies the subleading coefficient by `s`. -/
@[simp]
theorem nextCoeff_scaleRoots [Semiring R] (p : R[X]) (s : R) :
    (p.scaleRoots s).nextCoeff = p.nextCoeff * s := by
  rcases Nat.eq_zero_or_pos p.natDegree with h | h
  · simp [nextCoeff, h]
  · simp [nextCoeff_of_natDegree_pos, h, Nat.sub_sub_self h]

variable [CommSemiring R]

/-- Scaling roots commutes with a finite product of monic polynomials, even when the
coefficient semiring has zero divisors. -/
theorem prod_scaleRoots_of_monic (s : Finset ι) (f : ι → R[X]) (a : R)
    (hf : ∀ i ∈ s, (f i).Monic) :
    (∏ i ∈ s, f i).scaleRoots a = ∏ i ∈ s, (f i).scaleRoots a := by
  classical
  nontriviality R
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.forall_mem_insert] at hf
    rw [Finset.prod_insert hi, mul_scaleRoots', ih hf.2, Finset.prod_insert hi]
    simp [hf.1.leadingCoeff, (monic_prod_of_monic s f hf.2).leadingCoeff]

/-- Scaling all roots of a finite product scales the roots of every factor. -/
@[simp]
theorem prod_scaleRoots [NoZeroDivisors R] (s : Finset ι) (f : ι → R[X]) (a : R) :
    (∏ i ∈ s, f i).scaleRoots a = ∏ i ∈ s, (f i).scaleRoots a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp only [Finset.prod_insert hi, mul_scaleRoots_of_noZeroDivisors, ih]

/-- A ring map `φ` that preserves the degree of `p` sends the evaluation of `p.scaleRoots b` at
`a` to the evaluation of `(p.map φ).scaleRoots (φ b)` at `φ a`. -/
theorem map_eval_scaleRoots {S T : Type*} [Semiring S] [Semiring T]
    (φ : S →+* T) {p : S[X]} (hp : (p.map φ).natDegree = p.natDegree) (a b : S) :
    φ ((p.scaleRoots b).eval a) = ((p.map φ).scaleRoots (φ b)).eval (φ a) := by
  have hmap : (p.scaleRoots b).map φ = (p.map φ).scaleRoots (φ b) := by
    ext n
    simp [hp]
  rw [← hmap, eval_map, eval₂_at_apply]

/-- **The derivative of a root scaling.** Scaling the roots of `p` by `s` and differentiating
agrees with scaling the roots of `p'` by `s`, up to the factor `s ^ (d - 1 - d')` accounting for
the drop from `d = natDegree p` to `d' = natDegree p'`. -/
theorem derivative_scaleRoots (p : R[X]) (s : R) :
    derivative (p.scaleRoots s) =
      C (s ^ (p.natDegree - 1 - (derivative p).natDegree)) * (derivative p).scaleRoots s := by
  ext i
  rw [coeff_derivative, coeff_C_mul, coeff_scaleRoots, coeff_scaleRoots, coeff_derivative]
  rcases le_or_gt i (derivative p).natDegree with hi | hi
  · -- the exponents agree, as `i ≤ natDegree p' ≤ natDegree p - 1`
    have hd := natDegree_derivative_le p
    rw [show p.natDegree - (i + 1) = p.natDegree - 1 - (derivative p).natDegree +
      ((derivative p).natDegree - i) by omega, pow_add]
    ring
  · -- both coefficients vanish above the degree of `p'`
    have h0 : p.coeff (i + 1) * (i + 1 : R) = 0 := by
      rw [← coeff_derivative]
      exact coeff_eq_zero_of_natDegree_lt hi
    rw [mul_right_comm, h0]
    simp

/-- **Scaling the roots by a unit preserves separability.** -/
theorem Separable.scaleRoots {p : R[X]} (hp : p.Separable) {s : R} (hs : IsUnit s) :
    (p.scaleRoots s).Separable := by
  rw [Separable, derivative_scaleRoots, isCoprime_mul_unit_left_right (isUnit_C.mpr (hs.pow _))]
  exact isCoprime_scaleRoots _ _ s hs hp

end Polynomial

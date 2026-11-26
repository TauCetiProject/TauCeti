/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Polynomial.ScaleRoots

/-!
# Root scaling of finite products

Scaling roots commutes with finite products over a commutative semiring without zero
divisors, and with finite products of monic polynomials over any commutative semiring.
This transports factorizations into linear factors through integral normalization.
Over any semiring, scaling the roots by `s` also multiplies the subleading coefficient by `s`
on the right, so it preserves the vanishing of that coefficient.
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

end Polynomial

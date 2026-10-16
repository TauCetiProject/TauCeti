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
-/

public section

namespace Polynomial

variable {R ι : Type*} [CommSemiring R]

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
    have hfi := hf i (Finset.mem_insert_self i s)
    have hfs : ∀ j ∈ s, (f j).Monic := fun j hj ↦ hf j (Finset.mem_insert_of_mem hj)
    rw [Finset.prod_insert hi, mul_scaleRoots', ih hfs, Finset.prod_insert hi]
    simp [hfi.leadingCoeff, (monic_prod_of_monic s f hfs).leadingCoeff]

/-- Scaling all roots of a finite product scales the roots of every factor. -/
@[simp]
theorem prod_scaleRoots [NoZeroDivisors R] (s : Finset ι) (f : ι → R[X]) (a : R) :
    (∏ i ∈ s, f i).scaleRoots a = ∏ i ∈ s, (f i).scaleRoots a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp only [Finset.prod_insert hi, mul_scaleRoots_of_noZeroDivisors, ih]

end Polynomial

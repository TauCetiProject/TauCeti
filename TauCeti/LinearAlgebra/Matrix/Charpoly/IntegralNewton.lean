/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Charpoly.Roots
public import TauCeti.RingTheory.MvPolynomial.Symmetric.PowerSum.IntegralNewton

/-!
# Integral Newton identities for traces of matrix powers

For a square matrix with split characteristic polynomial over an integral domain, the integral
Newton polynomial of degree one greater than the matrix size vanishes at the traces of its
powers. This supplies a polynomial identity for traces without characteristic assumptions.

## Provenance

`Matrix.eval_integralNewtonPolynomial_trace_pow_eq_zero_of_splits` adapts the Newton-vanishing
step of `New.exists_rep_of_trace_identities` in
`src/Lib/GaloisRep/Pseudocharacter/Pseudorepresentations.lean` in grh-lean
(https://github.com/lsernau/grh-lean, commit `72fead1`, Apache 2.0,
Copyright 2026 Anthropic, PBC). The integral-domain formulation with an explicit splitting
hypothesis is new here.

## References

* I. G. Macdonald, *Symmetric Functions and Hall Polynomials*, 2nd ed. (1995), Chapter I, §2.
-/

public section

namespace Matrix

/-- If a matrix has split characteristic polynomial, its traces of powers annihilate the
integral Newton polynomial of degree one greater than its size. -/
theorem eval_integralNewtonPolynomial_trace_pow_eq_zero_of_splits
    {k n : Type*} [CommRing k] [IsDomain k] [Fintype n] [DecidableEq n]
    (A : Matrix n n k) (hA : A.charpoly.Splits) :
    MvPolynomial.eval (fun i : ℕ ↦ (A ^ i).trace)
      (TauCeti.integralNewtonPolynomial (Fintype.card n + 1) 1) = 0 := by
  have hp (i : ℕ) : (A ^ i).trace = (A.charpoly.roots.map fun a ↦ a ^ i).sum := by
    simpa using trace_aeval_eq_sum_roots_charpoly_of_splits hA (Polynomial.X ^ i)
  simp_rw [hp]
  rw [Multiset.eval_integralNewtonPolynomial]
  simp [Multiset.esymm_of_card_lt, ← hA.natDegree_eq_card_roots, charpoly_natDegree_eq_dim]

end Matrix

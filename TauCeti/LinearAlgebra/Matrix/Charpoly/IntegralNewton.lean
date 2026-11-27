/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Charpoly.Roots
public import TauCeti.RingTheory.MvPolynomial.Symmetric.PowerSum.IntegralNewton
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Integral Newton identities for traces of matrix powers

For every square matrix over a commutative ring, the integral Newton polynomial of degree one
greater than the matrix size vanishes at the traces of its powers. This supplies a polynomial
identity for traces without characteristic assumptions.

## Provenance

`Matrix.eval_integralNewtonPolynomial_trace_pow_eq_zero` adapts the Newton-vanishing
step of `New.exists_rep_of_trace_identities` in
`src/Lib/GaloisRep/Pseudocharacter/Pseudorepresentations.lean` in grh-lean
(https://github.com/lsernau/grh-lean, commit `72fead1`, Apache 2.0,
Copyright 2026 Anthropic, PBC). The commutative-ring formulation is new here.

## References

* I. G. Macdonald, *Symmetric Functions and Hall Polynomials*, 2nd ed. (1995), Chapter I, §2.
-/

public section

namespace Matrix

/-- Traces of powers of a square matrix annihilate the integral Newton polynomial of degree
one greater than its size, over any commutative ring. -/
theorem eval_integralNewtonPolynomial_trace_pow_eq_zero
    {k n : Type*} [CommRing k] [Fintype n] [DecidableEq n] (A : Matrix n n k) :
    MvPolynomial.eval (fun i : ℕ ↦ (A ^ i).trace)
      (TauCeti.integralNewtonPolynomial (Fintype.card n + 1) 1) = 0 := by
  -- Prove the identity on the universal matrix, which has integral-domain coefficients.
  let R := MvPolynomial (n × n) ℤ
  let U : Matrix n n R := of fun i j ↦ MvPolynomial.X (i, j)
  let K := AlgebraicClosure (FractionRing R)
  let f := (algebraMap (FractionRing R) K).comp (algebraMap R (FractionRing R))
  have hf : Function.Injective f :=
    (algebraMap (FractionRing R) K).injective.comp (IsFractionRing.injective R (FractionRing R))
  have hsplit := IsAlgClosed.splits (U.map f).charpoly
  have hp (i : ℕ) : ((U.map f) ^ i).trace =
      ((U.map f).charpoly.roots.map fun a ↦ a ^ i).sum := by
    simpa using trace_aeval_eq_sum_roots_charpoly_of_splits hsplit (Polynomial.X ^ i)
  have hU : MvPolynomial.eval (fun i : ℕ ↦ (U ^ i).trace)
      (TauCeti.integralNewtonPolynomial (Fintype.card n + 1) 1) = 0 := by
    apply hf
    rw [map_zero, MvPolynomial.map_eval, TauCeti.map_integralNewtonPolynomial]
    simp only [Function.comp_def, AddMonoidHom.map_trace, Matrix.map_pow]
    simp_rw [hp]
    rw [Multiset.eval_integralNewtonPolynomial]
    simp [Multiset.esymm_of_card_lt, ← hsplit.natDegree_eq_card_roots,
      charpoly_natDegree_eq_dim]
  -- Every matrix is a specialization of the universal matrix.
  let g : R →+* k := MvPolynomial.eval₂Hom (Int.castRingHom k) fun p ↦ A p.1 p.2
  have hmap : U.map g = A := by
    ext i j
    exact MvPolynomial.eval₂Hom_X' _ _ (i, j)
  have h := congrArg g hU
  rw [map_zero, MvPolynomial.map_eval, TauCeti.map_integralNewtonPolynomial] at h
  simpa only [Function.comp_def, AddMonoidHom.map_trace, Matrix.map_pow, hmap] using h

end Matrix

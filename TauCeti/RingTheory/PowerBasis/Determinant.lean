/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.RingTheory.PowerBasis
import Mathlib.Algebra.CharP.Lemmas
import TauCeti.RingTheory.Polynomial.Truncated.Determinant
import TauCeti.RingTheory.PowerBasis.Basic

/-!
# Determinants of power-expansion matrices in purely inseparable power bases

In exponential characteristic `p`, `(X - C c) ^ p ^ e = X ^ p ^ e - C (c ^ p ^ e)`. For a power
basis `pb` of `S` over `R` of dimension `pb.dim = p ^ e` with `pb.gen ^ pb.dim ∈ R`, the minimal
polynomial `pb.minpolyGen` is `X ^ pb.dim - C b`, so `PowerBasis.basis_repr_aeval` identifies the
matrix of the powers `1, f(pb.gen), …, f(pb.gen) ^ (pb.dim - 1)` in `pb.basis` with the
remainder matrix of `(f.map (algebraMap R S)) ^ i` modulo `(X - C pb.gen) ^ pb.dim`. Evaluating its
determinant via `Polynomial.det_coeff_pow_modByMonic_X_sub_C_pow` yields
`aeval pb.gen f.derivative ^ (pb.dim * (pb.dim - 1) / 2)` in `S`.

This is the local determinant step in Schröer's (2009) proof of Tate's (1952) genus-change theorem.

## Main results

* `PowerBasis.det_toMatrix_aeval_pow`: for a power basis `pb` of dimension `p ^ e` in exponential
  characteristic `p` with `pb.gen ^ pb.dim ∈ R`, the determinant of the transition matrix from
  `pb.basis` to the powers of `aeval pb.gen f` equals
  `aeval pb.gen f.derivative ^ (pb.dim * (pb.dim - 1) / 2)` in `S`.

## References

* S. Schröer, *On genus change in algebraic curves over imperfect fields*, Proc. Amer. Math. Soc.
  137 (2009), 1239–1243.
* J. Tate, *Genus change in inseparable extensions of function fields*, Proc. Amer. Math. Soc. 3
  (1952), 400–406.
-/

public section

open Polynomial

namespace PowerBasis

/-- **Determinant of the power-expansion matrix in a purely inseparable power basis**: if `pb` is a
power basis of `S` over `R` of dimension `pb.dim = p ^ e` in exponential characteristic `p` with
`pb.gen ^ pb.dim = algebraMap R S b`, then the transition matrix from `pb.basis` to the powers
`1, f(pb.gen), …, f(pb.gen) ^ (pb.dim - 1)` has determinant
`f'(pb.gen) ^ (pb.dim * (pb.dim - 1) / 2)` in `S`. -/
theorem det_toMatrix_aeval_pow {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {p e : ℕ} [ExpChar S p] (pb : PowerBasis R S) (hdim : pb.dim = p ^ e)
    {b : R} (hb : algebraMap R S b = pb.gen ^ pb.dim) (f : R[X]) :
    algebraMap R S
        (LinearMap.toMatrix pb.basis pb.basis
          (pb.basis.constr R fun i : Fin pb.dim ↦ aeval pb.gen f ^ (i : ℕ))).det =
      aeval pb.gen f.derivative ^ (pb.dim * (pb.dim - 1) / 2) := by
  nontriviality S
  have : Nontrivial R := (algebraMap R S).domain_nontrivial
  have hmin : pb.minpolyGen = X ^ pb.dim - C b := pb.minpolyGen_eq_X_pow_sub_C hb
  have hmod : X ^ pb.dim - C pb.gen ^ pb.dim = (X - C pb.gen) ^ pb.dim := by
    rw [hdim, sub_pow_expChar_pow]
  have hmat : (algebraMap R S).mapMatrix
      (LinearMap.toMatrix pb.basis pb.basis
        (pb.basis.constr R fun i : Fin pb.dim ↦ aeval pb.gen f ^ (i : ℕ))) =
      Matrix.of fun j i : Fin pb.dim ↦
        (((f.map (algebraMap R S)) ^ (i : ℕ)) %ₘ ((X - C pb.gen) ^ pb.dim)).coeff j := by
    ext j i
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, LinearMap.toMatrix_apply, pb.basis.constr_basis,
      ← map_pow, pb.basis_repr_aeval, hmin, Matrix.of_apply, ← coeff_map,
      Polynomial.map_modByMonic _ (monic_X_pow_sub_C b pb.dim_pos.ne'),
      Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_C, hb, C_pow, hmod]
  rw [RingHom.map_det, hmat, Polynomial.det_coeff_pow_modByMonic_X_sub_C_pow,
    Polynomial.derivative_map, Polynomial.eval_map, aeval_def]

end PowerBasis

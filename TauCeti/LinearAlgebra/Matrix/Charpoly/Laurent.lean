/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-!
# Characteristic polynomials of polynomial matrices over the Laurent polynomials

A polynomial matrix that specialises to the identity at zero and has, over the Laurent polynomials,
the same characteristic polynomial as a constant matrix forces the constant matrix to have the
characteristic polynomial of the identity.

## Main results

* `Matrix.charpoly_eq_charpoly_one_of_map_toLaurent`: the constant matrix has the characteristic
  polynomial `(X - 1) ^ n` of the identity.
-/

public section

namespace Matrix

open Polynomial

/-- If a polynomial matrix specialises to the identity at zero and has the same characteristic
polynomial over the Laurent polynomials as a constant matrix, the constant matrix has the
characteristic polynomial of the identity. -/
theorem charpoly_eq_charpoly_one_of_map_toLaurent {n : Type*} [Fintype n] [DecidableEq n]
    {A : Type*} [CommRing A] (P : Matrix n n (Polynomial A)) (G : Matrix n n A)
    (hzero : P.map (evalRingHom (0 : A)) = 1)
    (hLaurent : (P.map toLaurent).charpoly = (G.map LaurentPolynomial.C).charpoly) :
    G.charpoly = (1 : Matrix n n A).charpoly := by
  have hpoly : P.charpoly = G.charpoly.map C := by
    apply Polynomial.map_injective _ toLaurent_injective
    calc
      P.charpoly.map toLaurent =
          G.charpoly.map LaurentPolynomial.C := by
        simpa only [Matrix.charpoly_map] using hLaurent
      _ = (G.charpoly.map C).map toLaurent := by
        ext n
        simp
  have hzeroCharpoly := congrArg Matrix.charpoly hzero
  rw [Matrix.charpoly_map, hpoly, Polynomial.map_map] at hzeroCharpoly
  calc
    G.charpoly = G.charpoly.map ((evalRingHom (0 : A)).comp C) := by
      ext n
      simp
    _ = (1 : Matrix n n A).charpoly := hzeroCharpoly

end Matrix

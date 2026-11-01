/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Univ
public import Mathlib.Topology.Algebra.MvPolynomial
public import Mathlib.Topology.Instances.Matrix

/-!
# Continuity of characteristic coefficients

Each coefficient of the characteristic polynomial depends continuously on the matrix entries.
This is the coefficient-level interface needed to apply continuity of polynomial roots to
matrix spectra. It does not impose a topology on the space of polynomials.

The proof uses Mathlib's universal characteristic polynomial `Matrix.charpoly.univ`: its
coefficients are multivariate polynomials in the matrix entries.
-/

public section

namespace Matrix

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]
  [TopologicalSpace R] [IsTopologicalRing R]

/-- Every characteristic coefficient is continuous for the entrywise matrix topology. -/
@[continuity, fun_prop]
theorem continuous_charpoly_coeff (k : ℕ) :
    Continuous (fun A : Matrix n n R => A.charpoly.coeff k) := by
  have h : Continuous (fun A : Matrix n n R =>
      MvPolynomial.eval (Function.uncurry A) ((charpoly.univ R n).coeff k)) :=
    (MvPolynomial.continuous_eval (p := (charpoly.univ R n).coeff k)).comp
      (continuous_pi fun ij => continuous_id.matrix_elem ij.1 ij.2)
  have hmatrix (A : Matrix n n R) : of (Function.curry (Function.uncurry A)) = A := by
    ext i j
    rfl
  simpa only [MvPolynomial.eval, charpoly.univ_coeff_eval₂Hom, hmatrix] using h

end Matrix

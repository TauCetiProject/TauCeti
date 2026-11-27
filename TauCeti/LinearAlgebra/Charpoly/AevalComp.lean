/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.Algebra.Polynomial.Div
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

/-!
# The characteristic polynomial of a polynomial in a matrix

For a square matrix `Y` over a commutative ring and a polynomial `q`, the characteristic
polynomial of `Y` divides `χ ∘ q`, where `χ` is the characteristic polynomial of `q(Y)`: in
matrices over `R[X]` the matrix `X - Y` divides `q(X) - q(Y)`, and determinants are
multiplicative. As a consequence, an endomorphism `f` of a finite-dimensional vector space with
`P(f)` nilpotent, for an irreducible monic `P`, has characteristic polynomial a power of `P`.

## Main results

* `Matrix.charpoly_dvd_charpoly_aeval_comp`, `LinearMap.charpoly_dvd_charpoly_aeval_comp`: the
  characteristic polynomial of `Y` divides `(q(Y)).charpoly.comp q`.
* `LinearMap.exists_charpoly_eq_pow_of_isNilpotent_aeval`: if `P(f)` is nilpotent, with `P`
  monic and irreducible, the characteristic polynomial of `f` is a power of `P`.

## References

* Adapted from grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026
  Anthropic PBC): `New.charpoly_dvd_charpoly_aeval_comp` and `New.map_aeval_matrix` in
  `src/Lib/General/LinearAlgebra/MatrixPolynomials.lean`, and
  `New.charpoly_eq_pow_of_isNilpotent` in `src/Lib/LocalGL/Green/CuspidalFunctions.lean`.
-/

public section

open Polynomial

namespace Matrix

variable {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]

/-- Applying a ring map to the entries of `q(Y)` gives the image of `q` at the image of `Y`. -/
private theorem map_aeval {S : Type*} [CommRing S] (ψ : R →+* S) (Y : Matrix n n R) (q : R[X]) :
    (aeval Y q).map ψ = aeval (Y.map ψ) (q.map ψ) := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq => simp [Matrix.map_add, hp, hq]
  | monomial m a => simp [algebraMap_eq_diagonal, Matrix.map_mul, Matrix.map_pow, Pi.algebraMap_def]

/-- The characteristic polynomial of `Y` divides `χ ∘ q`, with `χ` the characteristic polynomial
of `q(Y)`. -/
theorem charpoly_dvd_charpoly_aeval_comp (Y : Matrix n n R) (q : R[X]) :
    Y.charpoly ∣ (aeval Y q).charpoly.comp q := by
  -- In `R[X][X]` the polynomial `C X - X` divides `C q - q.map C`. Evaluate the outer variable at
  -- `Y`: as matrices over `R[X]`, `X - Y` divides `q(X) - q(Y)`; take determinants.
  have h_poly : (C X - X : R[X][X]) ∣ C q - q.map C := by
    simpa [eval_map] using ((q.map C).map C).sub_dvd_eval_sub (C X) X
  have h_mat : charmatrix Y ∣ scalar n q - (aeval Y q).map C := by
    simpa [charmatrix, map_aeval, algebraMap_eq_diagonal, Pi.algebraMap_def] using
      aeval_dvd (x := Y.map C) h_poly
  have h_det : det (scalar n q - (aeval Y q).map C) = (aeval Y q).charpoly.comp q := by
    rw [← eval_charpoly, charpoly_map, eval_map, Polynomial.comp]
  simpa only [coe_detMonoidHom, h_det, ← charpoly.eq_def] using map_dvd detMonoidHom h_mat

end Matrix

namespace LinearMap

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Module.Free R M]
  [Module.Finite R M]

/-- The characteristic polynomial of `f` divides `χ ∘ q`, with `χ` the characteristic polynomial
of `q(f)`. -/
theorem charpoly_dvd_charpoly_aeval_comp (f : Module.End R M) (q : R[X]) :
    f.charpoly ∣ (aeval f q).charpoly.comp q := by
  let b := Module.Free.chooseBasis R M
  have h := (toMatrix b b f).charpoly_dvd_charpoly_aeval_comp q
  have he (g : Module.End R M) : toMatrixAlgEquiv b g = toMatrix b b g := rfl
  have h_aeval : aeval (toMatrix b b f) q = toMatrix b b (aeval f q) := by
    rw [← he, ← he, ← AlgEquiv.coe_toAlgHom, aeval_algHom_apply]
  rwa [charpoly_toMatrix, h_aeval, charpoly_toMatrix] at h

/-- If `P(f)` is nilpotent for a monic irreducible `P`, the characteristic polynomial of `f` is a
power of `P`. -/
theorem exists_charpoly_eq_pow_of_isNilpotent_aeval {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] [Module.Finite K V] (f : Module.End K V) {P : K[X]} (hP : Irreducible P)
    (hP_monic : P.Monic) (h : IsNilpotent (aeval f P)) : ∃ j : ℕ, f.charpoly = P ^ j := by
  -- `χ(P(f)) = X ^ d`, so `charpoly f` divides `P ^ d`; a monic divisor of a prime power is a
  -- power.
  have h_dvd : f.charpoly ∣ P ^ Module.finrank K V := by
    simpa [h.charpoly_eq_X_pow_finrank] using f.charpoly_dvd_charpoly_aeval_comp P
  obtain ⟨j, -, hj⟩ := (dvd_prime_pow hP.prime _).1 h_dvd
  exact ⟨j, eq_of_monic_of_associated f.charpoly_monic (hP_monic.pow j) hj⟩

end LinearMap

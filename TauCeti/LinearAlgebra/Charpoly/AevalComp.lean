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
* `minpoly.not_isUnit_aeval_of_dvd`: a factor `P` of positive degree of the minimal polynomial of
  `x` is not invertible at `x`.

## References

* Adapted from grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026
  Anthropic PBC): `New.charpoly_dvd_charpoly_aeval_comp` in
  `src/Lib/General/LinearAlgebra/MatrixPolynomials.lean` (with Mathlib's
  `Polynomial.map_aeval_eq_aeval_map` in place of `New.map_aeval_matrix`), and
  `New.charpoly_eq_pow_of_isNilpotent` in `src/Lib/LocalGL/Green/CuspidalFunctions.lean`.
-/

public section

open Polynomial

namespace Matrix

variable {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]

/-- The characteristic polynomial of `Y` divides `χ ∘ q`, with `χ` the characteristic polynomial
of `q(Y)`. -/
theorem charpoly_dvd_charpoly_aeval_comp (Y : Matrix n n R) (q : R[X]) :
    Y.charpoly ∣ (aeval Y q).charpoly.comp q := by
  -- In `R[X][X]` the polynomial `C X - X` divides `C q - q.map C`. Evaluate the outer variable at
  -- `Y`: as matrices over `R[X]`, `X - Y` divides `q(X) - q(Y)`; take determinants.
  have h_poly : (C X - X : R[X][X]) ∣ C q - q.map C := by
    simpa [eval_map] using ((q.map C).map C).sub_dvd_eval_sub (C X) X
  have h_map : (aeval Y q).map C = aeval (Y.map C) (q.map C) :=
    map_aeval_eq_aeval_map (ψ := (C : R →+* R[X]).mapMatrix)
      (RingHom.ext fun r ↦ by simp [algebraMap_eq_diagonal, Pi.algebraMap_def]) q Y
  have h_mat : charmatrix Y ∣ scalar n q - (aeval Y q).map C := by
    simpa [charmatrix, h_map, algebraMap_eq_diagonal, Pi.algebraMap_def] using
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
  have he (g : Module.End R M) : toMatrixAlgEquiv b g = toMatrix b b g := by
    ext i j
    rw [toMatrixAlgEquiv_apply, toMatrix_apply]
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

namespace minpoly

/-- If a polynomial `P` of positive degree divides the minimal polynomial of `x`, then `P(x)` is
not invertible. -/
theorem not_isUnit_aeval_of_dvd {k A : Type*} [Field k] [Ring A] [Algebra k A] {x : A}
    (hx : IsIntegral k x) {P : k[X]} (hP : 0 < P.natDegree) (h : P ∣ minpoly k x) :
    ¬IsUnit (Polynomial.aeval x P) := by
  intro hu
  obtain ⟨Q, hQ⟩ := h
  -- Then `Q(x) = 0`, although `Q` has smaller degree than the minimal polynomial.
  have hQ_zero : Polynomial.aeval x Q = 0 := by
    have h_min := minpoly.aeval k x
    rwa [hQ, map_mul, hu.mul_right_eq_zero] at h_min
  have hQ_ne : Q ≠ 0 := by
    rintro rfl
    exact minpoly.ne_zero hx (by simpa using hQ)
  have h_deg := natDegree_le_of_dvd (minpoly.dvd k x hQ_zero) hQ_ne
  rw [hQ, natDegree_mul (ne_zero_of_natDegree_gt hP) hQ_ne] at h_deg
  omega

end minpoly

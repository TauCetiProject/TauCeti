/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Charpoly.ToMatrix

/-!
# The characteristic polynomial of a scalar multiple

Scaling a matrix or an endomorphism by `c` scales the roots of its characteristic polynomial by
`c`. Integrally, without inverting `c`: substituting `c X` for `X` in `χ(c M)` gives
`cⁿ χ(M)`, since `c X - c M = c (X - M)`. When `c` is a unit this determines
`χ(c M) = cⁿ χ(M)(c⁻¹ X)`.

## Main results

* `Matrix.charpoly_smul_comp_C_mul_X`: `χ(c • M)(c X) = cⁿ χ(M)`.
* `LinearMap.charpoly_smul_comp_C_mul_X`: the same for an endomorphism of a finite free module,
  with `n` its rank.
* `LinearMap.charpoly_units_smul`: for a unit `c`, `χ(c • f) = cⁿ χ(f)(c⁻¹ X)`.
-/

public section

open Polynomial

namespace Matrix

variable {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]

/-- **Characteristic polynomial of a scalar multiple**, integrally: substituting `c X` for `X` in
`χ(c • M)` gives `c ^ n * χ(M)`. -/
theorem charpoly_smul_comp_C_mul_X (M : Matrix n n R) (c : R) :
    (c • M).charpoly.comp (C c * X) = C (c ^ Fintype.card n) * M.charpoly := by
  have h : (compRingHom (C c * X)).mapMatrix (c • M).charmatrix = C c • M.charmatrix := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [charmatrix_apply_eq, mul_sub]
    · simp [charmatrix_apply_ne _ _ _ hij]
  rw [charpoly, charpoly, ← coe_compRingHom_apply, RingHom.map_det, h, det_smul, ← C_pow]

end Matrix

namespace LinearMap

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Module.Free R M]
  [Module.Finite R M]

/-- **Characteristic polynomial of a scalar multiple**, integrally: substituting `c X` for `X` in
`χ(c • f)` gives `c ^ n * χ(f)` for `n` the rank. -/
theorem charpoly_smul_comp_C_mul_X (f : Module.End R M) (c : R) :
    (c • f).charpoly.comp (C c * X) = C (c ^ Module.finrank R M) * f.charpoly := by
  nontriviality R
  let b := Module.Free.chooseBasis R M
  rw [← charpoly_toMatrix (c • f) b, ← charpoly_toMatrix f b, map_smul,
    Matrix.charpoly_smul_comp_C_mul_X, Module.finrank_eq_card_chooseBasisIndex]

/-- **Characteristic polynomial of a scalar multiple** by a unit `c`:
`χ(c • f) = cⁿ χ(f)(c⁻¹ X)`, so the roots are scaled by `c`. -/
theorem charpoly_units_smul (f : Module.End R M) (c : Rˣ) :
    ((c : R) • f).charpoly =
      C ((c : R) ^ Module.finrank R M) * f.charpoly.comp (C ((c⁻¹ : Rˣ) : R) * X) := by
  have h := congrArg (fun p : R[X] ↦ p.comp (C ((c⁻¹ : Rˣ) : R) * X))
    (charpoly_smul_comp_C_mul_X f c)
  simp only [Polynomial.comp_assoc, Polynomial.mul_comp, Polynomial.C_comp, Polynomial.X_comp,
    ← mul_assoc, ← Polynomial.C_mul, Units.mul_inv, Polynomial.C_1, one_mul,
    Polynomial.comp_X] at h
  exact h

end LinearMap

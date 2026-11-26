/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Kronecker
public import TauCeti.RingTheory.MvPolynomial.LinearSubst
public import Mathlib.LinearAlgebra.Matrix.MvPolynomial

/-!
# The two-sided action on forms on rectangular matrices

The action of `GL_m × GL_n` on forms in the entries of an `m × n` matrix is
`((g, h) • P)(Z) = P(gᵀ * Z * h)`. This is the polynomial action of the Kronecker
product of `g` and `h` on the variables indexed by pairs. The generic-matrix formula
works over any commutative semiring, including finite fields where pointwise equality would
not determine a polynomial. This is the action on which polynomial Howe duality is stated.

## References

* R. Howe, *Perspectives on invariant theory*, Israel Math. Conf. Proc. 8 (1995), §2.1.
-/

public section

open Matrix MvPolynomial
open scoped Kronecker

namespace TauCeti

variable {R m n : Type*} [CommSemiring R] [Fintype m] [Fintype n]

/-- The polynomial action of a Kronecker product substitutes `Aᵀ * X * B` for the generic
rectangular matrix `X`. -/
theorem polynomialAction_kronecker (A : Matrix m m R) (B : Matrix n n R) :
    polynomialAction (A ⊗ₖ B) =
      aeval (fun p ↦
        (Aᵀ.map C * mvPolynomialX m n R * B.map C : Matrix m n (MvPolynomial (m × n) R))
          p.1 p.2) := by
  refine algHom_ext fun ⟨i, j⟩ ↦ ?_
  simp only [polynomialAction_X, aeval_X, Fintype.sum_prod_type, kronecker_apply, Matrix.mul_apply,
    transpose_apply, Matrix.map_apply, mvPolynomialX_apply, Finset.sum_mul, map_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦ by ac_rfl

variable [DecidableEq m] [DecidableEq n]

/-- The representation of `GL_m × GL_n` on degree-`d` forms in the entries of an `m × n`
matrix, with the transpose convention on the left factor. -/
noncomputable def rectangularHomogeneousMatrixRep (d : ℕ) :
    Representation R (GL m R × GL n R) (homogeneousSubmodule (m × n) R d) :=
  (polynomialRep (m × n) R d).comp Matrix.GeneralLinearGroup.kroneckerHom

/-- On the underlying polynomial the action is the substitution of standard vectors by the
Kronecker product. See `polynomialAction_kronecker` for the generic-matrix formula. -/
@[simp]
theorem coe_rectangularHomogeneousMatrixRep_apply {d : ℕ} (g : GL m R × GL n R)
    (P : homogeneousSubmodule (m × n) R d) :
    (rectangularHomogeneousMatrixRep d g P : MvPolynomial (m × n) R) =
      polynomialAction ((g.1 : Matrix m m R) ⊗ₖ (g.2 : Matrix n n R))
        (P : MvPolynomial (m × n) R) := by
  simp [rectangularHomogeneousMatrixRep]

/-- Evaluation of the transformed form at `Z` is evaluation of the original form at
`gᵀ * Z * h`. -/
theorem eval_rectangularHomogeneousMatrixRep {d : ℕ} (g : GL m R × GL n R)
    (P : homogeneousSubmodule (m × n) R d) (Z : Matrix m n R) :
    eval (Function.uncurry Z) (rectangularHomogeneousMatrixRep d g P) =
      eval (Function.uncurry ((g.1 : Matrix m m R)ᵀ * Z * (g.2 : Matrix n n R))) P := by
  simp only [coe_rectangularHomogeneousMatrixRep_apply, polynomialAction_kronecker,
    ← aeval_eq_eval, ← AlgHom.comp_apply, comp_aeval]
  congr 2
  funext p
  simp [Matrix.mul_apply, Function.uncurry]

end TauCeti

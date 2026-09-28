/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.LinearSubst

/-!
# The action of integral matrices on binary forms

Fix a commutative ring `R` and a natural number `w`. Let `V_w` be the `R`-module of binary forms
of degree `w`, modelled as `homogeneousSubmodule (Fin 2) R w` with `X = X 0` and `Y = X 1`.
Integral `2 × 2` matrices act on it on the right, `(P ∣ M)(X, Y) = P(aX + bY, cX + dY)` for
`M = !![a, b; c, d]`, so that `P ∣ (M * N) = (P ∣ M) ∣ N`. This action is the coefficient module
of both period polynomials and modular symbols of weight `w + 2`.

## Main definitions

* `TauCeti.binaryFormRep R w`: the right action of integral matrices on binary forms of degree
  `w`, as a representation of `(Matrix (Fin 2) (Fin 2) ℤ)ᵐᵒᵖ`.

## Main results

* `TauCeti.binaryFormRep_op_mul_apply`: the action is on the right, `P ∣ (M * N) =
  (P ∣ M) ∣ N`.
* `TauCeti.binaryFormRep_op_neg`, `TauCeti.binaryFormRep_op_scalar`: negated and scalar matrices
  act by `(-1)ʷ` and by the `w`th power of the scalar.
-/

public section

open Matrix MulOpposite MvPolynomial

namespace TauCeti

variable (R : Type*) [CommRing R] (w : ℕ)

/-- The right action `P ↦ P ∣ M` of integral `2 × 2` matrices on binary forms of degree `w`,
`(P ∣ M)(X, Y) = P(aX + bY, cX + dY)` for `M = !![a, b; c, d]`, as a representation of the
opposite matrix monoid. -/
noncomputable def binaryFormRep :
    Representation R (Matrix (Fin 2) (Fin 2) ℤ)ᵐᵒᵖ (homogeneousSubmodule (Fin 2) R w) :=
  (linearSubstRep (Fin 2) R w).comp
    (MonoidHom.op (Int.castRingHom R).mapMatrix.toMonoidHom)

variable {R w}

@[simp]
theorem coe_binaryFormRep_apply (M : Matrix (Fin 2) (Fin 2) ℤ)
    (P : homogeneousSubmodule (Fin 2) R w) :
    (binaryFormRep R w (op M) P : MvPolynomial (Fin 2) R) =
      linearSubst (M.map (Int.cast : ℤ → R)) P := by
  simp [binaryFormRep]

/-- The action is on the right: `P ∣ (M * N) = (P ∣ M) ∣ N`. -/
theorem binaryFormRep_op_mul_apply (M N : Matrix (Fin 2) (Fin 2) ℤ)
    (P : homogeneousSubmodule (Fin 2) R w) :
    binaryFormRep R w (op (M * N)) P = binaryFormRep R w (op N) (binaryFormRep R w (op M) P) := by
  rw [op_mul, map_mul, Module.End.mul_apply]

/-- Negating the matrix multiplies a form of degree `w` by `(-1)ʷ`. -/
theorem binaryFormRep_op_neg (M : Matrix (Fin 2) (Fin 2) ℤ) :
    binaryFormRep R w (op (-M)) = (-1 : R) ^ w • binaryFormRep R w (op M) := by
  refine LinearMap.ext fun P ↦ Subtype.ext ?_
  simp only [coe_binaryFormRep_apply, LinearMap.smul_apply, Submodule.coe_smul]
  rw [Matrix.map_neg _ Int.cast_neg, P.2.linearSubst_neg]

/-- For even `w`, a matrix and its negative act in the same way. -/
theorem binaryFormRep_op_neg_of_even (hw : Even w) (M : Matrix (Fin 2) (Fin 2) ℤ) :
    binaryFormRep R w (op (-M)) = binaryFormRep R w (op M) := by
  rw [binaryFormRep_op_neg, hw.neg_one_pow, one_smul]

/-- An integer scalar matrix acts on degree-`w` binary forms by its `w`th power. -/
@[simp]
theorem binaryFormRep_op_scalar (a : ℤ) :
    binaryFormRep R w (op !![a, 0; 0, a]) =
      (a : R) ^ w • (1 : Module.End R (homogeneousSubmodule (Fin 2) R w)) := by
  have hmat : (!![a, 0; 0, a] : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → R) =
      (a : R) • (1 : Matrix (Fin 2) (Fin 2) R) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.smul_apply]
  apply LinearMap.ext
  intro P
  apply Subtype.ext
  simp [hmat, P.2.linearSubst_smul]

end TauCeti

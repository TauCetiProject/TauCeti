/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
public import TauCeti.LinearAlgebra.Matrix.FixedDetMatrices

/-!
# Integral matrices of fixed determinant acting on the upper half-plane

For `n ≠ 0`, an integral `2 × 2` matrix `A` of determinant `n` acts on the upper half-plane
through its image `FixedDetMatrices.toGLReal hn A` in `GL(2, ℝ)`. For `0 < n` this is the Möbius
transformation `τ ↦ (a τ + b) / (c τ + d)`; for `n < 0` it is that transformation followed by
complex conjugation, `τ ↦ conj ((a τ + b) / (c τ + d))`, as for Mathlib's action of `GL(2, ℝ)`
on the upper half-plane. This file records that left multiplication by `SL(2, ℤ)` on `A`
becomes composition of the actions, and that for `0 < n` the action is holomorphic.

## Main results

* `FixedDetMatrices.toGLReal_smul_smul`: the action of `g • A` is that of `A` followed by `g`.
* `FixedDetMatrices.mdifferentiable_toGLReal_smul`: for `0 < n` the action of `A` is holomorphic.
* `FixedDetMatrices.toGLReal_smul_eq_vadd_smul`: for `0 < n` an upper-triangular representative
  `(a b; 0 d)` acts by `τ ↦ b / d + (a / d) τ`, a positive scaling followed by a real
  translation.
-/

public section

open Matrix UpperHalfPlane
open scoped MatrixGroups Manifold

namespace FixedDetMatrices

variable {n : ℤ}

/-- The action of `g • A` on the upper half-plane is that of `A` followed by that of `g`. -/
theorem toGLReal_smul_smul (hn : n ≠ 0) (g : SL(2, ℤ)) (A : FixedDetMatrix (Fin 2) ℤ n)
    (τ : ℍ) : toGLReal hn (g • A) • τ = g • toGLReal hn A • τ := by
  rw [toGLReal_smul, mul_smul]
  exact (MulAction.compHom_smul_def _ _ _).symm

/-- For `0 < n`, the action of an integral matrix of determinant `n` on the upper half-plane is
holomorphic. -/
theorem mdifferentiable_toGLReal_smul (hn : 0 < n) (A : FixedDetMatrix (Fin 2) ℤ n) :
    MDiff fun τ : ℍ ↦ toGLReal hn.ne' A • τ :=
  mdifferentiable_smul (by rw [det_toGLReal]; exact_mod_cast hn)

/-- The ratio `a / d` of the diagonal entries of a representative `(a b; 0 d)` of positive
determinant, as a positive real number. -/
noncomputable def repsScale (hn : 0 < n) {A : FixedDetMatrix (Fin 2) ℤ n} (hA : A ∈ reps n) :
    {x : ℝ // 0 < x} :=
  ⟨A.val 0 0 / A.val 1 1, div_pos (by exact_mod_cast hA.2.1)
    (by exact_mod_cast pos_val_one_one_of_mem_reps hn hA)⟩

/-- The value of `repsScale` is `a / d`. -/
@[simp]
theorem coe_repsScale (hn : 0 < n) {A : FixedDetMatrix (Fin 2) ℤ n} (hA : A ∈ reps n) :
    (repsScale hn hA : ℝ) = A.val 0 0 / A.val 1 1 :=
  (rfl)

/-- For `0 < n`, an upper-triangular representative `(a b; 0 d)` sends `τ` to `b / d + (a / d) τ`:
it acts by the positive scaling `repsScale` followed by a real translation. -/
theorem toGLReal_smul_eq_vadd_smul (hn : 0 < n) {A : FixedDetMatrix (Fin 2) ℤ n}
    (hA : A ∈ reps n) (τ : ℍ) :
    toGLReal hn.ne' A • τ = ((A.val 0 1 / A.val 1 1 : ℝ)) +ᵥ (repsScale hn hA • τ) := by
  have hd : ((A.val 1 1 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (pos_val_one_one_of_mem_reps hn hA).ne'
  have hdet : 0 < (toGLReal hn.ne' A).det.val := by
    rw [det_toGLReal]
    exact_mod_cast hn
  ext
  rw [coe_smul_of_det_pos hdet, coe_vadd, coe_pos_real_smul, coe_repsScale]
  simp only [num, denom, toGLReal_apply, hA.1, Int.cast_zero, Complex.ofReal_zero, zero_mul,
    zero_add, Complex.real_smul, Complex.ofReal_div, Complex.ofReal_intCast]
  push_cast at hd ⊢
  field_simp
  ring

end FixedDetMatrices

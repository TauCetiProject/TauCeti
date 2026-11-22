/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# Sending every variable to the same single variable

The `R`-algebra map `R[Xᵢ : i ∈ σ] → R[X]` sending every variable `Xᵢ` to `X` is
`MvPolynomial.aeval fun _ => Polynomial.X`. It is surjective as soon as `σ` is nonempty, and
following it by `X ↦ X_c` is the renaming that sends every variable to `X_c`. Scaling the
variables, `Tᵢ ↦ aᵢ X`, the coefficient of `X` in the image of `p * Tᵢ` is
`aᵢ * constantCoeff p`.

## Main results

* `MvPolynomial.rename_const_eq_aeval_aeval_X`: renaming every variable to `X_c` factors
  through `R[X]`.
* `MvPolynomial.aeval_const_X_surjective`: sending every variable to `X` is surjective
  onto `R[X]` when there is at least one variable.
* `MvPolynomial.eval_aeval_const_X`: evaluating `aeval (Function.const σ Polynomial.X) p` at `w`
  equals evaluating `p` at the diagonal point `Function.const σ w`.
* `MvPolynomial.coeff_one_aeval_C_mul_X_mul_X`: the coefficient of `X` after substituting
  `Tᵢ ↦ aᵢ X` in `p * Tᵢ`.
-/

public section

namespace MvPolynomial

variable {σ R : Type*} [CommSemiring R]

/-- Renaming every variable to `X_c` is the map sending every variable to `X`, followed by
`X ↦ X_c`. -/
theorem rename_const_eq_aeval_aeval_X (c : σ) (p : MvPolynomial σ R) :
    rename (fun _ => c) p =
      Polynomial.aeval (X c) (aeval (fun _ => (Polynomial.X : Polynomial R)) p) := by
  rw [comp_aeval_apply, rename_eq_aeval]
  simp [Function.comp_def]

variable (σ R) in
/-- Sending every variable to `X` is surjective onto `R[X]` when there is at least one
variable. -/
theorem aeval_const_X_surjective [Nonempty σ] :
    Function.Surjective (aeval (R := R) fun _ : σ => (Polynomial.X : Polynomial R)) := fun q =>
  let c : σ := Classical.arbitrary σ
  ⟨Polynomial.aeval (X c) q, by
    rw [← Polynomial.aeval_algHom_apply, aeval_X, Polynomial.aeval_X_left_apply]⟩

/-- Evaluating the diagonal specialization `aeval (Function.const σ Polynomial.X) p` at `w` equals
evaluating `p` at the constant tuple `Function.const σ w`. -/
@[simp]
theorem eval_aeval_const_X (w : R) (p : MvPolynomial σ R) :
    (aeval (Function.const σ (Polynomial.X : Polynomial R)) p).eval w =
      eval (Function.const σ w) p := by
  rw [← Polynomial.coe_aeval_eq_eval, comp_aeval_apply]
  simp [← Function.const_def]

/-- For the substitution `Tᵢ ↦ aᵢ X` of `R[Tᵢ : i ∈ σ]` into `R[X]`, the coefficient of `X` in
the image of `p * Tᵢ` is `aᵢ` times the constant coefficient of `p`. -/
theorem coeff_one_aeval_C_mul_X_mul_X (a : σ → R) (p : MvPolynomial σ R) (i : σ) :
    (aeval (fun j ↦ Polynomial.C (a j) * Polynomial.X) (p * X i)).coeff 1 =
      constantCoeff p * a i := by
  -- the constant coefficient of the image of `p` is `p` evaluated at `0`
  have h0 : (aeval (fun j ↦ Polynomial.C (a j) * Polynomial.X) p).coeff 0 = constantCoeff p := by
    rw [Polynomial.coeff_zero_eq_eval_zero, ← Polynomial.coe_aeval_eq_eval, comp_aeval_apply]
    simp [← eval_zero']
  -- `X i ↦ C (a i) * X`, and the coefficient of `X` in `q * C (a i) * X` is `q.coeff 0 * a i`
  simp [← mul_assoc, h0]

end MvPolynomial

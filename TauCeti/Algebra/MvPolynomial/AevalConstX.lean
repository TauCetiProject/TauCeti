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
  rw [← AlgHom.comp_apply]
  congr 1
  exact algHom_ext fun i => by simp

variable (σ R) in
/-- Sending every variable to `X` is surjective onto `R[X]` when there is at least one
variable. -/
theorem aeval_const_X_surjective [Nonempty σ] :
    Function.Surjective (aeval (R := R) fun _ : σ => (Polynomial.X : Polynomial R)) := fun q =>
  let c : σ := Classical.arbitrary σ
  ⟨Polynomial.aeval (X c) q, by
    rw [← Polynomial.aeval_algHom_apply, aeval_X, Polynomial.aeval_X_left_apply]⟩

/-- For the substitution `Tᵢ ↦ aᵢ X` of `R[Tᵢ : i ∈ σ]` into `R[X]`, the coefficient of `X` in
the image of `p * Tᵢ` is `aᵢ` times the constant coefficient of `p`. -/
theorem coeff_one_aeval_C_mul_X_mul_X (a : σ → R) (p : MvPolynomial σ R) (i : σ) :
    (aeval (fun j ↦ Polynomial.C (a j) * Polynomial.X) (p * X i)).coeff 1 =
      constantCoeff p * a i := by
  have hconst : (Polynomial.evalRingHom 0).comp
      (aeval (R := R) fun j ↦ Polynomial.C (a j) * Polynomial.X).toRingHom = constantCoeff :=
    ringHom_ext (by simp) (by simp)
  rw [map_mul, aeval_X, ← mul_assoc, Polynomial.coeff_mul_X, Polynomial.coeff_mul_C,
    Polynomial.coeff_zero_eq_eval_zero, ← Polynomial.coe_evalRingHom]
  exact congr($hconst p * a i)

end MvPolynomial

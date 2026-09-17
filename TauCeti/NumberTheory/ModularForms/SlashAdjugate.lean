/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ModularForms.SlashActions
public import TauCeti.Analysis.Complex.UpperHalfPlane.MoebiusAction
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Adjugate

/-!
# Slashing by a scalar matrix and by the main involution

The classical adjoint theory of the Hecke operators is written with the **main involution**
`α^ι = (det α) · α⁻¹` rather than with `α⁻¹`, because `α ↦ α^ι` preserves the integral matrices
and so acts on the Hecke cosets, which `α ↦ α⁻¹` does not. This file records what the weight-`k`
slash does to it. On `GL(2, R)` the main involution is `Matrix.adjugate`, so
`TauCeti.adjugateGL` is the map in question.

The two statements are the scalar case and the general one:

```text
f ∣[k] (u · I) = u ^ (k - 2) • f            f ∣[k] α^ι = (det α) ^ (k - 2) • (f ∣[k] α⁻¹).
```

Neither needs a determinant sign condition. The slash weights by `|det|`, and the determinant
of `u · I` is `u ^ 2 ≥ 0`; the scalar `u ^ (k - 2)` is real, so the conjugation `σ` that the
slash applies on the negative-determinant branch fixes it.

## Main results

* `ModularForm.slash_scalar`: slashing by `u · I` is multiplication by `u ^ (k - 2)`.
* `Matrix.GeneralLinearGroup.adjugateGL_eq_scalar_mul_inv` (in `Adjugate.lean`, beside
  `adjugateGL`): `α^ι = (det α · I) * α⁻¹`.
* `ModularForm.slash_adjugateGL`: the slash by the main involution, in terms of the slash by
  the inverse.
-/

public section

namespace ModularForm

open UpperHalfPlane Matrix TauCeti

/-- **Slashing by a scalar matrix is multiplication by `u ^ (k - 2)`.** The determinant of
`u · I` is `u ^ 2`, contributing `u ^ (2 * (k - 1))`, and the denominator is `u`, contributing
`u ^ (-k)`; the two combine to `u ^ (k - 2)`. No sign condition on `u`: the determinant is a
square, so the absolute value in the slash is inert. -/
@[simp]
theorem slash_scalar (k : ℤ) (u : ℝˣ) (f : ℍ → ℂ) :
    f ∣[k] (Matrix.GeneralLinearGroup.scalar (Fin 2) u) = ((u : ℝ) : ℂ) ^ (k - 2) • f := by
  have hu : ((u : ℝ) : ℂ) ≠ 0 := by exact_mod_cast u.ne_zero
  have hdet : ((Matrix.GeneralLinearGroup.scalar (Fin 2) u) :
      Matrix (Fin 2) (Fin 2) ℝ).det = (u : ℝ) ^ 2 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.det_scalar]
    simp [pow_succ]
  have hpos : (0 : ℝ) < ((Matrix.GeneralLinearGroup.scalar (Fin 2) u) :
      Matrix (Fin 2) (Fin 2) ℝ).det := by
    have hu0 : (u : ℝ) ≠ 0 := u.ne_zero
    rw [hdet]
    positivity
  ext τ
  rw [slash_apply, glScalar_smul, denom_scalar, UpperHalfPlane.σ_eq_refl_of_det_pos hpos,
    Matrix.GeneralLinearGroup.val_det_apply, hdet, abs_of_nonneg (sq_nonneg _)]
  have hcombine : (((u : ℝ) ^ 2 : ℝ) : ℂ) ^ (k - 1) * ((u : ℝ) : ℂ) ^ (-k) =
      ((u : ℝ) : ℂ) ^ (k - 2) := by
    push_cast
    rw [← zpow_natCast (((u : ℝ) : ℂ)) 2, ← zpow_mul, ← zpow_add₀ hu]
    ring_nf
  simp only [ContinuousAlgEquiv.refl_apply, Pi.smul_apply, smul_eq_mul, mul_assoc, hcombine]
  ring

/-- **The slash by the main involution.** `f ∣[k] α^ι = (det α) ^ (k - 2) • (f ∣[k] α⁻¹)`: the
involution and the inverse differ by the scalar `det α`, which slashes by `slash_scalar`.

This is the bridge between the two ways of writing the adjoint theory — the change-of-variables
form, which produces `α⁻¹` and a determinant factor, and the classical form, which uses `α^ι` and
carries no factor because the involution has absorbed it.

Adapted from AINTLIB (github.com/CBirkbeck/AINTLIB @ `6d87d596a537`, Apache-2.0),
`projects/LeanModularForms/LeanModularForms/HeckeRIngs/GL2/AdjointTheory.lean`, whose
`peterssonAdj` (:322) is this involution. -/
@[simp]
theorem slash_adjugateGL (k : ℤ) (g : GL (Fin 2) ℝ) (f : ℍ → ℂ) :
    f ∣[k] adjugateGL g =
      (((g : Matrix (Fin 2) (Fin 2) ℝ).det : ℝ) : ℂ) ^ (k - 2) • (f ∣[k] g⁻¹) := by
  rw [Matrix.GeneralLinearGroup.adjugateGL_eq_scalar_mul_inv, SlashAction.slash_mul,
    slash_scalar,
    Matrix.GeneralLinearGroup.val_det_apply, ← Complex.ofReal_zpow, smul_slash, σ_ofReal,
    Complex.ofReal_zpow]

end ModularForm

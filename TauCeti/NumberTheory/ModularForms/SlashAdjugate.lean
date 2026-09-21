/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.Basic
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Adjugate

/-!
# Slashing by the main involution

The classical adjoint theory of the Hecke operators is written with the **main involution**
`α^ι = (det α) · α⁻¹` rather than with `α⁻¹`, because `α ↦ α^ι` preserves the integral matrices
and so acts on the Hecke cosets, which `α ↦ α⁻¹` does not. This file records what the weight-`k`
slash does to it. On `GL(2, R)` the main involution is `Matrix.adjugate`, so
`TauCeti.adjugateGL` is the map in question:

```text
f ∣[k] α^ι = (det α) ^ (k - 2) • (f ∣[k] α⁻¹).
```

The proof reduces to the scalar case `f ∣[k] (u · I) = u ^ (k - 2) • f`, which is
`ModularForm.slash_scalar` from `TauCeti.NumberTheory.ModularForms.Basic`. No determinant sign
condition is needed: the scalar `(det α) ^ (k - 2)` is real, so the conjugation `σ` that the slash
applies on the negative-determinant branch fixes it.

## Main results

* `ModularForm.slash_adjugateGL`: the slash by the main involution, in terms of the slash by
  the inverse.

The factorization `α^ι = (det α · I) * α⁻¹` it uses is
`Matrix.GeneralLinearGroup.adjugateGL_eq_scalar_mul_inv`, in `Adjugate.lean` beside
`adjugateGL`.
-/

public section

namespace ModularForm

open UpperHalfPlane Matrix TauCeti

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

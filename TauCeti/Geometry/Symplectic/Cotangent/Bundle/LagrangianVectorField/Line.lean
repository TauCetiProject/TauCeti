/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.LagrangianVectorField.Potential
import TauCeti.Analysis.Calculus.SecondDerivative

/-!
# Lagrangian vector fields on the line

On the configuration space `Q = ℝ`, tangent vectors are pairs `(q, v)` of a position and a
velocity. This file works out the Lagrangian vector field `X_E`, the Hamiltonian vector field of
the energy `E_L` for the Cartan two-form `ω_L` with the convention `ι_(X_E) ω_L = dE_L`, for a
particle in a potential.

**A particle in a potential.** For `L(q, v) = (m / 2) v² - V(q)` with a mass `m ≠ 0`, the energy is
`E_L = (m / 2) v² + V(q)`, and the Lagrangian vector field is

`X_E(q, v) = (v, -V'(q) / m)`

(`TauCeti.hamiltonianVectorField_lagrangianEnergy_mul_sq_sub`): the field is second order, and it
is Newton's equation `m q'' = -V'(q)` written as a first-order system. This is the case
`f(v) = (m / 2) v²` of the Lagrangian vector field `(v, -D²f(v)⁻¹ DV(q))` of `f(v) - V(q)`
(`TauCeti.hamiltonianVectorField_lagrangianEnergy_comp_snd_sub`). The sign convention matters:
the opposite convention `ι_X ω_L = -dE_L` gives the field `(-v, V'(q) / m)`
(`TauCeti.hamiltonianVectorField_neg_lagrangianEnergy_mul_sq_sub`), whose base component is `-v`,
so it is not second order at any `v ≠ 0`
(`TauCeti.mfderiv_proj_hamiltonianVectorField_neg_lagrangianEnergy_mul_sq_sub_ne`).

The other check on the line, that `L(q, v) = v` is not regular and that the Hamiltonian vector
field of its energy is not second order, is the case `α = dq` of the Lagrangian of a one-form
(`TauCeti.snd_eq_oneFormLagrangian_mextDerivₗ_id`, `TauCeti.cartanTwoForm_snd_eq_zero`,
`TauCeti.mfderiv_proj_hamiltonianVectorField_lagrangianEnergy_snd_eq_zero`).

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Sections 12 and 15.
-/

public section

noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace TauCeti

/-! ### A particle in a potential -/

section Potential

variable {m : ℝ} {V : ℝ → ℝ}

/- The velocity `v.snd` lies in `TangentSpace 𝓘(ℝ, ℝ) v.proj`, which is `ℝ` but carries no power
instance, so the kinetic energy `(m / 2) v²` below names the power of `ℝ` explicitly. -/

/-- The second derivative of the kinetic energy `(m / 2) v²` sends `a` to the linear form
`b ↦ m a b`, so for `m ≠ 0` its inverse sends the linear form `φ` to `φ(1) / m`. -/
private theorem inverse_fderiv_fderiv_mul_sq (hm : m ≠ 0) (w : ℝ) (φ : ℝ →L[ℝ] ℝ) :
    (fderiv ℝ (fderiv ℝ fun v : ℝ ↦ m / 2 * v ^ 2) w).inverse φ = φ 1 / m := by
  have hD : ∀ a b, fderiv ℝ (fderiv ℝ fun v : ℝ ↦ m / 2 * v ^ 2) w a b = m * a * b := fun a b ↦ by
    rw [fderiv_fderiv_apply_eq_smul_iteratedDeriv]
    simp only [smul_eq_mul]
    -- The second derivative of `(m / 2) v²` is `m`.
    simp
    ring
  have hinv : (fderiv ℝ (fderiv ℝ fun v : ℝ ↦ m / 2 * v ^ 2) w).IsInvertible :=
    isInvertible_fderiv_fderiv_iff_iteratedDeriv_two_ne_zero.2 (by simpa using hm)
  rw [hinv.inverse_apply_eq]
  refine ContinuousLinearMap.ext_ring ?_
  rw [hD]
  field_simp

/-- **The Lagrangian vector field of a particle in a potential.** For the Lagrangian
`L(q, v) = (m / 2) v² - V(q)` on the line, with `m ≠ 0`, the Lagrangian vector field is
`(q, v) ↦ (v, -V'(q) / m)`, Newton's equation `m q'' = -V'(q)` written as a first-order
system. -/
theorem hamiltonianVectorField_lagrangianEnergy_mul_sq_sub (hm : m ≠ 0)
    (hL : ContMDiff 𝓘(ℝ, ℝ).tangent 𝓘(ℝ, ℝ) ∞
      fun v : TangentBundle 𝓘(ℝ, ℝ) ℝ ↦ m / 2 * @HPow.hPow ℝ ℕ ℝ _ v.snd 2 - V v.proj)
    (v : TangentBundle 𝓘(ℝ, ℝ) ℝ) :
    (cartanTwoForm _ hL).hamiltonianVectorField
        (lagrangianEnergy fun v : TangentBundle 𝓘(ℝ, ℝ) ℝ ↦
          m / 2 * @HPow.hPow ℝ ℕ ℝ _ v.snd 2 - V v.proj) v =
      ((v.snd, -deriv V v.proj / m) : TangentSpace 𝓘(ℝ, ℝ).tangent v) := by
  have h : -(fderiv ℝ (fderiv ℝ fun w : ℝ ↦ m / 2 * w ^ 2) v.snd).inverse (fderiv ℝ V v.proj) =
      -deriv V v.proj / m :=
    (congrArg Neg.neg (inverse_fderiv_fderiv_mul_sq hm v.snd _)).trans
      (by rw [fderiv_apply_one_eq_deriv, neg_div])
  rw [hamiltonianVectorField_lagrangianEnergy_comp_snd_sub (f := fun w : ℝ ↦ m / 2 * w ^ 2) hL
    (fun w ↦ isInvertible_fderiv_fderiv_iff_iteratedDeriv_two_ne_zero.2 (by simpa using hm)) v, h]

/-- **The opposite sign convention.** For `L(q, v) = (m / 2) v² - V(q)` with `m ≠ 0`, the vector
field `X` with `ι_X ω_L = -dE_L` is `(q, v) ↦ (-v, V'(q) / m)`. -/
theorem hamiltonianVectorField_neg_lagrangianEnergy_mul_sq_sub (hm : m ≠ 0)
    (hL : ContMDiff 𝓘(ℝ, ℝ).tangent 𝓘(ℝ, ℝ) ∞
      fun v : TangentBundle 𝓘(ℝ, ℝ) ℝ ↦ m / 2 * @HPow.hPow ℝ ℕ ℝ _ v.snd 2 - V v.proj)
    (v : TangentBundle 𝓘(ℝ, ℝ) ℝ) :
    (cartanTwoForm _ hL).hamiltonianVectorField
        (-lagrangianEnergy fun v : TangentBundle 𝓘(ℝ, ℝ) ℝ ↦
          m / 2 * @HPow.hPow ℝ ℕ ℝ _ v.snd 2 - V v.proj) v =
      ((-v.snd, deriv V v.proj / m) : TangentSpace 𝓘(ℝ, ℝ).tangent v) := by
  rw [SmoothTwoForm.hamiltonianVectorField_neg,
    hamiltonianVectorField_lagrangianEnergy_mul_sq_sub hm hL]
  have h : -(-deriv V v.proj / m) = deriv V v.proj / m := by ring
  exact Prod.ext rfl h

/-- **The opposite sign convention is not second order.** For `L(q, v) = (m / 2) v² - V(q)` with
`m ≠ 0`, the vector field `X` with `ι_X ω_L = -dE_L` has base component `-v ≠ v` at every
`v ≠ 0`. -/
theorem mfderiv_proj_hamiltonianVectorField_neg_lagrangianEnergy_mul_sq_sub_ne (hm : m ≠ 0)
    (hL : ContMDiff 𝓘(ℝ, ℝ).tangent 𝓘(ℝ, ℝ) ∞
      fun v : TangentBundle 𝓘(ℝ, ℝ) ℝ ↦ m / 2 * @HPow.hPow ℝ ℕ ℝ _ v.snd 2 - V v.proj)
    {v : TangentBundle 𝓘(ℝ, ℝ) ℝ} (hv : v.snd ≠ 0) :
    mfderiv 𝓘(ℝ, ℝ).tangent 𝓘(ℝ, ℝ) (π ℝ (TangentSpace 𝓘(ℝ, ℝ))) v
      ((cartanTwoForm _ hL).hamiltonianVectorField
        (-lagrangianEnergy fun v : TangentBundle 𝓘(ℝ, ℝ) ℝ ↦
          m / 2 * @HPow.hPow ℝ ℕ ℝ _ v.snd 2 - V v.proj) v) ≠
      v.snd := by
  rw [hamiltonianVectorField_neg_lagrangianEnergy_mul_sq_sub hm hL, Bundle.mfderiv_proj]
  -- The base component is `-v`, and `-v = v` forces `v = 0`.
  exact fun h ↦ hv ((CharZero.neg_eq_self_iff (R := ℝ)).1 h)

end Potential

end TauCeti

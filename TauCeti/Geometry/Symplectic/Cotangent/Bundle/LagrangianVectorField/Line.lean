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
the energy `E_L` for the Cartan two-form `ω_L` with the convention `ι_(X_E) ω_L = dE_L`, for two
Lagrangians that test the hypotheses of the general theory.

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

**A Lagrangian that is not regular.** For `L(q, v) = v` the Legendre map is `(q, v) ↦ (q, dq)`,
so the Cartan one-form is `dq` and the Cartan two-form vanishes
(`TauCeti.eval₂_cartanTwoForm_snd`); the fibre Hessian is zero, so `L` is not regular
(`TauCeti.not_isRegularLagrangian_snd`). The energy `v - v` is zero, and its Hamiltonian vector
field is `0` (`TauCeti.hamiltonianVectorField_lagrangianEnergy_snd`), whose base component is not
`v` when `v ≠ 0`. Every vector field is a Hamiltonian vector field of the energy
(`TauCeti.isHamiltonianVectorField_lagrangianEnergy_snd`). So the regularity hypothesis of the
second-order property `TauCeti.IsRegularLagrangian.mfderiv_proj_eq_snd_of_isHamiltonianVectorField`
cannot be removed.

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

/-! ### A Lagrangian that is not regular -/

/-- **`L(q, v) = v` is not regular**: its fibre Hessian, the second derivative of `v ↦ v`,
vanishes. -/
theorem not_isRegularLagrangian_snd :
    ¬IsRegularLagrangian fun v : TangentBundle 𝓘(ℝ, ℝ) ℝ ↦ v.snd := by
  intro h
  have h0 := (isRegularLagrangian_comp_snd_iff fun x : ℝ ↦ x).1 h 0
  rw [isInvertible_fderiv_fderiv_iff_iteratedDeriv_two_ne_zero] at h0
  simp [iteratedDeriv_succ] at h0

/-- The energy `Df(v)(v) - f(v)` of `L(q, v) = v` is `v - v = 0`. -/
@[simp]
theorem lagrangianEnergy_snd :
    lagrangianEnergy (fun v : TangentBundle 𝓘(ℝ, ℝ) ℝ ↦ v.snd) = 0 := by
  funext v
  rw [lagrangianEnergy_comp_snd fun x : ℝ ↦ x]
  -- The derivative of `x ↦ x` is the identity, so the energy is `v - v`.
  have h : ∀ w : ℝ, fderiv ℝ (fun x : ℝ ↦ x) w w - w = 0 := fun w ↦ by simp
  exact h v.snd

/-- **The Cartan two-form of `L(q, v) = v` vanishes**: the Cartan one-form is `dq`, which is
closed. -/
theorem eval₂_cartanTwoForm_snd
    (hL : ContMDiff 𝓘(ℝ, ℝ).tangent 𝓘(ℝ, ℝ) ∞ fun v : TangentBundle 𝓘(ℝ, ℝ) ℝ ↦ v.snd)
    (v : TangentBundle 𝓘(ℝ, ℝ) ℝ) (X W : TangentSpace 𝓘(ℝ, ℝ).tangent v) :
    SmoothBundleForm.eval₂ (cartanTwoForm _ hL) v X W = 0 := by
  -- The derivative of `x ↦ x` is constant, so its second derivative vanishes.
  have h0 : fderiv ℝ (fderiv ℝ fun x : ℝ ↦ x) = 0 := by
    have h1 : (fderiv ℝ fun x : ℝ ↦ x) = fun _ ↦ ContinuousLinearMap.id ℝ ℝ :=
      funext fun _ ↦ fderiv_fun_id
    funext w
    rw [h1, fderiv_const_apply]
    rfl
  rw [eval₂_cartanTwoForm_comp_snd (f := fun x : ℝ ↦ x) hL, h0]
  -- Both terms evaluate the zero bilinear form.
  exact sub_self (0 : ℝ)

/-- **Every vector field is Lagrangian for `L(q, v) = v`**: both the Cartan two-form and the
differential of the energy vanish. In particular the Lagrangian vector field need not be second
order without regularity. -/
theorem isHamiltonianVectorField_lagrangianEnergy_snd
    (hL : ContMDiff 𝓘(ℝ, ℝ).tangent 𝓘(ℝ, ℝ) ∞ fun v : TangentBundle 𝓘(ℝ, ℝ) ℝ ↦ v.snd)
    (X : (v : TangentBundle 𝓘(ℝ, ℝ) ℝ) → TangentSpace 𝓘(ℝ, ℝ).tangent v) :
    (cartanTwoForm _ hL).IsHamiltonianVectorField
      (lagrangianEnergy fun v : TangentBundle 𝓘(ℝ, ℝ) ℝ ↦ v.snd) X :=
  SmoothTwoForm.isHamiltonianVectorField_iff.2 fun v W ↦ by
    rw [eval₂_cartanTwoForm_snd, lagrangianEnergy_snd]
    exact (DFunLike.congr_fun (mvfderiv_zero (I := 𝓘(ℝ, ℝ).tangent) (x := v)) W).symm

/-- **The Hamiltonian vector field of the energy of `L(q, v) = v` is zero**, so its base component
is `0`, not `v`, at every `v ≠ 0`. -/
theorem hamiltonianVectorField_lagrangianEnergy_snd
    (hL : ContMDiff 𝓘(ℝ, ℝ).tangent 𝓘(ℝ, ℝ) ∞ fun v : TangentBundle 𝓘(ℝ, ℝ) ℝ ↦ v.snd) :
    (cartanTwoForm _ hL).hamiltonianVectorField
      (lagrangianEnergy fun v : TangentBundle 𝓘(ℝ, ℝ) ℝ ↦ v.snd) = 0 := by
  rw [lagrangianEnergy_snd]
  exact SmoothTwoForm.hamiltonianVectorField_const _ 0

end TauCeti

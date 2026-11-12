/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Legendre
public import TauCeti.Geometry.Symplectic.Hamiltonian.Manifold
import TauCeti.Geometry.Manifold.VectorBundle.Submersion

/-!
# The Lagrangian vector field is second order

Let `L : TM → ℝ` be a smooth Lagrangian on a manifold `M`, with Legendre map `FL : TM → T*M`,
energy `E_L(v) = FL(v)(v) - L(v)` and Cartan two-form `ω_L = FL^*ω`, the pullback of the canonical
symplectic form of the cotangent bundle (`TauCeti.cartanTwoForm`). The **Lagrangian vector field**
`X_E` (`TauCeti.lagrangianVectorField`) is the Hamiltonian vector field of `E_L` for `ω_L`, in the
convention `ι_(X_E) ω_L = dE_L`. When `L` is regular on a finite-dimensional boundaryless
manifold, `ω_L` is symplectic, so `X_E` is the unique vector field on `TM` with this property
(`TauCeti.IsRegularLagrangian.isHamiltonianVectorField_iff_eq_lagrangianVectorField`).

This file proves that for a regular Lagrangian on a finite-dimensional boundaryless manifold the
Lagrangian vector field is **second order**: its base component at a tangent vector `v` is `v`
itself,

`dπ (X_E(v)) = v`

(`TauCeti.IsRegularLagrangian.mfderiv_proj_lagrangianVectorField`). The proof pairs Hamilton's
equation with vertical vectors. Let `w` be a tangent vector at the base point `x` of `v`, and let
`w^v = (0, w)` be the velocity at `r = 0` of the line `r ↦ v + r w` in the fibre `T_x M`. Along
this line the energy is `FL(v + r w)(v + r w) - L(v + r w)`, so `dE_L(w^v) = Hess_v(w, v)`, where
`Hess_v` is the fibre Hessian of `L` at `v` (`TauCeti.mfderiv_lagrangianEnergy_apply_vertical`).
The differential of `FL` sends `w^v` to the vertical covector `Hess_v(w, ·)` and keeps base
components, so the chart formula of the canonical form gives
`ω_L(ξ, w^v) = Hess_v(w, dπ ξ)` (`TauCeti.eval₂_cartanTwoForm_apply_vertical`). Hamilton's
equation thus says `Hess_v(w, dπ X_E(v)) = Hess_v(w, v)` for every `w`. The fibre Hessian is
symmetric (`TauCeti.fiberHessian_apply_comm`) and invertible by regularity, hence `dπ X_E(v) = v`.

Consequently the integral curves of `X_E` are velocity curves: if `γ` is a curve in `TM` with
velocity `X_E(γ t)` at time `t`, then the base curve `π ∘ γ` has velocity `γ t` at `t`
(`TauCeti.IsRegularLagrangian.hasMFDerivAt_proj_comp`), since the projection of any curve in `TM`
has velocity the base component of its velocity (`Bundle.hasMFDerivAt_proj_comp`). This is the
intrinsic form of the first half of the Euler–Lagrange system, `q' = v`. The regularity hypothesis
cannot be dropped: for the Lagrangian `L(q, v) = v` on `ℝ` the energy vanishes, so the Hamiltonian
vector field of `E_L` is zero, which is not second order.

## Main definitions

* `TauCeti.lagrangianVectorField L hL`: the Hamiltonian vector field `X_E` of the energy for the
  Cartan two-form.

## Main results

* `TauCeti.IsRegularLagrangian.isHamiltonianVectorField_lagrangianVectorField`: for a regular
  Lagrangian, `ι_(X_E) ω_L = dE_L`.
* `TauCeti.IsRegularLagrangian.mfderiv_proj_lagrangianVectorField`: `dπ (X_E(v)) = v`.
* `TauCeti.IsRegularLagrangian.hasMFDerivAt_proj_comp`,
  `TauCeti.IsRegularLagrangian.hasMFDerivAt_proj_comp_of_isMIntegralCurve`: an integral curve of
  `X_E` is the velocity curve of its projection to `M`.

## References

* R. Abraham, J. E. Marsden, *Foundations of Mechanics*, 2nd ed., Benjamin/Cummings, 1978,
  Section 3.5 (the Lagrangian vector field of a regular Lagrangian is a second-order equation).
* J. E. Marsden, T. S. Ratiu, *Introduction to Mechanics and Symmetry*, 2nd ed., Texts in Applied
  Mathematics 17, Springer, 1999, Chapter 7.
-/

public section

noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace TauCeti

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

/-- The **Lagrangian vector field** `X_E` of a smooth Lagrangian `L : TM → ℝ`: the Hamiltonian
vector field of the energy `E_L` for the Cartan two-form `ω_L = FL^*ω`, in the convention
`ι_(X_E) ω_L = dE_L`. When `L` is regular on a finite-dimensional boundaryless manifold, it is the
unique vector field satisfying this equation
(`TauCeti.IsRegularLagrangian.isHamiltonianVectorField_iff_eq_lagrangianVectorField`). -/
def lagrangianVectorField (L : TangentBundle I M → ℝ) (hL : ContMDiff I.tangent 𝓘(ℝ, ℝ) ∞ L)
    (v : TangentBundle I M) : TangentSpace I.tangent v :=
  (cartanTwoForm L hL).hamiltonianVectorField (lagrangianEnergy L) v

/-- The Lagrangian vector field is the Hamiltonian vector field of the energy for the Cartan
two-form. -/
theorem lagrangianVectorField_def (L : TangentBundle I M → ℝ)
    (hL : ContMDiff I.tangent 𝓘(ℝ, ℝ) ∞ L) :
    lagrangianVectorField L hL = (cartanTwoForm L hL).hamiltonianVectorField (lagrangianEnergy L) :=
  (rfl)

variable [FiniteDimensional ℝ E] [BoundarylessManifold I.tangent (TangentBundle I M)]
  {L : TangentBundle I M → ℝ} (hL : ContMDiff I.tangent 𝓘(ℝ, ℝ) ∞ L)

namespace IsRegularLagrangian

include hL

/-- **Hamilton's equation for the Lagrangian vector field.** For a smooth regular Lagrangian on a
finite-dimensional boundaryless manifold, `ι_(X_E) ω_L = dE_L`. -/
theorem isHamiltonianVectorField_lagrangianVectorField (hreg : IsRegularLagrangian L) :
    (cartanTwoForm L hL).IsHamiltonianVectorField (lagrangianEnergy L)
      (lagrangianVectorField L hL) :=
  SmoothTwoForm.IsNondegenerate.isHamiltonianVectorField_hamiltonianVectorField
    (hreg.isSymplectic_cartanTwoForm hL).isNondegenerate (lagrangianEnergy L)

/-- **The Lagrangian vector field is the unique solution of Hamilton's equation.** For a smooth
regular Lagrangian on a finite-dimensional boundaryless manifold, a vector field `X` on `TM`
satisfies `ι_X ω_L = dE_L` exactly when it is the Lagrangian vector field. -/
theorem isHamiltonianVectorField_iff_eq_lagrangianVectorField (hreg : IsRegularLagrangian L)
    {X : (v : TangentBundle I M) → TangentSpace I.tangent v} :
    (cartanTwoForm L hL).IsHamiltonianVectorField (lagrangianEnergy L) X ↔
      X = lagrangianVectorField L hL :=
  (hreg.isSymplectic_cartanTwoForm hL).isNondegenerate.isHamiltonianVectorField_iff_eq

/-- **The Lagrangian vector field is second order.** For a smooth regular Lagrangian `L` on a
finite-dimensional boundaryless manifold, the projection `π : TM → M` sends the Lagrangian vector
field at a tangent vector `v` to `v` itself: `dπ (X_E(v)) = v`. -/
theorem mfderiv_proj_lagrangianVectorField (hreg : IsRegularLagrangian L) (v : TangentBundle I M) :
    mfderiv I.tangent I (π E (TangentSpace I)) v (lagrangianVectorField L hL v) = v.2 := by
  have hωL := hreg.isSymplectic_cartanTwoForm hL
  -- Hamilton's equation `ω_L(X_E, (0, w)) = dE_L(0, w)` against a vertical vector `(0, w)` reads
  -- `Hess_v(w, dπ X_E) = Hess_v(w, v)`.
  have key : ∀ w : TangentSpace I v.proj,
      fiberHessian L v w (mfderiv I.tangent I (π E (TangentSpace I)) v
        (lagrangianVectorField L hL v)) = fiberHessian L v w v.2 := by
    intro w
    rw [← eval₂_cartanTwoForm_apply_vertical hL, ← mfderiv_lagrangianEnergy_apply_vertical hL
      (by simp), lagrangianVectorField_def]
    -- The differential `mvfderiv` of a real function is its manifold derivative.
    exact hωL.isNondegenerate.eval₂_hamiltonianVectorField (lagrangianEnergy L) v ((0 : E), w)
  -- The fibre Hessian is symmetric and, by regularity, injective.
  refine (isRegularLagrangian_iff.1 hreg v).injective (ContinuousLinearMap.ext fun w ↦ ?_)
  exact (fiberHessian_apply_comm hL (by simp) v _ w).trans
    ((key w).trans (fiberHessian_apply_comm hL (by simp) v w _))

/-- **Integral curves of the Lagrangian vector field are velocity curves.** For a smooth regular
Lagrangian on a finite-dimensional boundaryless manifold, if a curve `γ` in `TM` has velocity
`X_E(γ t)` at time `t`, then its projection `π ∘ γ` to `M` has velocity `γ t` at `t`. -/
theorem hasMFDerivAt_proj_comp (hreg : IsRegularLagrangian L) {γ : ℝ → TangentBundle I M}
    {t : ℝ}
    (hγ : HasMFDerivAt 𝓘(ℝ) I.tangent γ t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (lagrangianVectorField L hL (γ t)))) :
    HasMFDerivAt 𝓘(ℝ) I (fun s ↦ (γ s).proj) t ((1 : ℝ →L[ℝ] ℝ).smulRight (γ t).2) := by
  -- Name the velocity as a vector of the model space `E × E`. By the second-order property its
  -- base component is `γ t`.
  obtain ⟨Y, hY⟩ : ∃ Y : E × E, lagrangianVectorField L hL (γ t) = Y := ⟨_, rfl⟩
  have h2 := mfderiv_proj_lagrangianVectorField hL hreg (γ t)
  rw [Bundle.mfderiv_proj, hY] at h2
  rw [hY] at hγ
  have h := Bundle.hasMFDerivAt_proj_comp hγ
  -- `h2` reads `Y.1 = (γ t).2` with the first projection applied as a linear map.
  rwa [show Y.1 = (γ t).2 from h2] at h

/-- **Integral curves of the Lagrangian vector field are velocity curves.** For a smooth regular
Lagrangian on a finite-dimensional boundaryless manifold, the projection to `M` of an integral
curve `γ` of `X_E` has velocity `γ t` at every time `t`. -/
theorem hasMFDerivAt_proj_comp_of_isMIntegralCurve (hreg : IsRegularLagrangian L)
    {γ : ℝ → TangentBundle I M} (hγ : IsMIntegralCurve γ (lagrangianVectorField L hL)) (t : ℝ) :
    HasMFDerivAt 𝓘(ℝ) I (fun s ↦ (γ s).proj) t ((1 : ℝ →L[ℝ] ℝ).smulRight (γ t).2) :=
  hasMFDerivAt_proj_comp hL hreg (hγ t)

end IsRegularLagrangian

end TauCeti

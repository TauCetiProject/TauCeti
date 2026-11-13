/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Hyperregular
public import TauCeti.Geometry.Manifold.MFDeriv.Curve
import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
import TauCeti.Geometry.Manifold.VectorBundle.CurveInTotalSpace
import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic
import TauCeti.Geometry.Manifold.VectorField.Regularity

/-!
# The Lagrangian vector field is second order

Let `L : TM → ℝ` be a smooth Lagrangian on a manifold `M`, with Legendre map `FL : TM → T*M`,
energy `E_L(v) = FL(v)(v) - L(v)` and Cartan two-form `ω_L = FL^*ω`
(`TauCeti.cartanTwoForm`), the pullback of the canonical symplectic form `ω = -dλ` of `T*M`. The
**Lagrangian vector field** is the Hamiltonian vector field `X_E` of the energy for `ω_L`, that is
`ι_(X_E) ω_L = dE_L`. This file proves that it is a *second-order* vector field: its base
component at a tangent vector `v` is `v` itself,

`dπ (X_E(v)) = v`,

where `π : TM → M` is the bundle projection
(`TauCeti.IsRegularLagrangian.mfderiv_proj_hamiltonianVectorField_lagrangianEnergy`). Hence every
integral curve `γ` of `X_E` is the velocity lift `t ↦ (c t, c' t)` of its base curve
`c = π ∘ γ` (`TauCeti.IsRegularLagrangian.eq_curveVelocityLift_of_isMIntegralCurve`): the
Lagrangian equations of motion are a second-order equation on `M`.

The proof pairs `X_E(v)` with the vertical vector `u^v` at `v` in a direction `u ∈ T_x M`. Along
the fibre `FL` is the fibre derivative of `L`, so its differential sends `u^v` to the vertical
covector `(Hess_v u)^v`, where `Hess_v` is the fibre Hessian (`TauCeti.fiberHessian`). The
canonical form pairs a tangent vector `ξ` of `T*M` with a vertical covector `β^v` by
`ω(ξ, β^v) = β(dπ ξ)`, so

`ω_L(X_E(v), u^v) = Hess_v(u, dπ X_E(v))`,

while differentiating `E_L` along the fibre gives `dE_L(u^v) = Hess_v(u, v)`
(`TauCeti.mvfderiv_lagrangianEnergy_vertical`). For a regular
Lagrangian the fibre Hessian is a nondegenerate symmetric form
(`TauCeti.fiberHessian_apply_comm`), so `dπ X_E(v) = v`. Only invertibility of the fibre Hessian
at `v` itself is used (`TauCeti.mfderiv_proj_eq_snd_of_eval₂_cartanTwoForm`).

For a hyperregular Lagrangian the Legendre diffeomorphism conjugates `X_E` with the Hamiltonian
vector field `X_H` of `H = E_L ∘ FL⁻¹` on `T*M`
(`TauCeti.IsHyperregularLagrangian.isMIntegralCurve_legendreMap_comp_iff`). So along every
integral curve `δ` of `X_H` the momentum is the Legendre transform of the velocity of the base
curve, `δ(t) = FL(c'(t))` for `c = π ∘ δ`
(`TauCeti.IsHyperregularLagrangian.eq_legendreMap_curveVelocityLift_of_isMIntegralCurve`): this is
Hamilton's first equation `dq/dt = ∂H/∂p`, in intrinsic form.

## Main results

* `TauCeti.mfderiv_proj_eq_snd_of_eval₂_cartanTwoForm`: at a tangent vector where the fibre
  Hessian is invertible, every vector `X` with `ι_X ω_L = dE_L` there satisfies `dπ X = v`.
* `TauCeti.IsRegularLagrangian.mfderiv_proj_hamiltonianVectorField_lagrangianEnergy`: the
  Lagrangian vector field of a smooth regular Lagrangian is second order.
* `TauCeti.IsRegularLagrangian.eq_curveVelocityLift_of_isMIntegralCurve`: its integral curves are
  velocity lifts of their base curves.
* `TauCeti.IsHyperregularLagrangian.eq_legendreMap_curveVelocityLift_of_isMIntegralCurve`: along
  a Hamiltonian trajectory of a hyperregular Lagrangian, the momentum is the Legendre transform of
  the base velocity.

## References

* R. Abraham, J. E. Marsden, *Foundations of Mechanics*, 2nd ed., Benjamin/Cummings, 1978,
  Section 3.5 (the Lagrangian vector field of a regular Lagrangian is second order).
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
  [IsManifold I ∞ M] {L : TangentBundle I M → ℝ}

/-- **The Lagrangian vector field is second order, pointwise.** At a tangent vector `v` where the
fibre Hessian of a smooth Lagrangian `L` is invertible, a tangent vector `X` of `TM` at `v` with
`ω_L(X, ·) = dE_L` satisfies `dπ X = v`: its base component is `v` itself. -/
theorem mfderiv_proj_eq_snd_of_eval₂_cartanTwoForm (hL : ContMDiff I.tangent 𝓘(ℝ, ℝ) ∞ L)
    {v : TangentBundle I M} (hv : (fiberHessian L v).IsInvertible) {X : TangentSpace I.tangent v}
    (hX : ∀ w, SmoothBundleForm.eval₂ (cartanTwoForm L hL) v X w =
      mvfderiv I.tangent (lagrangianEnergy L) v w) :
    mfderiv I.tangent I (π E (TangentSpace I)) v X = v.2 := by
  -- Pair `X` with the vertical vector of direction `u`: both sides of `ι_X ω_L = dE_L` give the
  -- fibre Hessian applied to `u`, on `dπ X` and on `v` respectively.
  have key : ∀ u : TangentSpace I v.proj,
      fiberHessian L v u (mfderiv I.tangent I (π E (TangentSpace I)) v X) =
        fiberHessian L v u v.2 := by
    intro u
    let Y : TangentSpace I.tangent v :=
      ((0 : E), (trivializationAt E (TangentSpace I) v.proj).continuousLinearMapAt ℝ v.proj u)
    -- `dFL` sends the vertical vector `Y` to the vertical covector of `Hess_v u`.
    have hY : mfderiv I.tangent (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (legendreMap L) v Y =
        ((0 : E), (trivializationAt (E →L[ℝ] ℝ) (fun x ↦ TangentSpace I x →L[ℝ] ℝ) v.proj
          ).continuousLinearMapAt ℝ v.proj (fiberHessian L v u)) :=
      mfderiv_legendreMap_vertical hL (by simp) v rfl u
    -- `FL` covers the identity of `M`, so `dFL` keeps the base component of `X`.
    have hX1 : (mfderiv I.tangent (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (legendreMap L) v X).1 = X.1 :=
      DFunLike.congr_fun (fst_comp_mfderiv_legendreMap hL (by simp) v) X
    -- The canonical form pairs a tangent vector with a vertical covector by `β(dπ ξ)`.
    have hω : ∀ a b : TangentSpace (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (legendreMap L v),
        SmoothBundleForm.eval₂ (CotangentBundle.symplecticForm I M) (legendreMap L v) a b =
          b.2 a.1 - a.2 b.1 := fun a b ↦
      (CotangentBundle.eval₂_symplecticForm _ a b).trans
        (strongDualCotangentSymplecticForm_apply a b)
    have h := hX Y
    rw [mvfderiv_lagrangianEnergy_vertical hL (by simp) v u,
      ← mpullback_legendreMap_symplecticForm hL,
      SmoothForm.eval₂_mpullback (legendreMap L) (contMDiff_legendreMap hL le_rfl), hω, hY,
      CotangentBundle.continuousLinearMapAt_trivializationAt_self, hX1] at h
    simp only [map_zero, sub_zero] at h
    rw [Bundle.mfderiv_proj]
    exact h
  -- The fibre Hessian is symmetric, so `Hess (dπ X) = Hess v`, and it is injective.
  obtain ⟨e, he⟩ := hv
  refine e.injective ?_
  rw [← ContinuousLinearEquiv.coe_coe, he]
  ext u
  rw [fiberHessian_apply_comm hL (by simp), key, fiberHessian_apply_comm hL (by simp)]

namespace IsRegularLagrangian

variable (hL : ContMDiff I.tangent 𝓘(ℝ, ℝ) ∞ L) (hreg : IsRegularLagrangian L)
  {X : (v : TangentBundle I M) → TangentSpace I.tangent v}
include hreg

/-- **The Lagrangian vector field is second order.** For a smooth regular Lagrangian, every
Hamiltonian vector field `X` of the energy for the Cartan two-form satisfies `dπ (X v) = v`. -/
theorem mfderiv_proj_eq_snd_of_isHamiltonianVectorField
    (hX : (cartanTwoForm L hL).IsHamiltonianVectorField (lagrangianEnergy L) X)
    (v : TangentBundle I M) :
    mfderiv I.tangent I (π E (TangentSpace I)) v (X v) = v.2 :=
  mfderiv_proj_eq_snd_of_eval₂_cartanTwoForm hL (isRegularLagrangian_iff.1 hreg v)
    (SmoothTwoForm.isHamiltonianVectorField_iff.1 hX v)

/-- **Integral curves of the Lagrangian vector field are velocity lifts.** For a smooth regular
Lagrangian, an integral curve `γ` of a Hamiltonian vector field of the energy for the Cartan
two-form is the velocity lift `t ↦ (c t, c' t)` of its base curve `c = π ∘ γ`. -/
theorem eq_curveVelocityLift_of_isMIntegralCurve
    (hX : (cartanTwoForm L hL).IsHamiltonianVectorField (lagrangianEnergy L) X)
    {γ : ℝ → TangentBundle I M} (hγ : IsMIntegralCurve γ X) (t : ℝ) :
    γ t = Manifold.curveVelocityLift I (fun s ↦ (γ s).proj) t :=
  Manifold.eq_curveVelocityLift_of_hasMFDerivAt (hγ t)
    (hreg.mfderiv_proj_eq_snd_of_isHamiltonianVectorField hL hX (γ t))

variable [FiniteDimensional ℝ E]
  [BoundarylessManifold I.tangent (TangentBundle I M)]

/-- **The Lagrangian vector field is second order.** For a smooth regular Lagrangian on a
finite-dimensional boundaryless manifold, the Hamiltonian vector field `X_E` of the energy for the
symplectic Cartan two-form satisfies `dπ (X_E v) = v`. -/
theorem mfderiv_proj_hamiltonianVectorField_lagrangianEnergy (v : TangentBundle I M) :
    mfderiv I.tangent I (π E (TangentSpace I)) v
      ((cartanTwoForm L hL).hamiltonianVectorField (lagrangianEnergy L) v) = v.2 :=
  hreg.mfderiv_proj_eq_snd_of_isHamiltonianVectorField hL
    ((hreg.isSymplectic_cartanTwoForm hL).isNondegenerate
      |>.isHamiltonianVectorField_hamiltonianVectorField _) v

end IsRegularLagrangian

namespace IsHyperregularLagrangian

variable [FiniteDimensional ℝ E]
  [BoundarylessManifold I.tangent (TangentBundle I M)]
  (h : IsHyperregularLagrangian L) (hL : ContMDiff I.tangent 𝓘(ℝ, ℝ) ∞ L)
include hL

/-- **Hamilton's first equation for a hyperregular Lagrangian.** Along an integral curve `δ` of the
Hamiltonian vector field of `H = E_L ∘ FL⁻¹` on `T*M`, the covector `δ t` is the Legendre transform
`FL(c'(t))` of the velocity of the base curve `c = π ∘ δ`. -/
theorem eq_legendreMap_curveVelocityLift_of_isMIntegralCurve {δ : ℝ → CotangentBundle I M}
    (hδ : IsMIntegralCurve δ
      ((CotangentBundle.symplecticForm I M).hamiltonianVectorField h.hamiltonian))
    (t : ℝ) :
    δ t = legendreMap L (Manifold.curveVelocityLift I (fun s ↦ (δ s).proj) t) := by
  -- Pull `δ` back to an integral curve of the Lagrangian vector field.
  set γ : ℝ → TangentBundle I M := fun s ↦ (h.legendreDiffeomorph hL).symm (δ s)
  have hFγ : legendreMap L ∘ γ = δ :=
    funext fun s ↦ h.legendreMap_legendreDiffeomorph_symm_apply hL (δ s)
  have hγ : IsMIntegralCurve γ
      ((cartanTwoForm L hL).hamiltonianVectorField (lagrangianEnergy L)) :=
    (h.isMIntegralCurve_legendreMap_comp_iff hL).1 (hFγ ▸ hδ)
  have hproj : (fun s ↦ (γ s).proj) = fun s ↦ (δ s).proj :=
    funext fun s ↦ h.proj_legendreDiffeomorph_symm_apply hL (δ s)
  rw [← hproj, ← Manifold.eq_curveVelocityLift_of_hasMFDerivAt (hγ t)
    (h.isRegularLagrangian.mfderiv_proj_hamiltonianVectorField_lagrangianEnergy hL (γ t))]
  exact (congrFun hFγ t).symm

end IsHyperregularLagrangian

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Legendre
public import TauCeti.Geometry.Symplectic.Hamiltonian.Manifold
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.VectorBundle.Cotangent.Basic
import TauCeti.Geometry.Manifold.VectorBundle.CurveInTotalSpace
import TauCeti.Geometry.Manifold.VectorBundle.Submersion
import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic
import TauCeti.Geometry.Manifold.VectorField.Regularity

/-!
# The Lagrangian vector field is second order

Let `L : TM → ℝ` be a smooth Lagrangian, with Legendre map `FL : TM → T*M`, energy
`E_L(v) = FL(v)(v) - L(v)` and Cartan two-form `ω_L = FL^*ω`. The **Lagrangian vector field** is
the Hamiltonian vector field `X_E` of the energy for `ω_L`, in the convention `ι_{X_E} ω_L = dE_L`.
This file proves that it is a **second-order** vector field when `L` is regular: the projection
`π : TM → M` sends `X_E(v)` to `v` itself,

`dπ(X_E(v)) = v`

(`TauCeti.IsRegularLagrangian.mfderiv_proj_hamiltonianVectorField`). Consequently every integral
curve `γ` of `X_E` in `TM` is the velocity curve of its projection: `(π ∘ γ)'(t) = γ(t)`
(`TauCeti.IsRegularLagrangian.hasMFDerivAt_proj_comp_of_isMIntegralCurve`). So the motions of the
Lagrangian system are curves in `M`, and `X_E` is the second-order equation that they solve.

The proof pairs a tangent vector `X` at `v` with the vertical vectors at `v`. If `Y` is the
vertical vector with fibre coordinate `w`, then `dFL(Y)` is the vertical covector with fibre
coordinate `∂²L/∂v∂v(w)`, the fibre Hessian applied to `w`, so

`ω_L(X, Y) = ∂²L/∂v∂v(w)(dπ X)`,

whereas the derivative of the energy along the fibre is `dE_L(Y) = ∂²L/∂v∂v(w)(v)`. If
`ι_X ω_L = dE_L` at `v`, the two right-hand sides agree for every `w`, and invertibility of the
fibre Hessian gives `dπ X = v` (`TauCeti.mfderiv_proj_eq_of_eval₂_cartanTwoForm_eq`). This
pointwise statement only needs `X` to solve `ι_X ω_L = dE_L` at the single vector `v` and the
fibre Hessian to be invertible there: it assumes neither finite dimension nor nondegeneracy of
`ω_L`, which are what make `X_E` exist and be unique. In particular it applies to the value at `v`
of every Hamiltonian vector field of `E_L` for `ω_L`
(`TauCeti.SmoothTwoForm.IsHamiltonianVectorField`).

## Main results

* `TauCeti.mfderiv_proj_eq_of_eval₂_cartanTwoForm_eq`: a solution `X` of `ι_X ω_L = dE_L` at a
  tangent vector `v` where the fibre Hessian is invertible projects to `v`.
* `TauCeti.IsRegularLagrangian.mfderiv_proj_hamiltonianVectorField`: the Lagrangian vector field
  of a smooth regular Lagrangian on a finite-dimensional boundaryless manifold is second order.
* `TauCeti.IsRegularLagrangian.hasMFDerivAt_proj_comp_of_isMIntegralCurve`: its integral curves are
  velocity curves.

## References

* R. Abraham, J. E. Marsden, *Foundations of Mechanics*, 2nd ed., Benjamin/Cummings, 1978,
  Section 3.5.
* J. E. Marsden, T. S. Ratiu, *Introduction to Mechanics and Symmetry*, 2nd ed., Texts in Applied
  Mathematics 17, Springer, 1999, Section 7.3.
-/

public section

noncomputable section

open Bundle Set
open scoped Manifold ContDiff

namespace TauCeti

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] {L : TangentBundle I M → ℝ}

/-- The line `r ↦ v + r • w` in the fibre through `v` has velocity the vertical vector `(0, w)`,
read in the chart at `v`. -/
private theorem hasMFDerivAt_verticalLine (v : TangentBundle I M) (w : TangentSpace I v.proj) :
    HasMFDerivAt 𝓘(ℝ) I.tangent (fun r : ℝ ↦ TotalSpace.mk' E v.proj (v.2 + r • w)) 0
      ((1 : ℝ →L[ℝ] ℝ).smulRight (((0 : E), w) : E × E)) := by
  have h := TauCeti.Manifold.hasMFDerivAt_totalSpaceMk_add_smul (𝕜 := ℝ) (F := E) (IB := I)
    (V := TangentSpace I) v.proj v.2 w
  simpa only [TauCeti.Manifold.continuousLinearMapAt_trivializationAt_self (I := I)] using h

/-- Along the line `r ↦ v + r • w` in the fibre through `v`, the energy has derivative
`∂²L/∂v∂v(w)(v)` at `r = 0`: the two first-order terms `FL(v)(w)` cancel. -/
private theorem hasDerivAt_lagrangianEnergy_verticalLine (hL : ContMDiff I.tangent 𝓘(ℝ, ℝ) ∞ L)
    (v : TangentBundle I M) (w : TangentSpace I v.proj) :
    HasDerivAt (fun r : ℝ ↦ lagrangianEnergy L (TotalSpace.mk' E v.proj (v.2 + r • w)))
      (fiberHessian L v w v.2) 0 := by
  -- Work on the model space `E`, where the fibre restriction `f` of `L` is an ordinary function.
  let w' : E := w
  let v' : E := v.2
  let Hs : E →L[ℝ] E →L[ℝ] ℝ := fiberHessian L v
  let f : E → ℝ := fun u ↦ L (TotalSpace.mk' E v.proj u)
  have h1 : HasDerivAt (fun r : ℝ ↦ v' + r • w') w' 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const w').const_add v'
  have hc : ContDiff ℝ ∞ f :=
    contMDiff_iff_contDiff.1 (hL.comp (contMDiff_tangentBundle_mk_constBase contMDiff_id v.proj))
  have hHs : Hs = fderiv ℝ (fderiv ℝ f) v' := fiberHessian_def L v
  have h2 : HasFDerivAt (fderiv ℝ f) Hs (v' + (0 : ℝ) • w') := by
    rw [zero_smul, add_zero, hHs]
    exact ((hc.fderiv_right (m := 1) (by simp)).differentiable one_ne_zero v').hasFDerivAt
  have h3 : HasFDerivAt f (fderiv ℝ f (v' + (0 : ℝ) • w')) (v' + (0 : ℝ) • w') :=
    (hc.differentiable (by simp) _).hasFDerivAt
  -- `E_L(v + r w) = Df(v + r w)(v + r w) - f(v + r w)`.
  have hA : HasDerivAt (fun r : ℝ ↦ fderiv ℝ f (v' + r • w')) (Hs w') 0 :=
    h2.comp_hasDerivAt (0 : ℝ) h1
  have hB := h3.comp_hasDerivAt (0 : ℝ) h1
  have h := (hA.clm_apply h1).sub hB
  rw [add_sub_cancel_right, zero_smul, add_zero] at h
  have hfun : (fun r : ℝ ↦ lagrangianEnergy L (TotalSpace.mk' E v.proj (v.2 + r • w))) =
      fun r : ℝ ↦ fderiv ℝ f (v' + r • w') (v' + r • w') - (f ∘ fun r : ℝ ↦ v' + r • w') r :=
    -- After unfolding the energy, both sides agree up to the projections of `TotalSpace.mk'`.
    funext fun r ↦ by rw [lagrangianEnergy_apply, legendreMap_snd]; rfl
  rw [hfun]
  exact h

/-- **The Cartan two-form against a vertical vector.** If `Y` is the vertical vector at `v` with
fibre coordinate `w`, then `ω_L(X, Y) = ∂²L/∂v∂v(w)(dπ X)`. -/
private theorem eval₂_cartanTwoForm_vertical (hL : ContMDiff I.tangent 𝓘(ℝ, ℝ) ∞ L)
    (v : TangentBundle I M) (X : TangentSpace I.tangent v) (w : TangentSpace I v.proj) :
    SmoothBundleForm.eval₂ (cartanTwoForm L hL) v X (((0 : E), w) : E × E) =
      fiberHessian L v w (mfderiv I.tangent I (π E (TangentSpace I)) v X) := by
  -- `dFL` sends the vertical vector `(0, w)` to the vertical covector `(0, ∂²L/∂v∂v(w))` and keeps
  -- the base coordinate.
  obtain ⟨T, hT⟩ : ∃ T : E × E →L[ℝ] E × (E →L[ℝ] ℝ),
      mfderiv I.tangent (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (legendreMap L) v = T := ⟨_, rfl⟩
  have hY : T ((0 : E), w) = ((0 : E), fiberHessian L v w) := by
    have h := mfderiv_legendreMap_vertical hL (by simp) v hT w
    simp only [Manifold.continuousLinearMapAt_trivializationAt_self,
      CotangentBundle.continuousLinearMapAt_trivializationAt_self] at h
    exact h
  have hY' : mfderiv I.tangent (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (legendreMap L) v
      (((0 : E), w) : E × E) = ((0 : E), fiberHessian L v w) := hT ▸ hY
  have hX : (mfderiv I.tangent (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (legendreMap L) v X).1 =
      mfderiv I.tangent I (π E (TangentSpace I)) v X := by
    rw [Bundle.mfderiv_proj]
    exact DFunLike.congr_fun (fst_comp_mfderiv_legendreMap hL (by simp) v) X
  -- Evaluate `ω_L = FL^*ω` through the linear formula for `ω` in the chart at `FL(v)`.
  have hpull := SmoothForm.eval₂_mpullback (legendreMap L) (contMDiff_legendreMap hL le_rfl)
    (CotangentBundle.symplecticForm I M) v X (((0 : E), w) : E × E)
  rw [mpullback_legendreMap_symplecticForm hL] at hpull
  rw [hpull, CotangentBundle.eval₂_symplecticForm]
  refine (strongDualCotangentSymplecticForm_apply _ _).trans ?_
  rw [hY', hX, map_zero, sub_zero]
  -- The second component of the pair `(0, ∂²L/∂v∂v(w))` is `∂²L/∂v∂v(w)`.
  rfl

/-- **The energy along a vertical vector.** If `Y` is the vertical vector at `v` with fibre
coordinate `w`, then `dE_L(Y) = ∂²L/∂v∂v(w)(v)`. -/
private theorem mvfderiv_lagrangianEnergy_vertical (hL : ContMDiff I.tangent 𝓘(ℝ, ℝ) ∞ L)
    (v : TangentBundle I M) (w : TangentSpace I v.proj) :
    mvfderiv I.tangent (lagrangianEnergy L) v (((0 : E), w) : E × E) = fiberHessian L v w v.2 := by
  -- Read the differential of the energy as a map on the model space of the chart.
  obtain ⟨S, hS⟩ : ∃ S : E × E →L[ℝ] ℝ,
      mfderiv I.tangent 𝓘(ℝ, ℝ) (lagrangianEnergy L) v = S := ⟨_, rfl⟩
  have hE : HasMFDerivAt I.tangent 𝓘(ℝ, ℝ) (lagrangianEnergy L)
      (TotalSpace.mk' E v.proj (v.2 + (0 : ℝ) • w)) S := by
    rw [zero_smul, add_zero, ← hS]
    exact ((contMDiff_lagrangianEnergy (m := ∞) hL le_rfl v).mdifferentiableAt (by simp)
      ).hasMFDerivAt
  -- The derivative of the energy along the vertical line through `v`, computed twice.
  have hEq : S.comp ((1 : ℝ →L[ℝ] ℝ).smulRight (((0 : E), w) : E × E)) =
      (1 : ℝ →L[ℝ] ℝ).smulRight (fiberHessian L v w v.2) :=
    (hE.comp 0 (hasMFDerivAt_verticalLine v w)).mfderiv.symm.trans
      (hasDerivAt_lagrangianEnergy_verticalLine hL v w).hasFDerivAt.hasMFDerivAt.mfderiv
  rw [mvfderiv_apply_eq_mfderiv_apply (lagrangianEnergy L) v (((0 : E), w) : E × E), hS]
  have h := DFunLike.congr_fun hEq 1
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
    one_apply_eq_self, one_smul] at h
  exact h

/-- **Solutions of `ι_X ω_L = dE_L` are second order.** Let `L` be a smooth Lagrangian whose
fibre Hessian at the tangent vector `v` is invertible. If a tangent vector `X` to `TM` at `v`
satisfies `ω_L(X, Y) = dE_L(Y)` for every `Y`, where `ω_L` is the Cartan two-form and `E_L` the
energy, then the projection `π : TM → M` sends `X` to `v`. -/
theorem mfderiv_proj_eq_of_eval₂_cartanTwoForm_eq (hL : ContMDiff I.tangent 𝓘(ℝ, ℝ) ∞ L)
    {v : TangentBundle I M} (hv : (fiberHessian L v).IsInvertible)
    {X : TangentSpace I.tangent v}
    (hX : ∀ Y, SmoothBundleForm.eval₂ (cartanTwoForm L hL) v X Y =
      mvfderiv I.tangent (lagrangianEnergy L) v Y) :
    mfderiv I.tangent I (π E (TangentSpace I)) v X = v.2 := by
  rw [← sub_eq_zero]
  -- Every covector is `∂²L/∂v∂v(w)` for some `w`, and each vanishes on `dπ X - v`.
  refine SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := ℝ) (V := E) fun ℓ ↦ ?_
  obtain ⟨w, rfl⟩ := hv.surjective ℓ
  have h := hX (((0 : E), w) : E × E)
  rw [eval₂_cartanTwoForm_vertical, mvfderiv_lagrangianEnergy_vertical hL] at h
  exact ((fiberHessian L v w).map_sub _ _).trans (by rw [h, sub_self])

variable [FiniteDimensional ℝ E] [BoundarylessManifold I.tangent (TangentBundle I M)]

/-- **The Lagrangian vector field is second order.** For a smooth regular Lagrangian `L` on a
finite-dimensional boundaryless manifold `M`, let `X_E` be the Hamiltonian vector field of the
energy `E_L` for the Cartan two-form `ω_L = FL^*ω`. Then the projection `π : TM → M` sends `X_E(v)`
to `v` itself, `dπ(X_E(v)) = v`, at every tangent vector `v`. -/
theorem IsRegularLagrangian.mfderiv_proj_hamiltonianVectorField
    (hL : ContMDiff I.tangent 𝓘(ℝ, ℝ) ∞ L) (hreg : IsRegularLagrangian L)
    (v : TangentBundle I M) :
    mfderiv I.tangent I (π E (TangentSpace I)) v
        ((cartanTwoForm L hL).hamiltonianVectorField (lagrangianEnergy L) v) = v.2 :=
  mfderiv_proj_eq_of_eval₂_cartanTwoForm_eq hL (isRegularLagrangian_iff.1 hreg v)
    ((hreg.isSymplectic_cartanTwoForm hL).isNondegenerate.eval₂_hamiltonianVectorField _ v)

/-- **Integral curves of the Lagrangian vector field are velocity curves.** For a smooth regular
Lagrangian `L` on a finite-dimensional boundaryless manifold `M`, if `γ` is an integral curve in
`TM` of the Hamiltonian vector field `X_E` of the energy for the Cartan two-form, then its
projection `π ∘ γ` to `M` has velocity `γ(t)` at every time `t`. -/
theorem IsRegularLagrangian.hasMFDerivAt_proj_comp_of_isMIntegralCurve
    (hL : ContMDiff I.tangent 𝓘(ℝ, ℝ) ∞ L) (hreg : IsRegularLagrangian L)
    {γ : ℝ → TangentBundle I M}
    (hγ : IsMIntegralCurve γ ((cartanTwoForm L hL).hamiltonianVectorField (lagrangianEnergy L)))
    (t : ℝ) :
    HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s ↦ (γ s).proj) t ((1 : ℝ →L[ℝ] ℝ).smulRight (γ t).2) := by
  have hπ : HasMFDerivAt I.tangent I (π E (TangentSpace I)) (γ t)
      (mfderiv I.tangent I (π E (TangentSpace I)) (γ t)) :=
    ((contMDiff_proj (TangentSpace I) (γ t)).mdifferentiableAt one_ne_zero).hasMFDerivAt
  have hder : (mfderiv I.tangent I (π E (TangentSpace I)) (γ t)).comp ((1 : ℝ →L[ℝ] ℝ).smulRight
      ((cartanTwoForm L hL).hamiltonianVectorField (lagrangianEnergy L) (γ t))) =
      (1 : ℝ →L[ℝ] ℝ).smulRight (γ t).2 := by
    rw [ContinuousLinearMap.smulRight_one_eq_toSpanSingleton,
      ContinuousLinearMap.smulRight_one_eq_toSpanSingleton,
      ContinuousLinearMap.comp_toSpanSingleton, hreg.mfderiv_proj_hamiltonianVectorField hL]
  exact (hπ.comp t (hγ t)).congr_mfderiv hder

end TauCeti

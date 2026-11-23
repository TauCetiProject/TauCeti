/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Hyperregular
public import TauCeti.Geometry.Manifold.MFDeriv.Curve
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Submersion
import TauCeti.Geometry.Symplectic.Hamiltonian.EulerLagrange.Covariance
import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
import TauCeti.Geometry.Manifold.VectorBundle.CurveInTotalSpace
import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic
import TauCeti.Geometry.Manifold.VectorField.Regularity

/-!
# The Lagrangian vector field is second order and solves the Euler–Lagrange equations

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
`c = π ∘ γ` (`TauCeti.IsRegularLagrangian.eq_curveVelocityLift_of_isMIntegralCurve`, and within
parameter sets `TauCeti.IsRegularLagrangian.eq_curveVelocityLiftWithin_of_isMIntegralCurveOn`):
the Lagrangian equations of motion are a second-order equation on `M`.

The proof pairs `X_E(v)` with the vertical vector `u^v` at `v` in a direction `u ∈ T_x M`. Along
the fibre `FL` is the fibre derivative of `L`, so its differential sends `u^v` to the vertical
covector `(Hess_v u)^v`, where `Hess_v` is the fibre Hessian (`TauCeti.fiberHessian`). The
canonical form pairs a tangent vector `ξ` of `T*M` with a vertical covector `β^v` by
`ω(ξ, β^v) = β(dπ ξ)`, so

`ω_L(X_E(v), u^v) = Hess_v(u, dπ X_E(v))`

(`TauCeti.eval₂_cartanTwoForm_vertical`), while differentiating `E_L` along the fibre gives
`dE_L(u^v) = Hess_v(u, v)` (`TauCeti.mvfderiv_lagrangianEnergy_vertical`). For a regular
Lagrangian the fibre Hessian is a nondegenerate symmetric form
(`TauCeti.fiberHessian_apply_comm`), so `dπ X_E(v) = v`. Only invertibility of the fibre Hessian
at `v` itself is used (`TauCeti.mfderiv_proj_eq_snd_of_eval₂_cartanTwoForm`).

In every tangent-bundle chart, the integral curves of `X_E`, including local ones, solve the
**Euler–Lagrange equations**
(`TauCeti.IsRegularLagrangian.eulerLagrange_extChartAt_of_isMIntegralCurveAt`). On a
boundaryless manifold, read the curve in the chart at any `w₀` whose source contains `γ t`, with
coordinates `(q, v)`, and let `ℓ = L ∘ (chart at w₀)⁻¹` be the local Lagrangian. Then `q' = v` and

`d/dt ∂_v ℓ(q, v) = ∂_q ℓ(q, v)` at `t`.

In the chart at `γ t` itself this is a computation at a single point. There the Legendre map reads
as the Legendre map `(q, u) ↦ (q, ∂_u ℓ(q, u))` of `ℓ`
(`TauCeti.mfderiv_legendreMap_eq_fderiv_linearLegendreMap`), `ω_L` as the pullback of the
canonical form of `E × E'` by its derivative
(`TauCeti.eval₂_cartanTwoForm_eq_fderiv_linearLegendreMap`), and `dE_L` as the derivative of the
local energy (`TauCeti.mvfderiv_lagrangianEnergy_eq_fderiv`). Pairing `ι_(X_E) ω_L = dE_L` with
horizontal directions then gives the equation
(`TauCeti.eulerLagrange_of_hasDerivAt_of_symplecticForm`). In any other chart it follows from the
invariance of the Euler–Lagrange equations under the change of base coordinates
(`TauCeti.eulerLagrange_of_comp`), whose tangent map is the change of tangent-bundle charts
(`TauCeti.Manifold.extChartAt_tangent_eq_fderiv`).

For a hyperregular Lagrangian the Legendre diffeomorphism conjugates `X_E` with the Hamiltonian
vector field `X_H` of `H = E_L ∘ FL⁻¹` on `T*M`
(`TauCeti.IsHyperregularLagrangian.isMIntegralCurve_legendreMap_comp_iff`). So along every
integral curve `δ` of `X_H` the momentum is the Legendre transform of the velocity of the base
curve, `δ(t) = FL(c'(t))` for `c = π ∘ δ`
(`TauCeti.IsHyperregularLagrangian.eq_legendreMap_curveVelocityLift_of_isMIntegralCurve`, and
within parameter sets
`TauCeti.IsHyperregularLagrangian.eq_legendreMap_curveVelocityLiftWithin_of_isMIntegralCurveOn`):
this is Hamilton's first equation `dq/dt = ∂H/∂p`, in intrinsic form.

## Main results

* `TauCeti.mfderiv_proj_eq_snd_of_eval₂_cartanTwoForm`: at a tangent vector where the fibre
  Hessian is invertible, every vector `X` with `ι_X ω_L = dE_L` there satisfies `dπ X = v`.
* `TauCeti.IsRegularLagrangian.mfderiv_proj_hamiltonianVectorField_lagrangianEnergy`: the
  Lagrangian vector field of a smooth regular Lagrangian is second order.
* `TauCeti.IsRegularLagrangian.eq_curveVelocityLift_of_isMIntegralCurve`: its integral curves are
  velocity lifts of their base curves.
* `TauCeti.IsRegularLagrangian.eq_curveVelocityLiftWithin_of_isMIntegralCurveOn`: the same within
  parameter sets with unique derivatives.
* `TauCeti.IsRegularLagrangian.eulerLagrange_extChartAt_of_isMIntegralCurveAt`: local integral
  curves of the Lagrangian vector field solve the Euler–Lagrange equations in every chart.
* `TauCeti.IsHyperregularLagrangian.eq_legendreMap_curveVelocityLift_of_isMIntegralCurve`: along
  a Hamiltonian trajectory of a hyperregular Lagrangian, the momentum is the Legendre transform of
  the base velocity.
* `TauCeti.IsHyperregularLagrangian.eq_legendreMap_curveVelocityLiftWithin_of_isMIntegralCurveOn`:
  the same within parameter sets with unique derivatives.

## References

* R. Abraham, J. E. Marsden, *Foundations of Mechanics*, 2nd ed., Benjamin/Cummings, 1978,
  Section 3.5 (the Lagrangian vector field of a regular Lagrangian is second order).
* J. E. Marsden, T. S. Ratiu, *Introduction to Mechanics and Symmetry*, 2nd ed., Texts in Applied
  Mathematics 17, Springer, 1999, Chapter 7.
-/

public section

noncomputable section

open Bundle Filter Set
open scoped Manifold ContDiff Topology

namespace TauCeti

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] {L : TangentBundle I M → ℝ}

/-- **The Cartan two-form on vertical vectors.** For a smooth Lagrangian `L`, the Cartan two-form
pairs a tangent vector `X` of `TM` at `v` with the vertical vector `u^v` of direction `u` at `v`
by the fibre Hessian: `ω_L(X, u^v) = Hess_v(u, dπ X)`. -/
theorem eval₂_cartanTwoForm_vertical (hL : ContMDiff I.tangent 𝓘(ℝ, ℝ) ∞ L)
    (v : TangentBundle I M) (X : TangentSpace I.tangent v) (u : TangentSpace I v.proj) :
    SmoothBundleForm.eval₂ (cartanTwoForm L hL) v X
        ((0 : E), (trivializationAt E (TangentSpace I) v.proj).continuousLinearMapAt ℝ v.proj u) =
      fiberHessian L v u (mfderiv I.tangent I (π E (TangentSpace I)) v X) := by
  -- Name the vertical vector, so that the rewrites below see a tangent vector of `TM`.
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
  have h : SmoothBundleForm.eval₂ (cartanTwoForm L hL) v X Y =
      fiberHessian L v u (mfderiv I.tangent I (π E (TangentSpace I)) v X) := by
    rw [← mpullback_legendreMap_symplecticForm hL,
      SmoothForm.eval₂_mpullback (legendreMap L) (contMDiff_legendreMap hL le_rfl), hω, hY,
      CotangentBundle.continuousLinearMapAt_trivializationAt_self, Bundle.mfderiv_proj]
    simp only [map_zero, sub_zero]
    -- `fst X` is the base component `X.1` of `X`, viewed in the model `E × E` of `TM`.
    exact congrArg (fiberHessian L v u) hX1
  exact h

/-- **The Lagrangian vector field is second order, pointwise.** At a tangent vector `v` where the
fibre Hessian of a smooth Lagrangian `L` is invertible, a tangent vector `X` of `TM` at `v` with
`ω_L(X, ·) = dE_L` satisfies `dπ X = v`: its base component is `v` itself. -/
theorem mfderiv_proj_eq_snd_of_eval₂_cartanTwoForm (hL : ContMDiff I.tangent 𝓘(ℝ, ℝ) ∞ L)
    {v : TangentBundle I M} (hv : (fiberHessian L v).IsInvertible) {X : TangentSpace I.tangent v}
    (hX : ∀ w, SmoothBundleForm.eval₂ (cartanTwoForm L hL) v X w =
      mvfderiv I.tangent (lagrangianEnergy L) v w) :
    mfderiv I.tangent I (π E (TangentSpace I)) v X = v.snd := by
  -- Pair `X` with the vertical vector of direction `u`: both sides of `ι_X ω_L = dE_L` give the
  -- fibre Hessian applied to `u`, on `dπ X` and on `v` respectively.
  have key : ∀ u : TangentSpace I v.proj,
      fiberHessian L v u (mfderiv I.tangent I (π E (TangentSpace I)) v X) =
        fiberHessian L v u v.snd := fun u ↦
    (eval₂_cartanTwoForm_vertical hL v X u).symm.trans
      ((hX _).trans (mvfderiv_lagrangianEnergy_vertical hL (by simp) v u))
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
    mfderiv I.tangent I (π E (TangentSpace I)) v (X v) = v.snd :=
  mfderiv_proj_eq_snd_of_eval₂_cartanTwoForm hL (isRegularLagrangian_iff.1 hreg v)
    (SmoothTwoForm.isHamiltonianVectorField_iff.1 hX v)

/-- **Integral curves of the Lagrangian vector field are velocity lifts, within a parameter
set.** For a smooth regular Lagrangian, an integral curve `γ` on `s` of a Hamiltonian vector field
of the energy for the Cartan two-form is, at each `t ∈ s` where `s` has unique derivatives, the
within-`s` velocity lift of its base curve `c = π ∘ γ`. -/
theorem eq_curveVelocityLiftWithin_of_isMIntegralCurveOn
    (hX : (cartanTwoForm L hL).IsHamiltonianVectorField (lagrangianEnergy L) X)
    {γ : ℝ → TangentBundle I M} {s : Set ℝ} {t : ℝ} (hs : UniqueDiffWithinAt ℝ s t)
    (hγ : IsMIntegralCurveOn γ X s) (ht : t ∈ s) :
    γ t = Manifold.curveVelocityLiftWithin I (fun r ↦ (γ r).proj) s t :=
  Manifold.eq_curveVelocityLiftWithin_of_hasMFDerivWithinAt hs (hγ t ht)
    (hreg.mfderiv_proj_eq_snd_of_isHamiltonianVectorField hL hX (γ t))

/-- **Integral curves of the Lagrangian vector field are velocity lifts.** For a smooth regular
Lagrangian, an integral curve `γ` of a Hamiltonian vector field of the energy for the Cartan
two-form is the velocity lift `t ↦ (c t, c' t)` of its base curve `c = π ∘ γ`. -/
theorem eq_curveVelocityLift_of_isMIntegralCurve
    (hX : (cartanTwoForm L hL).IsHamiltonianVectorField (lagrangianEnergy L) X)
    {γ : ℝ → TangentBundle I M} (hγ : IsMIntegralCurve γ X) (t : ℝ) :
    γ t = Manifold.curveVelocityLift I (fun s ↦ (γ s).proj) t := by
  rw [← Manifold.curveVelocityLiftWithin_univ]
  exact hreg.eq_curveVelocityLiftWithin_of_isMIntegralCurveOn hL hX uniqueDiffWithinAt_univ
    (hγ.isMIntegralCurveOn _) (Set.mem_univ t)

variable [FiniteDimensional ℝ E]
  [BoundarylessManifold I.tangent (TangentBundle I M)]

/-- **The Lagrangian vector field is second order.** For a smooth regular Lagrangian on a
finite-dimensional boundaryless manifold, the Hamiltonian vector field `X_E` of the energy for the
symplectic Cartan two-form satisfies `dπ (X_E v) = v`. -/
theorem mfderiv_proj_hamiltonianVectorField_lagrangianEnergy (v : TangentBundle I M) :
    mfderiv I.tangent I (π E (TangentSpace I)) v
      ((cartanTwoForm L hL).hamiltonianVectorField (lagrangianEnergy L) v) = v.snd :=
  hreg.mfderiv_proj_eq_snd_of_isHamiltonianVectorField hL
    ((hreg.isSymplectic_cartanTwoForm hL).isNondegenerate
      |>.isHamiltonianVectorField_hamiltonianVectorField _) v

end IsRegularLagrangian

namespace IsHyperregularLagrangian

variable [FiniteDimensional ℝ E]
  [BoundarylessManifold I.tangent (TangentBundle I M)]
  (h : IsHyperregularLagrangian L) (hL : ContMDiff I.tangent 𝓘(ℝ, ℝ) ∞ L)
include hL

/-- **Hamilton's first equation for a hyperregular Lagrangian, within a parameter set.** Along an
integral curve `δ` on `s` of the Hamiltonian vector field of `H = E_L ∘ FL⁻¹` on `T*M`, at each
`t ∈ s` where `s` has unique derivatives, the covector `δ t` is the Legendre transform of the
within-`s` velocity of the base curve `c = π ∘ δ`. -/
theorem eq_legendreMap_curveVelocityLiftWithin_of_isMIntegralCurveOn
    {δ : ℝ → CotangentBundle I M} {s : Set ℝ} {t : ℝ} (hs : UniqueDiffWithinAt ℝ s t)
    (hδ : IsMIntegralCurveOn δ
      ((CotangentBundle.symplecticForm I M).hamiltonianVectorField h.hamiltonian) s)
    (ht : t ∈ s) :
    δ t = legendreMap L (Manifold.curveVelocityLiftWithin I (fun r ↦ (δ r).proj) s t) := by
  -- Pull `δ` back to an integral curve `FL⁻¹ ∘ δ` of the Lagrangian vector field.
  have hγ := h.isMIntegralCurveOn_legendreDiffeomorph_symm_comp hL hδ
  have hproj : (fun r ↦ (((h.legendreDiffeomorph hL).symm ∘ δ) r).proj) = fun r ↦ (δ r).proj :=
    funext fun r ↦ h.proj_legendreDiffeomorph_symm_apply hL (δ r)
  rw [← hproj, ← Manifold.eq_curveVelocityLiftWithin_of_hasMFDerivWithinAt hs (hγ t ht)
    (h.isRegularLagrangian.mfderiv_proj_hamiltonianVectorField_lagrangianEnergy hL _)]
  exact (h.legendreMap_legendreDiffeomorph_symm_apply hL (δ t)).symm

/-- **Hamilton's first equation for a hyperregular Lagrangian.** Along an integral curve `δ` of the
Hamiltonian vector field of `H = E_L ∘ FL⁻¹` on `T*M`, the covector `δ t` is the Legendre transform
`FL(c'(t))` of the velocity of the base curve `c = π ∘ δ`. -/
theorem eq_legendreMap_curveVelocityLift_of_isMIntegralCurve {δ : ℝ → CotangentBundle I M}
    (hδ : IsMIntegralCurve δ
      ((CotangentBundle.symplecticForm I M).hamiltonianVectorField h.hamiltonian))
    (t : ℝ) :
    δ t = legendreMap L (Manifold.curveVelocityLift I (fun s ↦ (δ s).proj) t) := by
  rw [← Manifold.curveVelocityLiftWithin_univ]
  exact h.eq_legendreMap_curveVelocityLiftWithin_of_isMIntegralCurveOn hL uniqueDiffWithinAt_univ
    (hδ.isMIntegralCurveOn _) (Set.mem_univ t)

end IsHyperregularLagrangian

/-! ### The Euler–Lagrange equations in bundle charts -/

section Chart

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] {L : TangentBundle I M → ℝ}

variable [I.Boundaryless]

/-- The Euler–Lagrange equations in the tangent-bundle chart at the current point of a local
integral curve of the Lagrangian vector field. -/
private theorem IsRegularLagrangian.eulerLagrange_extChartAt_self_of_isMIntegralCurveAt
    (hL : ContMDiff I.tangent 𝓘(ℝ, ℝ) ∞ L) (hreg : IsRegularLagrangian L)
    {X : (v : TangentBundle I M) → TangentSpace I.tangent v}
    (hX : (cartanTwoForm L hL).IsHamiltonianVectorField (lagrangianEnergy L) X)
    {γ : ℝ → TangentBundle I M} {t : ℝ} (hγ : IsMIntegralCurveAt γ X t) :
    HasDerivAt (fun s ↦ (extChartAt I.tangent (γ t) (γ s)).1)
        (extChartAt I.tangent (γ t) (γ t)).2 t ∧
      HasDerivAt (fun s ↦ fderiv ℝ (fun u ↦ L ((extChartAt I.tangent (γ t)).symm
          ((extChartAt I.tangent (γ t) (γ s)).1, u))) (extChartAt I.tangent (γ t) (γ s)).2)
        (fderiv ℝ (fun y ↦ L ((extChartAt I.tangent (γ t)).symm
          (y, (extChartAt I.tangent (γ t) (γ t)).2))) (extChartAt I.tangent (γ t) (γ t)).1) t := by
  set Φ := extChartAt I.tangent (γ t)
  have hchart : HasDerivAt (fun s ↦ ((Φ (γ s)).1, (Φ (γ s)).2)) (X (γ t)) t :=
    Manifold.hasDerivAt_extChartAt_comp_curve hγ.hasMFDerivAt
  -- The base component of `X (γ t)` is `γ t` itself, which is its own fibre coordinate.
  have hX₁ : (X (γ t)).1 = (Φ (γ t)).2 := by
    have h := hreg.mfderiv_proj_eq_snd_of_isHamiltonianVectorField hL hX (γ t)
    rw [Bundle.mfderiv_proj] at h
    rw [Manifold.extChartAt_tangent_self_snd, ← h]
    -- `dπ` is the first projection of `E × E`, read on the tangent space of `TM`.
    rfl
  exact eulerLagrange_of_hasDerivAt_of_symplecticForm (L := L ∘ Φ.symm)
    (((hL (γ t)).contDiffAt_comp_extChartAt_symm).of_le (by norm_num)) hchart hX₁ fun W ↦
    (eval₂_cartanTwoForm_eq_fderiv_linearLegendreMap hL (γ t) _ W).symm.trans
      ((SmoothTwoForm.isHamiltonianVectorField_iff.1 hX (γ t) W).trans
        (DFunLike.congr_fun (mvfderiv_lagrangianEnergy_eq_fderiv hL (by simp) (γ t)) W))

/-- **Integral curves of the Lagrangian vector field solve the Euler–Lagrange equations in every
chart.** Let `L` be a smooth regular Lagrangian on a boundaryless manifold, and let `γ` be an
integral curve, defined near `t`, of a Hamiltonian vector field `X` of the energy for the Cartan
two-form. Read `γ` in the tangent-bundle chart at any `w₀` whose source contains `γ t`, with
coordinates `(q s, v s)`, and let `ℓ = L ∘ (chart at w₀)⁻¹` be the local Lagrangian. Then
`q'(t) = v(t)` and `d/dt ∂_v ℓ(q, v) = ∂_q ℓ(q, v)` at `t`. -/
theorem IsRegularLagrangian.eulerLagrange_extChartAt_of_isMIntegralCurveAt
    (hL : ContMDiff I.tangent 𝓘(ℝ, ℝ) ∞ L) (hreg : IsRegularLagrangian L)
    {X : (v : TangentBundle I M) → TangentSpace I.tangent v}
    (hX : (cartanTwoForm L hL).IsHamiltonianVectorField (lagrangianEnergy L) X)
    {γ : ℝ → TangentBundle I M} {t : ℝ} (hγ : IsMIntegralCurveAt γ X t) (w₀ : TangentBundle I M)
    (ht : γ t ∈ (extChartAt I.tangent w₀).source) :
    HasDerivAt (fun s ↦ (extChartAt I.tangent w₀ (γ s)).1) (extChartAt I.tangent w₀ (γ t)).2 t ∧
      HasDerivAt (fun s ↦ fderiv ℝ (fun u ↦ L ((extChartAt I.tangent w₀).symm
          ((extChartAt I.tangent w₀ (γ s)).1, u))) (extChartAt I.tangent w₀ (γ s)).2)
        (fderiv ℝ (fun y ↦ L ((extChartAt I.tangent w₀).symm
          (y, (extChartAt I.tangent w₀ (γ t)).2))) (extChartAt I.tangent w₀ (γ t)).1) t := by
  -- The equations hold in the chart `Φ` at `γ t`. Near `t` the coordinates in `Φ` and in the chart
  -- `Ψ` at `w₀` are related by the tangent map of the change of base charts, which carries the
  -- equations from `Φ` to `Ψ`.
  obtain ⟨hq, hEL⟩ := hreg.eulerLagrange_extChartAt_self_of_isMIntegralCurveAt hL hX hγ
  set Ψ := extChartAt I.tangent w₀
  set Φ := extChartAt I.tangent (γ t)
  -- The changes of base charts between the two tangent charts, in both directions.
  set φ := extChartAt I (γ t).proj ∘ (extChartAt I w₀.proj).symm
  set ψ := extChartAt I w₀.proj ∘ (extChartAt I (γ t).proj).symm
  have htΦ : γ t ∈ Φ.source := mem_extChartAt_source _
  have hev : ∀ᶠ s in 𝓝 t, γ s ∈ Ψ.source ∧ γ s ∈ Φ.source :=
    hγ.hasMFDerivAt.continuousAt.eventually
      (Filter.inter_mem (extChartAt_source_mem_nhds' ht) (extChartAt_source_mem_nhds' htΦ))
  have hΦ : ∀ᶠ s in 𝓝 t, Φ (γ s) = (φ (Ψ (γ s)).1, fderiv ℝ φ (Ψ (γ s)).1 (Ψ (γ s)).2) :=
    hev.mono fun s hs ↦ Manifold.extChartAt_tangent_eq_fderiv hs.1 hs.2
  have hΨ : ∀ᶠ s in 𝓝 t, Ψ (γ s) = (ψ (Φ (γ s)).1, fderiv ℝ ψ (Φ (γ s)).1 (Φ (γ s)).2) :=
    hev.mono fun s hs ↦ Manifold.extChartAt_tangent_eq_fderiv hs.2 hs.1
  have hbase₀ : (γ t).proj ∈ (extChartAt I w₀.proj).source :=
    ((Bundle.mem_extChartAt_source_iff w₀ (γ t)).1 ht).2
  have hbase : (γ t).proj ∈ (extChartAt I (γ t).proj).source := mem_extChartAt_source _
  -- Both changes of base charts are smooth at the relevant points.
  have hψ : ContDiffAt ℝ ∞ ψ (Φ (γ t)).1 :=
    contDiffAt_ext_coord_change _ _ (PartialEquiv.mem_symm_trans_source _ hbase hbase₀)
  have hφ : ContDiffAt ℝ ∞ φ (Ψ (γ t)).1 :=
    contDiffAt_ext_coord_change _ _ (PartialEquiv.mem_symm_trans_source _ hbase₀ hbase)
  -- The base coordinate in the chart at `w₀` has velocity the fibre coordinate there.
  have hq₀ : HasDerivAt (fun s ↦ (Ψ (γ s)).1) (Ψ (γ t)).2 t := by
    have h := (hψ.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt_of_eq t hq rfl
    have hΨt := hΨ.self_of_nhds
    rw [hΨt]
    exact h.congr_of_eventuallyEq (hΨ.mono fun s hs ↦ congrArg Prod.fst hs)
  refine ⟨hq₀, ?_⟩
  -- The Euler–Lagrange equation in the chart at `γ t` transfers to the chart at `w₀` along the
  -- change of coordinates `φ`, whose tangent map relates the two local Lagrangians.
  refine eulerLagrange_of_comp (L := fun _ ↦ L ∘ Ψ.symm) (L' := fun _ ↦ L ∘ Φ.symm) hq₀
    (hφ.of_le (by norm_num)) ?_ ?_ ?_
  · filter_upwards [hev] with s hs
    exact (Manifold.extChartAt_tangent_symm_eventuallyEq hs.1 hs.2).fun_comp L
  · have hsmooth : ∀ᶠ y in 𝓝 (Φ (γ t)), ContDiffAt ℝ 2 (L ∘ Φ.symm) y :=
      ((hL (γ t)).contDiffAt_comp_extChartAt_symm.of_le (by norm_num)).eventually (by simp)
    filter_upwards
      [((continuousAt_extChartAt (γ t)).comp hγ.hasMFDerivAt.continuousAt).eventually hsmooth, hΦ]
      with s hs hs'
    rw [← hs']
    exact hs.differentiableAt (by norm_num)
  · have hEq : (fun s ↦ fderiv ℝ (fun u ↦ (L ∘ Φ.symm) (φ (Ψ (γ s)).1, u))
        (fderiv ℝ φ (Ψ (γ s)).1 (Ψ (γ s)).2)) =ᶠ[𝓝 t]
        fun s ↦ fderiv ℝ (fun u ↦ L (Φ.symm ((Φ (γ s)).1, u))) (Φ (γ s)).2 :=
      hΦ.mono fun s hs ↦ by simp only [hs, Function.comp_apply]
    have ht' := hΦ.self_of_nhds
    rw [Prod.ext_iff] at ht'
    simp only [ht'.1, ht'.2] at hEL
    exact hEL.congr_of_eventuallyEq hEq

end Chart

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.LagrangianVectorField
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Legendre.Chart
import TauCeti.Geometry.Manifold.ContMDiff.Atlas
import TauCeti.Geometry.Manifold.VectorBundle.Submersion
import TauCeti.Geometry.Manifold.VectorBundle.Tangent.ChartChange
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import TauCeti.Geometry.Symplectic.Hamiltonian.EulerLagrange.Covariance

/-!
# The Lagrangian vector field solves the Euler–Lagrange equations in bundle charts

Let `L : TM → ℝ` be a smooth regular Lagrangian on a boundaryless manifold `M`, with energy `E_L`
and Cartan two-form `ω_L = FL^*ω`. Its Lagrangian vector field `X_E` is the Hamiltonian vector
field of `E_L` for `ω_L`, `ι_(X_E) ω_L = dE_L`. This file proves that the integral curves of `X_E`
solve the Euler–Lagrange equations in every preferred chart of `TM`: read a curve `γ` in `TM` in
such a chart, as `(q(s), v(s))`, and write `ℓ(q, v)` for `L` read in the same chart.
Then

`q' = v` and `d/ds ∂_v ℓ(q, v) = ∂_q ℓ(q, v)`

(`TauCeti.IsRegularLagrangian.eulerLagrange_extChartAt_of_isMIntegralCurve`), in the form of the
Euler–Lagrange equations of `TauCeti.hasDerivAt_noetherCharge` and
`TauCeti.eulerLagrange_iff_of_comp`.

The proof is pointwise. At a tangent vector `z₀`, in the chart at `z₀`, the Legendre map is
`(q, v) ↦ (q, P(q, v))` with momentum `P = ∂_v ℓ`, and the canonical form `ω` is the linear form
`ω((q, p), (q', p')) = p'(q) - p(q')`
(`TauCeti.CotangentBundle.eval₂_symplecticForm`). So for `X = (a, b)` and `Y = (δq, δv)`,

`ω_L(X, Y) = DP(Y)(a) - DP(X)(δq)` and `dE_L(Y) = DP(Y)(v₀) - ∂_q ℓ(δq)`

(`TauCeti.hasMFDerivAt_legendreMap`, `TauCeti.mvfderiv_lagrangianEnergy_apply`). Since `X_E` is
second order, `a = v₀` (`TauCeti.mfderiv_proj_eq_snd_of_eval₂_cartanTwoForm`), and the equation
`ι_X ω_L = dE_L` becomes `DP(X) = ∂_q ℓ`: the derivative of the momentum along `X` is the force
(`TauCeti.eulerLagrange_extChartAt_of_eval₂_cartanTwoForm`). Along an integral curve the chart
velocity at `t` in the chart at `γ t` is `X`, which gives the Euler–Lagrange equations in that
chart. Their covariance under changes of coordinates (`TauCeti.eulerLagrange_of_comp`), with the
change of tangent-bundle charts `(q, u) ↦ (φ q, Dφ_q u)`
(`TauCeti.Manifold.extChartAt_tangent_extChartAt_symm`), transports them to every preferred chart
whose domain contains `γ t` (`TauCeti.eulerLagrange_extChartAt_of_hasMFDerivAt`).

## Main results

* `TauCeti.eulerLagrange_extChartAt_of_eval₂_cartanTwoForm`: pointwise, in the chart at `z₀`, a
  vector `X` with `ι_X ω_L = dE_L` has base component `v₀` and differentiates the momentum to the
  force.
* `TauCeti.eulerLagrange_extChartAt_of_hasMFDerivAt`: a curve with such a velocity at `t` solves
  the Euler–Lagrange equations at `t` in every preferred chart of `TM` around `γ t`.
* `TauCeti.IsRegularLagrangian.eulerLagrange_extChartAt_of_isMIntegralCurve`,
  `TauCeti.IsRegularLagrangian.eulerLagrange_extChartAt_of_isMIntegralCurve_hamiltonianVectorField`:
  integral curves of the Lagrangian vector field of a smooth regular Lagrangian solve the
  Euler–Lagrange equations in every preferred chart of `TM` around them.

## References

* R. Abraham, J. E. Marsden, *Foundations of Mechanics*, 2nd ed., Benjamin/Cummings, 1978,
  Section 3.5 (the Lagrangian vector field of a regular Lagrangian and the Euler–Lagrange
  equations in local coordinates).
* J. E. Marsden, T. S. Ratiu, *Introduction to Mechanics and Symmetry*, 2nd ed., Texts in Applied
  Mathematics 17, Springer, 1999, Section 7.3.
-/

public section

noncomputable section

open Bundle Set Filter
open scoped Manifold ContDiff Topology

namespace TauCeti

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless] {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] {L : TangentBundle I M → ℝ}

/-- **The Euler–Lagrange equations at a point, in coordinates.** Let `L` be a smooth Lagrangian
on a boundaryless manifold, with invertible fibre Hessian at `z₀`, and let `X` be a tangent vector
of `TM` at `z₀` with `ι_X ω_L = dE_L`. Read `TM` in the chart at `z₀`, with `ℓ` the coordinate
expression of `L` and `z₀ = (q₀, v₀)`. Then the base component of `X` is `v₀`, and the momentum
`(q, v) ↦ ∂_v ℓ(q, v)` has derivative `∂_q ℓ(q₀, v₀)` along `X`. -/
theorem eulerLagrange_extChartAt_of_eval₂_cartanTwoForm
    (hL : ContMDiff I.tangent 𝓘(ℝ, ℝ) ∞ L) {z₀ : TangentBundle I M}
    (hv : (fiberHessian L z₀).IsInvertible) {X : TangentSpace I.tangent z₀}
    (hX : ∀ Y, SmoothBundleForm.eval₂ (cartanTwoForm L hL) z₀ X Y =
      mvfderiv I.tangent (lagrangianEnergy L) z₀ Y) :
    X.1 = (extChartAt I.tangent z₀ z₀).2 ∧
      fderiv ℝ (fun p : E × E ↦
        fderiv ℝ (fun u ↦ L ((extChartAt I.tangent z₀).symm (p.1, u))) p.2)
          (extChartAt I.tangent z₀ z₀) X =
        fderiv ℝ (fun q ↦ L ((extChartAt I.tangent z₀).symm (q, (extChartAt I.tangent z₀ z₀).2)))
          (extChartAt I.tangent z₀ z₀).1 := by
  -- In its own chart, the fibre coordinate of `z₀` is `z₀.2`.
  have hp₀ : (extChartAt I.tangent z₀ z₀).2 = z₀.2 := by
    have hb := FiberBundle.mem_baseSet_trivializationAt' (F := E) (E := TangentSpace I) z₀.proj
    rw [Bundle.extChartAt_apply_of_mem_baseSet z₀ hb]
    exact ((trivializationAt E (TangentSpace I) z₀.proj).continuousLinearMapAt_apply_of_mem
      (R := ℝ) hb z₀.2).symm.trans (Manifold.continuousLinearMapAt_trivializationAt_self _ _)
  set p₀ := extChartAt I.tangent z₀ z₀
  set DP := fderiv ℝ (fun p : E × E ↦
    fderiv ℝ (fun u ↦ L ((extChartAt I.tangent z₀).symm (p.1, u))) p.2) p₀
  -- The base component of `X` is the fibre coordinate of `z₀`: `X_E` is second order.
  have hX1 : X.1 = p₀.2 := by
    have h := mfderiv_proj_eq_snd_of_eval₂_cartanTwoForm hL hv hX
    rw [Bundle.mfderiv_proj] at h
    exact h.trans hp₀.symm
  refine ⟨hX1, ContinuousLinearMap.ext fun a ↦ ?_⟩
  -- In charts `dFL = (fst, DP)`, and `ω` is the linear cotangent form.
  have hdFL := (hasMFDerivAt_legendreMap hL (by simp) z₀).mfderiv
  have h := hX ((a, 0) : TangentSpace I.tangent z₀)
  rw [mvfderiv_lagrangianEnergy_apply hL (by simp) z₀,
    ← mpullback_legendreMap_symplecticForm hL] at h
  have h2 := SmoothForm.eval₂_mpullback (legendreMap L) (contMDiff_legendreMap hL le_rfl)
    (CotangentBundle.symplecticForm I M) z₀ X ((a, 0) : TangentSpace I.tangent z₀)
  have hω : ∀ b c : TangentSpace (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (legendreMap L z₀),
      SmoothBundleForm.eval₂ (CotangentBundle.symplecticForm I M) (legendreMap L z₀) b c =
        c.2 b.1 - b.2 c.1 := fun b c ↦
    (CotangentBundle.eval₂_symplecticForm _ b c).trans (strongDualCotangentSymplecticForm_apply b c)
  rw [h2, hω, hdFL] at h
  -- Tangent vectors at `z₀` and at `FL z₀` are pairs of model vectors, so the components of
  -- `(fst, DP)` applied to them are read off directly.
  have h' : DP (a, 0) X.1 - DP X a = DP (a, 0) p₀.2 -
      fderiv ℝ (fun q ↦ L ((extChartAt I.tangent z₀).symm (q, p₀.2))) p₀.1 a := h
  rw [hX1] at h'
  linarith

/-- The Euler–Lagrange equations along a curve with velocity `X` at `t`, in the chart at `γ t`. -/
private theorem eulerLagrange_extChartAt_self_of_hasMFDerivAt
    (hL : ContMDiff I.tangent 𝓘(ℝ, ℝ) ∞ L)
    {γ : ℝ → TangentBundle I M} {t : ℝ} (hv : (fiberHessian L (γ t)).IsInvertible)
    {X : TangentSpace I.tangent (γ t)}
    (hX : ∀ Y, SmoothBundleForm.eval₂ (cartanTwoForm L hL) (γ t) X Y =
      mvfderiv I.tangent (lagrangianEnergy L) (γ t) Y)
    (hγ : HasMFDerivAt 𝓘(ℝ, ℝ) I.tangent γ t ((1 : ℝ →L[ℝ] ℝ).smulRight X)) :
    HasDerivAt (fun s ↦ (extChartAt I.tangent (γ t) (γ s)).1)
        (extChartAt I.tangent (γ t) (γ t)).2 t ∧
      HasDerivAt (fun s ↦ fderiv ℝ (fun u ↦ L ((extChartAt I.tangent (γ t)).symm
          ((extChartAt I.tangent (γ t) (γ s)).1, u))) (extChartAt I.tangent (γ t) (γ s)).2)
        (fderiv ℝ (fun q ↦ L ((extChartAt I.tangent (γ t)).symm
          (q, (extChartAt I.tangent (γ t) (γ t)).2))) (extChartAt I.tangent (γ t) (γ t)).1) t := by
  obtain ⟨hX1, hEL⟩ := eulerLagrange_extChartAt_of_eval₂_cartanTwoForm hL hv hX
  -- In the chart at `γ t`, the curve has velocity `X`.
  have hc : HasDerivAt (extChartAt I.tangent (γ t) ∘ γ) X t :=
    Manifold.hasDerivAt_extChartAt_comp_curve hγ
  refine ⟨hX1 ▸ (hasFDerivAt_fst.comp_hasDerivAt (f := extChartAt I.tangent (γ t) ∘ γ) t hc :),
    ?_⟩
  have hP := ((contDiffAt_momentum_extChartAt hL (by simp) (γ t)).differentiableAt
    one_ne_zero).hasFDerivAt.comp_hasDerivAt t hc
  rw [← hEL]
  exact hP

/-- **The Euler–Lagrange equations in every chart, along a curve.** Let `L` be a smooth
Lagrangian on a boundaryless manifold, and let `γ` be a curve in `TM` whose velocity `X` at `t`
satisfies `ι_X ω_L = dE_L`, where the fibre Hessian of `L` at `γ t` is invertible. Read `γ` in a
preferred chart of `TM` whose domain contains `γ t`, as `(q(s), v(s))`, and let `ℓ` be `L` read
in the same chart. Then at `t`, `q' = v` and `d/ds ∂_v ℓ(q, v) = ∂_q ℓ(q, v)`. -/
theorem eulerLagrange_extChartAt_of_hasMFDerivAt (hL : ContMDiff I.tangent 𝓘(ℝ, ℝ) ∞ L)
    {γ : ℝ → TangentBundle I M} {t : ℝ} (hv : (fiberHessian L (γ t)).IsInvertible)
    {X : TangentSpace I.tangent (γ t)}
    (hX : ∀ Y, SmoothBundleForm.eval₂ (cartanTwoForm L hL) (γ t) X Y =
      mvfderiv I.tangent (lagrangianEnergy L) (γ t) Y)
    (hγ : HasMFDerivAt 𝓘(ℝ, ℝ) I.tangent γ t ((1 : ℝ →L[ℝ] ℝ).smulRight X))
    {z : TangentBundle I M} (hz : γ t ∈ (extChartAt I.tangent z).source) :
    HasDerivAt (fun s ↦ (extChartAt I.tangent z (γ s)).1) (extChartAt I.tangent z (γ t)).2 t ∧
      HasDerivAt (fun s ↦ fderiv ℝ (fun u ↦ L ((extChartAt I.tangent z).symm
          ((extChartAt I.tangent z (γ s)).1, u))) (extChartAt I.tangent z (γ s)).2)
        (fderiv ℝ (fun q ↦ L ((extChartAt I.tangent z).symm
          (q, (extChartAt I.tangent z (γ t)).2))) (extChartAt I.tangent z (γ t)).1) t := by
  obtain ⟨hq₀, hEL₀⟩ := eulerLagrange_extChartAt_self_of_hasMFDerivAt hL hv hX hγ
  set z₀ := γ t
  set c₀ := extChartAt I.tangent z₀
  set c := extChartAt I.tangent z
  -- The change of base charts from `z` to `z₀`.
  set φ := extChartAt I z₀.proj ∘ (extChartAt I z.proj).symm
  have hz₀ : z₀ ∈ c₀.source := mem_extChartAt_source z₀
  have hev : ∀ᶠ s in 𝓝 t, γ s ∈ c₀.source ∩ c.source :=
    hγ.continuousAt.preimage_mem_nhds
      (inter_mem (extChartAt_source_mem_nhds' hz₀) (extChartAt_source_mem_nhds' hz))
  -- Near `t`, the chart readings of the curve are related by the tangent chart change.
  have hc₀ : ∀ᶠ s in 𝓝 t, c₀ (γ s) = (φ (c (γ s)).1, fderiv ℝ φ (c (γ s)).1 (c (γ s)).2) :=
    Manifold.eventually_extChartAt_tangent_eq hγ.continuousAt hz hz₀
  have hzb := (mem_extChartAt_source_iff z z₀).1 hz
  have hz₀b := (mem_extChartAt_source_iff z₀ z₀).1 hz₀
  have hφ : ContDiffAt ℝ 2 φ (c z₀).1 := by
    rw [extChartAt_apply_of_mem_baseSet z hzb.1]
    exact contDiffAt_extChartAt_comp_extChartAt_symm hzb.2 hz₀b.2
  have hq : HasDerivAt (fun s ↦ (c (γ s)).1) (c z₀).2 t :=
    Manifold.hasDerivAt_extChartAt_tangent_fst hγ.continuousAt hz₀ hz hq₀
  refine ⟨hq, ?_⟩
  -- Near the curve, the Lagrangian read in the chart at `z` is the one read in the chart at `z₀`
  -- composed with the tangent map of `φ`.
  have hrel : ∀ᶠ s in 𝓝 t, (fun p ↦ L (c.symm p)) =ᶠ[𝓝 ((c (γ s)).1, (c (γ s)).2)]
      fun y ↦ L (c₀.symm (φ y.1, fderiv ℝ φ y.1 y.2)) := by
    filter_upwards [hev] with s hs
    exact Manifold.eventuallyEq_comp_extChartAt_tangent_symm (c.map_source hs.2)
      (by rw [c.left_inv hs.2]; exact hs.1)
  have hℓ₀ : ContDiffOn ℝ ∞ (fun p ↦ L (c₀.symm p)) c₀.target :=
    contMDiffOn_iff_contDiffOn.1 (hL.comp_contMDiffOn (contMDiffOn_extChartAt_symm z₀))
  have hdiff : ∀ᶠ s in 𝓝 t, DifferentiableAt ℝ (fun p ↦ L (c₀.symm p))
      (φ (c (γ s)).1, fderiv ℝ φ (c (γ s)).1 (c (γ s)).2) := by
    filter_upwards [hev, hc₀] with s hs hs'
    rw [← hs']
    exact (hℓ₀.contDiffAt ((isOpen_extChartAt_target z₀).mem_nhds (c₀.map_source hs.1))
      ).differentiableAt (by simp)
  -- The Euler–Lagrange equation in the chart at `z₀`, along the chart change of the curve.
  have hct₀ : c₀ z₀ = (φ (c z₀).1, fderiv ℝ φ (c z₀).1 (c z₀).2) := hc₀.self_of_nhds
  have hEL : HasDerivAt (fun s ↦ fderiv ℝ (fun u ↦ L (c₀.symm (φ (c (γ s)).1, u)))
      (fderiv ℝ φ (c (γ s)).1 (c (γ s)).2))
      (fderiv ℝ (fun y ↦ L (c₀.symm (y, fderiv ℝ φ (c z₀).1 (c z₀).2))) (φ (c z₀).1)) t := by
    have h1 : (c₀ z₀).1 = φ (c z₀).1 := congrArg Prod.fst hct₀
    have h2 : (c₀ z₀).2 = fderiv ℝ φ (c z₀).1 (c z₀).2 := congrArg Prod.snd hct₀
    rw [← h1, ← h2]
    exact hEL₀.congr_of_eventuallyEq (hc₀.mono fun s hs ↦ by simp only [hs])
  exact eulerLagrange_of_comp (L := fun _ p ↦ L (c.symm p)) (L' := fun _ p ↦ L (c₀.symm p))
    hq hφ hrel hdiff hEL

namespace IsRegularLagrangian

variable (hL : ContMDiff I.tangent 𝓘(ℝ, ℝ) ∞ L) (hreg : IsRegularLagrangian L)
include hreg

/-- **Integral curves of the Lagrangian vector field solve the Euler–Lagrange equations.** For a
smooth regular Lagrangian on a boundaryless manifold, an integral curve `γ` of a Hamiltonian
vector field of the energy for the Cartan two-form, read in any preferred chart of `TM` whose
domain contains `γ t` as `(q, v)`, satisfies at `t` the Euler–Lagrange equations `q' = v` and
`d/ds ∂_v ℓ(q, v) = ∂_q ℓ(q, v)` of `L` read in that chart. -/
theorem eulerLagrange_extChartAt_of_isMIntegralCurve
    {X : (v : TangentBundle I M) → TangentSpace I.tangent v}
    (hX : (cartanTwoForm L hL).IsHamiltonianVectorField (lagrangianEnergy L) X)
    {γ : ℝ → TangentBundle I M} (hγ : IsMIntegralCurve γ X) {t : ℝ} {z : TangentBundle I M}
    (hz : γ t ∈ (extChartAt I.tangent z).source) :
    HasDerivAt (fun s ↦ (extChartAt I.tangent z (γ s)).1) (extChartAt I.tangent z (γ t)).2 t ∧
      HasDerivAt (fun s ↦ fderiv ℝ (fun u ↦ L ((extChartAt I.tangent z).symm
          ((extChartAt I.tangent z (γ s)).1, u))) (extChartAt I.tangent z (γ s)).2)
        (fderiv ℝ (fun q ↦ L ((extChartAt I.tangent z).symm
          (q, (extChartAt I.tangent z (γ t)).2))) (extChartAt I.tangent z (γ t)).1) t :=
  eulerLagrange_extChartAt_of_hasMFDerivAt hL (isRegularLagrangian_iff.1 hreg (γ t))
    (SmoothTwoForm.isHamiltonianVectorField_iff.1 hX (γ t)) (hγ t) hz

/-- **Integral curves of the Lagrangian vector field `X_E` solve the Euler–Lagrange
equations.** For a smooth regular Lagrangian on a finite-dimensional boundaryless manifold, every
integral curve of the Hamiltonian vector field of the energy for the symplectic Cartan two-form
satisfies the Euler–Lagrange equations in every preferred chart of `TM` containing its value. -/
theorem eulerLagrange_extChartAt_of_isMIntegralCurve_hamiltonianVectorField
    [FiniteDimensional ℝ E] {γ : ℝ → TangentBundle I M}
    (hγ : IsMIntegralCurve γ ((cartanTwoForm L hL).hamiltonianVectorField (lagrangianEnergy L)))
    {t : ℝ} {z : TangentBundle I M} (hz : γ t ∈ (extChartAt I.tangent z).source) :
    HasDerivAt (fun s ↦ (extChartAt I.tangent z (γ s)).1) (extChartAt I.tangent z (γ t)).2 t ∧
      HasDerivAt (fun s ↦ fderiv ℝ (fun u ↦ L ((extChartAt I.tangent z).symm
          ((extChartAt I.tangent z (γ s)).1, u))) (extChartAt I.tangent z (γ s)).2)
        (fderiv ℝ (fun q ↦ L ((extChartAt I.tangent z).symm
          (q, (extChartAt I.tangent z (γ t)).2))) (extChartAt I.tangent z (γ t)).1) t :=
  hreg.eulerLagrange_extChartAt_of_isMIntegralCurve hL
    ((hreg.isSymplectic_cartanTwoForm hL).isNondegenerate
      |>.isHamiltonianVectorField_hamiltonianVectorField _) hγ hz

end IsRegularLagrangian
end TauCeti

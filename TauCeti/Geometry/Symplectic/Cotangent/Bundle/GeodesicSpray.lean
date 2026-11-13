/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Trajectory
public import TauCeti.Geometry.Manifold.Flow.Diffeomorph
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Nondegenerate.Christoffel
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Cogeodesic
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Hyperregular
import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Riesz
import TauCeti.Analysis.Calculus.Bilinear
import TauCeti.Analysis.Calculus.FDeriv.Prod
import TauCeti.Geometry.Manifold.VectorBundle.NondegenerateMetric.Musical

/-!
# The geodesic spray is the Lagrangian vector field of the kinetic energy

Let `g` be a smooth symmetric nondegenerate metric on a finite-dimensional manifold `M`, of any
signature (`TauCeti.Manifold.ContMDiffNondegenerateMetric`), and let
`L(v) = ½ g(v, v)` be its kinetic Lagrangian (`TauCeti.mechanicalLagrangian g 0`). Its Legendre
map `FL(v) = g(v, ·)` pulls the canonical symplectic form of `T*M` back to the Cartan two-form
`ω_L` on `TM`, and the *Lagrangian vector field* is the Hamiltonian vector field `X_E` of the energy
`E_L(v) = ½ g(v, v)` for `ω_L`, with `ι_(X_E) ω_L = dE_L`.

This file proves that `X_E` is the spray of the Levi-Civita connection of `g`: read in the chart
of `TM` at a tangent vector `v` at `x`, it is

`X_E(v) = (v, -Γ_x(v, v))`,

where `Γ` is the Christoffel map of any Levi-Civita connection of `g` in the trivialization at `x`
(`IsLeviCivitaConnection.hamiltonianVectorField_lagrangianEnergy_mechanicalLagrangian_zero`, in the
namespace `TauCeti.Manifold.ContMDiffNondegenerateMetric` like the other results on `g`).
The computation takes place in the chart at `v`, where `FL(q, u) = (q, G(q) u)` and
`E_L(q, u) = ½ G(q)(u, u)` for the chart metric `G`. The canonical form gives
`ω_L((a, b), (a', b')) = (G b' + DG(a') u)(a) - (G b + DG(a) u)(a')` at `(q, u)`, and metric
compatibility in coordinates, `DG(a)(v, w) = G(Γ(v, a), w) + G(v, Γ(w, a))`, together with the
symmetry of `G` and of `Γ` (torsion freeness) turns `ω_L((u, -Γ(u, u)), ·)` into `dE_L`
(`IsLeviCivitaConnection.eval₂_cartanTwoForm_mechanicalLagrangian_zero`).
This pointwise identity holds at boundary and corner points as well; identifying `X_E` itself uses
the nondegeneracy of `ω_L`, which is known on boundaryless tangent bundles.

For a Riemannian metric, given by the ambient Riemannian bundle instance, the Levi-Civita
connection is Mathlib's `CovariantDerivative.leviCivitaConnection`, so the Lagrangian vector field
of `½ ‖v‖²` is the geodesic spray `TauCeti.Manifold.geodesicSpray`
(`TauCeti.hamiltonianVectorField_lagrangianEnergy_eq_geodesicSpray`). The Hamiltonian of this
hyperregular Lagrangian is the kinetic energy `‖p‖² / 2` of covectors
(`TauCeti.IsHyperregularLagrangian.hamiltonian_eq_kineticEnergy`), so the Legendre map carries the
geodesic spray to the cogeodesic field, the Hamiltonian vector field of the kinetic energy for the
canonical symplectic form (`TauCeti.mfderiv_legendreMap_geodesicSpray`). Hence the metric geodesic
flow is the kinetic Hamiltonian flow: a `C²` curve `γ` is a geodesic exactly when the Legendre
transform `t ↦ g(γ'(t), ·)` of its velocity is an integral curve of the cogeodesic field.
The equivalence also holds within any parameter set with unique derivatives
(`TauCeti.isMIntegralCurveOn_legendreMap_comp_curveVelocityLiftWithin_iff`). On a boundaryless
manifold every kinetic Hamiltonian trajectory projects to a geodesic, and the Legendre map
conjugates the maximal flows and their domains, by `Diffeomorph.apply_flowOf` and
`Diffeomorph.mem_flowDomain_apply_iff`; no geodesic completeness is assumed.

## Main results

In the namespace `TauCeti.Manifold.ContMDiffNondegenerateMetric`:

* `isHyperregularLagrangian_mechanicalLagrangian`: the mechanical Lagrangian of a nondegenerate
  metric is hyperregular.
* `IsLeviCivitaConnection.hamiltonianVectorField_lagrangianEnergy_mechanicalLagrangian_zero`: the
  Lagrangian vector field of the kinetic Lagrangian is the spray `(v, -Γ(v, v))`.

In the namespace `TauCeti`:

* `TauCeti.hamiltonianVectorField_lagrangianEnergy_eq_geodesicSpray`: for a Riemannian metric it is
  the geodesic spray.
* `TauCeti.mfderiv_legendreMap_geodesicSpray`: the Legendre map carries the geodesic spray to the
  cogeodesic field.
* `TauCeti.isMIntegralCurve_legendreMap_comp_curveVelocityLift_iff`: a `C²` curve is a geodesic
  exactly when the Legendre transform of its velocity lift is an integral curve of the
  cogeodesic field.
* `TauCeti.isMIntegralCurveOn_legendreMap_comp_curveVelocityLiftWithin_iff`: the equivalence on
  parameter sets, including finite-lifetime geodesics.
* `TauCeti.isGeodesicCurveOn_proj_of_isMIntegralCurveOn_kineticEnergy`: arbitrary kinetic
  Hamiltonian trajectories project to geodesics.
* `TauCeti.legendreMap_flowOf_geodesicSpray` and
  `TauCeti.mem_flowDomain_kineticEnergy_legendreMap_iff`: conjugacy of the maximal flows and
  identification of their time domains with the maximal geodesic interval.

## References

* R. Abraham, J. E. Marsden, *Foundations of Mechanics*, 2nd ed., Benjamin/Cummings, 1978,
  Section 3.7 (the geodesic spray as the Lagrangian vector field of the kinetic energy).
* J. E. Marsden, T. S. Ratiu, *Introduction to Mechanics and Symmetry*, 2nd ed., Texts in Applied
  Mathematics 17, Springer, 1999, Section 7.5.
-/

public section

noncomputable section

open Bundle Set Filter
open scoped Manifold Topology ContDiff

namespace TauCeti

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

/-- A mechanical Lagrangian has the regularity of its potential, since the metric is smooth. -/
theorem Manifold.ContMDiffNondegenerateMetric.contMDiff_mechanicalLagrangian
    (g : Manifold.ContMDiffNondegenerateMetric (I := I) (M := M))
    {n : WithTop ℕ∞} {V : M → ℝ} (hn : n ≤ ∞) (hV : ContMDiff I 𝓘(ℝ) n V) :
    ContMDiff I.tangent 𝓘(ℝ) n (mechanicalLagrangian g V) :=
  TauCeti.contMDiff_mechanicalLagrangian (g.contMDiff.of_le hn) hV

/-- The kinetic Lagrangian is smooth because the metric is smooth and the potential is zero. -/
theorem Manifold.ContMDiffNondegenerateMetric.contMDiff_mechanicalLagrangian_zero
    (g : Manifold.ContMDiffNondegenerateMetric (I := I) (M := M)) :
    ContMDiff I.tangent 𝓘(ℝ) ∞ (mechanicalLagrangian g 0) :=
  g.contMDiff_mechanicalLagrangian le_rfl contMDiff_const

/-! ### Chart formulas -/

section Chart

variable (g : Manifold.ContMDiffNondegenerateMetric (I := I) (M := M))

/-- **The Legendre map of a mechanical Lagrangian in a chart.** Read in the preferred charts at
`z` and at its Legendre transform, it is `(q, u) ↦ (q, G(q) u)`, for the chart metric `G` of
`g` at `z.proj`. -/
private theorem writtenInExtChartAt_legendreMap_mechanicalLagrangian (V : M → ℝ)
    (z : TangentBundle I M) {w : E × E} (hw : w ∈ (extChartAt I.tangent z).target) :
    writtenInExtChartAt I.tangent (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) z
        (legendreMap (mechanicalLagrangian g V)) w =
      (w.1, g.chartMetric z.proj w.1 w.2) := by
  have hw1 := fst_mem_extChartAt_target z hw
  have hb := TangentBundle.extChartAt_symm_mem_trivializationAt_baseSet hw1
  rw [writtenInExtChartAt, Function.comp_apply, Function.comp_apply,
    extChartAt_symm_apply_of_mem_baseSet z hb w.2, CotangentBundle.extChartAt_apply,
    legendreMap_mechanicalLagrangian_snd g.apply_comm V, proj_legendreMap,
    proj_legendreMap]
  refine Prod.ext ((extChartAt I z.proj).right_inv hw1) (ContinuousLinearMap.ext fun u ↦ ?_)
  rw [g.chartMetric_apply hw1, ContinuousLinearMap.comp_apply, Trivialization.symmL_apply _ hb]

/-- **The energy of the kinetic Lagrangian in a chart** is `(q, u) ↦ ½ G(q)(u, u)`. -/
private theorem writtenInExtChartAt_lagrangianEnergy_mechanicalLagrangian_zero
    (z : TangentBundle I M)
    {w : E × E} (hw : w ∈ (extChartAt I.tangent z).target) :
    writtenInExtChartAt I.tangent 𝓘(ℝ) z (lagrangianEnergy (mechanicalLagrangian g 0)) w =
      2⁻¹ * g.chartMetric z.proj w.1 w.2 w.2 := by
  rw [writtenInExtChartAt, Function.comp_apply, Function.comp_apply, extChartAt_model_space_eq_id,
    PartialEquiv.refl_coe, id_eq, extChartAt_symm_apply_of_mem_baseSet z
      (TangentBundle.extChartAt_symm_mem_trivializationAt_baseSet
        (fst_mem_extChartAt_target z hw)) w.2,
    lagrangianEnergy_mechanicalLagrangian,
    g.chartMetric_apply (fst_mem_extChartAt_target z hw), Pi.zero_apply, add_zero]

/-- The derivative of the Legendre map of a mechanical Lagrangian at `(x, u)`, read in charts:
`(a, b) ↦ (a, G b + DG(a) u)` with `G` the chart metric at the chart image of `x`, `DG` its
derivative and `u` the tangent coordinate. -/
private def legendreChartDeriv (x : M) (u : E) : E × E →L[ℝ] E × (E →L[ℝ] ℝ) :=
  (ContinuousLinearMap.fst ℝ E E).prod
    ((g.chartMetric x (extChartAt I x x)).comp (ContinuousLinearMap.snd ℝ E E) +
      ((fderivWithin ℝ (g.chartMetric x) (extChartAt I x).target
        (extChartAt I x x)).comp (ContinuousLinearMap.fst ℝ E E)).flip u)

/-- The derivative of the energy of the kinetic Lagrangian at `(x, u)`, read in charts:
`(a, b) ↦ ½ (G(u, b) + G(b, u) + DG(a)(u, u))`. -/
private def energyChartDeriv (x : M) (u : E) : E × E →L[ℝ] ℝ :=
  (2⁻¹ : ℝ) • ((g.chartMetric x (extChartAt I x x) u).comp
      (ContinuousLinearMap.snd ℝ E E) +
    ((g.chartMetric x (extChartAt I x x)).comp (ContinuousLinearMap.snd ℝ E E) +
      ((fderivWithin ℝ (g.chartMetric x) (extChartAt I x).target
        (extChartAt I x x)).comp (ContinuousLinearMap.fst ℝ E E)).flip
          u).flip u)

@[simp]
private theorem legendreChartDeriv_apply (x : M) (u : E) (w : E × E) :
    legendreChartDeriv g x u w =
      (w.1, g.chartMetric x (extChartAt I x x) w.2 +
        fderivWithin ℝ (g.chartMetric x) (extChartAt I x).target
          (extChartAt I x x) w.1 u) := by
  simp only [legendreChartDeriv, ContinuousLinearMap.prod_apply, add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd']

@[simp]
private theorem energyChartDeriv_apply (x : M) (u : E) (w : E × E) :
    energyChartDeriv g x u w =
      2⁻¹ * (g.chartMetric x (extChartAt I x x) u w.2 +
        (g.chartMetric x (extChartAt I x x) w.2 u +
          fderivWithin ℝ (g.chartMetric x) (extChartAt I x).target
            (extChartAt I x x) w.1 u u)) := by
  simp only [energyChartDeriv, smul_apply, smul_eq_mul, add_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd']

/-- The Legendre map of a mechanical Lagrangian has derivative `legendreChartDeriv` in charts. -/
private theorem hasMFDerivAt_legendreMap_mechanicalLagrangian (V : M → ℝ)
    (z : TangentBundle I M) (hL : ContMDiff I.tangent 𝓘(ℝ) 2 (mechanicalLagrangian g V)) :
    HasMFDerivAt I.tangent (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (legendreMap (mechanicalLagrangian g V)) z
      (legendreChartDeriv g z.proj z.2) := by
  have hΦ := HasFDerivWithinAt.fst_prodMk_clm_apply_snd (E := E) (F := E)
    (p := ((extChartAt I z.proj z.proj : E), (z.2 : E)))
    ((g.contDiffOn_chartMetric z.proj _ (mem_extChartAt_target z.proj)).differentiableWithinAt
      (by simp)).hasFDerivWithinAt (fun _ ↦ fst_mem_extChartAt_target z)
  have hp := TangentBundle.extChartAt_self z
  -- On the chart target the chart expression is `(q, u) ↦ (q, G(q) u)`, and that target is a
  -- neighbourhood of the chart image of `z` within the range of the model.
  have h : HasFDerivWithinAt (writtenInExtChartAt I.tangent (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) z
      (legendreMap (mechanicalLagrangian g V))) (legendreChartDeriv g z.proj z.2) (range I.tangent)
      (extChartAt I.tangent z z) := by
    rw [hp]
    refine (hasFDerivWithinAt_inter' (hp ▸ extChartAt_target_mem_nhdsWithin z)).1 ?_
    refine (hΦ.mono inter_subset_right).congr (fun w hw ↦ ?_) ?_
    · exact writtenInExtChartAt_legendreMap_mechanicalLagrangian g V z hw.2
    · exact writtenInExtChartAt_legendreMap_mechanicalLagrangian g V z
        (hp ▸ mem_extChartAt_target z)
  exact ⟨(contMDiff_legendreMap (m := 0) hL (by norm_num) z).continuousAt,
    h.congr_fderiv (ContinuousLinearMap.ext fun _ ↦ rfl)⟩

/-- The energy of the kinetic Lagrangian has derivative `energyChartDeriv` in charts. -/
private theorem hasMFDerivAt_lagrangianEnergy_mechanicalLagrangian_zero (z : TangentBundle I M) :
    HasMFDerivAt I.tangent 𝓘(ℝ) (lagrangianEnergy (mechanicalLagrangian g 0)) z
      (energyChartDeriv g z.proj z.2) := by
  have hΦ := (HasFDerivWithinAt.comp_fst_clm_apply_snd_self (E := E) (F := E)
    (p := ((extChartAt I z.proj z.proj : E), (z.2 : E)))
    ((g.contDiffOn_chartMetric z.proj _ (mem_extChartAt_target z.proj)).differentiableWithinAt
      (by simp)).hasFDerivWithinAt (fun _ ↦ fst_mem_extChartAt_target z)).const_smul
    (2⁻¹ : ℝ)
  have hp := TangentBundle.extChartAt_self z
  have h : HasFDerivWithinAt (writtenInExtChartAt I.tangent 𝓘(ℝ) z
      (lagrangianEnergy (mechanicalLagrangian g 0))) (energyChartDeriv g z.proj z.2)
      (range I.tangent)
      (extChartAt I.tangent z z) := by
    rw [hp]
    refine (hasFDerivWithinAt_inter' (hp ▸ extChartAt_target_mem_nhdsWithin z)).1 ?_
    refine (hΦ.mono inter_subset_right).congr (fun w hw ↦ ?_) ?_
    · rw [writtenInExtChartAt_lagrangianEnergy_mechanicalLagrangian_zero g z hw.2, Pi.smul_apply,
        smul_eq_mul]
    · rw [writtenInExtChartAt_lagrangianEnergy_mechanicalLagrangian_zero g z
        (hp ▸ mem_extChartAt_target z), Pi.smul_apply, smul_eq_mul]
  exact ⟨(contMDiff_lagrangianEnergy (m := 0)
      g.contMDiff_mechanicalLagrangian_zero (by norm_num) z).continuousAt,
    h.congr_fderiv (ContinuousLinearMap.ext fun _ ↦ rfl)⟩

end Chart

/-! ### The Lagrangian vector field of a kinetic Lagrangian -/

namespace Manifold.ContMDiffNondegenerateMetric

variable [FiniteDimensional ℝ E] (g : ContMDiffNondegenerateMetric (I := I) (M := M))

/-- **The mechanical Lagrangian of a nondegenerate metric is hyperregular**: its Legendre map
`v ↦ g(v, ·)` is a bijection `TM → T*M`, for every potential `V`. -/
theorem isHyperregularLagrangian_mechanicalLagrangian (V : M → ℝ) :
    IsHyperregularLagrangian (mechanicalLagrangian g V) :=
  (isHyperregularLagrangian_mechanicalLagrangian_iff g.apply_comm V).2 g.isInvertible

variable {g} {cov : CovariantDerivative I E (fun x : M ↦ TangentSpace I x)}

open Module in
/-- **The spray of the Levi-Civita connection solves the Lagrangian equation of the kinetic
energy.** For the kinetic Lagrangian `L(v) = ½ g(v, v)` of a nondegenerate metric `g` and a
Levi-Civita connection of `g`, the vector `(v, -Γ_x(v, v))` at a tangent vector `v` at `x`, read in
the chart of `TM` at `v` with `Γ` the Christoffel map in the trivialization at `x`, satisfies
`ω_L((v, -Γ_x(v, v)), Y) = dE_L(Y)` for the Cartan two-form `ω_L` and the energy `E_L`. -/
theorem IsLeviCivitaConnection.eval₂_cartanTwoForm_mechanicalLagrangian_zero
    (hcov : g.IsLeviCivitaConnection cov)
    {ι : Type*} [Fintype ι] (basis : Basis ι ℝ E) (z : TangentBundle I M)
    (Y : TangentSpace I.tangent z) :
    SmoothBundleForm.eval₂
      (cartanTwoForm (mechanicalLagrangian g 0) g.contMDiff_mechanicalLagrangian_zero) z
        ((z.2, -christoffelMap basis (cov.isCovariantDerivativeOn
          (s := (trivializationAt E (TangentSpace I) z.proj).baseSet)) z.proj z.2 z.2) :
          TangentSpace I.tangent z) Y =
      mvfderiv I.tangent (lagrangianEnergy (mechanicalLagrangian g 0)) z Y := by
  have hL2 : ContMDiff I.tangent 𝓘(ℝ) 2 (mechanicalLagrangian g 0) :=
    g.contMDiff_mechanicalLagrangian_zero.of_le (by simp)
  obtain ⟨a, b⟩ := Y
  -- Abbreviations for the chart data at the base point `x`: the chart metric `G` at the chart
  -- image of `x`, its derivative `DG`, the fibre coordinate `u` and the Christoffel map `Γ`.
  let x := z.proj
  let u : E := z.2
  let G : E →L[ℝ] E →L[ℝ] ℝ := g.chartMetric x (extChartAt I x x)
  let DG := fderivWithin ℝ (g.chartMetric x) (extChartAt I x).target (extChartAt I x x)
  let Γ := christoffelMap basis (cov.isCovariantDerivativeOn
    (s := (trivializationAt E (TangentSpace I) x).baseSet)) x
  -- Evaluate the chart derivatives of the Legendre map and of the energy.
  have hX : mfderiv I.tangent (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (legendreMap (mechanicalLagrangian g 0)) z
      ((z.2, -Γ z.2 z.2) : TangentSpace I.tangent z) =
      ((u, G (-Γ u u) + DG u u) : E × (E →L[ℝ] ℝ)) := by
    rw [(hasMFDerivAt_legendreMap_mechanicalLagrangian g 0 z hL2).mfderiv]
    exact legendreChartDeriv_apply g z.proj z.2 _
  have hY : mfderiv I.tangent (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (legendreMap (mechanicalLagrangian g 0)) z
      ((a, b) : TangentSpace I.tangent z) = ((a, G b + DG a u) : E × (E →L[ℝ] ℝ)) := by
    rw [(hasMFDerivAt_legendreMap_mechanicalLagrangian g 0 z hL2).mfderiv]
    exact legendreChartDeriv_apply g z.proj z.2 _
  have hE : mvfderiv I.tangent (lagrangianEnergy (mechanicalLagrangian g 0)) z
      ((a, b) : TangentSpace I.tangent z) = 2⁻¹ * (G u b + (G b u + DG a u u)) := by
    rw [mvfderiv, (hasMFDerivAt_lagrangianEnergy_mechanicalLagrangian_zero g z).mfderiv]
    -- The model tangent space of ℝ is identified with ℝ by `fromTangentSpace`.
    exact energyChartDeriv_apply g z.proj z.2 (a, b)
  -- `ω_L = FL^* ω`, and `ω` is the linear cotangent form in the chart at `FL(z)`.
  have h := SmoothForm.eval₂_mpullback (legendreMap (mechanicalLagrangian g 0))
    (contMDiff_legendreMap g.contMDiff_mechanicalLagrangian_zero (by simp))
    (CotangentBundle.symplecticForm I M) z
    ((z.2, -Γ z.2 z.2) : TangentSpace I.tangent z) ((a, b) : TangentSpace I.tangent z)
  rw [mpullback_legendreMap_symplecticForm g.contMDiff_mechanicalLagrangian_zero,
    CotangentBundle.eval₂_symplecticForm, hX, hY] at h
  rw [h, hE, strongDualCotangentSymplecticForm_apply]
  dsimp only
  -- Metric compatibility in coordinates, and the symmetries of `G` and of `Γ`.
  have hx : x ∈ (extChartAt I x).source := mem_extChartAt_source x
  have hc (p q r : E) : DG p q r = G (Γ q p) r + G q (Γ r p) :=
    hcov.isMetricCompatible.fderivWithin_chartMetric_apply basis hx p q r
  have hsymm (p q : E) : G p q = G q p :=
    (g.isSymm_chartMetric (mem_extChartAt_target x)).eq p q
  have : IsManifold I (minSmoothness ℝ 2) M := by
    rw [minSmoothness_of_isRCLikeNormedField]
    infer_instance
  have hΓ (p q : E) : Γ p q = Γ q p :=
    christoffelMap_comm ((CovariantDerivative.isTorsionFree_iff_torsion_eq_zero cov).2
      hcov.torsion) basis x hx p q
  rw [add_apply, add_apply, hc a u u, hc u u a, map_neg G,
    neg_apply (G (Γ u u)) a, hΓ a u, hsymm u b, hsymm u (Γ u a)]
  ring

open Module in
/-- **The Lagrangian vector field of the kinetic energy is the spray of the Levi-Civita
connection.** For the kinetic Lagrangian `L(v) = ½ g(v, v)` of a nondegenerate metric `g` on a
finite-dimensional manifold with boundaryless tangent bundle, the Hamiltonian vector field of the
energy for the Cartan two-form is, at a tangent vector `v` at `x` and in the chart of `TM` at `v`,
the vector `(v, -Γ_x(v, v))`, where `Γ` is the Christoffel map of a Levi-Civita connection of `g`
in the trivialization at `x`. -/
theorem IsLeviCivitaConnection.hamiltonianVectorField_lagrangianEnergy_mechanicalLagrangian_zero
    [BoundarylessManifold I.tangent (TangentBundle I M)] (hcov : g.IsLeviCivitaConnection cov)
    {ι : Type*} [Fintype ι] (basis : Basis ι ℝ E) (z : TangentBundle I M) :
    (cartanTwoForm (mechanicalLagrangian g 0)
      g.contMDiff_mechanicalLagrangian_zero).hamiltonianVectorField
        (lagrangianEnergy (mechanicalLagrangian g 0)) z =
      ((z.2, -christoffelMap basis (cov.isCovariantDerivativeOn
          (s := (trivializationAt E (TangentSpace I) z.proj).baseSet)) z.proj z.2 z.2) :
          TangentSpace I.tangent z) := by
  have : CompleteSpace E := FiniteDimensional.completeSpace ℝ E
  have hω := ((g.isHyperregularLagrangian_mechanicalLagrangian 0).isRegularLagrangian
    |>.isSymplectic_cartanTwoForm g.contMDiff_mechanicalLagrangian_zero).isNondegenerate
  exact congrFun (hω.isHamiltonianVectorField_iff_eq.1
    (SmoothTwoForm.isHamiltonianVectorField_iff.2
      (hcov.eval₂_cartanTwoForm_mechanicalLagrangian_zero basis))).symm z

end Manifold.ContMDiffNondegenerateMetric

/-! ### The geodesic spray and the cogeodesic flow -/

section Riemannian

open _root_.TauCeti.Manifold

variable [FiniteDimensional ℝ E] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- The Hamiltonian of a Riemannian mechanical Lagrangian is covector kinetic energy plus
its potential. -/
theorem IsHyperregularLagrangian.hamiltonian_mechanicalLagrangian_ofRiemannianBundle
    {V : M → ℝ} (h : IsHyperregularLagrangian
      (mechanicalLagrangian (ContMDiffNondegenerateMetric.ofRiemannianBundle I M) V))
    (p : CotangentBundle I M) :
    h.hamiltonian p = CotangentBundle.kineticEnergy I M p + V p.proj := by
  let g := ContMDiffNondegenerateMetric.ofRiemannianBundle I M
  have hinv := g.isInvertible p.proj
  -- The metric lowers the index of the Riesz dual of `p` back to `p`.
  have hR : g p.proj (Riemannian.Tensor.rieszDual (I := I) p.proj p.2) = p.2 := by
    ext w
    rw [ContMDiffNondegenerateMetric.ofRiemannianBundle_apply, Riemannian.Tensor.inner_rieszDual]
  rw [h.hamiltonian_mechanicalLagrangian g.apply_comm, CotangentBundle.kineticEnergy_apply,
    Riemannian.Tensor.norm_sq_eq_apply_rieszDual, ← hR, hinv.inverse_apply_self, hR]
  ring

/-- **The Hamiltonian of the kinetic Lagrangian is the kinetic energy of covectors.** For the
Lagrangian `½ ‖v‖²` of a Riemannian metric, the Hamiltonian `E_L ∘ FL⁻¹` is `‖p‖² / 2`, for the
norm of covectors induced by the metric. -/
@[simp]
theorem IsHyperregularLagrangian.hamiltonian_eq_kineticEnergy
    (h : IsHyperregularLagrangian
      (mechanicalLagrangian (ContMDiffNondegenerateMetric.ofRiemannianBundle I M) 0)) :
    h.hamiltonian = CotangentBundle.kineticEnergy I M := by
  funext p
  simpa using h.hamiltonian_mechanicalLagrangian_ofRiemannianBundle p

variable [BoundarylessManifold I.tangent (TangentBundle I M)]

/-- **The geodesic spray is the Lagrangian vector field of the kinetic energy.** For the Lagrangian
`½ ‖v‖²` of a Riemannian metric, the Hamiltonian vector field of the energy for the Cartan two-form
is the geodesic spray. -/
@[simp]
theorem hamiltonianVectorField_lagrangianEnergy_eq_geodesicSpray :
    SmoothTwoForm.hamiltonianVectorField
      (cartanTwoForm _
        (ContMDiffNondegenerateMetric.ofRiemannianBundle I M).contMDiff_mechanicalLagrangian_zero)
        (lagrangianEnergy
          (mechanicalLagrangian (ContMDiffNondegenerateMetric.ofRiemannianBundle I M) 0)) =
      geodesicSpray I M := by
  funext z
  rw [(ContMDiffNondegenerateMetric.isLeviCivitaConnection_ofRiemannianBundle_leviCivitaConnection
      I M).hamiltonianVectorField_lagrangianEnergy_mechanicalLagrangian_zero
      (Module.finBasis ℝ E) z,
    geodesicSpray_apply]
  -- The two sides differ only in the smoothness instances through which the Levi-Civita
  -- connection of the Riemannian metric is elaborated.
  rfl

/-- **The Legendre map carries the geodesic spray to the cogeodesic field.** For the Lagrangian
`½ ‖v‖²` of a Riemannian metric, the differential of the Legendre map `v ↦ ⟪v, ·⟫` sends the
geodesic spray to the Hamiltonian vector field of the kinetic energy `‖p‖² / 2` for the canonical
symplectic form of `T*M`. -/
theorem mfderiv_legendreMap_geodesicSpray
    (z : TangentBundle I M) :
    mfderiv I.tangent (I.prod 𝓘(ℝ, E →L[ℝ] ℝ))
        (legendreMap (mechanicalLagrangian (ContMDiffNondegenerateMetric.ofRiemannianBundle I M) 0))
        z (geodesicSpray I M z) =
      (CotangentBundle.symplecticForm I M).hamiltonianVectorField
        (CotangentBundle.kineticEnergy I M)
        (legendreMap (mechanicalLagrangian (ContMDiffNondegenerateMetric.ofRiemannianBundle I M) 0)
          z) := by
  have : CompleteSpace E := FiniteDimensional.completeSpace ℝ E
  have h := ContMDiffNondegenerateMetric.isHyperregularLagrangian_mechanicalLagrangian
    (ContMDiffNondegenerateMetric.ofRiemannianBundle I M) 0
  rw [← h.hamiltonian_eq_kineticEnergy,
    ← hamiltonianVectorField_lagrangianEnergy_eq_geodesicSpray]
  exact h.mfderiv_legendreMap_hamiltonianVectorField
    (ContMDiffNondegenerateMetric.ofRiemannianBundle I M).contMDiff_mechanicalLagrangian_zero z

/-- On any parameter set, the Legendre map identifies integral curves of the geodesic spray
with integral curves of the kinetic Hamiltonian vector field. -/
theorem isMIntegralCurveOn_legendreMap_comp_iff_geodesicSpray
    {γ : ℝ → TangentBundle I M} {s : Set ℝ} :
    IsMIntegralCurveOn
        (legendreMap
          (mechanicalLagrangian (ContMDiffNondegenerateMetric.ofRiemannianBundle I M) 0) ∘ γ)
        ((CotangentBundle.symplecticForm I M).hamiltonianVectorField
          (CotangentBundle.kineticEnergy I M)) s ↔
      IsMIntegralCurveOn γ (geodesicSpray I M) s := by
  have : CompleteSpace E := FiniteDimensional.completeSpace ℝ E
  let g := ContMDiffNondegenerateMetric.ofRiemannianBundle I M
  let h := g.isHyperregularLagrangian_mechanicalLagrangian 0
  let Φ := h.legendreDiffeomorph g.contMDiff_mechanicalLagrangian_zero
  have hcoe : ⇑Φ = legendreMap (mechanicalLagrangian g 0) :=
    h.coe_legendreDiffeomorph g.contMDiff_mechanicalLagrangian_zero
  have hΦ : ∀ z, mfderiv I.tangent (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) Φ z
      (geodesicSpray I M z) =
      (CotangentBundle.symplecticForm I M).hamiltonianVectorField
        (CotangentBundle.kineticEnergy I M) (Φ z) := by
    rw [hcoe]
    exact mfderiv_legendreMap_geodesicSpray (I := I) (M := M)
  constructor
  · intro hγ
    have hback := hγ.map_of_mfderiv_eq (fun _ _ ↦ Φ.symm.mdifferentiable (by simp) _)
      (fun _ _ ↦ Φ.mfderiv_symm_apply_eq_of_mfderiv_apply_eq (by simp) hΦ _)
    simpa only [Function.comp_def, Φ, g,
      IsHyperregularLagrangian.legendreDiffeomorph_symm_apply_legendreMap] using hback
  · intro hγ
    simpa only [Φ, g, IsHyperregularLagrangian.coe_legendreDiffeomorph] using
      hγ.map_of_mfderiv_eq (fun _ _ ↦ Φ.mdifferentiable (by simp) _) (fun _ _ ↦ hΦ _)

/-- A `C²` curve is a geodesic on a parameter set with unique derivatives exactly when the
Legendre transform of its within-velocity lift is an integral curve of the kinetic Hamiltonian
vector field there. This includes finite-lifetime geodesics on incomplete manifolds. -/
theorem isMIntegralCurveOn_legendreMap_comp_curveVelocityLiftWithin_iff
    {γ : ℝ → M} {s : Set ℝ} (hs : UniqueDiffOn ℝ s)
    (hγ : ContMDiffOn 𝓘(ℝ) I 2 γ s) :
    IsMIntegralCurveOn
        (legendreMap
          (mechanicalLagrangian (ContMDiffNondegenerateMetric.ofRiemannianBundle I M) 0) ∘
            curveVelocityLiftWithin I γ s)
        ((CotangentBundle.symplecticForm I M).hamiltonianVectorField
          (CotangentBundle.kineticEnergy I M)) s ↔
      IsGeodesicCurveOn I γ s := by
  rw [isMIntegralCurveOn_legendreMap_comp_iff_geodesicSpray]
  exact isMIntegralCurveOn_curveVelocityLiftWithin_iff hs hγ

/-- **The geodesic flow is the cogeodesic flow.** A `C²` curve `γ` in a Riemannian manifold is a
geodesic exactly when the Legendre transform `t ↦ ⟪γ'(t), ·⟫` of its velocity is an integral curve
of the Hamiltonian vector field of the kinetic energy `‖p‖² / 2` on `T*M`. -/
theorem isMIntegralCurve_legendreMap_comp_curveVelocityLift_iff
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ) I 2 γ) :
    IsMIntegralCurve
        (legendreMap
          (mechanicalLagrangian (ContMDiffNondegenerateMetric.ofRiemannianBundle I M) 0) ∘
            curveVelocityLift I γ)
        ((CotangentBundle.symplecticForm I M).hamiltonianVectorField
          (CotangentBundle.kineticEnergy I M)) ↔
      IsGeodesicCurve I γ := by
  rw [isMIntegralCurve_iff_isMIntegralCurveOn, ← isGeodesicCurveOn_univ,
    ← curveVelocityLiftWithin_univ]
  exact isMIntegralCurveOn_legendreMap_comp_curveVelocityLiftWithin_iff uniqueDiffOn_univ
    (contMDiffOn_univ.2 hγ)

variable [I.Boundaryless]

/-- Every integral curve of the kinetic Hamiltonian vector field projects to a geodesic;
the integral-curve equation supplies the projection's `C²` regularity. -/
theorem isGeodesicCurveOn_proj_of_isMIntegralCurveOn_kineticEnergy
    {δ : ℝ → CotangentBundle I M} {s : Set ℝ} (hs : UniqueDiffOn ℝ s)
    (hδ : IsMIntegralCurveOn δ ((CotangentBundle.symplecticForm I M).hamiltonianVectorField
      (CotangentBundle.kineticEnergy I M)) s) :
    IsGeodesicCurveOn I (fun t ↦ (δ t).proj) s := by
  have : CompleteSpace E := FiniteDimensional.completeSpace ℝ E
  let g := ContMDiffNondegenerateMetric.ofRiemannianBundle I M
  let h := g.isHyperregularLagrangian_mechanicalLagrangian 0
  let Φ := h.legendreDiffeomorph g.contMDiff_mechanicalLagrangian_zero
  have hz : IsMIntegralCurveOn (Φ.symm ∘ δ) (geodesicSpray I M) s :=
    isMIntegralCurveOn_legendreMap_comp_iff_geodesicSpray.1 (by
      simpa only [Function.comp_def, Φ, g,
        IsHyperregularLagrangian.legendreMap_legendreDiffeomorph_symm_apply] using hδ)
  simpa only [Function.comp_apply, Φ, g,
    IsHyperregularLagrangian.proj_legendreDiffeomorph_symm_apply] using
    isGeodesicCurveOn_proj_of_isMIntegralCurveOn hs hz

omit [I.Boundaryless] in
/-- A kinetic Hamiltonian trajectory is the Legendre transform of the within-velocity lift of
its projection on every parameter set with unique derivatives. -/
theorem eqOn_legendreMap_comp_curveVelocityLiftWithin_of_isMIntegralCurveOn_kineticEnergy
    {δ : ℝ → CotangentBundle I M} {s : Set ℝ} (hs : UniqueDiffOn ℝ s)
    (hδ : IsMIntegralCurveOn δ ((CotangentBundle.symplecticForm I M).hamiltonianVectorField
      (CotangentBundle.kineticEnergy I M)) s) :
    EqOn δ (legendreMap
      (mechanicalLagrangian (ContMDiffNondegenerateMetric.ofRiemannianBundle I M) 0) ∘
        curveVelocityLiftWithin I (fun t ↦ (δ t).proj) s) s := by
  have : CompleteSpace E := FiniteDimensional.completeSpace ℝ E
  let g := ContMDiffNondegenerateMetric.ofRiemannianBundle I M
  let h := g.isHyperregularLagrangian_mechanicalLagrangian 0
  let Φ := h.legendreDiffeomorph g.contMDiff_mechanicalLagrangian_zero
  have hz : IsMIntegralCurveOn (Φ.symm ∘ δ) (geodesicSpray I M) s :=
    isMIntegralCurveOn_legendreMap_comp_iff_geodesicSpray.1 (by
      simpa only [Function.comp_def, Φ, g,
        IsHyperregularLagrangian.legendreMap_legendreDiffeomorph_symm_apply] using hδ)
  intro t ht
  have hlift := eq_curveVelocityLiftWithin_of_isMIntegralCurveOn (hs t ht) hz ht
  simpa only [Function.comp_apply, Φ, g, IsHyperregularLagrangian.coe_legendreDiffeomorph,
    IsHyperregularLagrangian.proj_legendreDiffeomorph_symm_apply,
    IsHyperregularLagrangian.legendreMap_legendreDiffeomorph_symm_apply] using
    congrArg Φ hlift

/-- The kinetic Hamiltonian flow through the Legendre transform of `(p, v)` has exactly the
maximal geodesic interval of `(p, v)` as its time domain. -/
theorem mem_flowDomain_kineticEnergy_legendreMap_iff
    (p : M) (v : TangentSpace I p) (t : ℝ) :
    (t, legendreMap
      (mechanicalLagrangian (ContMDiffNondegenerateMetric.ofRiemannianBundle I M) 0)
        (TotalSpace.mk' E p v)) ∈
      flowDomain ((CotangentBundle.symplecticForm I M).hamiltonianVectorField
        (CotangentBundle.kineticEnergy I M)) ↔ t ∈ geodesicInterval I M p v := by
  have : CompleteSpace E := FiniteDimensional.completeSpace ℝ E
  let g := ContMDiffNondegenerateMetric.ofRiemannianBundle I M
  let h := g.isHyperregularLagrangian_mechanicalLagrangian 0
  let Φ := h.legendreDiffeomorph g.contMDiff_mechanicalLagrangian_zero
  have hcoe : ⇑Φ = legendreMap (mechanicalLagrangian g 0) :=
    h.coe_legendreDiffeomorph g.contMDiff_mechanicalLagrangian_zero
  have hdomain := Φ.mem_flowDomain_apply_iff (by simp)
    (X := geodesicSpray I M)
    (Y := (CotangentBundle.symplecticForm I M).hamiltonianVectorField
      (CotangentBundle.kineticEnergy I M))
    (by rw [hcoe]; exact mfderiv_legendreMap_geodesicSpray (I := I) (M := M))
    (t := t) (x := TotalSpace.mk' E p v)
  simpa only [hcoe, mem_flowDomain,
    maximalIntegralCurveInterval_geodesicSpray] using hdomain

/-- The Legendre map conjugates the maximal geodesic-spray flow and the kinetic Hamiltonian
flow, including their initial-point junk values outside the common maximal domain. -/
theorem legendreMap_flowOf_geodesicSpray [T2Space M] (t : ℝ) (z : TangentBundle I M) :
    legendreMap
        (mechanicalLagrangian (ContMDiffNondegenerateMetric.ofRiemannianBundle I M) 0)
        (flowOf (geodesicSpray I M) t z) =
      flowOf ((CotangentBundle.symplecticForm I M).hamiltonianVectorField
        (CotangentBundle.kineticEnergy I M)) t
        (legendreMap
          (mechanicalLagrangian (ContMDiffNondegenerateMetric.ofRiemannianBundle I M) 0) z) := by
  have : CompleteSpace E := FiniteDimensional.completeSpace ℝ E
  have : IsManifold I (∞ + 1) M := IsManifold.of_le (n := ∞) (by simp)
  let g := ContMDiffNondegenerateMetric.ofRiemannianBundle I M
  let h := g.isHyperregularLagrangian_mechanicalLagrangian 0
  let Φ := h.legendreDiffeomorph g.contMDiff_mechanicalLagrangian_zero
  have hcoe : ⇑Φ = legendreMap (mechanicalLagrangian g 0) :=
    h.coe_legendreDiffeomorph g.contMDiff_mechanicalLagrangian_zero
  simpa only [hcoe] using
    Φ.apply_flowOf (by simp)
      (CotangentBundle.isSymplectic_symplecticForm.isNondegenerate.contMDiff_hamiltonianVectorField
        (n := 1) (by simp) ((CotangentBundle.contMDiff_kineticEnergy (n := ∞)).of_le (by simp)))
      (X := geodesicSpray I M)
      (by rw [hcoe]; exact mfderiv_legendreMap_geodesicSpray (I := I) (M := M)) t z

/-- Projecting the kinetic Hamiltonian flow with initial covector `g(v, ·)` gives the maximal
geodesic with initial data `(p, v)`. -/
theorem proj_flowOf_kineticEnergy_legendreMap [T2Space M]
    (p : M) (v : TangentSpace I p) (t : ℝ) :
    (flowOf ((CotangentBundle.symplecticForm I M).hamiltonianVectorField
      (CotangentBundle.kineticEnergy I M)) t
      (legendreMap
        (mechanicalLagrangian (ContMDiffNondegenerateMetric.ofRiemannianBundle I M) 0)
          (TotalSpace.mk' E p v))).proj = maximalGeodesic I M p v t := by
  rw [← legendreMap_flowOf_geodesicSpray, proj_legendreMap, flowOf_apply, maximalGeodesic_def]

end Riemannian

end TauCeti

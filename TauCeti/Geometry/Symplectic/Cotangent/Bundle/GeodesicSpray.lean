/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Spray
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Nondegenerate.Christoffel
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Cogeodesic
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Hyperregular
import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Riesz

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
(`IsLeviCivitaConnection.hamiltonianVectorField_lagrangianEnergy_mechanicalLagrangian`, in the
namespace `TauCeti.Manifold.ContMDiffNondegenerateMetric` like the other results on `g`).
The computation takes place in the chart at `v`, where `FL(q, u) = (q, G(q) u)` and
`E_L(q, u) = ½ G(q)(u, u)` for the chart metric `G`. The canonical form gives
`ω_L((a, b), (a', b')) = (G b' + DG(a') u)(a) - (G b + DG(a) u)(a')` at `(q, u)`, and metric
compatibility in coordinates, `DG(a)(v, w) = G(Γ(v, a), w) + G(v, Γ(w, a))`, together with the
symmetry of `G` and of `Γ` (torsion freeness) turns `ω_L((u, -Γ(u, u)), ·)` into `dE_L`
(`IsLeviCivitaConnection.eval₂_cartanTwoForm_mechanicalLagrangian`).
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
transform `t ↦ g(γ'(t), ·)` of its velocity is an integral curve of the cogeodesic field
(`TauCeti.isMIntegralCurve_legendreMap_comp_curveVelocityLift_iff`).

## Main results

In the namespace `TauCeti.Manifold.ContMDiffNondegenerateMetric`:

* `isHyperregularLagrangian_mechanicalLagrangian`: the mechanical Lagrangian of a nondegenerate
  metric is hyperregular.
* `IsLeviCivitaConnection.hamiltonianVectorField_lagrangianEnergy_mechanicalLagrangian`: the
  Lagrangian vector field of the kinetic Lagrangian is the spray `(v, -Γ(v, v))`.

In the namespace `TauCeti`:

* `TauCeti.hamiltonianVectorField_lagrangianEnergy_eq_geodesicSpray`: for a Riemannian metric it is
  the geodesic spray.
* `TauCeti.mfderiv_legendreMap_geodesicSpray`: the Legendre map carries the geodesic spray to the
  cogeodesic field.
* `TauCeti.isMIntegralCurve_legendreMap_comp_curveVelocityLift_iff`: geodesics are the projections
  of the integral curves of the cogeodesic field.

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

/-! ### Chart formulas -/

section Chart

/-- The inverse of the preferred chart of `TM` at `z` sends `(q, u)` to the tangent vector with
fibre coordinate `u`, in the trivialization at `z.proj`, at the point with chart coordinate `q`. -/
private theorem extChartAt_tangent_symm_apply (z : TangentBundle I M) {w : E × E}
    (hw : w ∈ (extChartAt I.tangent z).target) :
    (extChartAt I.tangent z).symm w =
      TotalSpace.mk' E ((extChartAt I z.proj).symm w.1)
        ((trivializationAt E (TangentSpace I) z.proj).symm ((extChartAt I z.proj).symm w.1)
          w.2) := by
  have hb : (extChartAt I z.proj).symm w.1 ∈
      (trivializationAt E (TangentSpace I) z.proj).baseSet := by
    rw [FiberBundle.extChartAt_target] at hw
    exact hw.1.2
  rw [FiberBundle.extChartAt]
  exact ((trivializationAt E (TangentSpace I) z.proj).mk_symm hb w.2).symm

/-- In its own preferred chart, a tangent vector `z` has coordinates the chart image of its base
point and its own fibre coordinate. -/
private theorem extChartAt_tangent_self (z : TangentBundle I M) :
    extChartAt I.tangent z z = (extChartAt I z.proj z.proj, (id z.2 : E)) := by
  rw [FiberBundle.extChartAt]
  refine Prod.ext rfl ?_
  simp only [PartialEquiv.coe_trans, Function.comp_apply, PartialEquiv.prod_coe,
    PartialEquiv.refl_coe, id_eq]
  exact ((trivializationAt E (TangentSpace I) z.proj).continuousLinearMapAt_apply_of_mem (R := ℝ)
    (FiberBundle.mem_baseSet_trivializationAt' z.proj) z.2).symm.trans
    (Manifold.continuousLinearMapAt_trivializationAt_self z.proj z.2)

/-- The derivative of `w ↦ (w.1, G w.1 w.2)`, the chart shape of the Legendre map of a mechanical
Lagrangian. -/
private theorem hasFDerivWithinAt_fst_prodMk_apply {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {G : E → E →L[ℝ] F} {G' : E →L[ℝ] E →L[ℝ] F} {s : Set (E × E)}
    {t : Set E} {p : E × E} (hG : HasFDerivWithinAt G G' t p.1) (hs : MapsTo Prod.fst s t) :
    HasFDerivWithinAt (fun w : E × E ↦ (w.1, G w.1 w.2))
      ((ContinuousLinearMap.fst ℝ E E).prod
        ((G p.1).comp (ContinuousLinearMap.snd ℝ E E) +
          (G'.comp (ContinuousLinearMap.fst ℝ E E)).flip p.2)) s p :=
  hasFDerivWithinAt_fst.prodMk
    ((hG.comp p hasFDerivWithinAt_fst hs).clm_apply hasFDerivWithinAt_snd)

/-- The derivative of `w ↦ G w.1 w.2 w.2`, the chart shape of the energy of a mechanical
Lagrangian. -/
private theorem hasFDerivWithinAt_apply_apply {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {G : E → E →L[ℝ] E →L[ℝ] F} {G' : E →L[ℝ] E →L[ℝ] E →L[ℝ] F}
    {s : Set (E × E)} {t : Set E} {p : E × E} (hG : HasFDerivWithinAt G G' t p.1)
    (hs : MapsTo Prod.fst s t) :
    HasFDerivWithinAt (fun w : E × E ↦ G w.1 w.2 w.2)
      ((G p.1 p.2).comp (ContinuousLinearMap.snd ℝ E E) +
        ((G p.1).comp (ContinuousLinearMap.snd ℝ E E) +
          (G'.comp (ContinuousLinearMap.fst ℝ E E)).flip p.2).flip p.2) s p :=
  ((hG.comp p hasFDerivWithinAt_fst hs).clm_apply hasFDerivWithinAt_snd).clm_apply
    hasFDerivWithinAt_snd

/-- The first coordinate of a point of the target of the chart of `TM` at `z` lies in the target
of the chart of `M` at `z.proj`. -/
private theorem mapsTo_fst_extChartAt_tangent_target (z : TangentBundle I M) :
    MapsTo Prod.fst (extChartAt I.tangent z).target (extChartAt I z.proj).target := fun w hw ↦ by
  rw [FiberBundle.extChartAt_target] at hw
  exact hw.1.1

variable (g : Manifold.ContMDiffNondegenerateMetric (I := I) (M := M))

/-- **The Legendre map of a mechanical Lagrangian in a chart.** Read in the preferred charts at
`z` and at its Legendre transform, it is `(q, u) ↦ (q, G(q) u)`, for the chart metric `G` of
`g` at `z.proj`. -/
private theorem writtenInExtChartAt_legendreMap_mechanicalLagrangian (V : M → ℝ)
    (z : TangentBundle I M) {w : E × E} (hw : w ∈ (extChartAt I.tangent z).target) :
    writtenInExtChartAt I.tangent (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) z
        (legendreMap (mechanicalLagrangian g V)) w =
      (w.1, g.chartMetric z.proj w.1 w.2) := by
  have hw1 := mapsTo_fst_extChartAt_tangent_target z hw
  have hb : (extChartAt I z.proj).symm w.1 ∈
      (trivializationAt E (TangentSpace I) z.proj).baseSet := by
    rw [FiberBundle.extChartAt_target] at hw
    exact hw.1.2
  rw [writtenInExtChartAt, Function.comp_apply, Function.comp_apply,
    extChartAt_tangent_symm_apply z hw, CotangentBundle.extChartAt_apply,
    legendreMap_mechanicalLagrangian_snd (fun x v w ↦ (g.symm x).eq v w) V, proj_legendreMap,
    proj_legendreMap]
  refine Prod.ext ((extChartAt I z.proj).right_inv hw1) (ContinuousLinearMap.ext fun u ↦ ?_)
  rw [g.chartMetric_apply hw1, ContinuousLinearMap.comp_apply, Trivialization.symmL_apply _ hb]

/-- **The energy of the kinetic Lagrangian in a chart** is `(q, u) ↦ ½ G(q)(u, u)`. -/
private theorem writtenInExtChartAt_lagrangianEnergy_mechanicalLagrangian (z : TangentBundle I M)
    {w : E × E} (hw : w ∈ (extChartAt I.tangent z).target) :
    writtenInExtChartAt I.tangent 𝓘(ℝ) z (lagrangianEnergy (mechanicalLagrangian g 0)) w =
      2⁻¹ * g.chartMetric z.proj w.1 w.2 w.2 := by
  rw [writtenInExtChartAt, Function.comp_apply, Function.comp_apply, extChartAt_model_space_eq_id,
    PartialEquiv.refl_coe, id_eq, extChartAt_tangent_symm_apply z hw,
    lagrangianEnergy_mechanicalLagrangian,
    g.chartMetric_apply (mapsTo_fst_extChartAt_tangent_target z hw), Pi.zero_apply, add_zero]

/-- The derivative of the Legendre map of a mechanical Lagrangian at `z`, read in charts:
`(a, b) ↦ (a, G b + DG(a) u)` with `G` the chart metric at the chart image of `z.proj`, `DG` its
derivative and `u` the fibre coordinate of `z`. -/
private def legendreChartDeriv (z : TangentBundle I M) : E × E →L[ℝ] E × (E →L[ℝ] ℝ) :=
  (ContinuousLinearMap.fst ℝ E E).prod
    ((g.chartMetric z.proj (extChartAt I z.proj z.proj)).comp (ContinuousLinearMap.snd ℝ E E) +
      ((fderivWithin ℝ (g.chartMetric z.proj) (extChartAt I z.proj).target
        (extChartAt I z.proj z.proj)).comp (ContinuousLinearMap.fst ℝ E E)).flip (id z.2 : E))

/-- The derivative of the energy of the kinetic Lagrangian at `z`, read in charts:
`(a, b) ↦ ½ (G(u, b) + G(b, u) + DG(a)(u, u))`. -/
private def energyChartDeriv (z : TangentBundle I M) : E × E →L[ℝ] ℝ :=
  (2⁻¹ : ℝ) • ((g.chartMetric z.proj (extChartAt I z.proj z.proj) (id z.2 : E)).comp
      (ContinuousLinearMap.snd ℝ E E) +
    ((g.chartMetric z.proj (extChartAt I z.proj z.proj)).comp (ContinuousLinearMap.snd ℝ E E) +
      ((fderivWithin ℝ (g.chartMetric z.proj) (extChartAt I z.proj).target
        (extChartAt I z.proj z.proj)).comp (ContinuousLinearMap.fst ℝ E E)).flip
          (id z.2 : E)).flip (id z.2 : E))

/-- The Legendre map of a mechanical Lagrangian has derivative `legendreChartDeriv` in charts. -/
private theorem hasMFDerivAt_legendreMap_mechanicalLagrangian (V : M → ℝ)
    (z : TangentBundle I M) (hL : ContMDiff I.tangent 𝓘(ℝ) 2 (mechanicalLagrangian g V)) :
    HasMFDerivAt I.tangent (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (legendreMap (mechanicalLagrangian g V)) z
      (legendreChartDeriv g z) := by
  have hΦ := hasFDerivWithinAt_fst_prodMk_apply
    (p := ((extChartAt I z.proj z.proj : E), (id z.2 : E)))
    ((g.contDiffOn_chartMetric z.proj _ (mem_extChartAt_target z.proj)).differentiableWithinAt
      (by simp)).hasFDerivWithinAt (mapsTo_fst_extChartAt_tangent_target z)
  have hp := extChartAt_tangent_self z
  -- On the chart target the chart expression is `(q, u) ↦ (q, G(q) u)`, and that target is a
  -- neighbourhood of the chart image of `z` within the range of the model.
  have h : HasFDerivWithinAt (writtenInExtChartAt I.tangent (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) z
      (legendreMap (mechanicalLagrangian g V))) (legendreChartDeriv g z) (range I.tangent)
      (extChartAt I.tangent z z) := by
    rw [hp]
    refine (hasFDerivWithinAt_inter' (hp ▸ extChartAt_target_mem_nhdsWithin z)).1 ?_
    refine (hΦ.mono inter_subset_right).congr (fun w hw ↦ ?_) ?_
    · exact writtenInExtChartAt_legendreMap_mechanicalLagrangian g V z hw.2
    · rw [← hp]
      exact writtenInExtChartAt_legendreMap_mechanicalLagrangian g V z (mem_extChartAt_target z)
  exact ⟨(contMDiff_legendreMap (m := 0) hL (by norm_num) z).continuousAt,
    h.congr_fderiv (ContinuousLinearMap.ext fun _ ↦ rfl)⟩

/-- The energy of the kinetic Lagrangian has derivative `energyChartDeriv` in charts. -/
private theorem hasMFDerivAt_lagrangianEnergy_mechanicalLagrangian (z : TangentBundle I M)
    (hL : ContMDiff I.tangent 𝓘(ℝ) 2 (mechanicalLagrangian g 0)) :
    HasMFDerivAt I.tangent 𝓘(ℝ) (lagrangianEnergy (mechanicalLagrangian g 0)) z
      (energyChartDeriv g z) := by
  have hΦ := (hasFDerivWithinAt_apply_apply
    (p := ((extChartAt I z.proj z.proj : E), (id z.2 : E)))
    ((g.contDiffOn_chartMetric z.proj _ (mem_extChartAt_target z.proj)).differentiableWithinAt
      (by simp)).hasFDerivWithinAt (mapsTo_fst_extChartAt_tangent_target z)).const_smul
    (2⁻¹ : ℝ)
  have hp := extChartAt_tangent_self z
  have h : HasFDerivWithinAt (writtenInExtChartAt I.tangent 𝓘(ℝ) z
      (lagrangianEnergy (mechanicalLagrangian g 0))) (energyChartDeriv g z) (range I.tangent)
      (extChartAt I.tangent z z) := by
    rw [hp]
    refine (hasFDerivWithinAt_inter' (hp ▸ extChartAt_target_mem_nhdsWithin z)).1 ?_
    refine (hΦ.mono inter_subset_right).congr (fun w hw ↦ ?_) ?_
    · rw [writtenInExtChartAt_lagrangianEnergy_mechanicalLagrangian g z hw.2, Pi.smul_apply,
        smul_eq_mul]
    · rw [← hp, writtenInExtChartAt_lagrangianEnergy_mechanicalLagrangian g z
        (mem_extChartAt_target z), Pi.smul_apply, smul_eq_mul]
  exact ⟨(contMDiff_lagrangianEnergy (m := 0) hL (by norm_num) z).continuousAt,
    h.congr_fderiv (ContinuousLinearMap.ext fun _ ↦ rfl)⟩

end Chart

/-! ### The Lagrangian vector field of a kinetic Lagrangian -/

namespace Manifold.ContMDiffNondegenerateMetric

variable [FiniteDimensional ℝ E] (g : ContMDiffNondegenerateMetric (I := I) (M := M))

/-- **The mechanical Lagrangian of a nondegenerate metric is hyperregular**: its Legendre map
`v ↦ g(v, ·)` is a bijection `TM → T*M`, for every potential `V`. -/
theorem isHyperregularLagrangian_mechanicalLagrangian (V : M → ℝ) :
    IsHyperregularLagrangian (mechanicalLagrangian g V) :=
  (isHyperregularLagrangian_mechanicalLagrangian_iff (fun x v w ↦ (g.symm x).eq v w) V).2
    fun x ↦ (ContinuousLinearMap.isInvertible_iff_nondegenerate_toBilinForm (𝕜 := ℝ) (E := E)).2
      (g.nondegenerate x)

variable {g} {cov : CovariantDerivative I E (fun x : M ↦ TangentSpace I x)}

open Module in
/-- **The spray of the Levi-Civita connection solves the Lagrangian equation of the kinetic
energy.** For the kinetic Lagrangian `L(v) = ½ g(v, v)` of a nondegenerate metric `g` and a
Levi-Civita connection of `g`, the vector `(v, -Γ_x(v, v))` at a tangent vector `v` at `x`, read in
the chart of `TM` at `v` with `Γ` the Christoffel map in the trivialization at `x`, satisfies
`ω_L((v, -Γ_x(v, v)), Y) = dE_L(Y)` for the Cartan two-form `ω_L` and the energy `E_L`. -/
theorem IsLeviCivitaConnection.eval₂_cartanTwoForm_mechanicalLagrangian
    (hcov : g.IsLeviCivitaConnection cov)
    (hL : ContMDiff I.tangent 𝓘(ℝ) ∞ (mechanicalLagrangian g 0)) (z : TangentBundle I M)
    (Y : TangentSpace I.tangent z) :
    SmoothBundleForm.eval₂ (cartanTwoForm (mechanicalLagrangian g 0) hL) z
        ((z.2, -christoffelMap (finBasis ℝ E) (cov.isCovariantDerivativeOn
          (s := (trivializationAt E (TangentSpace I) z.proj).baseSet)) z.proj z.2 z.2) :
          TangentSpace I.tangent z) Y =
      mvfderiv I.tangent (lagrangianEnergy (mechanicalLagrangian g 0)) z Y := by
  have hL2 : ContMDiff I.tangent 𝓘(ℝ) 2 (mechanicalLagrangian g 0) := hL.of_le (by simp)
  obtain ⟨a, b⟩ := Y
  -- Abbreviations for the chart data at the base point `x`: the chart metric `G` at the chart
  -- image of `x`, its derivative `DG`, the fibre coordinate `u` and the Christoffel map `Γ`.
  let x := z.proj
  let u : E := z.2
  let G : E →L[ℝ] E →L[ℝ] ℝ := g.chartMetric x (extChartAt I x x)
  let DG := fderivWithin ℝ (g.chartMetric x) (extChartAt I x).target (extChartAt I x x)
  let Γ := christoffelMap (finBasis ℝ E) (cov.isCovariantDerivativeOn
    (s := (trivializationAt E (TangentSpace I) x).baseSet)) x
  -- The derivatives of the Legendre map and of the energy, read in charts; each `rfl` evaluates
  -- the chart derivative on a pair, by its definition.
  have hX : mfderiv I.tangent (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (legendreMap (mechanicalLagrangian g 0)) z
      ((z.2, -Γ z.2 z.2) : TangentSpace I.tangent z) =
      ((u, G (-Γ u u) + DG u u) : E × (E →L[ℝ] ℝ)) := by
    rw [(hasMFDerivAt_legendreMap_mechanicalLagrangian g 0 z hL2).mfderiv]
    rfl
  have hY : mfderiv I.tangent (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (legendreMap (mechanicalLagrangian g 0)) z
      ((a, b) : TangentSpace I.tangent z) = ((a, G b + DG a u) : E × (E →L[ℝ] ℝ)) := by
    rw [(hasMFDerivAt_legendreMap_mechanicalLagrangian g 0 z hL2).mfderiv]
    rfl
  have hE : mvfderiv I.tangent (lagrangianEnergy (mechanicalLagrangian g 0)) z
      ((a, b) : TangentSpace I.tangent z) = 2⁻¹ * (G u b + (G b u + DG a u u)) := by
    rw [mvfderiv, (hasMFDerivAt_lagrangianEnergy_mechanicalLagrangian g z hL2).mfderiv]
    rfl
  -- `ω_L = FL^* ω`, and `ω` is the linear cotangent form in the chart at `FL(z)`.
  have h := SmoothForm.eval₂_mpullback (legendreMap (mechanicalLagrangian g 0))
    (contMDiff_legendreMap hL (by simp)) (CotangentBundle.symplecticForm I M) z
    ((z.2, -Γ z.2 z.2) : TangentSpace I.tangent z) ((a, b) : TangentSpace I.tangent z)
  rw [mpullback_legendreMap_symplecticForm hL, CotangentBundle.eval₂_symplecticForm, hX, hY] at h
  rw [h, hE, strongDualCotangentSymplecticForm_apply]
  dsimp only
  -- Metric compatibility in coordinates, and the symmetries of `G` and of `Γ`.
  have hx : x ∈ (extChartAt I x).source := mem_extChartAt_source x
  have hc (p q r : E) : DG p q r = G (Γ q p) r + G q (Γ r p) :=
    hcov.isMetricCompatible.fderivWithin_chartMetric_apply (finBasis ℝ E) hx p q r
  have hsymm (p q : E) : G p q = G q p :=
    (g.isSymm_chartMetric (mem_extChartAt_target x)).eq p q
  have : IsManifold I (minSmoothness ℝ 2) M := by
    rw [minSmoothness_of_isRCLikeNormedField]
    infer_instance
  have hΓ (p q : E) : Γ p q = Γ q p :=
    christoffelMap_comm ((CovariantDerivative.isTorsionFree_iff_torsion_eq_zero cov).2
      hcov.torsion) (finBasis ℝ E) x hx p q
  have hneg : G (-Γ u u) a = -G (Γ u u) a := by
    rw [map_neg]
    -- Negation of continuous linear maps is pointwise.
    rfl
  rw [add_apply, add_apply, hc a u u, hc u u a, hneg, hΓ a u, hsymm u b, hsymm u (Γ u a)]
  ring

open Module in
/-- **The Lagrangian vector field of the kinetic energy is the spray of the Levi-Civita
connection.** For the kinetic Lagrangian `L(v) = ½ g(v, v)` of a nondegenerate metric `g` on a
finite-dimensional manifold with boundaryless tangent bundle, the Hamiltonian vector field of the
energy for the Cartan two-form is, at a tangent vector `v` at `x` and in the chart of `TM` at `v`,
the vector `(v, -Γ_x(v, v))`, where `Γ` is the Christoffel map of a Levi-Civita connection of `g`
in the trivialization at `x`. -/
theorem IsLeviCivitaConnection.hamiltonianVectorField_lagrangianEnergy_mechanicalLagrangian
    [BoundarylessManifold I.tangent (TangentBundle I M)] (hcov : g.IsLeviCivitaConnection cov)
    (hL : ContMDiff I.tangent 𝓘(ℝ) ∞ (mechanicalLagrangian g 0)) (z : TangentBundle I M) :
    (cartanTwoForm (mechanicalLagrangian g 0) hL).hamiltonianVectorField
        (lagrangianEnergy (mechanicalLagrangian g 0)) z =
      ((z.2, -christoffelMap (finBasis ℝ E) (cov.isCovariantDerivativeOn
          (s := (trivializationAt E (TangentSpace I) z.proj).baseSet)) z.proj z.2 z.2) :
          TangentSpace I.tangent z) := by
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hω := ((g.isHyperregularLagrangian_mechanicalLagrangian 0).isRegularLagrangian
    |>.isSymplectic_cartanTwoForm hL).isNondegenerate
  -- Both vectors have the flat `dE_L`, and the flat of `ω_L` is injective.
  refine ((hω.isInvertible_flat z).injective ?_).symm
  rw [hω.flat_hamiltonianVectorField]
  ext Y
  exact (SmoothTwoForm.flat_apply _ _ _ _).trans
    (hcov.eval₂_cartanTwoForm_mechanicalLagrangian hL z Y)

end Manifold.ContMDiffNondegenerateMetric

/-! ### The geodesic spray and the cogeodesic flow -/

section Riemannian

open _root_.TauCeti.Manifold

variable [FiniteDimensional ℝ E] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- **The Hamiltonian of the kinetic Lagrangian is the kinetic energy of covectors.** For the
Lagrangian `½ ‖v‖²` of a Riemannian metric, the Hamiltonian `E_L ∘ FL⁻¹` is `‖p‖² / 2`, for the
norm of covectors induced by the metric. -/
@[simp]
theorem IsHyperregularLagrangian.hamiltonian_eq_kineticEnergy
    (h : IsHyperregularLagrangian
      (mechanicalLagrangian (ContMDiffNondegenerateMetric.ofRiemannianBundle I M) 0)) :
    h.hamiltonian = CotangentBundle.kineticEnergy I M := by
  funext p
  have hg (x : M) (v w : TangentSpace I x) :=
    ((ContMDiffNondegenerateMetric.ofRiemannianBundle I M).symm x).eq v w
  have hinv := (isHyperregularLagrangian_mechanicalLagrangian_iff hg 0).1 h p.proj
  -- The metric lowers the index of the Riesz dual of `p` back to `p`.
  have hR : ContMDiffNondegenerateMetric.ofRiemannianBundle I M p.proj
      (Riemannian.Tensor.rieszDual (I := I) p.proj p.2) = p.2 := by
    ext w
    rw [ContMDiffNondegenerateMetric.ofRiemannianBundle_apply, Riemannian.Tensor.inner_rieszDual]
  rw [h.hamiltonian_mechanicalLagrangian hg, CotangentBundle.kineticEnergy_apply,
    Riemannian.Tensor.norm_sq_eq_apply_rieszDual, ← hR, hinv.inverse_apply_self, hR,
    Pi.zero_apply, add_zero]
  ring

variable [BoundarylessManifold I.tangent (TangentBundle I M)]

/-- **The geodesic spray is the Lagrangian vector field of the kinetic energy.** For the Lagrangian
`½ ‖v‖²` of a Riemannian metric, the Hamiltonian vector field of the energy for the Cartan two-form
is the geodesic spray. -/
@[simp]
theorem hamiltonianVectorField_lagrangianEnergy_eq_geodesicSpray
    (hL : ContMDiff I.tangent 𝓘(ℝ) ∞
      (mechanicalLagrangian (ContMDiffNondegenerateMetric.ofRiemannianBundle I M) 0)) :
    (cartanTwoForm _ hL).hamiltonianVectorField
        (lagrangianEnergy
          (mechanicalLagrangian (ContMDiffNondegenerateMetric.ofRiemannianBundle I M) 0)) =
      geodesicSpray I M := by
  funext z
  rw [(ContMDiffNondegenerateMetric.isLeviCivitaConnection_ofRiemannianBundle_leviCivitaConnection
      I M).hamiltonianVectorField_lagrangianEnergy_mechanicalLagrangian hL z,
    geodesicSpray_apply]
  -- The two sides differ only in the smoothness instances through which the Levi-Civita
  -- connection of the Riemannian metric is elaborated.
  rfl

/-- **The Legendre map carries the geodesic spray to the cogeodesic field.** For the Lagrangian
`½ ‖v‖²` of a Riemannian metric, the differential of the Legendre map `v ↦ ⟪v, ·⟫` sends the
geodesic spray to the Hamiltonian vector field of the kinetic energy `‖p‖² / 2` for the canonical
symplectic form of `T*M`. -/
theorem mfderiv_legendreMap_geodesicSpray
    (hL : ContMDiff I.tangent 𝓘(ℝ) ∞
      (mechanicalLagrangian (ContMDiffNondegenerateMetric.ofRiemannianBundle I M) 0))
    (z : TangentBundle I M) :
    mfderiv I.tangent (I.prod 𝓘(ℝ, E →L[ℝ] ℝ))
        (legendreMap (mechanicalLagrangian (ContMDiffNondegenerateMetric.ofRiemannianBundle I M) 0))
        z (geodesicSpray I M z) =
      (CotangentBundle.symplecticForm I M).hamiltonianVectorField
        (CotangentBundle.kineticEnergy I M)
        (legendreMap (mechanicalLagrangian (ContMDiffNondegenerateMetric.ofRiemannianBundle I M) 0)
          z) := by
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  have h := ContMDiffNondegenerateMetric.isHyperregularLagrangian_mechanicalLagrangian
    (ContMDiffNondegenerateMetric.ofRiemannianBundle I M) 0
  rw [← h.hamiltonian_eq_kineticEnergy,
    ← hamiltonianVectorField_lagrangianEnergy_eq_geodesicSpray hL]
  exact h.mfderiv_legendreMap_hamiltonianVectorField hL z

/-- **The geodesic flow is the cogeodesic flow.** A `C²` curve `γ` in a Riemannian manifold is a
geodesic exactly when the Legendre transform `t ↦ ⟪γ'(t), ·⟫` of its velocity is an integral curve
of the Hamiltonian vector field of the kinetic energy `‖p‖² / 2` on `T*M`. -/
theorem isMIntegralCurve_legendreMap_comp_curveVelocityLift_iff
    (hL : ContMDiff I.tangent 𝓘(ℝ) ∞
      (mechanicalLagrangian (ContMDiffNondegenerateMetric.ofRiemannianBundle I M) 0))
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ) I 2 γ) :
    IsMIntegralCurve
        (legendreMap
          (mechanicalLagrangian (ContMDiffNondegenerateMetric.ofRiemannianBundle I M) 0) ∘
            curveVelocityLift I γ)
        ((CotangentBundle.symplecticForm I M).hamiltonianVectorField
          (CotangentBundle.kineticEnergy I M)) ↔
      IsGeodesicCurve I γ := by
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  have h := ContMDiffNondegenerateMetric.isHyperregularLagrangian_mechanicalLagrangian
    (ContMDiffNondegenerateMetric.ofRiemannianBundle I M) 0
  rw [← h.hamiltonian_eq_kineticEnergy, h.isMIntegralCurve_legendreMap_comp_iff hL,
    hamiltonianVectorField_lagrangianEnergy_eq_geodesicSpray hL]
  exact isMIntegralCurve_curveVelocityLift_iff hγ

end Riemannian

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Flow.Basic
public import Mathlib.Geometry.Manifold.VectorField.Pullback
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Dynamics.Flow.Variational
import TauCeti.Geometry.Manifold.VectorField.Regularity

/-!
# The variational equation of the flow of a vector field on a manifold

Let `v` be a `C¹` vector field on a boundaryless `C²` manifold `M` modelled on a
finite-dimensional space `E`, and `Φₜ = flowOf v t` its maximal flow. The differential `dΦₜ(x)`
describes how a perturbation of the initial point `x` evolves along the orbit of `x`. Read in an
extended chart `e` whose source contains `Φₜ₀ x`, the coordinate vector `J(t) = de(dΦₜ(x) w)` of
the perturbation of a tangent vector `w` solves near `t₀` the linear equation

`J'(t) = DV(e (Φₜ x)) J(t)`,

where `V` is the coordinate expression of `v` in the chart, the pullback
`VectorField.mpullbackWithin 𝓘(ℝ, E) I e.symm v (range I)` of `v` along the inverse chart. Only
the spatial derivative of `v` enters. This is the equation satisfied by the linearized flow along
a trajectory, whose propagator over a period is the linearized return map of a periodic orbit.
For a `C²` field and a torsion-free connection `∇`, the linearized flow `W(t) = dΦₜ(x) w` solves
the covariant form `D_t W = ∇_W v` of this equation
(`CovariantDerivative.alongCurve_mfderiv_timeDependentFlowOf`); the chart form here needs only a
`C¹` field and no connection.

The equation is stated for the operators `t ↦ D(e ∘ Φₜ)(x)`
(`TauCeti.hasDerivAt_mfderiv_extChartAt_comp_flowOf`) and for the vectors `de(dΦₜ(x) w)`
(`TauCeti.hasDerivAt_mfderiv_extChartAt_mfderiv_flowOf_apply`). The chart is any extended chart
whose source contains `Φₜ₀ x`; since its source is open, the same chart serves at every time near
`t₀`, so the equation holds along the trajectory in one fixed chart. Charts not centred at the
point need the manifold to be `C²`, for the coordinate expression of a `C¹` field in such a chart
to be `C¹` (`ContMDiffOn.contDiffOn_mpullback_extChartAt_symm`).

## Proof

The flow law `Φₜ = Φₜ₋ₜ₀ ∘ Φₜ₀` reduces the equation to time `0`, for the family
`G τ z = e (Φ_τ (e⁻¹ z))` read in the chart near `z₀ = e (Φₜ₀ x)`. The coordinate field `V` is
`C¹` near `z₀`, so it agrees near `z₀` with a globally Lipschitz `C¹` field `w` on `E`, its product
with a smooth cutoff (`ContDiffAt.exists_contDiff_lipschitzWith_eventuallyEq`). For small times
and initial points near `z₀` the curves of `G` stay where `w = V`, so by uniqueness of solutions
they are the orbits of the global flow of `w`. The variational equation of that flow
(`TauCeti.hasDerivAt_fderiv_flowOfLipschitz`) at time `0` is the claim, since `Dw(z₀) = DV(z₀)`.

## Main results

* `TauCeti.hasDerivAt_mfderiv_extChartAt_comp_flowOf`: the derivative of `t ↦ D(e ∘ Φₜ)(x)` at
  `t₀` is `DV(e (Φₜ₀ x)) ∘ D(e ∘ Φₜ₀)(x)`.
* `TauCeti.hasDerivAt_mfderiv_extChartAt_mfderiv_flowOf_apply`: the same for the coordinate
  vectors `de(dΦₜ(x) w)` of the perturbation of a tangent vector `w`.

## References

* P. Hartman, *Ordinary Differential Equations*, 2nd ed., SIAM, 2002, Chapter V, Theorem 3.1.
-/

public section

open Filter Function Set
open scoped Manifold Topology ContDiff NNReal

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M] {v : (x : M) → TangentSpace I x}

/-- **Read in a chart, the flow is the flow of a cut-off coordinate field.** Let `w` be a globally
Lipschitz field on `E` equal near `e p` to the coordinate expression of `v` in the extended chart
`e` at `y`, for a point `p` of its source. For times near `0` and initial points near `e p`, the
flow of `v` read in `e` is the flow of `w`. -/
private theorem eventually_extChartAt_flowOf_eq_flowOfLipschitz [IsManifold I 1 M]
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M))) {y p : M}
    (hp : p ∈ (extChartAt I y).source) {w : E → E} {K : ℝ≥0} (hw : LipschitzWith K w)
    (hwv : w =ᶠ[𝓝 (extChartAt I y p)]
      VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I y).symm v (range I)) :
    ∀ᶠ τ in 𝓝 (0 : ℝ), ∀ᶠ z in 𝓝 (extChartAt I y p),
      extChartAt I y (flowOf v τ ((extChartAt I y).symm z)) = flowOfLipschitz w hw τ z := by
  set e := extChartAt I y
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hwv
  have hz₀ : e p ∈ e.target := e.map_source hp
  -- The pair `(τ, e⁻¹ z)` and the point `Φ_τ (e⁻¹ z)` depend continuously on `(τ, z)`.
  have hpair : ContinuousAt (fun q : ℝ × E ↦ (q.1, e.symm q.2)) (0, e p) :=
    continuousAt_fst.prodMk (ContinuousAt.comp (g := e.symm) (continuousAt_extChartAt_symm' hp)
      continuousAt_snd)
  have hdom : ((0 : ℝ), e.symm (e p)) ∈ flowDomain v := by
    rw [e.left_inv hp]
    exact mem_flowDomain_zero hv p
  have hflow : ContinuousAt (fun q : ℝ × E ↦ flowOf v q.1 (e.symm q.2)) (0, e p) := by
    have h := (contMDiffOn_flowOf le_rfl hv).continuousOn.continuousAt
      ((isOpen_flowDomain hv).mem_nhds hdom)
    exact h.comp (f := fun q : ℝ × E ↦ (q.1, e.symm q.2)) hpair
  have hp' : flowOf v 0 (e.symm (e p)) ∈ e.source := by rwa [e.left_inv hp, flowOf_zero]
  -- On a product neighbourhood of `(0, e p)` every condition used below holds.
  have hS : ∀ᶠ q : ℝ × E in 𝓝 (0, e p), q.2 ∈ e.target ∧ (q.1, e.symm q.2) ∈ flowDomain v ∧
      flowOf v q.1 (e.symm q.2) ∈ e.source ∧
      e (flowOf v q.1 (e.symm q.2)) ∈ Metric.ball (e p) r := by
    refine (continuousAt_snd.eventually_mem (extChartAt_target_mem_nhds' hz₀)).and
      ((hpair.eventually_mem ((isOpen_flowDomain hv).mem_nhds hdom)).and
        ((hflow.eventually_mem ((isOpen_extChartAt_source y).mem_nhds hp')).and ?_))
    have hG : ContinuousAt (fun q : ℝ × E ↦ e (flowOf v q.1 (e.symm q.2))) (0, e p) :=
      (continuousAt_extChartAt' hp').comp
        (f := fun q : ℝ × E ↦ flowOf v q.1 (e.symm q.2)) hflow
    refine hG.eventually_mem (Metric.isOpen_ball.mem_nhds ?_)
    rw [e.left_inv hp, flowOf_zero]
    exact Metric.mem_ball_self hr
  rw [nhds_prod_eq] at hS
  obtain ⟨T, hT, U, hU, hTU⟩ := mem_prod_iff.mp hS
  obtain ⟨ε, hε, hεT⟩ := Metric.mem_nhds_iff.mp hT
  filter_upwards [Metric.ball_mem_nhds 0 hε] with τ hτ
  filter_upwards [hU] with z hz
  -- Along the curve `σ ↦ e (Φ_σ (e⁻¹ z))`, `σ ∈ (-ε, ε)`, the field `w` is the coordinate field.
  have hgood (σ : ℝ) (hσ : σ ∈ Metric.ball (0 : ℝ) ε) := hTU (mk_mem_prod (hεT hσ) hz)
  have hcurve : IsIntegralCurveOn (fun σ ↦ e (flowOf v σ (e.symm z))) (fun _ u ↦ w u)
      (Metric.ball 0 ε) := by
    intro σ hσ
    obtain ⟨-, hσdom, hσsrc, hσball⟩ := hgood σ hσ
    have h := HasMFDerivAt.hasDerivAt_extChartAt_comp_mpullbackWithin
      (isMIntegralCurveAt_flowOf hv hσdom).hasMFDerivAt hσsrc
    rw [← hball hσball] at h
    exact h.hasDerivWithinAt
  have hsub : uIcc 0 τ ⊆ Metric.ball (0 : ℝ) ε :=
    (convex_ball (0 : ℝ) ε).ordConnected.uIcc_subset (Metric.mem_ball_self hε) hτ
  have h := eq_flowOfLipschitz_of_isIntegralCurveOn hw hcurve hsub
  rwa [flowOf_zero, e.right_inv (hgood 0 (Metric.mem_ball_self hε)).1] at h

/-- **The variational equation at time `0`, read in a chart.** For a point `p` of the source of
the extended chart `e` at `y`, the maps `z ↦ e (Φ_τ (e⁻¹ z))` are differentiable at `e p` for `τ`
near `0`, and their derivatives at `e p` have derivative `DV(e p)` at `τ = 0`. -/
private theorem hasDerivAt_fderiv_extChartAt_flowOf_zero [IsManifold I 2 M]
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M))) {y p : M}
    (hp : p ∈ (extChartAt I y).source) :
    (∀ᶠ τ in 𝓝 (0 : ℝ), DifferentiableAt ℝ
      (fun z ↦ extChartAt I y (flowOf v τ ((extChartAt I y).symm z))) (extChartAt I y p)) ∧
    HasDerivAt
      (fun τ ↦ fderiv ℝ (fun z ↦ extChartAt I y (flowOf v τ ((extChartAt I y).symm z)))
        (extChartAt I y p))
      (fderiv ℝ (VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I y).symm v (range I))
        (extChartAt I y p)) 0 := by
  have : IsManifold I 1 M := IsManifold.of_le (n := 2) one_le_two
  -- On a boundaryless model the pullback within the model range is the plain pullback, which is
  -- `C¹` on the open chart target because the manifold is `C²`.
  have hvc : ContDiffAt ℝ 1
      (VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I y).symm v (range I))
      (extChartAt I y p) := by
    rw [I.range_eq_univ, VectorField.mpullbackWithin_univ]
    refine (hv.contMDiffOn (s := univ)).contDiffOn_mpullback_extChartAt_symm (n := 2)
      (by norm_num) |>.contDiffAt (Filter.inter_mem ?_ (by simp))
    rw [(isOpen_extChartAt_target y).interior_eq]
    exact extChartAt_target_mem_nhds' ((extChartAt I y).map_source hp)
  obtain ⟨w, hwC, ⟨K, hwK⟩, hwv⟩ := hvc.exists_contDiff_lipschitzWith_eventuallyEq one_ne_zero
  have hwC' : ContDiff ℝ 1 w := by exact_mod_cast hwC
  have hev := eventually_extChartAt_flowOf_eq_flowOfLipschitz hv hp hwK hwv
  refine ⟨hev.mono fun τ hτ ↦ ?_, ?_⟩
  · exact ((differentiable_flowOfLipschitz_apply hwK hwC' τ) _).congr_of_eventuallyEq hτ
  · have h := hasDerivAt_fderiv_flowOfLipschitz hwK hwC' (extChartAt I y p) 0
    have hid : flowOfLipschitz w hwK 0 = id := funext fun z ↦ Flow.map_zero_apply _ z
    rw [hid, fderiv_id, ContinuousLinearMap.comp_id, id_eq, hwv.fderiv_eq] at h
    refine h.congr_of_eventuallyEq ?_
    filter_upwards [hev] with τ hτ
    exact Filter.EventuallyEq.fderiv_eq hτ

variable [IsManifold I 2 M]

/-- **The variational equation of a flow, read in a chart.** Let `v` be a `C¹` vector field on a
boundaryless `C²` manifold modelled on a finite-dimensional space, let `(t₀, x)` be in the domain
of its maximal flow `Φ`, and let `e` be an extended chart whose source contains `Φₜ₀ x`. Then
`t ↦ D(e ∘ Φₜ)(x)` has derivative `DV(e (Φₜ₀ x)) ∘ D(e ∘ Φₜ₀)(x)` at `t₀`, where `V` is the
coordinate expression of `v` in `e`. -/
theorem hasDerivAt_mfderiv_extChartAt_comp_flowOf
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M))) {t₀ : ℝ} {x y : M}
    (ht₀ : (t₀, x) ∈ flowDomain v) (hy : flowOf v t₀ x ∈ (extChartAt I y).source) :
    HasDerivAt (F := E →L[ℝ] E) (fun t ↦ mfderiv I 𝓘(ℝ, E) (extChartAt I y ∘ flowOf v t) x)
      ((fderiv ℝ (VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I y).symm v (range I))
          (extChartAt I y (flowOf v t₀ x))).comp
        (mfderiv I 𝓘(ℝ, E) (extChartAt I y ∘ flowOf v t₀) x)) t₀ := by
  have : IsManifold I 1 M := IsManifold.of_le (n := 2) one_le_two
  set L : E →L[ℝ] E := mfderiv I 𝓘(ℝ, E) (extChartAt I y ∘ flowOf v t₀) x
  obtain ⟨hdiff, hderiv⟩ := hasDerivAt_fderiv_extChartAt_flowOf_zero hv hy
  have hΦ := contMDiffAt_flowOf_comp le_rfl hv contMDiffAt_const contMDiffAt_id ht₀
  have heΦ : MDifferentiableAt I 𝓘(ℝ, E) (extChartAt I y ∘ flowOf v t₀) x :=
    (mdifferentiableAt_extChartAt (by rwa [extChartAt_source] at hy)).comp x
      (hΦ.mdifferentiableAt one_ne_zero)
  -- Near `t₀`, flowing for `t` is flowing for `t₀` and then for `t - t₀`, read in the chart.
  have hcomp : ∀ᶠ t in 𝓝 t₀, mfderiv I 𝓘(ℝ, E) (extChartAt I y ∘ flowOf v t) x =
      (fderiv ℝ (fun z ↦ extChartAt I y (flowOf v (t - t₀) ((extChartAt I y).symm z)))
        (extChartAt I y (flowOf v t₀ x))).comp L := by
    have hjoint : ∀ᶠ q : ℝ × M in 𝓝 t₀ ×ˢ 𝓝 x, q ∈ flowDomain v := by
      rw [← nhds_prod_eq]
      exact (isOpen_flowDomain hv).mem_nhds ht₀
    have ht : Tendsto (fun t ↦ t - t₀) (𝓝 t₀) (𝓝 0) := tendsto_sub_nhds_zero_iff.2 tendsto_id
    filter_upwards [ht.eventually hdiff, hjoint.curry] with t htd htx
    have hloc : (extChartAt I y ∘ flowOf v t) =ᶠ[𝓝 x]
        (fun z ↦ extChartAt I y (flowOf v (t - t₀) ((extChartAt I y).symm z))) ∘
          (extChartAt I y ∘ flowOf v t₀) := by
      have hsrc : ∀ᶠ x' in 𝓝 x, flowOf v t₀ x' ∈ (extChartAt I y).source :=
        hΦ.continuousAt.eventually_mem ((isOpen_extChartAt_source y).mem_nhds hy)
      have hdom : ∀ᶠ x' in 𝓝 x, (t₀, x') ∈ flowDomain v :=
        (isOpen_setOf_mem_flowDomain hv continuous_const continuous_id).mem_nhds ht₀
      filter_upwards [hsrc, hdom, htx] with x' hx'src hx'dom hx't
      have hadd := flowOf_add hv hx'dom
        ((mem_flowDomain_flowOf_iff hv hx'dom).2 (by rwa [add_sub_cancel]))
      simp only [comp_apply, (extChartAt I y).left_inv hx'src, hadd.2, add_sub_cancel]
    rw [hloc.mfderiv_eq, mfderiv_comp x (htd.mdifferentiableAt) heΦ, mfderiv_eq_fderiv]
    rfl
  rw [← sub_self t₀] at hderiv
  refine ((hderiv.comp_sub_const t₀ t₀).clm_comp (hasDerivAt_const t₀ L)
    |>.congr_of_eventuallyEq hcomp).congr_deriv ?_
  simp

/-- **The variational equation of a flow, for a tangent vector.** In an extended chart `e` whose
source contains `Φₜ₀ x`, the coordinate vector `J(t) = de(dΦₜ(x) w)` of the perturbation of a
tangent vector `w` at `x` has derivative `DV(e (Φₜ₀ x)) J(t₀)` at `t₀`, where `V` is the
coordinate expression of `v` in `e`. -/
theorem hasDerivAt_mfderiv_extChartAt_mfderiv_flowOf_apply
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M))) {t₀ : ℝ} {x y : M}
    (ht₀ : (t₀, x) ∈ flowDomain v) (hy : flowOf v t₀ x ∈ (extChartAt I y).source)
    (w : E) :
    HasDerivAt (F := E)
      (fun t ↦ mfderiv I 𝓘(ℝ, E) (extChartAt I y) (flowOf v t x)
        (mfderiv I I (flowOf v t) x w))
      (fderiv ℝ (VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I y).symm v (range I))
        (extChartAt I y (flowOf v t₀ x))
        (mfderiv I 𝓘(ℝ, E) (extChartAt I y) (flowOf v t₀ x) (mfderiv I I (flowOf v t₀) x w)))
      t₀ := by
  have : IsManifold I 1 M := IsManifold.of_le (n := 2) one_le_two
  -- Wherever `Φₜ x` stays in the chart source, `de ∘ dΦₜ = d(e ∘ Φₜ)`.
  have hchain : ∀ᶠ t in 𝓝 t₀, (mfderiv I 𝓘(ℝ, E) (extChartAt I y) (flowOf v t x)
      (mfderiv I I (flowOf v t) x w) : E) =
        mfderiv I 𝓘(ℝ, E) (extChartAt I y ∘ flowOf v t) x w := by
    have hcont : ContinuousAt (fun t ↦ flowOf v t x) t₀ :=
      (mdifferentiableAt_flowOf hv ht₀).continuousAt
    have hdom : ∀ᶠ t in 𝓝 t₀, (t, x) ∈ flowDomain v :=
      (isOpen_setOf_mem_flowDomain hv continuous_id continuous_const).mem_nhds ht₀
    filter_upwards [hdom, hcont.eventually_mem ((isOpen_extChartAt_source y).mem_nhds hy)]
      with t htdom htsrc
    exact (mfderiv_comp_apply x (mdifferentiableAt_extChartAt
      (by rwa [extChartAt_source] at htsrc))
      ((contMDiffAt_flowOf_comp le_rfl hv contMDiffAt_const contMDiffAt_id
        htdom).mdifferentiableAt one_ne_zero) w).symm
  -- Evaluation at `w` is a continuous linear map on the operators `E →L[ℝ] E`.
  have h := (ContinuousLinearMap.apply ℝ E w).hasFDerivAt.comp_hasDerivAt t₀
    (hasDerivAt_mfderiv_extChartAt_comp_flowOf hv ht₀ hy)
  refine (h.congr_of_eventuallyEq hchain).congr_deriv ?_
  rw [hchain.self_of_nhds]
  rfl

end TauCeti

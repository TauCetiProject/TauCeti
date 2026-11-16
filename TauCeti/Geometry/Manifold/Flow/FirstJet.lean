/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Flow.TimeDependent
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.FirstJet.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic
import TauCeti.Dynamics.Flow.RestPoint
import TauCeti.Geometry.Manifold.VectorBundle.FirstJet.Connection

/-!
# Time-dependent flows of fields with zero first jet

A jointly `C¹` time-dependent vector field whose first jet vanishes at a point
between two times has a flow fixing that point with identity differential on its full
ambient tangent space. The primary statements use the intrinsic first jet, without choosing a
connection. Corollaries express its vanishing using a covariant derivative.
Both `HasMFDerivAt` and its differential and
pointwise consequences are provided. Only vanishing between the specified times is required,
even when the vector field is not complete. A local connection suffices for the covariant
formulations.

This is the flow ingredient in the refinement of relative Moser's theorem which preserves the
ambient first jet along a submanifold, rather than just its points.

## Main results

* `TauCeti.hasMFDerivAt_timeDependentFlowOf_of_jet_eq_zero` and its `mfderiv` and evaluation
  consequences give the identity differential from vanishing of the intrinsic first jet.
* `TauCeti.timeDependentFlowOf_eq_self_of_jet_eq_zero`: the stationary-point equation
  used to identify the source and target tangent spaces.
* `IsCovariantDerivativeOn.hasMFDerivAt_timeDependentFlowOf_of_forall_eq_zero` and its
  differential and evaluation consequences require connection laws only on a set containing
  the point.
* `CovariantDerivative.hasMFDerivAt_timeDependentFlowOf_of_forall_eq_zero` and its consequences
  specialize these statements to a globally defined covariant derivative.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Theorem 9.48.
* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapter 4.
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, §7 (relative Moser theorem).

The coordinate variational argument uses
`TauCeti.exists_eventually_forall_hasDerivAt_fderiv_of_contDiffOn`. The connection bridge uses
`TauCeti.FirstJetBundle.connectionEquiv`, built from the local-frame comparison
`TauCeti.Manifold.covariantDerivative_eq_add_christoffelForm`.
-/

public section

open Bundle Set
open scoped ContDiff Manifold Topology

namespace TauCeti

open TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I 2 M]
  [BoundarylessManifold I M]
  {X : ℝ → Π x : M, TangentSpace I x} {x : M}

omit [FiniteDimensional ℝ E] [T2Space M] [BoundarylessManifold I M] in
private theorem contDiffOn_timeDependentField_coordinates
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent 1
      (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M))) (s t : ℝ) :
    ContDiffOn ℝ 1 (fun p : ℝ × E ↦ (t - s) •
      ((trivializationAt E (TangentSpace I) x)
        ⟨(extChartAt I x).symm p.2,
          X (s + p.1 * (t - s)) ((extChartAt I x).symm p.2)⟩).2)
      (univ ×ˢ interior (extChartAt I x).target) := by
  rintro p hp
  have hc := (contMDiffOn_extChartAt_symm x (n := 1) p.2
    (interior_subset hp.2)).contMDiffAt (mem_interior_iff_mem_nhds.1 hp.2)
  have hα : ContMDiffAt 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ) 1
      (fun q : ℝ × E ↦ s + q.1 * (t - s)) p :=
    contMDiffAt_iff_contDiffAt.2 (by fun_prop)
  have hp₂ : ContMDiffAt 𝓘(ℝ, ℝ × E) 𝓘(ℝ, E) 1 Prod.snd p :=
    contMDiffAt_iff_contDiffAt.2 (by fun_prop)
  have hh := hX.contMDiffAt.comp p
    (hα.prodMk
      (hc.comp p hp₂))
  have he : (⟨(extChartAt I x).symm p.2,
      X (s + p.1 * (t - s)) ((extChartAt I x).symm p.2)⟩ : TangentBundle I M) ∈
      (trivializationAt E (TangentSpace I) x).source := by
    simpa only [Trivialization.mem_source, TangentBundle.trivializationAt_baseSet,
      extChartAt_source] using
      (extChartAt I x).map_target (interior_subset hp.2)
  have hcoord :=
    ((trivializationAt E (TangentSpace I) x).contMDiffAt (IB := I) (n := 1) he).snd.comp p hh
  exact ((contMDiffAt_iff_contDiffAt.1 hcoord).const_smul (t - s)).contDiffWithinAt

private theorem eventually_timeDependentFlowOf_in_chart_ball
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent 1
      (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)))
    (s t : ℝ) (hx : ∀ u ∈ uIcc s t, X u x = 0) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ z in 𝓝 (extChartAt I x x), ∀ τ ∈ Icc (0 : ℝ) 1,
      ((s, s + τ * (t - s)), (extChartAt I x).symm z) ∈ timeDependentFlowDomain X ∧
      timeDependentFlowOf X s (s + τ * (t - s)) ((extChartAt I x).symm z) ∈
        (extChartAt I x).source ∧
      extChartAt I x
        (timeDependentFlowOf X s (s + τ * (t - s)) ((extChartAt I x).symm z)) ∈
        Metric.ball (extChartAt I x x) ε := by
  have : IsManifold I (1 : ℕ∞) M := IsManifold.of_le (n := 2) (by norm_num)
  let c := extChartAt I x
  let D : Set (ℝ × M) := {p | ((s, s + p.1 * (t - s)), p.2) ∈ timeDependentFlowDomain X}
  let N := c.source ∩ c ⁻¹' Metric.ball (c x) ε
  have hD : IsOpen D := (isOpen_timeDependentFlowDomain hX).preimage (by fun_prop)
  have hN : IsOpen N :=
    (continuousOn_extChartAt x).isOpen_inter_preimage
      (isOpen_extChartAt_source x) Metric.isOpen_ball
  have hF : ContinuousOn (fun p : ℝ × M ↦ timeDependentFlowOf X s (s + p.1 * (t - s)) p.2) D :=
    (contMDiffOn_timeDependentFlowOf (n := 1) le_rfl hX).continuousOn.comp
      (by fun_prop : ContinuousOn
        (fun p : ℝ × M ↦ ((s, s + p.1 * (t - s)), p.2)) D) (fun _ hp ↦ hp)
  have hgood := hF.isOpen_inter_preimage hD hN
  obtain ⟨T, U, -, hU, hIT, hxU, hTU⟩ := generalized_tube_lemma
    (isCompact_Icc (a := (0 : ℝ)) (b := 1)) (isCompact_singleton (x := x)) hgood (fun p hp ↦ by
      have hp₂ : p.2 = x := hp.2
      have hp₁ : s + p.1 * (t - s) ∈ uIcc s t := by
        simpa only [smul_eq_mul] using
          (convex_uIcc s t).add_smul_sub_mem left_mem_uIcc right_mem_uIcc hp.1
      refine ⟨?_, ?_⟩
      · simpa only [D, mem_ofPred_eq, hp₂] using
          mem_timeDependentFlowDomain_of_forall_mem_uIcc_eq_zero hX s (s + p.1 * (t - s))
            (fun u hu ↦ hx u (uIcc_subset_uIcc_left hp₁ hu))
      · have hfix := timeDependentFlowOf_eq_self_of_forall_mem_uIcc_eq_zero hX
          s (s + p.1 * (t - s))
          (fun u hu ↦ hx u (uIcc_subset_uIcc_left hp₁ hu))
        simp only [mem_preimage, hp₂, hfix]
        exact ⟨mem_extChartAt_source x, Metric.mem_ball_self hε⟩)
  have hc : ContinuousAt c.symm (c x) := continuousAt_extChartAt_symm x
  have hcxU : c.symm (c x) ∈ U :=
    hxU (by simp only [mem_singleton_iff, c, extChartAt_to_inv])
  filter_upwards [hc.preimage_mem_nhds (hU.mem_nhds hcxU)] with z hz τ hτ
  exact hTU (mk_mem_prod (hIT hτ) hz)

private theorem eventually_timeDependentFlowOf_chart_eq_localFlow
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent 1
      (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)))
    (s t : ℝ) (hx : ∀ u ∈ uIcc s t, X u x = 0) {ε : ℝ} (hε : 0 < ε)
    (hY : ContDiffOn ℝ 1 (fun p : ℝ × E ↦ (t - s) •
      FirstJetBundle.localRep I E (X (s + p.1 * (t - s))) x p.2)
      (Icc (0 : ℝ) 1 ×ˢ Metric.closedBall (extChartAt I x x) ε))
    {ψ : ℝ → E → E} (hψ₀ : ψ 0 = id)
    (hev : ∀ᶠ z in 𝓝 (extChartAt I x x), ∀ τ ∈ Icc (0 : ℝ) 1,
      ψ τ z ∈ Metric.ball (extChartAt I x x) ε ∧
        HasDerivAt (fun r ↦ ψ r z)
          ((t - s) • FirstJetBundle.localRep I E (X (s + τ * (t - s))) x (ψ τ z)) τ) :
    (fun z ↦ extChartAt I x (timeDependentFlowOf X s t ((extChartAt I x).symm z)))
      =ᶠ[𝓝 (extChartAt I x x)] ψ 1 := by
  have : IsManifold I (1 : ℕ∞) M := IsManifold.of_le (n := 2) (by norm_num)
  let c := extChartAt I x
  let e := trivializationAt E (TangentSpace I) x
  let Y : ℝ → E → E := fun τ z ↦ (t - s) •
    FirstJetBundle.localRep I E (X (s + τ * (t - s))) x z
  have htarget : c x ∈ interior c.target :=
    ModelWithCorners.isInteriorPoint_iff.1 BoundarylessManifold.isInteriorPoint
  obtain ⟨K, hK⟩ := (hY).exists_lipschitzOnWith
    one_ne_zero ((convex_Icc 0 1).prod (convex_closedBall (c x) ε))
    (isCompact_Icc.prod (isCompact_closedBall (c x) ε))
  have hKt (τ : ℝ) (hτ : τ ∈ Icc (0 : ℝ) 1) :
      LipschitzOnWith K (Y τ) (Metric.closedBall (c x) ε) := by
    have h := hK.comp (LipschitzWith.prodMk_left τ).lipschitzOnWith
      (fun z hz ↦ mk_mem_prod hτ hz)
    rwa [mul_one] at h
  filter_upwards [hev, eventually_timeDependentFlowOf_in_chart_ball hX s t hx hε,
    isOpen_interior.mem_nhds htarget] with z hz hflowz hzc
  let φ : ℝ → E := fun τ ↦ c (timeDependentFlowOf X s (s + τ * (t - s)) (c.symm z))
  have hφ (τ : ℝ) (hτ : τ ∈ Icc (0 : ℝ) 1) : HasDerivAt φ (Y τ (φ τ)) τ := by
    have hsrc := (hflowz τ hτ).2.1
    have hd := (hasMFDerivAt_timeDependentFlowOf hX
      (hflowz τ hτ).1).hasDerivAt_extChartAt_comp hsrc
    have htime : HasDerivAt (fun r : ℝ ↦ s + r * (t - s)) (t - s) τ := by
      simpa only [zero_add, one_mul, Pi.add_apply, id_eq] using! (hasDerivAt_const τ s).add
        ((hasDerivAt_id τ).mul_const (t - s))
    have hcomp := hd.scomp τ htime
    dsimp only [Y, φ]
    rw [FirstJetBundle.localRep_apply, c.left_inv hsrc]
    simpa only [Function.comp_def, c, e,
      TangentBundle.trivializationAt_apply_tangentCoordChange] using hcomp
  have hsame := ODE_solution_unique_of_mem_Icc_right
    (fun τ hτ ↦ hKt τ (Ico_subset_Icc_self hτ))
    (fun τ hτ ↦ (hφ τ hτ).continuousAt.continuousWithinAt)
    (fun τ hτ ↦ (hφ τ (Ico_subset_Icc_self hτ)).hasDerivWithinAt)
    (fun τ hτ ↦ Metric.ball_subset_closedBall (hflowz τ (Ico_subset_Icc_self hτ)).2.2)
    (fun τ hτ ↦ (hz τ hτ).2.continuousAt.continuousWithinAt)
    (fun τ hτ ↦ (hz τ (Ico_subset_Icc_self hτ)).2.hasDerivWithinAt)
    (fun τ hτ ↦ Metric.ball_subset_closedBall (hz τ (Ico_subset_Icc_self hτ)).1)
    (by simp only [φ, zero_mul, add_zero, timeDependentFlowOf_self, hψ₀, id_eq,
      c.right_inv (interior_subset hzc)]) (right_mem_Icc.2 zero_le_one)
  simpa only [φ, one_mul, add_sub_cancel] using hsame

omit [FiniteDimensional ℝ E] [T2Space M] in
private theorem fderiv_timeDependentField_coordinates_eq_zero
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent 1
      (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)))
    (u a : ℝ) (hjet : FirstJetBundle.jet I E (X u) x = 0) :
    fderiv ℝ (fun z ↦ a • FirstJetBundle.localRep I E (X u) x z)
      (extChartAt I x x) = 0 := by
  have hS : MDifferentiableAt I I.tangent
      (fun y ↦ (⟨y, X u y⟩ : TangentBundle I M)) x :=
    ((hX.comp (contMDiff_const.prodMk contMDiff_id)).mdifferentiable one_ne_zero) x
  have hrep := (FirstJetBundle.differentiableWithinAt_localRep I E hS
    (FirstJetBundle.mem_baseSet_self E (TangentSpace I) x)).hasFDerivWithinAt
  rw [FirstJetBundle.fderivWithin_localRep_eq_zero_of_jet_eq_zero I E hjet] at hrep
  exact ((hrep.hasFDerivAt
    (range_mem_nhds_isInteriorPoint BoundarylessManifold.isInteriorPoint)).const_smul
    a).fderiv.trans (smul_zero _)

private theorem hasFDerivAt_timeDependentFlowOf_chart_of_jet_eq_zero
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent 1
      (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)))
    (s t : ℝ)
    (hjet : ∀ u ∈ uIcc s t, FirstJetBundle.jet I E (X u) x = 0) :
    HasFDerivAt (fun z ↦ extChartAt I x
      (timeDependentFlowOf X s t ((extChartAt I x).symm z)))
      (ContinuousLinearMap.id ℝ E) (extChartAt I x x) := by
  have hx (u : ℝ) (hu : u ∈ uIcc s t) : X u x = 0 := by
    simpa only [FirstJetBundle.value_jet, map_zero] using
      congrArg (FirstJetBundle.value I E x) (hjet u hu)
  let c := extChartAt I x
  let Y : ℝ → E → E := fun τ z ↦ (t - s) •
    FirstJetBundle.localRep I E (X (s + τ * (t - s))) x z
  have htarget : c x ∈ interior c.target :=
    ModelWithCorners.isInteriorPoint_iff.1 BoundarylessManifold.isInteriorPoint
  obtain ⟨ε, hε, hεc⟩ := Metric.nhds_basis_closedBall.mem_iff.1
    (isOpen_interior.mem_nhds htarget)
  have hY : ContDiffOn ℝ 1 (fun p : ℝ × E ↦ Y p.1 p.2)
      (univ ×ˢ interior c.target) := by
    simpa only [Y, FirstJetBundle.localRep_apply] using
      contDiffOn_timeDependentField_coordinates (x := x) hX s t
  have htime (τ : ℝ) (hτ : τ ∈ Icc (0 : ℝ) 1) : s + τ * (t - s) ∈ uIcc s t := by
    simpa only [smul_eq_mul] using
      (convex_uIcc s t).add_smul_sub_mem left_mem_uIcc right_mem_uIcc hτ
  have hY₀ (τ : ℝ) (hτ : τ ∈ Icc (0 : ℝ) 1) : Y τ (c x) = 0 := by
    dsimp only [Y]
    rw [FirstJetBundle.localRep_apply, extChartAt_to_inv, hx _ (htime τ hτ)]
    rw [← (trivializationAt E (TangentSpace I) x).continuousLinearMapAt_apply_of_mem ℝ
      (mem_baseSet_trivializationAt E (TangentSpace I) x), map_zero, smul_zero]
  have hY' (τ : ℝ) (hτ : τ ∈ Icc (0 : ℝ) 1) : fderiv ℝ (Y τ) (c x) = 0 :=
    fderiv_timeDependentField_coordinates_eq_zero hX _ _ (hjet _ (htime τ hτ))
  -- Subtracting the value at the center makes it stationary for all times; on the
  -- interval of comparison this changes neither the field nor its spatial derivative.
  let Z : ℝ → E → E := fun τ z ↦ Y τ z - Y τ (c x)
  have hZ : ContDiffOn ℝ 1 (fun p : ℝ × E ↦ Z p.1 p.2)
      (univ ×ˢ interior c.target) :=
    hY.sub (hY.comp (contDiff_fst.prodMk contDiff_const).contDiffOn
      (fun _ _ ↦ ⟨mem_univ _, htarget⟩))
  have hZ' (τ : ℝ) (hτ : τ ∈ Icc (0 : ℝ) 1) : fderiv ℝ (Z τ) (c x) = 0 := by
    simpa only [Z, fderiv_sub_const] using hY' τ hτ
  obtain ⟨ψ, hψ₀, hψderiv, hev⟩ := exists_localFlow_hasFDerivAt_id isOpen_univ
    Metric.isOpen_ball (subset_univ _) (Metric.mem_ball_self hε)
    (hZ.mono (prod_mono subset_rfl (Metric.ball_subset_closedBall.trans hεc)))
    (fun τ _ ↦ sub_self _) hZ'
  have hevY : ∀ᶠ z in 𝓝 (c x), ∀ τ ∈ Icc (0 : ℝ) 1,
      ψ τ z ∈ Metric.ball (c x) ε ∧ HasDerivAt (fun r ↦ ψ r z) (Y τ (ψ τ z)) τ := by
    filter_upwards [hev] with z hz τ hτ
    simpa only [Z, hY₀ τ hτ, sub_zero] using hz τ hτ
  exact hψderiv.congr_of_eventuallyEq
    (eventually_timeDependentFlowOf_chart_eq_localFlow hX s t hx hε
      (hY.mono (prod_mono (subset_univ _) hεc)) hψ₀ hevY)


omit [FiniteDimensional ℝ E] in
/-- A time-dependent field with zero first jet at `x` between two times fixes `x`
under the corresponding time map. No vanishing assumption is needed outside that interval. -/
theorem timeDependentFlowOf_eq_self_of_jet_eq_zero [CompleteSpace E]
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent 1
      (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)))
    (s t : ℝ) (hjet : ∀ u ∈ uIcc s t, FirstJetBundle.jet I E (X u) x = 0) :
    timeDependentFlowOf X s t x = x := by
  have : IsManifold I (1 : ℕ∞) M := .of_le (n := 2) (by norm_num)
  apply timeDependentFlowOf_eq_self_of_forall_mem_uIcc_eq_zero hX s t
  intro u hu
  simpa only [FirstJetBundle.value_jet, map_zero] using
    congrArg (FirstJetBundle.value I E x) (hjet u hu)

/-- If a jointly `C¹` time-dependent vector field has zero first jet at `x` between
`s` and `t`, its time map has identity derivative.
The identity is transported to the target tangent space using the stationary-point equation. No
completeness is required. -/
theorem hasMFDerivAt_timeDependentFlowOf_of_jet_eq_zero
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent 1
      (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)))
    (s t : ℝ)
    (hjet : ∀ u ∈ uIcc s t, FirstJetBundle.jet I E (X u) x = 0) :
    HasMFDerivAt I I (timeDependentFlowOf X s t) x
      ((timeDependentFlowOf_eq_self_of_jet_eq_zero hX s t hjet).symm ▸
          ContinuousLinearMap.id ℝ (TangentSpace I x)) := by
  have hcoord := hasFDerivAt_timeDependentFlowOf_chart_of_jet_eq_zero hX s t hjet
  have : IsManifold I (1 : ℕ∞) M := .of_le (n := 2) (by norm_num)
  have hfix := timeDependentFlowOf_eq_self_of_jet_eq_zero hX s t hjet
  have hcont : ContinuousAt (timeDependentFlowOf X s t) x :=
    (((contMDiffOn_timeDependentFlowOf (n := 1) le_rfl hX).contMDiffAt
      ((isOpen_timeDependentFlowDomain hX).mem_nhds
        (mem_timeDependentFlowDomain_of_forall_mem_uIcc_eq_zero hX s t (fun u hu ↦ by
          simpa only [FirstJetBundle.value_jet, map_zero] using
            congrArg (FirstJetBundle.value I E x) (hjet u hu))))).comp x
      (contMDiffAt_const.prodMk contMDiffAt_id)).continuousAt
  have hcast (y : M) (hy : x = y) :
      (tangentSpaceCastModel I y).toContinuousLinearMap ∘L
        (hy ▸ ContinuousLinearMap.id ℝ (TangentSpace I x) :
          TangentSpace I x →L[ℝ] TangentSpace I y) ∘L
        (tangentSpaceCastModel I x).symm.toContinuousLinearMap =
      ContinuousLinearMap.id ℝ E := by
    subst y
    ext v
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply]
  refine ⟨hcont, ?_⟩
  rw [hcast _ hfix.symm]
  simpa only [writtenInExtChartAt, hfix, Function.comp_def] using hcoord.hasFDerivWithinAt

/-- A jointly `C¹` time-dependent field whose first jet vanishes at `x` between
`s` and `t` has identity differential on all tangent vectors
at `x`. The identity is transported to the tangent space at the flow image. -/
theorem mfderiv_timeDependentFlowOf_eq_id_of_jet_eq_zero
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent 1
      (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)))
    (s t : ℝ)
    (hjet : ∀ u ∈ uIcc s t, FirstJetBundle.jet I E (X u) x = 0) :
    mfderiv I I (timeDependentFlowOf X s t) x =
      (timeDependentFlowOf_eq_self_of_jet_eq_zero hX s t hjet).symm ▸
          ContinuousLinearMap.id ℝ (TangentSpace I x) :=
  (hasMFDerivAt_timeDependentFlowOf_of_jet_eq_zero hX s t hjet).mfderiv

/-- For a jointly `C¹` time-dependent field whose first jet vanishes at `x` between
`s` and `t`, the linearized flow fixes each tangent vector at
`x`, transported to the tangent space at the image. -/
theorem mfderiv_timeDependentFlowOf_eq_id_of_jet_eq_zero_apply
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent 1
      (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)))
    (s t : ℝ)
    (hjet : ∀ u ∈ uIcc s t, FirstJetBundle.jet I E (X u) x = 0)
    (v : TangentSpace I x) :
    mfderiv I I (timeDependentFlowOf X s t) x v =
      (timeDependentFlowOf_eq_self_of_jet_eq_zero hX s t hjet).symm ▸ v := by
  have happly (y : M) (hy : x = y) :
      (hy ▸ ContinuousLinearMap.id ℝ (TangentSpace I x) :
        TangentSpace I x →L[ℝ] TangentSpace I y) v = hy ▸ v := by
    subst y
    exact ContinuousLinearMap.id_apply v
  rw [mfderiv_timeDependentFlowOf_eq_id_of_jet_eq_zero hX s t hjet, happly]

end TauCeti


namespace IsCovariantDerivativeOn

open TauCeti TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I 2 M]
  [BoundarylessManifold I M]
  {X : ℝ → Π x : M, TangentSpace I x} {x : M}

variable {cov : (Π x : M, TangentSpace I x) →
    Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x}
  {U : Set M}

/-- If a jointly `C¹` time-dependent field and its covariant derivative vanish at `x`
between `s` and `t`, the time map has identity derivative. The connection laws need hold
only on a set containing `x`. No completeness is required. -/
theorem hasMFDerivAt_timeDependentFlowOf_of_forall_eq_zero
    (hcov : IsCovariantDerivativeOn E cov U) (hxU : x ∈ U)
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent 1
      (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)))
    (s t : ℝ) (hx : ∀ u ∈ uIcc s t, X u x = 0)
    (hcovzero : ∀ u ∈ uIcc s t, cov (X u) x = 0) :
    HasMFDerivAt I I (timeDependentFlowOf X s t) x
      ((timeDependentFlowOf_eq_self_of_forall_mem_uIcc_eq_zero hX s t hx).symm ▸
          ContinuousLinearMap.id ℝ (TangentSpace I x)) := by
  apply TauCeti.hasMFDerivAt_timeDependentFlowOf_of_jet_eq_zero hX s t
  intro u hu
  exact (FirstJetBundle.jet_eq_zero_iff hcov hxU
    (((hX.comp (contMDiff_const.prodMk contMDiff_id)).mdifferentiable one_ne_zero) x)).2
      ⟨hx u hu, hcovzero u hu⟩

/-- The time map of a field with zero value and covariant derivative at `x` between two
times has identity differential, transported to the tangent space of the image. -/
theorem mfderiv_timeDependentFlowOf_eq_id_of_forall_eq_zero
    (hcov : IsCovariantDerivativeOn E cov U) (hxU : x ∈ U)
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent 1
      (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)))
    (s t : ℝ) (hx : ∀ u ∈ uIcc s t, X u x = 0)
    (hcovzero : ∀ u ∈ uIcc s t, cov (X u) x = 0) :
    mfderiv I I (timeDependentFlowOf X s t) x =
      (timeDependentFlowOf_eq_self_of_forall_mem_uIcc_eq_zero hX s t hx).symm ▸
          ContinuousLinearMap.id ℝ (TangentSpace I x) :=
  (hcov.hasMFDerivAt_timeDependentFlowOf_of_forall_eq_zero hxU hX s t hx hcovzero).mfderiv

/-- Under interval vanishing of the field and its covariant derivative, the linearized
flow fixes each tangent vector, transported to the tangent space of the image. -/
theorem mfderiv_timeDependentFlowOf_eq_id_of_forall_eq_zero_apply
    (hcov : IsCovariantDerivativeOn E cov U) (hxU : x ∈ U)
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent 1
      (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)))
    (s t : ℝ) (hx : ∀ u ∈ uIcc s t, X u x = 0)
    (hcovzero : ∀ u ∈ uIcc s t, cov (X u) x = 0)
    (v : TangentSpace I x) :
    mfderiv I I (timeDependentFlowOf X s t) x v =
      (timeDependentFlowOf_eq_self_of_forall_mem_uIcc_eq_zero hX s t hx).symm ▸ v := by
  apply TauCeti.mfderiv_timeDependentFlowOf_eq_id_of_jet_eq_zero_apply hX s t _ v
  intro u hu
  exact (FirstJetBundle.jet_eq_zero_iff hcov hxU
    (((hX.comp (contMDiff_const.prodMk contMDiff_id)).mdifferentiable one_ne_zero) x)).2
      ⟨hx u hu, hcovzero u hu⟩

end IsCovariantDerivativeOn

namespace CovariantDerivative

open TauCeti TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I 2 M]
  [BoundarylessManifold I M]
  {X : ℝ → Π x : M, TangentSpace I x} {x : M}

/-- If a jointly `C¹` time-dependent field and its covariant derivative vanish at `x`
between `s` and `t`, its time map has identity derivative. No completeness is required. -/
theorem hasMFDerivAt_timeDependentFlowOf_of_forall_eq_zero
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent 1
      (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)))
    (s t : ℝ) (hx : ∀ u ∈ uIcc s t, X u x = 0)
    (hcovzero : ∀ u ∈ uIcc s t, cov (X u) x = 0) :
    HasMFDerivAt I I (timeDependentFlowOf X s t) x
      ((timeDependentFlowOf_eq_self_of_forall_mem_uIcc_eq_zero hX s t hx).symm ▸
          ContinuousLinearMap.id ℝ (TangentSpace I x)) :=
  cov.isCovariantDerivativeOnUniv.hasMFDerivAt_timeDependentFlowOf_of_forall_eq_zero
    (mem_univ x) hX s t hx hcovzero

/-- Interval vanishing of a field and its covariant derivative gives identity differential
of the time map, transported to the tangent space of the image. -/
theorem mfderiv_timeDependentFlowOf_eq_id_of_forall_eq_zero
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent 1
      (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)))
    (s t : ℝ) (hx : ∀ u ∈ uIcc s t, X u x = 0)
    (hcovzero : ∀ u ∈ uIcc s t, cov (X u) x = 0) :
    mfderiv I I (timeDependentFlowOf X s t) x =
      (timeDependentFlowOf_eq_self_of_forall_mem_uIcc_eq_zero hX s t hx).symm ▸
          ContinuousLinearMap.id ℝ (TangentSpace I x) :=
  cov.isCovariantDerivativeOnUniv.mfderiv_timeDependentFlowOf_eq_id_of_forall_eq_zero
    (mem_univ x) hX s t hx hcovzero

/-- Interval vanishing of a field and its covariant derivative makes the linearized flow
fix each tangent vector, transported to the tangent space of the image. -/
theorem mfderiv_timeDependentFlowOf_eq_id_of_forall_eq_zero_apply
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent 1
      (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)))
    (s t : ℝ) (hx : ∀ u ∈ uIcc s t, X u x = 0)
    (hcovzero : ∀ u ∈ uIcc s t, cov (X u) x = 0)
    (v : TangentSpace I x) :
    mfderiv I I (timeDependentFlowOf X s t) x v =
      (timeDependentFlowOf_eq_self_of_forall_mem_uIcc_eq_zero hX s t hx).symm ▸ v :=
  cov.isCovariantDerivativeOnUniv.mfderiv_timeDependentFlowOf_eq_id_of_forall_eq_zero_apply
    (mem_univ x) hX s t hx hcovzero v

end CovariantDerivative

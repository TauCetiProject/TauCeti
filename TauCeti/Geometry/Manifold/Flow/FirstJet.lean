/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Flow.TimeDependent
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import TauCeti.Dynamics.Flow.RestPoint
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LocalFrame
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Time-dependent flows of fields with zero first jet

A jointly `C¹` time-dependent vector field vanishing at a point at all times and to first
order there between two times has a flow fixing that point with identity differential on its full
ambient tangent space. Vanishing of the first derivative is expressed using an auxiliary connection.
Both `HasMFDerivAt` and its differential and
pointwise consequences are provided. The constant solution exists for all time even when the
vector field is not complete; vanishing of the covariant derivative is needed only between the
specified times.

This is the flow ingredient in the refinement of relative Moser's theorem which preserves the
ambient first jet along a submanifold, rather than just its points.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapter 6
  (variations and the symmetry lemma).
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, §7 (relative Moser theorem).
-/

public section

open Bundle Set
open scoped ContDiff Manifold Topology

namespace CovariantDerivative

open TauCeti TauCeti.Manifold

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
    (hx : ∀ u, X u x = 0) (s t : ℝ) {ε : ℝ} (hε : 0 < ε) :
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
      refine ⟨?_, ?_⟩
      · simpa only [D, mem_ofPred_eq, hp₂] using
          mem_timeDependentFlowDomain_of_forall_eq_zero hx s (s + p.1 * (t - s))
      · simp only [mem_preimage, hp₂, timeDependentFlowOf_eq_self_of_forall_eq_zero hX hx]
        exact ⟨mem_extChartAt_source x, Metric.mem_ball_self hε⟩)
  have hc : ContinuousAt c.symm (c x) := continuousAt_extChartAt_symm x
  have hcxU : c.symm (c x) ∈ U :=
    hxU (by simp only [mem_singleton_iff, c, extChartAt_to_inv])
  filter_upwards [hc.preimage_mem_nhds (hU.mem_nhds hcxU)] with z hz τ hτ
  exact hTU (mk_mem_prod (hIT hτ) hz)

private theorem hasFDerivAt_timeDependentFlowOf_chart_of_forall_eq_zero
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent 1
      (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)))
    (hx : ∀ u, X u x = 0) (s t : ℝ)
    (hcov : ∀ u ∈ uIcc s t, cov (X u) x = 0) :
    HasFDerivAt (fun z ↦ extChartAt I x
      (timeDependentFlowOf X s t ((extChartAt I x).symm z)))
      (ContinuousLinearMap.id ℝ E) (extChartAt I x x) := by
  let c := extChartAt I x
  let e := trivializationAt E (TangentSpace I) x
  let Y : ℝ → E → E := fun τ z ↦ (t - s) •
    (e ⟨c.symm z, X (s + τ * (t - s)) (c.symm z)⟩).2
  have htarget : c x ∈ interior c.target :=
    ModelWithCorners.isInteriorPoint_iff.1 BoundarylessManifold.isInteriorPoint
  obtain ⟨ε, hε, hεc⟩ := Metric.nhds_basis_closedBall.mem_iff.1
    (isOpen_interior.mem_nhds htarget)
  have hY := contDiffOn_timeDependentField_coordinates (x := x) hX s t
  have hY₀ (τ : ℝ) : Y τ (c x) = 0 := by
    dsimp only [Y]
    rw [extChartAt_to_inv, hx]
    rw [← e.continuousLinearMapAt_apply_of_mem ℝ
      (mem_baseSet_trivializationAt E (TangentSpace I) x), map_zero, smul_zero]
  -- At a zero of the field, the Christoffel term vanishes. Thus the covariant
  -- first-jet condition is exactly the vanishing of the coordinate derivative.
  have hY' (τ : ℝ) (hτ : τ ∈ Icc (0 : ℝ) 1) : fderiv ℝ (Y τ) (c x) = 0 := by
    have hτst : s + τ * (t - s) ∈ uIcc s t := by
      rw [mem_uIcc]
      rcases le_total s t with hst | hts
      · left
        constructor <;> nlinarith [hτ.1, hτ.2]
      · right
        constructor <;> nlinarith [hτ.1, hτ.2]
    have hS : MDifferentiableAt I I.tangent
        (fun y ↦ (⟨y, X (s + τ * (t - s)) y⟩ : TangentBundle I M)) x :=
      ((hX.comp (contMDiff_const.prodMk contMDiff_id)).mdifferentiable one_ne_zero) x
    have hzero := hx (s + τ * (t - s))
    have hcovzero := hcov (s + τ * (t - s)) hτst
    have hbase : HasFDerivAt (fun z ↦ (e ⟨c.symm z,
        X (s + τ * (t - s)) (c.symm z)⟩).2) (0 : E →L[ℝ] E) (c x) := by
      let b := Module.finBasis ℝ E
      let g : M → E := fun y ↦ (e ⟨y, (X (s + τ * (t - s))) y⟩).2
      have he : x ∈ e.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) x
      have hg : MDifferentiableAt I 𝓘(ℝ, E) g x :=
        (e.mdifferentiableAt_section_iff I (X (s + τ * (t - s))) he).1 hS
      have hcoeff : ∀ i, (fun y ↦ e.localFrameCoeff I b i y ((X (s + τ * (t - s))) y)) =ᶠ[𝓝 x]
          fun y ↦ b.coord i (g y) := by
        intro i
        filter_upwards [e.open_baseSet.mem_nhds he] with y hy
        exact e.localFrameCoeff_eq_coeff hy
      have hflat := TauCeti.Manifold.frameCovariantDerivative_eq_symmL_comp b
        hg.hasMFDerivAt hcoeff he
      have h := TauCeti.Manifold.covariantDerivative_eq_add_christoffelForm b
        cov.isCovariantDerivativeOn he hS
      rw [hzero, map_zero, add_zero, hcovzero, hflat] at h
      have hD : mvfderiv I g x = 0 := by
        ext v
        have hv := congrArg (fun L : TangentSpace I x →L[ℝ] TangentSpace I x ↦
          e.continuousLinearMapAt ℝ x (L v)) h
        simp only [zero_apply, map_zero] at hv
        -- Read the model-valued derivative in `E` so the inverse trivialization can cancel.
        change 0 = e.continuousLinearMapAt ℝ x
          (e.symmL ℝ x (mvfderiv I g x v)) at hv
        rw [e.continuousLinearMapAt_symmL he] at hv
        exact hv.symm
      have hD' : mfderiv I 𝓘(ℝ, E) g x = 0 := hD
      have hf := hg.hasMFDerivAt
      rw [hD'] at hf
      have hd : HasFDerivWithinAt (g ∘ (extChartAt I x).symm) (0 : E →L[ℝ] E)
          (range I) (extChartAt I x x) := by
        simpa only [writtenInExtChartAt, extChartAt_model_space_eq_id, PartialEquiv.refl_coe,
          Function.id_comp, ContinuousLinearMap.comp_zero, ContinuousLinearMap.zero_comp] using hf.2
      exact hd.hasFDerivAt (range_mem_nhds_isInteriorPoint BoundarylessManifold.isInteriorPoint)
    exact (hbase.const_smul (t - s)).fderiv.trans (smul_zero _)
  -- The existing finite-dimensional C¹ rest-point theorem supplies a local flow and
  -- its variational equation, whose right-hand side is now zero along the fixed point.
  have hYball : ContDiffOn ℝ 1 (fun p : ℝ × E ↦ Y p.1 p.2)
      (univ ×ˢ Metric.ball (c x) ε) :=
    hY.mono (prod_mono subset_rfl (Metric.ball_subset_closedBall.trans hεc))
  obtain ⟨ψ, ψ', hψ, -, -, -, hψ₀, hψfix, hev⟩ :=
    exists_eventually_forall_hasDerivAt_fderiv_of_contDiffOn (r := 1) le_rfl isOpen_univ
      Metric.isOpen_ball (subset_univ _) (Metric.mem_ball_self hε) hYball (fun τ _ ↦ hY₀ τ)
  have hψx (τ : ℝ) : ψ τ (c x) = c x := hψfix _ (fun τ _ ↦ hY₀ τ) τ
  have hDψ (τ : ℝ) (hτ : τ ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun r ↦ fderiv ℝ (ψ r) (c x)) 0 τ := by
    simpa only [hψx, hY' τ hτ, ContinuousLinearMap.zero_comp] using
      (hev.self_of_nhds τ hτ).2.2
  have hDψ₁ : fderiv ℝ (ψ 1) (c x) = ContinuousLinearMap.id ℝ E := by
    have hbound := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_deriv_le
      (fun τ hτ ↦ (hDψ τ hτ).differentiableAt)
      (fun τ hτ ↦ by rw [(hDψ τ hτ).deriv, norm_zero])
      (left_mem_Icc.2 zero_le_one) (right_mem_Icc.2 zero_le_one)
    have hcst : fderiv ℝ (ψ 1) (c x) = fderiv ℝ (ψ 0) (c x) := by
      simpa only [zero_mul, norm_le_zero_iff, sub_eq_zero] using hbound
    simpa only [hψ₀, fderiv_id] using hcst
  have hψderiv : HasFDerivAt (ψ 1) (ContinuousLinearMap.id ℝ E) (c x) := by
    rw [← hDψ₁]
    exact (hψ.differentiable one_ne_zero _).hasFDerivAt
  -- Compare this local flow to the actual maximal manifold flow in the same chart.
  -- Compactness keeps nearby trajectories in one ball for the whole rescaled interval.
  obtain ⟨K, hK⟩ := (hY.mono (prod_mono (subset_univ (Icc (0 : ℝ) 1)) hεc)).exists_lipschitzOnWith
    one_ne_zero ((convex_Icc 0 1).prod (convex_closedBall (c x) ε))
    (isCompact_Icc.prod (isCompact_closedBall (c x) ε))
  have hKt (τ : ℝ) (hτ : τ ∈ Icc (0 : ℝ) 1) :
      LipschitzOnWith K (Y τ) (Metric.closedBall (c x) ε) := by
    have h := hK.comp (LipschitzWith.prodMk_left τ).lipschitzOnWith
      (fun z hz ↦ mk_mem_prod hτ hz)
    rwa [mul_one] at h
  have hEq : (fun z ↦ c (timeDependentFlowOf X s t (c.symm z))) =ᶠ[𝓝 (c x)] ψ 1 := by
    filter_upwards [hev, eventually_timeDependentFlowOf_in_chart_ball hX hx s t hε,
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
      rw [c.left_inv hsrc]
      simpa only [Function.comp_def, c, e, TangentBundle.trivializationAt_apply,
        tangentCoordChange_def, extChartAt] using hcomp
    have hsame := ODE_solution_unique_of_mem_Icc_right
      (fun τ hτ ↦ hKt τ (Ico_subset_Icc_self hτ))
      (fun τ hτ ↦ (hφ τ hτ).continuousAt.continuousWithinAt)
      (fun τ hτ ↦ (hφ τ (Ico_subset_Icc_self hτ)).hasDerivWithinAt)
      (fun τ hτ ↦ Metric.ball_subset_closedBall (hflowz τ (Ico_subset_Icc_self hτ)).2.2)
      (fun τ hτ ↦ (hz τ hτ).2.1.continuousAt.continuousWithinAt)
      (fun τ hτ ↦ (hz τ (Ico_subset_Icc_self hτ)).2.1.hasDerivWithinAt)
      (fun τ hτ ↦ Metric.ball_subset_closedBall (hz τ (Ico_subset_Icc_self hτ)).1)
      (by simp only [φ, zero_mul, add_zero, timeDependentFlowOf_self, hψ₀, id_eq,
        c.right_inv (interior_subset hzc)]) (right_mem_Icc.2 zero_le_one)
    simpa only [φ, one_mul, add_sub_cancel] using hsame
  exact hψderiv.congr_of_eventuallyEq hEq


/-- If a jointly `C¹` time-dependent vector field vanishes at `x` at every time and its
covariant derivative vanishes there between `s` and `t`, its time map has identity derivative.
The identity is transported to the target tangent space using the stationary-point equation. No
completeness is required. -/
theorem hasMFDerivAt_timeDependentFlowOf_of_forall_eq_zero
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent 1
      (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)))
    (hx : ∀ u, X u x = 0) (s t : ℝ)
    (hcov : ∀ u ∈ uIcc s t, cov (X u) x = 0) :
    HasMFDerivAt I I (timeDependentFlowOf X s t) x
      ((timeDependentFlowOf_eq_self_of_forall_eq_zero hX hx s t).symm ▸
          ContinuousLinearMap.id ℝ (TangentSpace I x)) := by
  have hcoord := hasFDerivAt_timeDependentFlowOf_chart_of_forall_eq_zero cov hX hx s t hcov
  have : IsManifold I (1 : ℕ∞) M := .of_le (n := 2) (by norm_num)
  have hfix := timeDependentFlowOf_eq_self_of_forall_eq_zero hX hx s t
  have hcont : ContinuousAt (timeDependentFlowOf X s t) x :=
    (((contMDiffOn_timeDependentFlowOf (n := 1) le_rfl hX).contMDiffAt
      ((isOpen_timeDependentFlowDomain hX).mem_nhds
        (mem_timeDependentFlowDomain_of_forall_eq_zero hx s t))).comp x
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

/-- A jointly `C¹` time-dependent field vanishing at `x` at every time and whose covariant
derivative vanishes at `x` between `s` and `t` has identity differential on all tangent vectors
at `x`. The identity is transported to the tangent space at the flow image. -/
theorem mfderiv_timeDependentFlowOf_eq_id_of_forall_eq_zero
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent 1
      (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)))
    (hx : ∀ u, X u x = 0) (s t : ℝ)
    (hcov : ∀ u ∈ uIcc s t, cov (X u) x = 0) :
    mfderiv I I (timeDependentFlowOf X s t) x =
      (timeDependentFlowOf_eq_self_of_forall_eq_zero hX hx s t).symm ▸
          ContinuousLinearMap.id ℝ (TangentSpace I x) :=
  (cov.hasMFDerivAt_timeDependentFlowOf_of_forall_eq_zero hX hx s t hcov).mfderiv

/-- For a jointly `C¹` time-dependent field vanishing at `x` at every time and whose covariant
derivative vanishes at `x` between `s` and `t`, the linearized flow fixes each tangent vector at
`x`, transported to the tangent space at the image. -/
theorem mfderiv_timeDependentFlowOf_eq_id_of_forall_eq_zero_apply
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent 1
      (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)))
    (hx : ∀ u, X u x = 0) (s t : ℝ)
    (hcov : ∀ u ∈ uIcc s t, cov (X u) x = 0)
    (v : TangentSpace I x) :
    mfderiv I I (timeDependentFlowOf X s t) x v =
      (timeDependentFlowOf_eq_self_of_forall_eq_zero hX hx s t).symm ▸ v := by
  have happly (y : M) (hy : x = y) :
      (hy ▸ ContinuousLinearMap.id ℝ (TangentSpace I x) :
        TangentSpace I x →L[ℝ] TangentSpace I y) v = hy ▸ v := by
    subst y
    exact ContinuousLinearMap.id_apply v
  rw [cov.mfderiv_timeDependentFlowOf_eq_id_of_forall_eq_zero hX hx s t hcov, happly]

end CovariantDerivative

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Restriction
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Existence
import TauCeti.Geometry.Manifold.ContMDiff.Subtype
import TauCeti.Geometry.Manifold.IsManifold.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic

/-!
# Chartwise realization of a Riemannian metric on the model space

Around an interior point `x₀` of a smooth Riemannian manifold `(M, g)` modelled on `(E, H, I)`, the
inverse extended chart `(extChartAt I x₀).symm` pulls `g` back to a smooth Riemannian metric on an
open coordinate ball in `E` centred at `extChartAt I x₀ x₀`. Extending that local metric from a
closed ball to all of `E` via `TauCeti.exists_contMDiffRiemannianMetric_inner_eq_of_locallyFinite`
produces a global smooth Riemannian metric `gE` on the model space `E` for which the restricted
extended chart is a smooth `TauCeti.RiemannianIsometry` from an open neighbourhood `W` of `x₀` onto
the open coordinate ball in `(E, gE)`.

This transfers local Riemannian PDE and curvature problems around an interior point of a manifold
to global problems on `(E, gE)` via `TauCeti.IsLocalRiemannianIsometry`, without requiring `M` to
be boundaryless or paracompact.

## Main results

* `TauCeti.IsLocalRiemannianIsometry.of_comp` and
  `TauCeti.IsLocalRiemannianIsometry.inclusion`: left-cancellation for local Riemannian isometries
  and local Riemannian isometry of open-submanifold inclusions.
* `Bundle.ContMDiffRiemannianMetric.exists_contMDiffRiemannianMetric_model_space_of_isInteriorPoint`
  constructs, near an interior point `x₀`, a global metric `gE` on `E` and a `RiemannianIsometry`
  realizing `extChartAt I x₀` from an open chart neighbourhood `W ⊆ U` of `x₀` onto an open ball
  around `extChartAt I x₀ x₀`.
* `Bundle.ContMDiffRiemannianMetric.exists_contMDiffRiemannianMetric_model_space`: the
  `BoundarylessManifold` specialization.
* `TauCeti.exists_contMDiffRiemannianMetric_model_space_of_isInteriorPoint` and
  `TauCeti.exists_contMDiffRiemannianMetric_model_space`: the corresponding statements for an
  installed `RiemannianBundle` instance.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 2.
-/

public section

open Bundle Filter Function Metric Set TopologicalSpace
open scoped ContDiff Manifold Topology TauCeti

noncomputable section

namespace TauCeti.IsLocalRiemannianIsometry

section Cancellation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  {H'' : Type*} [TopologicalSpace H''] {K : ModelWithCorners ℝ G H''}
  {P : Type*} [TopologicalSpace P] [ChartedSpace H'' P]
  [RiemannianBundle (fun z : P ↦ TangentSpace K z)]

/-- Left-cancellation for local Riemannian isometries: if `g` and `g ∘ f` are local Riemannian
isometries and `f` is smooth, then `f` is a local Riemannian isometry. -/
theorem of_comp {f : M → N} {g : N → P} (hg : IsLocalRiemannianIsometry J K g)
    (hgf : IsLocalRiemannianIsometry I K (g ∘ f)) (hf : ContMDiff I J ∞ f) :
    IsLocalRiemannianIsometry I J f where
  contMDiff := hf
  isInvertible_mfderiv x := by
    obtain ⟨eg, heg⟩ := hg.isInvertible_mfderiv (f x)
    obtain ⟨egf, hegf⟩ := hgf.isInvertible_mfderiv x
    have hcomp := mfderiv_comp x (hg.mdifferentiableAt (f x)) (hf.mdifferentiableAt (by simp))
    refine ⟨egf.trans eg.symm, ContinuousLinearMap.ext fun v ↦ eg.injective ?_⟩
    simpa only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.trans_apply,
      ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearMap.comp_apply, ← heg] using
      (DFunLike.congr_fun (hegf.trans hcomp) v)
  inner_mfderiv x v w := by
    have hcomp := mfderiv_comp x (hg.mdifferentiableAt (f x)) (hf.mdifferentiableAt (by simp))
    rw [← hg.inner_mfderiv (f x), ← ContinuousLinearMap.comp_apply,
      ← ContinuousLinearMap.comp_apply, ← hcomp, hgf.inner_mfderiv x]

/-- The canonical inclusion between open submanifolds `U ⊆ V` is a local Riemannian isometry for
the restricted Riemannian bundles. -/
theorem inclusion {U V : Opens M} (h : (U : Set M) ⊆ V) :
    IsLocalRiemannianIsometry I I (fun x : U ↦ (⟨x.1, h x.2⟩ : V)) :=
  (IsLocalRiemannianIsometry.subtype_val V).of_comp (IsLocalRiemannianIsometry.subtype_val U)
    ((ContMDiff.subtypeVal_comp_iff V _).1 contMDiff_subtype_val)

end Cancellation

end TauCeti.IsLocalRiemannianIsometry

namespace Bundle.ContMDiffRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- Pull back a smooth metric `g` along `(extChartAt I x₀).symm` on the interior of the chart
target, and extend it from a closed coordinate ball inside a prescribed open neighbourhood to a
global smooth metric on `E`. -/
private theorem exists_global_chart_metric_of_isInteriorPoint
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) {x₀ : M}
    (hx₀ : I.IsInteriorPoint x₀) {U : Set M} (hU : U ∈ 𝓝 x₀) :
    ∃ (gE : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (fun z : E ↦ TangentSpace 𝓘(ℝ, E) z))
      (r : ℝ), 0 < r ∧
      closedBall (extChartAt I x₀ x₀) r ⊆
        interior (extChartAt I x₀).target ∩ (extChartAt I x₀).symm ⁻¹' interior U ∧
      ∀ z ∈ closedBall (extChartAt I x₀ x₀) r, ∀ u v : TangentSpace 𝓘(ℝ, E) z,
        gE.inner z u v =
          g.inner ((extChartAt I x₀).symm z)
            (mfderiv 𝓘(ℝ, E) I (extChartAt I x₀).symm z u)
            (mfderiv 𝓘(ℝ, E) I (extChartAt I x₀).symm z v) := by
  let f : E → M := (extChartAt I x₀).symm
  let UE : Set E := interior (extChartAt I x₀).target
  let z₀ : E := extChartAt I x₀ x₀
  have hz₀UE : z₀ ∈ UE := (ModelWithCorners.isInteriorPoint_iff (I := I)).1 hx₀
  have hSE_open : IsOpen (UE ∩ f ⁻¹' interior U) :=
    ((continuousOn_extChartAt_symm x₀).mono interior_subset).isOpen_inter_preimage
      isOpen_interior isOpen_interior
  have hz₀SE : z₀ ∈ UE ∩ f ⁻¹' interior U := by
    refine ⟨hz₀UE, ?_⟩
    simpa only [f, z₀, mem_preimage, extChartAt_to_inv] using mem_interior_iff_mem_nhds.2 hU
  obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (hSE_open.mem_nhds hz₀SE)
  let β (z : E) : TangentSpace 𝓘(ℝ, E) z →L[ℝ] TangentSpace 𝓘(ℝ, E) z →L[ℝ] ℝ :=
    (ContinuousLinearMap.precomp ℝ (mfderiv 𝓘(ℝ, E) I f z)).comp
      ((g.inner (f z)).comp (mfderiv 𝓘(ℝ, E) I f z))
  have hf_smooth {z : E} (hz : z ∈ UE) : ContMDiffAt 𝓘(ℝ, E) I (∞ + 1) f z :=
    (contMDiffOn_extChartAt_symm (I := I) (n := ∞) x₀).contMDiffAt
      (mem_interior_iff_mem_nhds.1 hz)
  have hβ_smooth : ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) (⊤ : ℕ∞)
      (fun z ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) z (β z)) UE := fun z hz ↦
    (g.contMDiffAt_pullback (hf_smooth hz)).contMDiffWithinAt
  have hβ_pos {z : E} (hz : z ∈ UE) (v : TangentSpace 𝓘(ℝ, E) z) (hv : v ≠ 0) : 0 < β z v v := by
    have hinj := ((TauCeti.isLocalDiffeomorphAt_extChartAt_symm (I := I) (n := ∞)
      hz).isInvertible_mfderiv (by simp)).injective
    exact g.pos (f z) _ ((map_ne_zero_iff _ hinj).2 hv)
  let _ : ContMDiffVectorBundle (⊤ : ℕ∞) E (fun z : E ↦ TangentSpace 𝓘(ℝ, E) z) 𝓘(ℝ, E) :=
    TangentBundle.contMDiffVectorBundle (I := 𝓘(ℝ, E))
  obtain ⟨gE, hgE⟩ := TauCeti.exists_contMDiffRiemannianMetric_inner_eq_of_locallyFinite
    (IB := 𝓘(ℝ, E)) (n := (⊤ : ℕ∞)) (F := E) (E := fun z : E ↦ TangentSpace 𝓘(ℝ, E) z)
    (ι := Unit) (A := fun _ ↦ closedBall z₀ r) (U := fun _ ↦ UE) (β := fun _ ↦ β)
    (fun _ ↦ isClosed_closedBall) (locallyFinite_of_finite _) (fun i j hij ↦ (hij (Subsingleton.elim
      i j)).elim) (fun _ ↦ isOpen_interior) (fun _ ↦ hball.trans inter_subset_left)
    (fun _ ↦ hβ_smooth) (fun _ z _ u v ↦ g.symm (f z) _ _) (fun _ _ hz v hv ↦ hβ_pos hz v hv)
  exact ⟨gE, r, hr, hball, fun z hz u v ↦ by rw [hgE () z hz]; rfl⟩

omit [FiniteDimensional ℝ E] in
/-- Restrict `extChartAt I x₀` to a smooth diffeomorphism between an open ball around
`extChartAt I x₀ x₀` inside `interior (extChartAt I x₀).target` and its preimage in
`(extChartAt I x₀).source`. -/
private abbrev extChartAtBallDiffeomorph {x₀ : M} {r : ℝ}
    (hbtgt : closedBall (extChartAt I x₀ x₀) r ⊆ interior (extChartAt I x₀).target) :
    (⟨ball (extChartAt I x₀ x₀) r, isOpen_ball⟩ : Opens E) ≃ₘ^∞⟮𝓘(ℝ, E), I⟯
      (⟨(extChartAt I x₀).source ∩ extChartAt I x₀ ⁻¹' ball (extChartAt I x₀ x₀) r,
        isOpen_extChartAt_preimage' (I := I) x₀ isOpen_ball⟩ : Opens M) where
  toFun z := ⟨(extChartAt I x₀).symm z.1,
    let hzt := interior_subset (hbtgt (ball_subset_closedBall z.2))
    ⟨(extChartAt I x₀).map_target hzt,
      by rw [mem_preimage, (extChartAt I x₀).right_inv hzt]; exact z.2⟩⟩
  invFun y := ⟨extChartAt I x₀ y.1, y.2.2⟩
  left_inv z := Subtype.ext <|
    (extChartAt I x₀).right_inv (interior_subset (hbtgt (ball_subset_closedBall z.2)))
  right_inv y := Subtype.ext ((extChartAt I x₀).left_inv y.2.1)
  contMDiff_toFun := (TauCeti.ContMDiff.subtypeVal_comp_iff _ _).1 <|
    (contMDiffOn_extChartAt_symm x₀).comp_contMDiff contMDiff_subtype_val
      fun z ↦ interior_subset (hbtgt (ball_subset_closedBall z.2))
  contMDiff_invFun := (TauCeti.ContMDiff.subtypeVal_comp_iff _ _).1 <|
    (contMDiffOn_extChartAt (I := I) (x := x₀)).comp_contMDiff contMDiff_subtype_val
      fun y ↦ by simpa only [extChartAt_source] using y.2.1

/-- **Chartwise model-space realization of a Riemannian metric near an interior point.** Given a
smooth Riemannian metric `g` on `M`, an interior point `x₀`, and a neighbourhood `U ∈ 𝓝 x₀`, there
exist a global smooth Riemannian metric `gE` on the model space `E`, a radius `r > 0`, and an open
chart neighbourhood `W ⊆ U` of `x₀` such that `extChartAt I x₀` restricts to a smooth
`TauCeti.RiemannianIsometry` from `(W, g|_W)` onto `(Metric.ball (extChartAt I x₀ x₀) r, gE|_B)`. -/
theorem exists_contMDiffRiemannianMetric_model_space_of_isInteriorPoint
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) {x₀ : M}
    (hx₀ : I.IsInteriorPoint x₀) {U : Set M} (hU : U ∈ 𝓝 x₀) :
    ∃ (gE : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (fun z : E ↦ TangentSpace 𝓘(ℝ, E) z))
      (r : ℝ) (_ : 0 < r) (W : Opens M) (_ : x₀ ∈ W),
      (W : Set M) ⊆ U ∧
      closedBall (extChartAt I x₀ x₀) r ⊆ interior (extChartAt I x₀).target ∧
      (W : Set M) = (extChartAt I x₀).source ∩ extChartAt I x₀ ⁻¹' ball (extChartAt I x₀ x₀) r ∧
      letI : RiemannianBundle (fun x : W ↦ TangentSpace I x) :=
        ⟨(g.restrictOpenTangentSpace W).toRiemannianMetric⟩
      letI : RiemannianBundle
          (fun z : (⟨ball (extChartAt I x₀ x₀) r, isOpen_ball⟩ : Opens E) ↦
            TangentSpace 𝓘(ℝ, E) z) :=
        ⟨(gE.restrictOpenTangentSpace
          ⟨ball (extChartAt I x₀ x₀) r, isOpen_ball⟩).toRiemannianMetric⟩
      ∃ Ψ : TauCeti.RiemannianIsometry I 𝓘(ℝ, E) W
          (⟨ball (extChartAt I x₀ x₀) r, isOpen_ball⟩ : Opens E),
        (∀ y : W, (Ψ y : E) = extChartAt I x₀ y.1) ∧
        ∀ z : (⟨ball (extChartAt I x₀ x₀) r, isOpen_ball⟩ : Opens E),
          (Ψ.symm z : M) = (extChartAt I x₀).symm z.1 := by
  obtain ⟨gE, r, hr, hball, hgE⟩ := g.exists_global_chart_metric_of_isInteriorPoint hx₀ hU
  let z₀ : E := extChartAt I x₀ x₀
  have hbtgt : closedBall z₀ r ⊆ interior (extChartAt I x₀).target := hball.trans inter_subset_left
  let W : Opens M := ⟨(extChartAt I x₀).source ∩ extChartAt I x₀ ⁻¹' ball z₀ r,
    isOpen_extChartAt_preimage' (I := I) x₀ isOpen_ball⟩
  let B : Opens E := ⟨ball z₀ r, isOpen_ball⟩
  have hx₀W : x₀ ∈ W := ⟨mem_extChartAt_source x₀, mem_ball_self hr⟩
  have hWU : (W : Set M) ⊆ U := fun y hy ↦ by
    have hyU := (hball (ball_subset_closedBall hy.2)).2
    rw [mem_preimage, (extChartAt I x₀).left_inv hy.1] at hyU
    exact interior_subset hyU
  let d : B ≃ₘ^∞⟮𝓘(ℝ, E), I⟯ W := extChartAtBallDiffeomorph hbtgt
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  let _ : RiemannianBundle (fun z : E ↦ TangentSpace 𝓘(ℝ, E) z) := ⟨gE.toRiemannianMetric⟩
  let _ : RiemannianBundle (fun x : W ↦ TangentSpace I x) :=
    ⟨(g.restrictOpenTangentSpace W).toRiemannianMetric⟩
  let _ : RiemannianBundle (fun z : B ↦ TangentSpace 𝓘(ℝ, E) z) :=
    ⟨(gE.restrictOpenTangentSpace B).toRiemannianMetric⟩
  have hιW := g.isLocalRiemannianIsometry_restrictOpenTangentSpace W
  have hιB := gE.isLocalRiemannianIsometry_restrictOpenTangentSpace B
  let Ψsymm : TauCeti.RiemannianIsometry 𝓘(ℝ, E) I B W :=
    { toDiffeomorph := d
      inner_mfderiv' := fun z u v ↦ by
        have hzd : MDifferentiableAt 𝓘(ℝ, E) I (extChartAt I x₀).symm z.1 :=
          ((contMDiffOn_extChartAt_symm (I := I) (n := ∞) x₀).contMDiffAt
            (mem_interior_iff_mem_nhds.1 (hbtgt (ball_subset_closedBall z.2)))).mdifferentiableAt
            (by simp)
        have hdf (w : TangentSpace 𝓘(ℝ, E) z) :
            mfderiv I I (Subtype.val : W → M) (d z) (mfderiv 𝓘(ℝ, E) I d z w) =
              mfderiv 𝓘(ℝ, E) I (extChartAt I x₀).symm z.1
                (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Subtype.val : B → E) z w) := by
          rw [← mfderiv_comp_apply z (hιW.mdifferentiableAt (d z))
              (d.contMDiff.mdifferentiableAt (by simp)),
            ← mfderiv_comp_apply z hzd (hιB.mdifferentiableAt z)]
          rfl
        rw [← hιW.inner_mfderiv (d z), hdf u, hdf v, ← hιB.inner_mfderiv z]
        exact (hgE z.1 (ball_subset_closedBall z.2) _ _).symm }
  refine ⟨gE, r, hr, W, hx₀W, hWU, hbtgt, rfl, Ψsymm.symm, fun y ↦ ?_, fun z ↦ ?_⟩
  · rw [Ψsymm.coe_symm]
    rfl
  · rw [congrArg (⇑Ψsymm.symm.symm) (Ψsymm.symm_apply_apply z).symm, Ψsymm.symm.symm_apply_apply]
    rfl

/-- **Chartwise model-space realization of a Riemannian metric on a boundaryless manifold.** -/
theorem exists_contMDiffRiemannianMetric_model_space [BoundarylessManifold I M]
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) {x₀ : M}
    {U : Set M} (hU : U ∈ 𝓝 x₀) :
    ∃ (gE : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (fun z : E ↦ TangentSpace 𝓘(ℝ, E) z))
      (r : ℝ) (_ : 0 < r) (W : Opens M) (_ : x₀ ∈ W),
      (W : Set M) ⊆ U ∧
      closedBall (extChartAt I x₀ x₀) r ⊆ interior (extChartAt I x₀).target ∧
      (W : Set M) = (extChartAt I x₀).source ∩ extChartAt I x₀ ⁻¹' ball (extChartAt I x₀ x₀) r ∧
      letI : RiemannianBundle (fun x : W ↦ TangentSpace I x) :=
        ⟨(g.restrictOpenTangentSpace W).toRiemannianMetric⟩
      letI : RiemannianBundle
          (fun z : (⟨ball (extChartAt I x₀ x₀) r, isOpen_ball⟩ : Opens E) ↦
            TangentSpace 𝓘(ℝ, E) z) :=
        ⟨(gE.restrictOpenTangentSpace
          ⟨ball (extChartAt I x₀ x₀) r, isOpen_ball⟩).toRiemannianMetric⟩
      ∃ Ψ : TauCeti.RiemannianIsometry I 𝓘(ℝ, E) W
          (⟨ball (extChartAt I x₀ x₀) r, isOpen_ball⟩ : Opens E),
        (∀ y : W, (Ψ y : E) = extChartAt I x₀ y.1) ∧
        ∀ z : (⟨ball (extChartAt I x₀ x₀) r, isOpen_ball⟩ : Opens E),
          (Ψ.symm z : M) = (extChartAt I x₀).symm z.1 :=
  g.exists_contMDiffRiemannianMetric_model_space_of_isInteriorPoint
    BoundarylessManifold.isInteriorPoint hU

end Bundle.ContMDiffRiemannianMetric

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [instRB : RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- **Chartwise model-space realization for an installed `RiemannianBundle` near an interior
point.** -/
theorem exists_contMDiffRiemannianMetric_model_space_of_isInteriorPoint {x₀ : M}
    (hx₀ : I.IsInteriorPoint x₀) {U : Set M} (hU : U ∈ 𝓝 x₀) :
    ∃ (gE : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (fun z : E ↦ TangentSpace 𝓘(ℝ, E) z))
      (r : ℝ) (_ : 0 < r) (W : Opens M) (_ : x₀ ∈ W),
      (W : Set M) ⊆ U ∧
      closedBall (extChartAt I x₀ x₀) r ⊆ interior (extChartAt I x₀).target ∧
      (W : Set M) = (extChartAt I x₀).source ∩ extChartAt I x₀ ⁻¹' ball (extChartAt I x₀ x₀) r ∧
      letI : RiemannianBundle
          (fun z : (⟨ball (extChartAt I x₀ x₀) r, isOpen_ball⟩ : Opens E) ↦
            TangentSpace 𝓘(ℝ, E) z) :=
        ⟨(gE.restrictOpenTangentSpace
          ⟨ball (extChartAt I x₀ x₀) r, isOpen_ball⟩).toRiemannianMetric⟩
      ∃ Ψ : RiemannianIsometry I 𝓘(ℝ, E) W
          (⟨ball (extChartAt I x₀ x₀) r, isOpen_ball⟩ : Opens E),
        (∀ y : W, (Ψ y : E) = extChartAt I x₀ y.1) ∧
        ∀ z : (⟨ball (extChartAt I x₀ x₀) r, isOpen_ball⟩ : Opens E),
          (Ψ.symm z : M) = (extChartAt I x₀).symm z.1 := by
  let g := ContMDiffRiemannianMetric.ofIsContMDiffRiemannianBundle
    (IB := I) (n := ∞) (F := E) (V := fun x : M ↦ TangentSpace I x)
  obtain ⟨gE, r, hr, W, hx₀W, hWU, hbtgt, hW, hex⟩ :=
    g.exists_contMDiffRiemannianMetric_model_space_of_isInteriorPoint hx₀ hU
  have hgM : (⟨g.toRiemannianMetric⟩ : RiemannianBundle (fun x : M ↦ TangentSpace I x)) =
      instRB := by
    have hinner : g.toRiemannianMetric.inner = instRB.g.inner := by
      funext x
      ext v w
      exact ContMDiffRiemannianMetric.ofIsContMDiffRiemannianBundle_inner x v w
    rcases instRB with ⟨⟨_, _, _, _, _⟩⟩
    rcases h : g.toRiemannianMetric with ⟨_, _, _, _, _⟩
    rw [h] at hinner
    subst hinner
    rfl
  have hinst : Manifold.instRiemannianBundleOpen (I := I) W =
      ⟨(g.restrictOpenTangentSpace W).toRiemannianMetric⟩ :=
    hgM ▸ g.riemannianBundle_restrictOpenTangentSpace_eq W
  exact ⟨gE, r, hr, W, hx₀W, hWU, hbtgt, hW, hinst.symm ▸ hex⟩

/-- **Chartwise model-space realization for an installed `RiemannianBundle` on a boundaryless
manifold.** -/
theorem exists_contMDiffRiemannianMetric_model_space [BoundarylessManifold I M] {x₀ : M}
    {U : Set M} (hU : U ∈ 𝓝 x₀) :
    ∃ (gE : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (fun z : E ↦ TangentSpace 𝓘(ℝ, E) z))
      (r : ℝ) (_ : 0 < r) (W : Opens M) (_ : x₀ ∈ W),
      (W : Set M) ⊆ U ∧
      closedBall (extChartAt I x₀ x₀) r ⊆ interior (extChartAt I x₀).target ∧
      (W : Set M) = (extChartAt I x₀).source ∩ extChartAt I x₀ ⁻¹' ball (extChartAt I x₀ x₀) r ∧
      letI : RiemannianBundle
          (fun z : (⟨ball (extChartAt I x₀ x₀) r, isOpen_ball⟩ : Opens E) ↦
            TangentSpace 𝓘(ℝ, E) z) :=
        ⟨(gE.restrictOpenTangentSpace
          ⟨ball (extChartAt I x₀ x₀) r, isOpen_ball⟩).toRiemannianMetric⟩
      ∃ Ψ : RiemannianIsometry I 𝓘(ℝ, E) W
          (⟨ball (extChartAt I x₀ x₀) r, isOpen_ball⟩ : Opens E),
        (∀ y : W, (Ψ y : E) = extChartAt I x₀ y.1) ∧
        ∀ z : (⟨ball (extChartAt I x₀ x₀) r, isOpen_ball⟩ : Opens E),
          (Ψ.symm z : M) = (extChartAt I x₀).symm z.1 :=
  exists_contMDiffRiemannianMetric_model_space_of_isInteriorPoint
    BoundarylessManifold.isInteriorPoint hU

end TauCeti

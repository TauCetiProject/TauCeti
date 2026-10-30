/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Hyperbolic
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Restriction
public import TauCeti.Geometry.Manifold.Riemannian.SMulGroupoid.Basic

/-!
# The curvature of an `(Isom X, X)`-manifold

Let `X` be a Riemannian manifold and `M` an `(Isom X, X)`-manifold, carrying the metric of `X`
read through its charts (`TauCeti.contMDiffChartRiemannianMetric`). Every chart of `M` restricts
to a local Riemannian isometry from its source, an open submanifold of `M`, to `X`. Curvature is
natural under local Riemannian isometries, so each chart carries the Riemann curvature tensor of
`M` to that of `X`:

`de_y (R(u, v) w) = R(de_y u, de_y v) (de_y w)`.

In particular, if `X` has constant curvature `κ`, then so does `M`. For `X` hyperbolic space, the
orbit space `X / Γ` of a free, properly discontinuous group `Γ` of isometries is an
`(Isom X, X)`-manifold (`TauCeti.hasGroupoid_smulGroupoid_quotient_subgroup`), so this is how a
hyperbolic manifold presented as `X / Γ`, or by any other `(Isom X, X)`-atlas, receives its metric
of constant curvature `-1`. When `M` is compact and connected this metric is complete, so it is a
`TauCeti.HyperbolicMetric`, and `M` is hyperbolic in the metric sense used by hyperbolic volume.

## Main results

* `TauCeti.isLocalRiemannianIsometry_restrict_of_mem_atlas`: a chart of an `(Isom X, X)`-manifold,
  restricted to its source, is a local Riemannian isometry to `X`.
* `TauCeti.mfderiv_curvatureTensor_of_mem_atlas`: every chart carries the curvature tensor of the
  chart metric to that of `X`.
* `TauCeti.isConstantCurvatureTensor_contMDiffChartRiemannianMetric`: the chart metric has constant
  curvature `κ` when the metric of `X` does.
* `TauCeti.chartHyperbolicMetric` and `TauCeti.isHyperbolic_of_hasGroupoid_smulGroupoid`:
  a compact connected `(Isom X, X)`-manifold over a space of constant curvature `-1` carries a
  hyperbolic metric.

## References

* W. P. Thurston, *Three-Dimensional Geometry and Topology, Vol. 1*, Princeton University Press,
  1997, Section 3.4 (the metric a `(G, X)`-manifold inherits from `X`, and hyperbolic manifolds as
  `(Isom ℍⁿ, ℍⁿ)`-manifolds).
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Proposition 7.6 (naturality of the curvature tensor under local isometries).
-/

public section

open Bundle Manifold TopologicalSpace CovariantDerivative
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X]
  [RiemannianBundle (fun x : X ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : X ↦ TangentSpace I x)]
  {M : Type*} [TopologicalSpace M] [ChartedSpace X M]
  [HasGroupoid M (smulGroupoid (Isom I X) X)]

omit [IsManifold I ∞ X] [IsContMDiffRiemannianBundle I ∞ E (fun x : X ↦ TangentSpace I x)] in
/-- The derivative of a chart `e` restricted to its source is the derivative of `e` after that of
the inclusion of the source. -/
private theorem mfderiv_restrict_of_mem_atlas {e : OpenPartialHomeomorph M X}
    (he : e ∈ atlas X M) (y : (⟨e.source, e.open_source⟩ : Opens M)) :
    letI := ChartedSpace.comp H X M
    mfderiv I I (fun z : (⟨e.source, e.open_source⟩ : Opens M) ↦ e z) y =
      (mfderiv I I e y).comp
        (mfderiv I I (Subtype.val : (⟨e.source, e.open_source⟩ : Opens M) → M) y) :=
  letI := ChartedSpace.comp H X M
  mfderiv_comp (f := Subtype.val) y
    (((contMDiffOn_of_mem_atlas_of_hasGroupoid_smulGroupoid (I := I) (n := 1) (Isom I X)
      he).contMDiffAt (e.open_source.mem_nhds y.2)).mdifferentiableAt one_ne_zero)
    (contMDiff_subtype_val.mdifferentiableAt one_ne_zero)

variable (I) in
/-- A chart `e` of an `(Isom X, X)`-manifold, restricted to its source, is a local Riemannian
isometry from the chart metric restricted to the source to the metric of `X`. -/
theorem isLocalRiemannianIsometry_restrict_of_mem_atlas {e : OpenPartialHomeomorph M X}
    (he : e ∈ atlas X M) :
    letI := ChartedSpace.comp H X M
    haveI := isManifold_of_hasGroupoid_smulGroupoid I ∞ (Isom I X) (X := X) M
    letI : RiemannianBundle (fun y : (⟨e.source, e.open_source⟩ : Opens M) ↦ TangentSpace I y) :=
      ⟨((contMDiffChartRiemannianMetric I X M ∞).restrictOpenTangentSpace
        ⟨e.source, e.open_source⟩).toRiemannianMetric⟩
    IsLocalRiemannianIsometry I I fun y : (⟨e.source, e.open_source⟩ : Opens M) ↦ e y := by
  let := ChartedSpace.comp H X M
  have := isManifold_of_hasGroupoid_smulGroupoid I ∞ (Isom I X) (X := X) M
  set U : Opens M := ⟨e.source, e.open_source⟩
  let : RiemannianBundle (fun y : U ↦ TangentSpace I y) :=
    ⟨((contMDiffChartRiemannianMetric I X M ∞).restrictOpenTangentSpace U).toRiemannianMetric⟩
  have hsmooth := contMDiffOn_of_mem_atlas_of_hasGroupoid_smulGroupoid (I := I) (n := ∞)
    (Isom I X) he
  have hderiv := mfderiv_restrict_of_mem_atlas (I := I) he
  refine ⟨fun y ↦ (hsmooth.contMDiffAt (e.open_source.mem_nhds y.2)).comp y
    contMDiff_subtype_val.contMDiffAt, fun y ↦ ?_, fun y v w ↦ ?_⟩
  · -- Near `y`, the chart `e` is the preferred chart at `y`, whose derivative at `y` is the
    -- identity, followed by an isometry `γ` of `X`, whose derivative is invertible.
    obtain ⟨γ, hγ⟩ := exists_smul_eventuallyEq_chartAt (G := Isom I X) he y.2
    have hd := ((γ.mdifferentiableAt _).hasMFDerivAt.comp (y : M)
      (hasMFDerivAt_chartAt_comp (y : M))).congr_of_eventuallyEq hγ
    rw [hderiv, hd.mfderiv, TauCeti.Manifold.mfderiv_subtype_val]
    exact ((γ.toDiffeomorph.isInvertible_mfderiv (by simp)).comp
      ⟨ContinuousLinearEquiv.refl ℝ _, rfl⟩).comp ContinuousLinearMap.isInvertible_equiv
  · rw [hderiv, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      inner_mfderiv_of_mem_atlas he y.2, ContMDiffRiemannianMetric.inner_riemannianBundle,
      ContMDiffRiemannianMetric.restrictOpenTangentSpace_inner,
      TauCeti.Manifold.mfderiv_subtype_val, contMDiffChartRiemannianMetric_inner,
      ContinuousLinearEquiv.coe_coe]

section Curvature

variable [FiniteDimensional ℝ E] [T2Space X] [T2Space M]

variable (I) in
/-- **Charts of an `(Isom X, X)`-manifold preserve curvature.** Every chart `e` carries the Riemann
curvature tensor of the chart metric to that of `X`:
`de_y (R(u, v) w) = R(de_y u, de_y v) (de_y w)`. -/
theorem mfderiv_curvatureTensor_of_mem_atlas {e : OpenPartialHomeomorph M X} (he : e ∈ atlas X M)
    {y : M} (hy : y ∈ e.source) :
    letI := ChartedSpace.comp H X M
    haveI := isManifold_of_hasGroupoid_smulGroupoid I ∞ (Isom I X) (X := X) M
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
      ⟨(contMDiffChartRiemannianMetric I X M ∞).toRiemannianMetric⟩
    ∀ u v w : TangentSpace I y,
      mfderiv I I e y ((leviCivitaConnection I M).curvatureTensor y u v w) =
        (leviCivitaConnection I X).curvatureTensor (e y) (mfderiv I I e y u) (mfderiv I I e y v)
          (mfderiv I I e y w) := by
  let := ChartedSpace.comp H X M
  have := isManifold_of_hasGroupoid_smulGroupoid I ∞ (Isom I X) (X := X) M
  let g := contMDiffChartRiemannianMetric I X M ∞
  let : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  intro u v w
  set U : Opens M := ⟨e.source, e.open_source⟩
  let : RiemannianBundle (fun z : U ↦ TangentSpace I z) :=
    ⟨(g.restrictOpenTangentSpace U).toRiemannianMetric⟩
  let y' : U := ⟨y, hy⟩
  let τ := TauCeti.Manifold.tangentSpaceOpenEquiv (I := I) y'
  -- Both the inclusion of the chart source and the restricted chart are local isometries.
  have hι := g.isLocalRiemannianIsometry_restrictOpenTangentSpace U
  have hf := isLocalRiemannianIsometry_restrict_of_mem_atlas I he
  have hval : mfderiv I I (Subtype.val : U → M) y' = τ.toContinuousLinearMap :=
    TauCeti.Manifold.mfderiv_subtype_val y'
  have hderiv := mfderiv_restrict_of_mem_atlas (I := I) he y'
  have hcomp (z : TangentSpace I y') :
      mfderiv I I (fun z : U ↦ e z) y' z = mfderiv I I e y (τ z) := by
    rw [hderiv, ContinuousLinearMap.comp_apply, hval, ContinuousLinearEquiv.coe_coe]
  have hR := hι.mfderiv_curvatureTensor y' (τ.symm u) (τ.symm v) (τ.symm w)
  rw [hval, ContinuousLinearEquiv.coe_coe, τ.apply_symm_apply, τ.apply_symm_apply,
    τ.apply_symm_apply] at hR
  rw [← hR, ← hcomp, hf.mfderiv_curvatureTensor, hcomp, hcomp, hcomp, τ.apply_symm_apply,
    τ.apply_symm_apply, τ.apply_symm_apply]

/-- **An `(Isom X, X)`-manifold has the constant curvature of `X`.** If the Levi-Civita connection
of `X` has the constant-curvature tensor `κ`, then so does that of the chart metric of `M`. -/
theorem isConstantCurvatureTensor_contMDiffChartRiemannianMetric {κ : ℝ}
    (hX : ∀ (x : X) (w u v : TangentSpace I x), (leviCivitaConnection I X).curvatureTensor x w u v =
      κ • (inner ℝ u v • w - inner ℝ w v • u)) :
    letI := ChartedSpace.comp H X M
    haveI := isManifold_of_hasGroupoid_smulGroupoid I ∞ (Isom I X) (X := X) M
    (contMDiffChartRiemannianMetric I X M ∞).IsConstantCurvatureTensor κ := by
  let := ChartedSpace.comp H X M
  have := isManifold_of_hasGroupoid_smulGroupoid I ∞ (Isom I X) (X := X) M
  rw [ContMDiffRiemannianMetric.isConstantCurvatureTensor_iff]
  intro x w u v
  -- Read everything in the preferred chart at `x`, whose derivative at `x` is the identity.
  have h := mfderiv_curvatureTensor_of_mem_atlas I (chart_mem_atlas X x) (mem_chart_source X x)
    w u v
  have hid (a : TangentSpace I x) : mfderiv I I (chartAt X x) x a = a := by
    rw [(hasMFDerivAt_chartAt_comp x).mfderiv]
    rfl
  have hinner (a b : TangentSpace I x) :
      inner ℝ (mfderiv I I (chartAt X x) x a) (mfderiv I I (chartAt X x) x b) =
        (chartRiemannianMetric I X M).inner x a b :=
    inner_mfderiv_of_mem_atlas (chart_mem_atlas X x) (mem_chart_source X x) a b
  rw [hid, hid, hid, hid] at h
  simp only [hid] at hinner
  refine h.trans ((hX _ w u v).trans ?_)
  rw [ContMDiffRiemannianMetric.inner_riemannianBundle,
    ContMDiffRiemannianMetric.inner_riemannianBundle, contMDiffChartRiemannianMetric_inner,
    ← hinner, ← hinner]
  -- The two sides differ only in reading `u`, `v`, `w` in `T_x M` or in `T_(chartAt X x x) X`,
  -- both of which are the model space `E`.
  rfl

end Curvature

section Hyperbolic

variable [FiniteDimensional ℝ E] [T2Space X] [CompactSpace M] [T3Space M] [PreconnectedSpace M]

/-- The chart metric of a compact connected `(Isom X, X)`-manifold over a space `X` of constant
curvature `-1`, as a hyperbolic metric: it has constant curvature `-1`, and it is complete because
`M` is compact. -/
def chartHyperbolicMetric
    (hX : ∀ (x : X) (w u v : TangentSpace I x), (leviCivitaConnection I X).curvatureTensor x w u v =
      (-1 : ℝ) • (inner ℝ u v • w - inner ℝ w v • u)) :
    letI := ChartedSpace.comp H X M
    haveI := isManifold_of_hasGroupoid_smulGroupoid I ∞ (Isom I X) (X := X) M
    HyperbolicMetric (I := I) (M := M) :=
  letI := ChartedSpace.comp H X M
  haveI := isManifold_of_hasGroupoid_smulGroupoid I ∞ (Isom I X) (X := X) M
  HyperbolicMetric.ofCompactSpace (isConstantCurvatureTensor_contMDiffChartRiemannianMetric hX)

/-- The metric of `TauCeti.chartHyperbolicMetric` is the chart metric. -/
@[simp]
theorem chartHyperbolicMetric_metric
    (hX : ∀ (x : X) (w u v : TangentSpace I x), (leviCivitaConnection I X).curvatureTensor x w u v =
      (-1 : ℝ) • (inner ℝ u v • w - inner ℝ w v • u)) :
    letI := ChartedSpace.comp H X M
    haveI := isManifold_of_hasGroupoid_smulGroupoid I ∞ (Isom I X) (X := X) M
    (chartHyperbolicMetric hX (M := M)).metric = contMDiffChartRiemannianMetric I X M ∞ :=
  letI := ChartedSpace.comp H X M
  haveI := isManifold_of_hasGroupoid_smulGroupoid I ∞ (Isom I X) (X := X) M
  HyperbolicMetric.metric_ofCompactSpace _

/-- **Compact hyperbolic `(Isom X, X)`-manifolds are hyperbolic.** A compact connected
`(Isom X, X)`-manifold over a space `X` of constant curvature `-1` carries a hyperbolic metric for
its composite charts. -/
theorem isHyperbolic_of_hasGroupoid_smulGroupoid
    (hX : ∀ (x : X) (w u v : TangentSpace I x), (leviCivitaConnection I X).curvatureTensor x w u v =
      (-1 : ℝ) • (inner ℝ u v • w - inner ℝ w v • u)) :
    letI := ChartedSpace.comp H X M
    haveI := isManifold_of_hasGroupoid_smulGroupoid I ∞ (Isom I X) (X := X) M
    IsHyperbolic (I := I) (M := M) :=
  letI := ChartedSpace.comp H X M
  haveI := isManifold_of_hasGroupoid_smulGroupoid I ∞ (Isom I X) (X := X) M
  isHyperbolic_iff.2 ⟨chartHyperbolicMetric hX⟩

end Hyperbolic

end TauCeti

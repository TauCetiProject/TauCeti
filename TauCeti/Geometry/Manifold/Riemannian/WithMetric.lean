/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import TauCeti.Geometry.Manifold.PullbackGroupoid
public import TauCeti.Geometry.Manifold.Riemannian.Pullback
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.ChartGram

/-!
# A manifold carrying a chosen Riemannian metric

The Riemannian API (gradient, volume density, Levi-Civita connection, curvature) is driven by a
`RiemannianBundle` instance on the tangent bundle. Comparing two metrics `g` and `g'` on the same
manifold `M`, for instance a metric and a conformal rescaling of it, would require two
incompatible instances on the same carrier. Instead, `TauCeti.WithMetric g` is a copy of `M`
whose `RiemannianBundle` instance is `g`; different metrics give different copies, and each
copy has exactly one metric instance.

The copy carries the topology, charts and manifold structure of `M`, transported along the
tautological equivalence `ofWithMetric : WithMetric g → M`, and the Borel `σ`-algebra of that
topology. The map `ofWithMetric` is a diffeomorphism of every order, its differential is the
identity of the model space, and the metric of the copy is the pullback of `g` along it. Two
copies of `M` are related by the identity diffeomorphism
`TauCeti.WithMetric.diffeomorphWithMetric`.

## Main definitions

* `TauCeti.WithMetric g`: the manifold `M` with the Riemannian metric `g`, together with the
  conversions `TauCeti.WithMetric.toWithMetric` and `TauCeti.WithMetric.ofWithMetric`.
* `TauCeti.WithMetric.diffeomorph`: the diffeomorphism `WithMetric g ≃ M`.
* `TauCeti.WithMetric.diffeomorphWithMetric`: the identity diffeomorphism between the copies of
  `M` carrying two metrics.
* `TauCeti.WithMetric.metric`: the metric of the copy, the pullback of `g` along `ofWithMetric`,
  installed as its `RiemannianBundle` instance.

## Main results

* `TauCeti.WithMetric.mfderiv_ofWithMetric`: the differential of `ofWithMetric` is the identity.
* `TauCeti.WithMetric.mfderiv_comp_ofWithMetric`: the chain rule for a function read on the copy,
  without a differentiability hypothesis.
* `TauCeti.WithMetric.inner_def`: the inner product of the copy is `g` evaluated on the
  transported tangent vectors.
* `TauCeti.WithMetric.mfderiv_ofWithMetric_chartLocalFrame`: the chart frames of the copy are
  those of `M`.
-/

public section

open Bundle Set
open scoped Manifold ContDiff Topology

noncomputable section

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

/-- The manifold `M` carrying the Riemannian metric `g`: a copy of `M` whose `RiemannianBundle`
instance is `g`. Distinct metrics on `M` give distinct copies, so that two metrics can be compared
without installing two metric instances on one carrier. -/
@[ext]
structure WithMetric (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)) where
  /-- The point of `M` regarded as a point of the copy carrying `g`. -/
  toWithMetric (g) ::
  /-- The underlying point of `M`. -/
  ofWithMetric : M

namespace WithMetric

section Charts

variable (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x))

/-- The tautological equivalence between the copy of `M` carrying `g` and `M`. -/
def equiv : WithMetric g ≃ M where
  toFun := ofWithMetric
  invFun := toWithMetric g
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem equiv_apply (x : WithMetric g) : equiv g x = x.ofWithMetric :=
  (rfl)

@[simp]
theorem equiv_symm_apply (x : M) : (equiv g).symm x = toWithMetric g x :=
  (rfl)

@[simp]
theorem ofWithMetric_toWithMetric (x : M) : (toWithMetric g x).ofWithMetric = x :=
  (rfl)

@[simp]
theorem toWithMetric_ofWithMetric (x : WithMetric g) : toWithMetric g x.ofWithMetric = x :=
  (rfl)

variable {g} in
theorem ofWithMetric_injective : Function.Injective (ofWithMetric : WithMetric g → M) :=
  (equiv g).injective

theorem toWithMetric_injective : Function.Injective (toWithMetric g) :=
  (equiv g).symm.injective

variable {g} in
@[simp]
theorem ofWithMetric_inj {x y : WithMetric g} : x.ofWithMetric = y.ofWithMetric ↔ x = y :=
  ofWithMetric_injective.eq_iff

/-- Two points of `M` give the same point of the copy only if they are equal. Not tagged
`@[simp]`: `simp` already proves it with the constructor lemma
`TauCeti.WithMetric.toWithMetric.injEq`. -/
theorem toWithMetric_inj {x y : M} : toWithMetric g x = toWithMetric g y ↔ x = y :=
  (toWithMetric_injective g).eq_iff

/-- The copy of `M` carrying `g` has the topology of `M`. -/
instance : TopologicalSpace (WithMetric g) :=
  TopologicalSpace.induced ofWithMetric ‹_›

/-- The tautological homeomorphism between the copy of `M` carrying `g` and `M`. -/
def homeomorph : WithMetric g ≃ₜ M where
  toEquiv := equiv g
  continuous_toFun := continuous_induced_dom
  continuous_invFun := continuous_induced_rng.2 continuous_id

@[simp]
theorem coe_homeomorph : ⇑(homeomorph g) = ofWithMetric :=
  (rfl)

@[simp]
theorem coe_homeomorph_symm : ⇑(homeomorph g).symm = toWithMetric g :=
  (rfl)

/-- The copy of a compact manifold is compact. -/
instance [CompactSpace M] : CompactSpace (WithMetric g) :=
  (homeomorph g).symm.compactSpace

/-- The copy of a Lindelöf manifold is Lindelöf. -/
instance [LindelofSpace M] : LindelofSpace (WithMetric g) :=
  isLindelof_univ_iff.1 <| by
    simpa only [(homeomorph g).symm.surjective.range_eq] using
      isLindelof_range (homeomorph g).symm.continuous

/-- The copy of `M` carrying `g` is measured on its Borel `σ`-algebra. -/
instance : MeasurableSpace (WithMetric g) := borel _

instance : BorelSpace (WithMetric g) := ⟨rfl⟩

/-- The copy of `M` carrying `g` has the charts of `M`, precomposed with `ofWithMetric`. -/
instance : ChartedSpace H (WithMetric g) :=
  (homeomorph g).pullbackChartedSpace

theorem chartAt_eq (x : WithMetric g) :
    chartAt H x = (homeomorph g).transOpenPartialHomeomorph (chartAt H x.ofWithMetric) :=
  (rfl)

/-- The chart transitions of the copy are those of `M`, so it is a manifold of the same
smoothness. -/
instance {k : ℕ∞ω} [IsManifold I k M] : IsManifold I k (WithMetric g) :=
  (homeomorph g).pullback_isManifold I k

variable {g}

theorem mem_chartAt_source_iff (α x : WithMetric g) :
    x ∈ (chartAt H α).source ↔ x.ofWithMetric ∈ (chartAt H α.ofWithMetric).source :=
  Iff.rfl

theorem extChartAt_apply (α x : WithMetric g) :
    extChartAt I α x = extChartAt I α.ofWithMetric x.ofWithMetric :=
  (rfl)

theorem extChartAt_symm_apply (α : WithMetric g) (z : E) :
    (extChartAt I α).symm z = toWithMetric g ((extChartAt I α.ofWithMetric).symm z) :=
  (rfl)

/-- The tangent trivializations of the copy read a tangent vector in the same coordinates as
those of `M`. -/
theorem trivializationAt_apply_snd (α x : WithMetric g) (v : TangentSpace I x) :
    (trivializationAt E (TangentSpace I) α ⟨x, v⟩).2 =
      (trivializationAt E (TangentSpace I) α.ofWithMetric ⟨x.ofWithMetric, v⟩).2 :=
  (rfl)

/-- The tangent trivializations of the copy and of `M` have the same inverse on fibres. -/
theorem trivializationAt_linearEquivAt_symm_apply (α x : WithMetric g)
    (hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (hx' : x.ofWithMetric ∈ (trivializationAt E (TangentSpace I) α.ofWithMetric).baseSet)
    (z : E) :
    ((trivializationAt E (TangentSpace I) α).linearEquivAt ℝ x hx).symm z =
      ((trivializationAt E (TangentSpace I) α.ofWithMetric).linearEquivAt ℝ x.ofWithMetric
        hx').symm z := by
  apply ((trivializationAt E (TangentSpace I) α).linearEquivAt ℝ x hx).injective
  rw [LinearEquiv.apply_symm_apply]
  exact ((trivializationAt_apply_snd α x _).trans
    (Trivialization.linearEquivAt_apply _ _ hx' _).symm |>.trans
      (LinearEquiv.apply_symm_apply _ _)).symm

end Charts

variable {g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)}

section Diffeomorph

variable (g) in
/-- The tautological diffeomorphism, of every order, between the copy of `M` carrying `g` and
`M`. -/
def diffeomorph (k : ℕ∞ω) : WithMetric g ≃ₘ^k⟮I, I⟯ M :=
  (homeomorph g).pullbackDiffeomorph I k

@[simp]
theorem coe_diffeomorph (k : ℕ∞ω) : ⇑(diffeomorph g k) = ofWithMetric :=
  (homeomorph g).coe_pullbackDiffeomorph I k

@[simp]
theorem coe_diffeomorph_symm (k : ℕ∞ω) : ⇑(diffeomorph g k).symm = toWithMetric g :=
  (homeomorph g).coe_pullbackDiffeomorph_symm I k

end Diffeomorph

section Derivatives

theorem continuous_ofWithMetric : Continuous (ofWithMetric : WithMetric g → M) :=
  (homeomorph g).continuous

theorem continuous_toWithMetric : Continuous (toWithMetric g) :=
  (homeomorph g).symm.continuous

/-- In charts, `ofWithMetric` is the identity near the base point. -/
private theorem writtenInExtChartAt_ofWithMetric_eventuallyEq (x : WithMetric g) :
    writtenInExtChartAt I I x ofWithMetric =ᶠ[𝓝[range I] extChartAt I x x] id := by
  filter_upwards [extChartAt_target_mem_nhdsWithin (I := I) x.ofWithMetric] with z hz
  simp only [writtenInExtChartAt, Function.comp_apply, extChartAt_symm_apply]
  exact (extChartAt I x.ofWithMetric).right_inv hz

/-- In charts, `toWithMetric g` is the identity near the base point. -/
private theorem writtenInExtChartAt_toWithMetric_eventuallyEq (x : M) :
    writtenInExtChartAt I I x (toWithMetric g) =ᶠ[𝓝[range I] extChartAt I x x] id := by
  filter_upwards [extChartAt_target_mem_nhdsWithin (I := I) x] with z hz
  simp only [writtenInExtChartAt, Function.comp_apply, extChartAt_apply]
  exact (extChartAt I x).right_inv hz

/-- `ofWithMetric` is a diffeomorphism, hence smooth of every order. -/
theorem contMDiff_ofWithMetric {k : ℕ∞ω} :
    ContMDiff I I k (ofWithMetric : WithMetric g → M) :=
  coe_diffeomorph (g := g) k ▸ (diffeomorph g k).contMDiff

/-- `toWithMetric g` is a diffeomorphism, hence smooth of every order. -/
theorem contMDiff_toWithMetric {k : ℕ∞ω} : ContMDiff I I k (toWithMetric g) :=
  coe_diffeomorph_symm (g := g) k ▸ (diffeomorph g k).symm.contMDiff

/-- The differential of `ofWithMetric` is the identity of the model space. -/
theorem hasMFDerivAt_ofWithMetric (x : WithMetric g) :
    HasMFDerivAt I I ofWithMetric x (ContinuousLinearMap.id ℝ (TangentSpace I x)) :=
  ⟨continuous_ofWithMetric.continuousAt, (hasFDerivWithinAt_id _ _).congr_of_eventuallyEq
    (writtenInExtChartAt_ofWithMetric_eventuallyEq x)
    ((writtenInExtChartAt_ofWithMetric_eventuallyEq x).eq_of_nhdsWithin (mem_range_self _))⟩

/-- The differential of `toWithMetric g` is the identity of the model space. -/
theorem hasMFDerivAt_toWithMetric (x : M) :
    HasMFDerivAt I I (toWithMetric g) x (ContinuousLinearMap.id ℝ (TangentSpace I x)) :=
  ⟨continuous_toWithMetric.continuousAt, (hasFDerivWithinAt_id _ _).congr_of_eventuallyEq
    (writtenInExtChartAt_toWithMetric_eventuallyEq x)
    ((writtenInExtChartAt_toWithMetric_eventuallyEq x).eq_of_nhdsWithin (mem_range_self _))⟩

/-! The tangent spaces `TangentSpace I x` of a point `x` of the copy and
`TangentSpace I x.ofWithMetric` of the underlying point of `M` are both, by definition, the model
space `E`. The following lemmas state that the differentials of `ofWithMetric` and `toWithMetric g`
are the identity under this identification; later statements comparing tangent vectors of the copy
with tangent vectors of `M` go through these lemmas rather than through the identification. -/

/-- The differential of `ofWithMetric` is the identity of the model space. -/
theorem mfderiv_ofWithMetric (x : WithMetric g) :
    mfderiv I I ofWithMetric x = ContinuousLinearMap.id ℝ (TangentSpace I x) :=
  (hasMFDerivAt_ofWithMetric x).mfderiv

/-- The differential of `toWithMetric g` is the identity of the model space. -/
theorem mfderiv_toWithMetric (x : M) :
    mfderiv I I (toWithMetric g) x = ContinuousLinearMap.id ℝ (TangentSpace I x) :=
  (hasMFDerivAt_toWithMetric x).mfderiv

/-- The differential of `ofWithMetric` maps a tangent vector to itself. -/
theorem mfderiv_ofWithMetric_apply (x : WithMetric g) (v : TangentSpace I x) :
    mfderiv I I ofWithMetric x v = v :=
  DFunLike.congr_fun (mfderiv_ofWithMetric x) v

/-- The differential of `toWithMetric g` maps a tangent vector to itself. -/
theorem mfderiv_toWithMetric_apply (x : M) (v : TangentSpace I x) :
    mfderiv I I (toWithMetric g) x v = v :=
  DFunLike.congr_fun (mfderiv_toWithMetric x) v

/-- Transporting a tangent vector of `M` to the copy and back gives the vector itself. -/
@[simp]
theorem mfderiv_ofWithMetric_mfderiv_toWithMetric (x : M) (v : TangentSpace I x) :
    mfderiv I I ofWithMetric (toWithMetric g x) (mfderiv I I (toWithMetric g) x v) = v := by
  rw [mfderiv_ofWithMetric_apply, mfderiv_toWithMetric_apply]

/-- Transporting a tangent vector of the copy to `M` and back gives the vector itself. -/
@[simp]
theorem mfderiv_toWithMetric_mfderiv_ofWithMetric (x : WithMetric g) (v : TangentSpace I x) :
    mfderiv I I (toWithMetric g) x.ofWithMetric (mfderiv I I ofWithMetric x v) = v := by
  rw [mfderiv_toWithMetric_apply, mfderiv_ofWithMetric_apply]

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']

/-- A map out of `M` is differentiable at a point exactly when it is differentiable as a map out
of the copy of `M`. -/
theorem mdifferentiableAt_comp_ofWithMetric_iff {u : M → M'} {x : WithMetric g} :
    MDifferentiableAt I I' (u ∘ ofWithMetric) x ↔ MDifferentiableAt I I' u x.ofWithMetric := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.comp x (hasMFDerivAt_ofWithMetric x).mdifferentiableAt⟩
  exact h.comp (g := u ∘ ofWithMetric) (f := toWithMetric g) x.ofWithMetric
    (hasMFDerivAt_toWithMetric x.ofWithMetric).mdifferentiableAt

/-- The chain rule along `ofWithMetric`. Since `ofWithMetric` is a diffeomorphism, it holds
without a differentiability hypothesis on `u`. -/
theorem mfderiv_comp_ofWithMetric (u : M → M') (x : WithMetric g) :
    mfderiv I I' (u ∘ ofWithMetric) x =
      (mfderiv I I' u x.ofWithMetric).comp (mfderiv I I ofWithMetric x) := by
  by_cases h : MDifferentiableAt I I' u x.ofWithMetric
  · exact mfderiv_comp x h (hasMFDerivAt_ofWithMetric x).mdifferentiableAt
  · rw [mfderiv_zero_of_not_mdifferentiableAt h, ContinuousLinearMap.zero_comp,
      mfderiv_zero_of_not_mdifferentiableAt (mdifferentiableAt_comp_ofWithMetric_iff.not.2 h)]

/-- The differential of a vector-valued function read on the copy of `M`. -/
theorem mvfderiv_comp_ofWithMetric_apply {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (u : M → F) (x : WithMetric g) (v : TangentSpace I x) :
    mvfderiv I (u ∘ ofWithMetric) x v =
      mvfderiv I u x.ofWithMetric (mfderiv I I ofWithMetric x v) := by
  simp only [mvfderiv, ContinuousLinearMap.comp_apply, mfderiv_comp_ofWithMetric]
  -- The remaining goal only differs by `(u ∘ ofWithMetric) x = u x.ofWithMetric`.
  rfl

end Derivatives

section DiffeomorphWithMetric

variable (g) in
/-- The identity diffeomorphism from the copy of `M` carrying `g` to the copy carrying `g'`. -/
def diffeomorphWithMetric
    (g' : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)) (k : ℕ∞ω) :
    WithMetric g ≃ₘ^k⟮I, I⟯ WithMetric g' :=
  (diffeomorph g k).trans (diffeomorph g' k).symm

@[simp]
theorem diffeomorphWithMetric_apply
    (g' : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)) (k : ℕ∞ω)
    (x : WithMetric g) :
    diffeomorphWithMetric g g' k x = toWithMetric g' x.ofWithMetric := by
  simp [diffeomorphWithMetric]

@[simp]
theorem diffeomorphWithMetric_symm
    (g' : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)) (k : ℕ∞ω) :
    (diffeomorphWithMetric g g' k).symm = diffeomorphWithMetric g' g k :=
  Diffeomorph.ext fun _ ↦ (diffeomorphWithMetric g g' k).injective (by simp)

@[simp]
theorem diffeomorphWithMetric_trans
    (g' g'' : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)) (k : ℕ∞ω) :
    (diffeomorphWithMetric g g' k).trans (diffeomorphWithMetric g' g'' k) =
      diffeomorphWithMetric g g'' k :=
  Diffeomorph.ext fun _ ↦ by simp

/-- The differential of the identity diffeomorphism between two copies of `M` is the identity of
the model space. -/
theorem mfderiv_diffeomorphWithMetric
    (g' : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)) (k : ℕ∞ω)
    (x : WithMetric g) :
    mfderiv I I (diffeomorphWithMetric g g' k) x = ContinuousLinearMap.id ℝ (TangentSpace I x) := by
  rw [show ⇑(diffeomorphWithMetric g g' k) = toWithMetric g' ∘ ofWithMetric from
    funext (diffeomorphWithMetric_apply g' k)]
  exact ((hasMFDerivAt_toWithMetric x.ofWithMetric).comp x (hasMFDerivAt_ofWithMetric x)).mfderiv

end DiffeomorphWithMetric

section Metric

variable [FiniteDimensional ℝ E]

variable (g) in
/-- The metric of the copy of `M` carrying `g`: the pullback of `g` along `ofWithMetric`. -/
def metric : ContMDiffRiemannianMetric I n E (fun x : WithMetric g ↦ TangentSpace I x) :=
  g.pullback ofWithMetric contMDiff_ofWithMetric fun x ↦ by
    rw [mfderiv_ofWithMetric]
    exact Function.injective_id

/-- The copy of `M` carrying `g` has the metric `g`. -/
instance : RiemannianBundle (fun x : WithMetric g ↦ TangentSpace I x) :=
  ⟨(metric g).toRiemannianMetric⟩

/-- The metric of the copy of `M` carrying a `C^n` metric is `C^n`. -/
instance : IsContMDiffRiemannianBundle I n E (fun x : WithMetric g ↦ TangentSpace I x) :=
  Bundle.instIsContMDiffRiemannianBundle (metric g)

/-- The metric of the copy of `M` carrying `g` is continuous. -/
instance : IsContinuousRiemannianBundle E (fun x : WithMetric g ↦ TangentSpace I x) :=
  Bundle.instIsContinuousRiemannianBundle (metric g).toContinuousRiemannianMetric

/-- The inner product of two tangent vectors of the copy of `M` carrying `g` is `g` evaluated on
the corresponding tangent vectors of `M`. -/
theorem inner_def (x : WithMetric g) (v w : TangentSpace I x) :
    inner ℝ v w =
      g.inner x.ofWithMetric (mfderiv I I ofWithMetric x v) (mfderiv I I ofWithMetric x w) :=
  ContMDiffRiemannianMetric.pullback_inner _ _ _ _ x v w

/-- The chart frames of the copy of `M` are those of `M`. -/
theorem mfderiv_ofWithMetric_chartLocalFrame (α x : WithMetric g)
    (i : Fin (Module.finrank ℝ E)) :
    mfderiv I I ofWithMetric x (Riemannian.Tensor.chartLocalFrame (I := I) α i x) =
      Riemannian.Tensor.chartLocalFrame (I := I) α.ofWithMetric i x.ofWithMetric := by
  by_cases hx : x ∈ (chartAt H α).source
  · rw [Riemannian.Tensor.chartLocalFrame_apply_of_mem_chart_source α hx,
      Riemannian.Tensor.chartLocalFrame_apply_of_mem_chart_source α.ofWithMetric
        ((mem_chartAt_source_iff α x).1 hx),
      mfderiv_ofWithMetric_apply]
    simp only [Trivialization.basisAt, Module.Basis.map_apply]
    exact trivializationAt_linearEquivAt_symm_apply α x _ _ _
  · rw [Riemannian.Tensor.chartLocalFrame_def, Riemannian.Tensor.chartLocalFrame_def,
      Trivialization.localFrame_apply_of_notMem _ _
        (by simpa only [TangentBundle.trivializationAt_baseSet] using hx),
      Trivialization.localFrame_apply_of_notMem _ _
        (by simpa only [TangentBundle.trivializationAt_baseSet] using
          (mem_chartAt_source_iff α x).not.1 hx),
      map_zero]

end Metric

end WithMetric

end TauCeti

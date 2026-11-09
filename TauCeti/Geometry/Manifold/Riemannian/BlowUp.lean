/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.IteratedFDeriv.Prod
public import TauCeti.Geometry.Manifold.ContMDiff.Subtype
public import TauCeti.Geometry.Manifold.ExtChartAt
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Pullback
public import TauCeti.Geometry.Manifold.Riemannian.Scaling
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Topology
public import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic

/-!
# Blowing up a metric at a point

Let `h` be a smooth Riemannian metric on an open subset `U` of a real vector space `V` that is
star-shaped about the origin, for example a normal domain of the exponential map. For `t` in
`[0, 1]` the *blow-up* `h.blowUp hU t` is the metric on `U` whose value at `v` is the value of `h`
at `t • v`, on the same tangent vectors. For `t > 0` it is the metric `t⁻² μ_t^* h` obtained by
pulling `h` back along the homothety `μ_t : v ↦ t • v` and scaling by `t⁻²`
(`Bundle.ContMDiffRiemannianMetric.blowUp_eq_rescale_pullback`), so it has scalar curvature
`t² Scal(h)(t • v)` at `v`. At `t = 0` it is the constant metric with the value of `h` at the
origin.

The family is continuous in `t` for every chart `Cᵏ` topology on metrics
(`Bundle.ContMDiffRiemannianMetric.continuous_blowUp_chartCk`). In coordinates the blow-up at `t`
reads `z ↦ h(t • z)`, whose order-`m` derivative `t ^ m D^m h(t • z)` depends jointly
continuously on `t` and `z`. Hence the rescaled metrics `t⁻² μ_t^* h` converge, as `t → 0`, to the
constant metric `h(0)` uniformly on compact sets together with all their derivatives. This is the
rescaled `C²` comparison, at a point, behind the Gromov–Lawson surgery construction: the metric
near the centre of a small ball, magnified to unit size, is `C²`-close to the flat metric of the
tangent space.

The open subset is a manifold modelled on `V` whose charts are all restrictions of the identity,
so its tangent-bundle trivializations are the identity
(`TauCeti.Manifold.trivializationAt_opens_model_space_symmL`). A field of bilinear forms on `U` is
then a smooth section exactly when it is smooth as a map into `V →L[ℝ] V →L[ℝ] ℝ`
(`TauCeti.Manifold.contMDiffAt_section_opens_model_space_iff`), and the chart metric of a metric
on `U` is the metric itself (`Bundle.ContMDiffRiemannianMetric.chartMetric_opens_model_space`).

## Main definitions

* `StarConvex.opensHomothety`: the homothety `v ↦ t • v` of a star-shaped open set, `t ∈ [0, 1]`.
* `Bundle.ContMDiffRiemannianMetric.blowUp`: the metric `v ↦ h(t • v)` on a star-shaped open set.

## Main results

* `Bundle.ContMDiffRiemannianMetric.continuous_blowUp_chartCk`: the blow-up is continuous in
  `t ∈ [0, 1]` for every chart `Cᵏ` topology, with value at `0` the constant metric `h(0)`.
* `Bundle.ContMDiffRiemannianMetric.blowUp_eq_rescale_pullback`: for `t > 0` the blow-up is
  `t⁻² μ_t^* h`.
* `Bundle.ContMDiffRiemannianMetric.scalarCurvature_blowUp`: for `t > 0` the blow-up has scalar
  curvature `t² Scal(h)(t • v)` at `v`.

## References

* M. Gromov, H. B. Lawson, *The classification of simply connected manifolds of positive scalar
  curvature*, Ann. of Math. 111 (1980), 423–434, proof of Theorem A.
-/

public section

open Bundle Set TopologicalSpace
open scoped ContDiff Manifold Topology

noncomputable section

/-! ### Open subsets of a vector space -/

namespace TauCeti.Manifold

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {U : Opens V}

omit [NormedSpace ℝ V] in
/-- All charts of an open subset of a vector space are the same restriction of the identity. -/
theorem chartAt_opens_model_space_eq (x y : U) : chartAt V x = chartAt V y := by
  simp only [Opens.chartAt_eq]
  rfl

/-- Every tangent-bundle trivialization of an open subset of a vector space is defined over the
whole subset. -/
theorem mem_trivializationAt_opens_model_space_baseSet (x y : U) :
    y ∈ (trivializationAt V (TangentSpace 𝓘(ℝ, V) : U → Type _) x).baseSet := by
  simp only [TangentBundle.trivializationAt_baseSet, chartAt_opens_model_space_eq x y]
  exact mem_chart_source V y

/-- The tangent-bundle trivializations of an open subset of a vector space are the identity. -/
theorem trivializationAt_opens_model_space_symmL (x y : U) (u : V) :
    (trivializationAt V (TangentSpace 𝓘(ℝ, V) : U → Type _) x).symmL ℝ y u = u := by
  rw [TangentBundle.symmL_trivializationAt_eq_core (by
    simpa using mem_trivializationAt_opens_model_space_baseSet x y)]
  rw [show achart V x = achart V y from Subtype.ext (chartAt_opens_model_space_eq x y)]
  exact (tangentBundleCore 𝓘(ℝ, V) U).coordChange_self _ _ (mem_achart_source V y) u

/-- On an open subset of a vector space, a field of bilinear forms on the tangent spaces is a
`C^n` section exactly when it is `C^n` as a map into the bilinear forms on the vector space. -/
theorem contMDiffAt_section_opens_model_space_iff {n : ℕ∞ω}
    {b : ∀ x : U, TangentSpace 𝓘(ℝ, V) x →L[ℝ] TangentSpace 𝓘(ℝ, V) x →L[ℝ] ℝ} {x₀ : U} :
    ContMDiffAt 𝓘(ℝ, V) (𝓘(ℝ, V).prod 𝓘(ℝ, V →L[ℝ] V →L[ℝ] ℝ)) n
      (fun x ↦ TotalSpace.mk' (V →L[ℝ] V →L[ℝ] ℝ)
        (E := fun x : U ↦ TangentSpace 𝓘(ℝ, V) x →L[ℝ] TangentSpace 𝓘(ℝ, V) x →L[ℝ] ℝ) x
        (b x)) x₀ ↔
      ContMDiffAt 𝓘(ℝ, V) 𝓘(ℝ, V →L[ℝ] V →L[ℝ] ℝ) n
        (fun x : U ↦ show V →L[ℝ] V →L[ℝ] ℝ from b x) x₀ := by
  rw [contMDiffAt_section]
  refine Filter.EventuallyEq.contMDiffAt_iff (Filter.Eventually.of_forall fun y ↦ ?_)
  have hy := mem_trivializationAt_opens_model_space_baseSet x₀ y
  refine ContinuousLinearMap.ext fun v ↦ ContinuousLinearMap.ext fun w ↦ ?_
  simp only [hom_trivializationAt_apply]
  rw [inCoordinates_apply_eq₂ hy hy (by simp)]
  simp only [Trivial.fiberBundle_trivializationAt', Trivial.linearMapAt_trivialization,
    LinearMap.id_apply]
  rw [← Trivialization.symmL_apply (R := ℝ) _ hy, trivializationAt_opens_model_space_symmL,
    ← Trivialization.symmL_apply (R := ℝ) _ hy, trivializationAt_opens_model_space_symmL]
  -- Both sides are `b y v w`, read in `V` and in the tangent space `TangentSpace 𝓘(ℝ, V) y = V`.
  rfl

end TauCeti.Manifold

/-! ### Homotheties of star-shaped open sets -/

namespace StarConvex

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {U : Opens V}
  (hU : StarConvex ℝ 0 (U : Set V))

/-- The homothety `v ↦ t • v` with centre `0` and ratio `t ∈ [0, 1]`, as a self-map of an open set
that is star-shaped about `0`. -/
@[expose]
def opensHomothety (t : Icc (0 : ℝ) 1) (v : U) : U :=
  ⟨(t : ℝ) • (v : V), starConvex_zero_iff.1 hU v.2 t.2.1 t.2.2⟩

@[simp]
theorem coe_opensHomothety (t : Icc (0 : ℝ) 1) (v : U) :
    (hU.opensHomothety t v : V) = (t : ℝ) • (v : V) :=
  rfl

theorem contMDiff_opensHomothety {n : ℕ∞ω} (t : Icc (0 : ℝ) 1) :
    ContMDiff 𝓘(ℝ, V) 𝓘(ℝ, V) n (hU.opensHomothety t) :=
  (TauCeti.ContMDiff.subtypeVal_comp_iff U (hU.opensHomothety t)).1
    ((contDiff_const_smul (t : ℝ)).contMDiff.comp contMDiff_subtype_val)

/-- The differential of the homothety of ratio `t` is multiplication by `t`. -/
theorem mfderiv_opensHomothety (t : Icc (0 : ℝ) 1) (v : U) :
    mfderiv 𝓘(ℝ, V) 𝓘(ℝ, V) (hU.opensHomothety t) v = (t : ℝ) • ContinuousLinearMap.id ℝ V := by
  ext u
  have h := TauCeti.Manifold.tangentSpaceOpenEquiv_mfderiv_apply
    (A := ⇑((t : ℝ) • ContinuousLinearMap.id ℝ V))
    ((hU.contMDiff_opensHomothety t (n := 1) v).mdifferentiableAt one_ne_zero) rfl u
  simp only [TauCeti.Manifold.tangentSpaceOpenEquiv_apply] at h
  rw [h, ContinuousLinearMap.mfderiv_eq]
  rfl

/-- A homothety of nonzero ratio has invertible differential. -/
theorem isInvertible_mfderiv_opensHomothety [FiniteDimensional ℝ V] (t : Icc (0 : ℝ) 1)
    (ht : (t : ℝ) ≠ 0) (v : U) :
    (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, V) (hU.opensHomothety t) v).IsInvertible := by
  refine ⟨(LinearEquiv.smulOfNeZero ℝ V (t : ℝ) ht).toContinuousLinearEquiv, ?_⟩
  rw [hU.mfderiv_opensHomothety t v]
  rfl

end StarConvex

/-! ### The blow-up of a metric -/

namespace Bundle.ContMDiffRiemannianMetric

open TauCeti.Manifold

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {U : Opens V}

-- As in the chart topology module, cache the canonical operator norms to keep inference for
-- iterated multilinear maps into the space of bilinear forms within the instance-search limit.
private local instance : NormedAddCommGroup (V →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance : NormedSpace ℝ (V →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
private local instance : NormedAddCommGroup (V →L[ℝ] V →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance : NormedSpace ℝ (V →L[ℝ] V →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

/-- On an open subset of a vector space, the chart metric of a metric at a point of the subset is
the value of the metric there. -/
theorem chartMetric_opens_model_space
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, V) ∞ V (fun x : U ↦ TangentSpace 𝓘(ℝ, V) x))
    (x₀ : U) {z : V} (hz : z ∈ U) :
    g.toNondegenerateMetric.chartMetric x₀ z = g.inner ⟨z, hz⟩ := by
  have hsymm : (extChartAt 𝓘(ℝ, V) x₀).symm z = ⟨z, hz⟩ := by
    simp only [extChartAt, Opens.chartAt_eq, OpenPartialHomeomorph.subtypeRestr]
    exact Subtype.ext ((U.openPartialHomeomorphSubtypeCoe _).right_inv (by simpa using hz))
  ext u w
  rw [TauCeti.Manifold.ContMDiffNondegenerateMetric.chartMetric_apply _
      (by rwa [Opens.extChartAt_opens_target]), hsymm,
    ← Trivialization.symmL_apply (R := ℝ) _ (mem_trivializationAt_opens_model_space_baseSet _ _),
    ← Trivialization.symmL_apply (R := ℝ) _ (mem_trivializationAt_opens_model_space_baseSet _ _),
    trivializationAt_opens_model_space_symmL, trivializationAt_opens_model_space_symmL]
  exact toNondegenerateMetric_apply g ⟨z, hz⟩ u w

variable (h : ContMDiffRiemannianMetric 𝓘(ℝ, V) ∞ V (fun x : U ↦ TangentSpace 𝓘(ℝ, V) x))
  (hU : StarConvex ℝ 0 (U : Set V))

/-- The *blow-up* of a metric `h` on an open set `U` star-shaped about `0`, at scale
`t ∈ [0, 1]`: the metric whose value at `v` is the value of `h` at `t • v`, on the same tangent
vectors. For `t > 0` this is `t⁻² μ_t^* h` for the homothety `μ_t` of ratio `t`
(`Bundle.ContMDiffRiemannianMetric.blowUp_eq_rescale_pullback`); for `t = 0` it is the constant
metric with the value of `h` at `0`. -/
@[expose]
def blowUp (t : Icc (0 : ℝ) 1) :
    ContMDiffRiemannianMetric 𝓘(ℝ, V) ∞ V (fun x : U ↦ TangentSpace 𝓘(ℝ, V) x) where
  inner v := h.inner (hU.opensHomothety t v)
  symm v := h.symm (hU.opensHomothety t v)
  pos v := h.pos (hU.opensHomothety t v)
  isVonNBounded v := h.isVonNBounded (hU.opensHomothety t v)
  contMDiff v₀ := contMDiffAt_section_opens_model_space_iff.2
    ((contMDiffAt_section_opens_model_space_iff.1 (h.contMDiff (hU.opensHomothety t v₀))).comp v₀
      (hU.contMDiff_opensHomothety t v₀))

@[simp]
theorem blowUp_inner (t : Icc (0 : ℝ) 1) (v : U) :
    (h.blowUp hU t).inner v = h.inner (hU.opensHomothety t v) :=
  rfl

/-- At scale `0` the blow-up is the constant metric with the value of `h` at the origin. -/
theorem blowUp_zero_inner (v : U) :
    (h.blowUp hU 0).inner v =
      h.inner ⟨0, by simpa using starConvex_zero_iff.1 hU v.2 le_rfl zero_le_one⟩ := by
  rw [blowUp_inner]
  congr 1
  exact Subtype.ext (zero_smul ℝ (v : V))

/-- At scale `1` the blow-up is the metric itself. -/
@[simp]
theorem blowUp_one : h.blowUp hU 1 = h := by
  ext ⟨v, hv⟩ u w
  exact congrArg (fun p : U ↦ (show V →L[ℝ] V →L[ℝ] ℝ from h.inner p) u w)
    (Subtype.ext (one_smul ℝ v))

/-- In coordinates, the blow-up at scale `t` reads the chart metric of `h` at `t • z`. -/
theorem chartMetric_blowUp (t : Icc (0 : ℝ) 1) (x₀ : U) {z : V} (hz : z ∈ U) :
    (h.blowUp hU t).toNondegenerateMetric.chartMetric x₀ z =
      h.toNondegenerateMetric.chartMetric x₀ ((t : ℝ) • z) := by
  rw [chartMetric_opens_model_space _ _ hz,
    chartMetric_opens_model_space _ _ (starConvex_zero_iff.1 hU hz t.2.1 t.2.2)]
  rfl

/-- **The rescaled comparison at a point.** The blow-up `t ↦ h.blowUp hU t` is continuous on
`[0, 1]` for every chart `Cᵏ` topology on metrics, `k ≤ ∞`. Its value at `0` is the constant metric
`h(0)`, so the rescaled metrics `t⁻² μ_t^* h` converge to `h(0)` as `t → 0`, uniformly on compact
sets with derivatives of every order. -/
theorem continuous_blowUp_chartCk [FiniteDimensional ℝ V] (k : ℕ∞) :
    letI := chartCkTopology (I := 𝓘(ℝ, V)) (M := U) k
    Continuous (h.blowUp hU) := by
  let _ := chartCkTopology (I := 𝓘(ℝ, V)) (M := U) k
  refine (continuous_chartCk_iff k).2 fun x m _ ↦ continuous_iff_continuousAt.2 fun q ↦ ?_
  obtain ⟨⟨t₀, ht₀⟩, z₀, hz₀⟩ := q
  rw [Opens.extChartAt_opens_target] at hz₀
  set H := h.toNondegenerateMetric.chartMetric x
  have hH := h.toNondegenerateMetric.contDiffOn_chartMetric x
  rw [Opens.extChartAt_opens_target] at hH
  -- Near `(t₀, z₀)`, the coordinate expression `(t, z) ↦ H (t • z)` of the family is smooth on a
  -- product of open sets, so its partial derivatives in `z` are jointly continuous.
  let W : Set (ℝ × V) := (fun p : ℝ × V ↦ p.1 • p.2) ⁻¹' U ∩ (Prod.snd ⁻¹' U)
  have hW : IsOpen W := (U.isOpen.preimage (continuous_fst.smul continuous_snd)).inter
    (U.isOpen.preimage continuous_snd)
  obtain ⟨s, u, hs, hu, hts, hzu, hsu⟩ := isOpen_prod_iff.1 hW t₀ z₀
    ⟨starConvex_zero_iff.1 hU hz₀ ht₀.1 ht₀.2, hz₀⟩
  have hF : ContDiffOn ℝ ∞ (fun p : ℝ × V ↦ H (p.1 • p.2)) (s ×ˢ u) :=
    hH.comp (contDiff_fst.smul contDiff_snd).contDiffOn fun p hp ↦ (hsu hp).1
  have hcont := (ContDiffOn.continuousOn_iteratedFDerivWithin_prod_right hF
    (hs.uniqueDiffOn.prod hu.uniqueDiffOn) m (by simp)).continuousAt
      (x := (t₀, z₀)) ((hs.prod hu).mem_nhds ⟨hts, hzu⟩)
  have hmap : Continuous fun q : Icc (0 : ℝ) 1 × (extChartAt 𝓘(ℝ, V) x).target ↦
      ((q.1 : ℝ), (q.2 : V)) :=
    (continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd)
  refine (hcont.comp (f := fun q : Icc (0 : ℝ) 1 × (extChartAt 𝓘(ℝ, V) x).target ↦
      ((q.1 : ℝ), (q.2 : V))) hmap.continuousAt).congr ?_
  filter_upwards [hmap.continuousAt.preimage_mem_nhds ((hs.prod hu).mem_nhds ⟨hts, hzu⟩)]
    with q hq
  obtain ⟨⟨t, ht⟩, z, hz⟩ := q
  simp only [Set.mem_preimage, Set.mem_prod] at hq
  simp only [Function.comp_apply]
  rw [iteratedFDerivWithin_of_isOpen _ hu hq.2]
  rw [Opens.extChartAt_opens_target] at hz
  have heq : (h.blowUp hU ⟨t, ht⟩).toNondegenerateMetric.chartMetric x =ᶠ[𝓝 z]
      fun y ↦ H (t • y) := by
    filter_upwards [U.isOpen.mem_nhds hz] with y hy
    exact chartMetric_blowUp h hU ⟨t, ht⟩ x hy
  exact (heq.iteratedFDeriv ℝ m).eq_of_nhds.symm

variable [FiniteDimensional ℝ V]

/-- For `t > 0`, the blow-up at scale `t` is the pullback of `h` along the homothety of ratio `t`,
scaled by `t⁻²`. -/
theorem blowUp_eq_rescale_pullback (t : Icc (0 : ℝ) 1) (ht : 0 < (t : ℝ)) :
    h.blowUp hU t = (h.pullback (hU.opensHomothety t) (hU.contMDiff_opensHomothety t)
      fun v ↦ (hU.isInvertible_mfderiv_opensHomothety t ht.ne' v).injective).rescale
        (fun _ ↦ ((t : ℝ) ^ 2)⁻¹) contMDiff_const fun _ ↦ by positivity := by
  have hs (B : V →L[ℝ] V →L[ℝ] ℝ) (a b : V) :
      B ((t : ℝ) • a) ((t : ℝ) • b) = (t : ℝ) ^ 2 * B a b := by
    simp only [map_smul, smul_apply, smul_eq_mul]
    ring
  ext v u w
  simp only [blowUp_inner, rescale_inner, pullback_inner, StarConvex.mfderiv_opensHomothety]
  -- `hs` is stated in `V`; the metric pairs the tangent space `TangentSpace 𝓘(ℝ, V) _ = V`.
  erw [hs (h.inner (hU.opensHomothety t v)) u w]
  field_simp
  rfl

/-- For `t > 0`, the blow-up at scale `t` has scalar curvature `t² Scal(h)(t • v)` at `v`. -/
theorem scalarCurvature_blowUp (t : Icc (0 : ℝ) 1) (ht : 0 < (t : ℝ)) (v : U) :
    (h.blowUp hU t).scalarCurvature v =
      (t : ℝ) ^ 2 * h.scalarCurvature (hU.opensHomothety t v) := by
  rw [blowUp_eq_rescale_pullback h hU t ht, scalarCurvature_rescale_const,
    scalarCurvature_pullback_of_isInvertible _ _
      (hU.isInvertible_mfderiv_opensHomothety t ht.ne'), inv_inv]

end Bundle.ContMDiffRiemannianMetric

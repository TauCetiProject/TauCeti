/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.IteratedFDeriv.Prod
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

The open subset is a manifold modelled on `V` whose tangent-bundle trivializations are the
identity, so a field of bilinear forms on `U` is a smooth section exactly when it is smooth as a
map into `V →L[ℝ] V →L[ℝ] ℝ` (`TauCeti.Manifold.contMDiffAt_section_opens_model_space_iff`), and
the chart metric of a metric on `U` is the metric itself
(`Bundle.ContMDiffRiemannianMetric.chartMetric_opens_model_space`). The blow-up is built from the
homothety `StarConvex.opensHomothety` of `U`.

## Main definitions

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

variable (h : ContMDiffRiemannianMetric 𝓘(ℝ, V) ∞ V (fun x : U ↦ TangentSpace 𝓘(ℝ, V) x))
  (hU : StarConvex ℝ 0 (U : Set V))

/-- The *blow-up* of a metric `h` on an open set `U` star-shaped about `0`, at scale
`t ∈ [0, 1]`: the metric whose value at `v` is the value of `h` at `t • v`, on the same tangent
vectors. For `t > 0` this is `t⁻² μ_t^* h` for the homothety `μ_t` of ratio `t`
(`Bundle.ContMDiffRiemannianMetric.blowUp_eq_rescale_pullback`); for `t = 0` it is the constant
metric with the value of `h` at `0`. -/
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
  (rfl)

/-- At scale `0` the blow-up is the constant metric with the value of `h` at the origin. -/
theorem blowUp_zero_inner (v : U) :
    (h.blowUp hU 0).inner v =
      h.inner ⟨0, by simpa using starConvex_zero_iff.1 hU v.2 le_rfl zero_le_one⟩ := by
  rw [blowUp_inner]
  congr 1
  exact Subtype.ext ((hU.coe_opensHomothety 0 v).trans (zero_smul ℝ (v : V)))

/-- At scale `1` the blow-up is the metric itself. -/
@[simp]
theorem blowUp_one : h.blowUp hU 1 = h := by
  ext ⟨v, hv⟩ u w
  exact congrArg (fun p : U ↦ (show V →L[ℝ] V →L[ℝ] ℝ from h.inner p) u w)
    (Subtype.ext ((hU.coe_opensHomothety 1 ⟨v, hv⟩).trans (one_smul ℝ v)))

/-- In coordinates, the blow-up at scale `t` reads the chart metric of `h` at `t • z`. -/
theorem chartMetric_blowUp (t : Icc (0 : ℝ) 1) (x₀ : U) {z : V} (hz : z ∈ U) :
    (h.blowUp hU t).toNondegenerateMetric.chartMetric x₀ z =
      h.toNondegenerateMetric.chartMetric x₀ ((t : ℝ) • z) := by
  rw [chartMetric_opens_model_space _ _ hz,
    chartMetric_opens_model_space _ _ (starConvex_zero_iff.1 hU hz t.2.1 t.2.2), blowUp_inner]
  congr 1
  exact Subtype.ext (hU.coe_opensHomothety t _)

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

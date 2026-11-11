/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.LocallyConvex.WeakSpace
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import TauCeti.Analysis.Sobolev.LipschitzDomain.HalfDisc.Basic
public import TauCeti.Analysis.Sobolev.LipschitzDomain.Morrey

/-!
# Vanishing on the flat segment of the half-disc

The frontier of the half-disc `TauCeti.halfDisc r` contains the flat segment
`TauCeti.halfDiscFlatSegment r = {x | ‖x‖ ≤ r ∧ x.fst = 0}`. In the complex coordinate
`z = s + it` of the module docstring of `TauCeti.Analysis.Sobolev.LipschitzDomain.HalfDisc.Basic`,
the first coordinate is `t = Im z`, so the flat segment is the real interval `[-r, r]`.

The totally real boundary condition `ξ(s) ∈ ℝⁿ` of a `ℂⁿ`-valued map on the half-disc says that
the imaginary part of each component vanishes on the flat segment. This file studies that
condition for one real-valued function `u ∈ W^{1,p}(halfDisc r)`, `1 ≤ p < ∞`:

* `TauCeti.W1p.halfDiscFlatTraceZeroSubmodule` is the subspace of `u` whose boundary trace
  `TauCeti.W1p.frontierTrace u` vanishes almost everywhere on the flat segment, for normalized
  one-dimensional Euclidean Hausdorff measure. It is the kernel of a bounded linear map, hence a
  closed subspace (`TauCeti.W1p.isClosed_halfDiscFlatTraceZeroSubmodule`), closed under
  `W^{1,p}` limits and weakly closed.
* If `u` has a representative continuous up to the boundary, the condition says exactly that this
  representative vanishes at every point of the flat segment
  (`TauCeti.W1p.mem_halfDiscFlatTraceZeroSubmodule_iff_of_continuousOn`). For `p > 2` every `u`
  has such a representative by Morrey's embedding
  (`TauCeti.W1p.exists_continuousOn_mem_halfDiscFlatTraceZeroSubmodule_iff`), so the trace
  condition is the pointwise condition.

The pointwise reading needs one measure-theoretic input: surface measure on the flat segment is
the image of Lebesgue measure on `[-r, r]` under the isometry `t ↦ (0, t)`
(`TauCeti.euclideanHausdorffMeasure_restrict_halfDiscFlatSegment`), so a continuous function that
vanishes almost everywhere on the segment vanishes everywhere on it.

For `p = 2` the trace is genuinely needed: the function `log log (2 / |1 - z|)` of
`TauCeti.Analysis.Sobolev.W1p.LogLogTraceExample` lies in `W^{1,2}` of the disc but has no
continuous boundary value at `1`.

## Main declarations

* `TauCeti.halfDiscFlatSegment`: the flat segment of the frontier of the half-disc.
* `TauCeti.euclideanHausdorffMeasure_restrict_halfDiscFlatSegment`: surface measure on the flat
  segment is Lebesgue measure on `[-r, r]`.
* `TauCeti.W1p.halfDiscFlatTraceL`: the trace on the flat segment, a bounded linear map.
* `TauCeti.W1p.halfDiscFlatTraceZeroSubmodule`: its kernel, the functions of zero trace on the
  flat segment.
* `TauCeti.W1p.mem_halfDiscFlatTraceZeroSubmodule_iff`: membership in terms of the trace operator
  of any Lipschitz constant of the half-disc.
* `TauCeti.W1p.isClosed_halfDiscFlatTraceZeroSubmodule`,
  `TauCeti.W1p.isClosed_toWeakSpace_halfDiscFlatTraceZeroSubmodule`: the subspace is closed and
  weakly closed.
* `TauCeti.W1p.mem_halfDiscFlatTraceZeroSubmodule_iff_of_continuousOn`,
  `TauCeti.W1p.exists_continuousOn_mem_halfDiscFlatTraceZeroSubmodule_iff`: the pointwise reading,
  and for `p > 2` the existence of the continuous representative.
* `TauCeti.W1p.exists_value_ae_eq_fst_mem_halfDiscFlatTraceZeroSubmodule` and
  `TauCeti.W1p.const_notMem_halfDiscFlatTraceZeroSubmodule`: the normal coordinate satisfies the
  condition, a nonzero constant does not.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Appendix B.4
  (boundary conditions on the half-disc).
* L. C. Evans, *Partial Differential Equations*, 2nd ed., §5.5.
-/

public section

noncomputable section

open Bornology MeasureTheory Metric Module Set TopologicalSpace
open scoped ENNReal NNReal Gradient

namespace TauCeti

/-- The flat segment `{x | ‖x‖ ≤ r ∧ x.fst = 0}` of the frontier of `TauCeti.halfDisc r`. In the
complex coordinate `z = s + it` with `t = x.fst` it is the real interval `[-r, r]`. -/
def halfDiscFlatSegment (r : ℝ) : Set (WithLp 2 (ℝ × ℝ)) :=
  closedBall 0 r ∩ {x | x.fst = 0}

theorem mem_halfDiscFlatSegment {r : ℝ} {x : WithLp 2 (ℝ × ℝ)} :
    x ∈ halfDiscFlatSegment r ↔ ‖x‖ ≤ r ∧ x.fst = 0 := by
  rw [halfDiscFlatSegment, mem_inter_iff, mem_closedBall_zero_iff, mem_ofPred_eq]

theorem isClosed_halfDiscFlatSegment (r : ℝ) : IsClosed (halfDiscFlatSegment r) :=
  isClosed_closedBall.inter
    (isClosed_eq (WithLp.prod_continuous_ofLp 2 ℝ ℝ).fst continuous_const)

theorem measurableSet_halfDiscFlatSegment (r : ℝ) : MeasurableSet (halfDiscFlatSegment r) :=
  (isClosed_halfDiscFlatSegment r).measurableSet

/-- For `0 < r` the flat segment lies in the frontier of the half-disc. -/
theorem halfDiscFlatSegment_subset_frontier {r : ℝ} (hr : 0 < r) :
    halfDiscFlatSegment r ⊆ frontier (halfDisc r : Set (WithLp 2 (ℝ × ℝ))) := by
  rw [frontier_halfDisc hr]
  exact subset_union_left

/-- For `0 < r` the flat segment lies in the closed half-disc. -/
theorem halfDiscFlatSegment_subset_closure {r : ℝ} (hr : 0 < r) :
    halfDiscFlatSegment r ⊆ closure (halfDisc r : Set (WithLp 2 (ℝ × ℝ))) :=
  (halfDiscFlatSegment_subset_frontier hr).trans frontier_subset_closure

/-- The norm of `(0, t)` is `|t|`. -/
private theorem norm_toLp_zero_prod (t : ℝ) : ‖WithLp.toLp 2 ((0 : ℝ), t)‖ = |t| := by
  rw [WithLp.prod_norm_eq_of_L2]
  simp [Real.sqrt_sq_eq_abs]

/-- The map `t ↦ (0, t)` is an isometry onto the line containing the flat segment. -/
private theorem isometry_toLp_zero_prod : Isometry fun t : ℝ => WithLp.toLp 2 ((0 : ℝ), t) := by
  refine Isometry.of_dist_eq fun s t => ?_
  rw [dist_eq_norm, dist_eq_norm, ← WithLp.toLp_sub, Prod.mk_sub_mk, sub_zero,
    norm_toLp_zero_prod, Real.norm_eq_abs]

/-- The flat segment is the image of `[-r, r]` under `t ↦ (0, t)`. -/
private theorem image_Icc_toLp_zero_prod (r : ℝ) :
    (fun t : ℝ => WithLp.toLp 2 ((0 : ℝ), t)) '' Icc (-r) r = halfDiscFlatSegment r := by
  ext x
  rw [mem_image, mem_halfDiscFlatSegment]
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨(norm_toLp_zero_prod t).trans_le (abs_le.2 ht), rfl⟩
  · rintro ⟨hx, hx₁⟩
    have hx' : WithLp.toLp 2 ((0 : ℝ), x.snd) = x := by
      rw [← hx₁]
      rfl
    refine ⟨x.snd, abs_le.1 ?_, hx'⟩
    rwa [← norm_toLp_zero_prod, hx']

/-- **Surface measure on the flat segment.** Normalized one-dimensional Euclidean Hausdorff
measure on the flat segment of the half-disc is the image of Lebesgue measure on `[-r, r]` under
the isometry `t ↦ (0, t)`. -/
theorem euclideanHausdorffMeasure_restrict_halfDiscFlatSegment (r : ℝ) :
    (μHE[1] : Measure (WithLp 2 (ℝ × ℝ))).restrict (halfDiscFlatSegment r) =
      (volume.restrict (Icc (-r) r)).map fun t : ℝ => WithLp.toLp 2 ((0 : ℝ), t) := by
  have hι := isometry_toLp_zero_prod
  have hvol : (μHE[1] : Measure ℝ) = volume := by
    simpa using InnerProductSpace.euclideanHausdorffMeasure_eq_volume (V := ℝ)
  have hpre : (fun t : ℝ => WithLp.toLp 2 ((0 : ℝ), t)) ⁻¹' halfDiscFlatSegment r = Icc (-r) r := by
    rw [← image_Icc_toLp_zero_prod, hι.injective.preimage_image]
  rw [← hpre, ← Measure.restrict_map hι.continuous.measurable
    (measurableSet_halfDiscFlatSegment r), ← hvol, hι.map_euclideanHausdorffMeasure,
    Measure.restrict_restrict (measurableSet_halfDiscFlatSegment r), inter_eq_left.2]
  rw [← image_Icc_toLp_zero_prod]
  exact image_subset_range _ _

/-- The flat segment of the half-disc of radius `r` has length `2 r`. -/
theorem euclideanHausdorffMeasure_halfDiscFlatSegment (r : ℝ) :
    (μHE[1] : Measure (WithLp 2 (ℝ × ℝ))) (halfDiscFlatSegment r) = ENNReal.ofReal (2 * r) := by
  rw [← Measure.restrict_apply_univ, euclideanHausdorffMeasure_restrict_halfDiscFlatSegment,
    Measure.map_apply isometry_toLp_zero_prod.continuous.measurable MeasurableSet.univ,
    preimage_univ, Measure.restrict_apply_univ, Real.volume_Icc]
  ring_nf

/-- **Continuous functions are determined by their values almost everywhere on the flat
segment.** For `0 < r`, two functions continuous on the flat segment that agree almost everywhere
for surface measure on it agree at every point of it. -/
theorem eqOn_halfDiscFlatSegment_of_ae_eq {r : ℝ} (hr : 0 < r) {f g : WithLp 2 (ℝ × ℝ) → ℝ}
    (hf : ContinuousOn f (halfDiscFlatSegment r)) (hg : ContinuousOn g (halfDiscFlatSegment r))
    (hfg : f =ᵐ[(μHE[1] : Measure (WithLp 2 (ℝ × ℝ))).restrict (halfDiscFlatSegment r)] g) :
    EqOn f g (halfDiscFlatSegment r) := by
  have hι := isometry_toLp_zero_prod
  have hmaps : MapsTo (fun t : ℝ => WithLp.toLp 2 ((0 : ℝ), t)) (Icc (-r) r)
      (halfDiscFlatSegment r) := by
    rw [← image_Icc_toLp_zero_prod]
    exact mapsTo_image _ _
  rw [euclideanHausdorffMeasure_restrict_halfDiscFlatSegment] at hfg
  have hEq := Measure.eqOn_Icc_of_ae_eq volume (by linarith : -r ≠ r)
    (ae_of_ae_map (p := fun y => f y = g y) hι.continuous.aemeasurable hfg)
    (hf.comp hι.continuous.continuousOn hmaps) (hg.comp hι.continuous.continuousOn hmaps)
  rw [← image_Icc_toLp_zero_prod]
  rintro _ ⟨t, ht, rfl⟩
  exact hEq ht

/-- The half-disc has finite Lebesgue measure. -/
instance isFiniteMeasure_volume_restrict_halfDisc (r : ℝ) :
    IsFiniteMeasure (volume.restrict (halfDisc r : Set (WithLp 2 (ℝ × ℝ)))) :=
  isFiniteMeasure_restrict.2 (isBounded_halfDisc r).measure_lt_top.ne

/-! ### The trace condition on the flat segment -/

section Trace

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {r : ℝ}

/-- The trace operator of a bounded Lipschitz domain does not depend on the Lipschitz constant
used to construct it. -/
private theorem W1p.frontierTrace_halfDisc_eq (hp : p ≠ (∞ : ℝ≥0∞)) {L L' : ℝ≥0}
    (hΩ : (halfDisc r : Set (WithLp 2 (ℝ × ℝ))).IsLipschitzDomainWith L)
    (hΩ' : (halfDisc r : Set (WithLp 2 (ℝ × ℝ))).IsLipschitzDomainWith L') :
    W1p.frontierTrace hp hΩ (isBounded_halfDisc r) =
      W1p.frontierTrace hp hΩ' (isBounded_halfDisc r) :=
  W1p.eq_frontierTrace hp hΩ' _ _ fun φ =>
    W1p.frontierTrace_ae_eq_of_continuousOn hp hΩ _ φ.continuous.continuousOn
      (W1p.value_restrictL_ofTestFunctionₗ_ae le_top φ)

/-- Almost-everywhere statements transfer along an equality of measures. -/
private theorem ae_iff_of_measure_eq {X : Type*} [MeasurableSpace X] {μ ν : Measure X}
    (h : μ = ν) {P : X → Prop} : (∀ᵐ x ∂μ, P x) ↔ ∀ᵐ x ∂ν, P x :=
  h ▸ Iff.rfl

/-- Surface measure on the frontier of the half-disc, restricted to the flat segment, is surface
measure on the flat segment. -/
private theorem restrict_frontier_restrict_halfDiscFlatSegment (hr : 0 < r) :
    ((μHE[finrank ℝ ℝ] : Measure (WithLp 2 (ℝ × ℝ))).restrict
        (frontier (halfDisc r : Set (WithLp 2 (ℝ × ℝ))))).restrict (halfDiscFlatSegment r) =
      (μHE[1] : Measure (WithLp 2 (ℝ × ℝ))).restrict (halfDiscFlatSegment r) := by
  rw [Measure.restrict_restrict (measurableSet_halfDiscFlatSegment r),
    inter_eq_left.2 (halfDiscFlatSegment_subset_frontier hr), finrank_self]

/-- **The trace on the flat segment** of the half-disc, `W^{1,p}(halfDisc r) → Lᵖ(flat segment)`
for `p < ∞`: the boundary trace `TauCeti.W1p.frontierTrace`, for one choice of Lipschitz
constant, restricted to the flat segment. By `TauCeti.W1p.mem_halfDiscFlatTraceZeroSubmodule_iff`
its kernel does not depend on that choice. -/
def W1p.halfDiscFlatTraceL (hp : p ≠ (∞ : ℝ≥0∞)) (r : ℝ) :
    W1p volume (halfDisc r) p →L[ℝ] Lp ℝ p
      (((μHE[finrank ℝ ℝ] : Measure (WithLp 2 (ℝ × ℝ))).restrict
        (frontier (halfDisc r : Set (WithLp 2 (ℝ × ℝ))))).restrict (halfDiscFlatSegment r)) :=
  (LpToLpRestrictCLM (WithLp 2 (ℝ × ℝ)) ℝ ℝ _ p (halfDiscFlatSegment r)).comp
    (W1p.frontierTrace hp (exists_isLipschitzDomainWith_halfDisc r).choose_spec
      (isBounded_halfDisc r))

/-- **Functions of zero trace on the flat segment.** The subspace of `W^{1,p}(halfDisc r)`,
`p < ∞`, of functions whose boundary trace vanishes almost everywhere on the flat segment: the
kernel of `TauCeti.W1p.halfDiscFlatTraceL`. This is the real part of the totally real boundary
condition `ξ ∈ ℝⁿ` on the flat segment, applied to the imaginary parts of the components. -/
def W1p.halfDiscFlatTraceZeroSubmodule (hp : p ≠ (∞ : ℝ≥0∞)) (r : ℝ) :
    Submodule ℝ (W1p volume (halfDisc r) p) :=
  LinearMap.ker (W1p.halfDiscFlatTraceL hp r).toLinearMap

/-- A function lies in `TauCeti.W1p.halfDiscFlatTraceZeroSubmodule` exactly when its trace, for
any Lipschitz constant of the half-disc, vanishes almost everywhere on the flat segment for
surface measure. -/
theorem W1p.mem_halfDiscFlatTraceZeroSubmodule_iff (hp : p ≠ (∞ : ℝ≥0∞)) (hr : 0 < r)
    {L : ℝ≥0} (hΩ : (halfDisc r : Set (WithLp 2 (ℝ × ℝ))).IsLipschitzDomainWith L)
    {u : W1p volume (halfDisc r) p} :
    u ∈ W1p.halfDiscFlatTraceZeroSubmodule hp r ↔
      ∀ᵐ x ∂(μHE[1] : Measure (WithLp 2 (ℝ × ℝ))).restrict (halfDiscFlatSegment r),
        W1p.frontierTrace hp hΩ (isBounded_halfDisc r) u x = 0 := by
  rw [W1p.halfDiscFlatTraceZeroSubmodule, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
    W1p.halfDiscFlatTraceL, ContinuousLinearMap.comp_apply,
    W1p.frontierTrace_halfDisc_eq hp _ hΩ, Lp.eq_zero_iff_ae_eq_zero,
    ← ae_iff_of_measure_eq (restrict_frontier_restrict_halfDiscFlatSegment hr)]
  have hcoe := LpToLpRestrictCLM_coeFn ℝ (halfDiscFlatSegment r)
    (W1p.frontierTrace hp hΩ (isBounded_halfDisc r) u)
  constructor
  · intro h
    filter_upwards [hcoe, h] with x hx hx'
    rw [← hx, hx', Pi.zero_apply]
  · intro h
    filter_upwards [hcoe, h] with x hx hx'
    rw [hx, hx', Pi.zero_apply]

/-- **The zero-trace condition is closed** in `W^{1,p}(halfDisc r)`. -/
theorem W1p.isClosed_halfDiscFlatTraceZeroSubmodule (hp : p ≠ (∞ : ℝ≥0∞)) (r : ℝ) :
    IsClosed (W1p.halfDiscFlatTraceZeroSubmodule hp r : Set (W1p volume (halfDisc r) p)) :=
  (W1p.halfDiscFlatTraceL hp r).isClosed_ker

/-- **The zero-trace condition passes to `W^{1,p}` limits.** -/
theorem W1p.mem_halfDiscFlatTraceZeroSubmodule_of_tendsto (hp : p ≠ (∞ : ℝ≥0∞)) {ι : Type*}
    {l : Filter ι} [l.NeBot] {u : ι → W1p volume (halfDisc r) p} {v : W1p volume (halfDisc r) p}
    (hv : Filter.Tendsto u l (nhds v))
    (hu : ∀ᶠ i in l, u i ∈ W1p.halfDiscFlatTraceZeroSubmodule hp r) :
    v ∈ W1p.halfDiscFlatTraceZeroSubmodule hp r :=
  (W1p.isClosed_halfDiscFlatTraceZeroSubmodule hp r).mem_of_tendsto hv hu

/-- **The zero-trace condition is weakly closed**: its image in the weak topology of
`W^{1,p}(halfDisc r)` is closed, since it is a closed convex set. -/
theorem W1p.isClosed_toWeakSpace_halfDiscFlatTraceZeroSubmodule (hp : p ≠ (∞ : ℝ≥0∞)) (r : ℝ) :
    IsClosed (toWeakSpace ℝ (W1p volume (halfDisc r) p) ''
      (W1p.halfDiscFlatTraceZeroSubmodule hp r : Set (W1p volume (halfDisc r) p))) := by
  rw [← (W1p.isClosed_halfDiscFlatTraceZeroSubmodule hp r).closure_eq,
    (W1p.halfDiscFlatTraceZeroSubmodule hp r).convex.toWeakSpace_closure ℝ]
  exact isClosed_closure

/-- **The pointwise reading of the zero-trace condition.** If `u ∈ W^{1,p}(halfDisc r)` agrees
almost everywhere with a function `f` continuous on the closed half-disc, then the trace of `u`
vanishes almost everywhere on the flat segment exactly when `f` vanishes at every point of the
flat segment. -/
theorem W1p.mem_halfDiscFlatTraceZeroSubmodule_iff_of_continuousOn (hp : p ≠ (∞ : ℝ≥0∞))
    (hr : 0 < r) {u : W1p volume (halfDisc r) p} {f : WithLp 2 (ℝ × ℝ) → ℝ}
    (hf : ContinuousOn f (closure (halfDisc r : Set (WithLp 2 (ℝ × ℝ)))))
    (hu : W1p.value u =ᵐ[volume.restrict (halfDisc r : Set (WithLp 2 (ℝ × ℝ)))] f) :
    u ∈ W1p.halfDiscFlatTraceZeroSubmodule hp r ↔ ∀ x ∈ halfDiscFlatSegment r, f x = 0 := by
  obtain ⟨L, hΩ⟩ := exists_isLipschitzDomainWith_halfDisc r
  have htr : W1p.frontierTrace hp hΩ (isBounded_halfDisc r) u
      =ᵐ[(μHE[1] : Measure (WithLp 2 (ℝ × ℝ))).restrict (halfDiscFlatSegment r)] f := by
    rw [Filter.EventuallyEq,
      ← ae_iff_of_measure_eq (restrict_frontier_restrict_halfDiscFlatSegment hr)]
    exact ae_restrict_of_ae
      (W1p.frontierTrace_ae_eq_of_continuousOn hp hΩ (isBounded_halfDisc r) hf hu)
  rw [W1p.mem_halfDiscFlatTraceZeroSubmodule_iff hp hr hΩ]
  constructor
  · intro h
    refine eqOn_halfDiscFlatSegment_of_ae_eq (g := 0) hr
      (hf.mono (halfDiscFlatSegment_subset_closure hr)) continuousOn_const ?_
    filter_upwards [htr, h] with x hx hx'
    rw [← hx, hx', Pi.zero_apply]
  · intro h
    filter_upwards [htr, ae_restrict_mem (measurableSet_halfDiscFlatSegment r)] with x hx hxS
    rw [hx, h x hxS]

/-- **The normal coordinate satisfies the boundary condition.** Every `u ∈ W^{1,p}(halfDisc r)`
represented by the normal coordinate `x ↦ x.fst` (the function `t = Im z`) lies in
`TauCeti.W1p.halfDiscFlatTraceZeroSubmodule`. -/
theorem W1p.mem_halfDiscFlatTraceZeroSubmodule_of_value_ae_eq_fst (hp : p ≠ (∞ : ℝ≥0∞))
    (hr : 0 < r) {u : W1p volume (halfDisc r) p}
    (hu : W1p.value u =ᵐ[volume.restrict (halfDisc r : Set (WithLp 2 (ℝ × ℝ)))]
      fun x => x.fst) :
    u ∈ W1p.halfDiscFlatTraceZeroSubmodule hp r :=
  (W1p.mem_halfDiscFlatTraceZeroSubmodule_iff_of_continuousOn hp hr
    (WithLp.prod_continuous_ofLp 2 ℝ ℝ).fst.continuousOn hu).2 fun _ hx =>
      (mem_halfDiscFlatSegment.1 hx).2

/-- **Check: the normal coordinate.** The normal coordinate `x ↦ x.fst` (the function `t = Im z`)
defines an element of `W^{1,p}(halfDisc r)` satisfying the boundary condition. -/
theorem W1p.exists_value_ae_eq_fst_mem_halfDiscFlatTraceZeroSubmodule (hp : p ≠ (∞ : ℝ≥0∞))
    (hr : 0 < r) :
    ∃ u : W1p volume (halfDisc r) p,
      W1p.value u =ᵐ[volume.restrict (halfDisc r : Set (WithLp 2 (ℝ × ℝ)))] (fun x => x.fst) ∧
        u ∈ W1p.halfDiscFlatTraceZeroSubmodule hp r := by
  have hfst : (fun x : WithLp 2 (ℝ × ℝ) => x.fst) = WithLp.fstL 2 ℝ ℝ ℝ := rfl
  have hgrad : MemLp (∇ fun x : WithLp 2 (ℝ × ℝ) => x.fst) p
      (volume.restrict (halfDisc r : Set (WithLp 2 (ℝ × ℝ)))) := by
    rw [hfst]
    have : (∇ ⇑(WithLp.fstL 2 ℝ ℝ ℝ)) = fun _ => (InnerProductSpace.toDual ℝ _).symm
        (WithLp.fstL 2 ℝ ℝ ℝ) := by
      ext1 x
      rw [_root_.gradient, (WithLp.fstL 2 ℝ ℝ ℝ).fderiv]
    rw [this]
    exact memLp_const _
  have hval : MemLp (fun x : WithLp 2 (ℝ × ℝ) => x.fst) p
      (volume.restrict (halfDisc r : Set (WithLp 2 (ℝ × ℝ)))) := by
    refine MemLp.of_bound (WithLp.prod_continuous_ofLp 2 ℝ ℝ).fst.aestronglyMeasurable r ?_
    refine (ae_restrict_iff' (halfDisc r).isOpen.measurableSet).2 (ae_of_all _ fun x hx => ?_)
    rw [SetLike.mem_coe, mem_halfDisc] at hx
    exact (WithLp.norm_fst_le (α := ℝ) x).trans hx.1.le
  obtain ⟨u, hu, -⟩ := W1p.exists_value_gradient_ae_eq_of_contDiffOn (mu := volume)
    (Omega := halfDisc r) (hfst ▸ (WithLp.fstL 2 ℝ ℝ ℝ).contDiff.contDiffOn) hval hgrad
  exact ⟨u, hu, W1p.mem_halfDiscFlatTraceZeroSubmodule_of_value_ae_eq_fst hp hr hu⟩

/-- **Check: a nonzero constant violates the boundary condition.** For `c ≠ 0` the constant
function `c` on the half-disc does not lie in `TauCeti.W1p.halfDiscFlatTraceZeroSubmodule`. -/
theorem W1p.const_notMem_halfDiscFlatTraceZeroSubmodule (hp : p ≠ (∞ : ℝ≥0∞)) (hr : 0 < r)
    {c : ℝ} (hc : c ≠ 0) :
    (W1p.const c : W1p volume (halfDisc r) p) ∉ W1p.halfDiscFlatTraceZeroSubmodule hp r := by
  have hu : W1p.value (W1p.const c : W1p volume (halfDisc r) p)
      =ᵐ[volume.restrict (halfDisc r : Set (WithLp 2 (ℝ × ℝ)))] fun _ => c := by
    rw [W1p.value_const]
    exact Lp.coeFn_const p _ c
  rw [W1p.mem_halfDiscFlatTraceZeroSubmodule_iff_of_continuousOn hp hr continuousOn_const hu]
  exact fun h => hc (h 0 (mem_halfDiscFlatSegment.2 ⟨by simpa using hr.le, rfl⟩))

end Trace

/-! ### The pointwise condition for `p > 2` -/

section Morrey

variable {p : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))] {r : ℝ}

/-- **For `p > 2` the trace condition is the pointwise condition.** Every
`u ∈ W^{1,p}(halfDisc r)` with `2 < p < ∞` agrees almost everywhere with a function `f` continuous
on the closed half-disc, and `u` has zero trace on the flat segment exactly when `f` vanishes at
every point of it. -/
theorem W1p.exists_continuousOn_mem_halfDiscFlatTraceZeroSubmodule_iff (hp : 2 < p)
    (hr : 0 < r) (u : W1p volume (halfDisc r) p) :
    ∃ f : WithLp 2 (ℝ × ℝ) → ℝ, ContinuousOn f (closure (halfDisc r : Set (WithLp 2 (ℝ × ℝ)))) ∧
      W1p.value u =ᵐ[volume.restrict (halfDisc r : Set (WithLp 2 (ℝ × ℝ)))] f ∧
      (u ∈ W1p.halfDiscFlatTraceZeroSubmodule ENNReal.coe_ne_top r ↔
        ∀ x ∈ halfDiscFlatSegment r, f x = 0) := by
  obtain ⟨L, hΩ⟩ := exists_isLipschitzDomainWith_halfDisc r
  have hdim : ((finrank ℝ (WithLp 2 (ℝ × ℝ)) : ℕ) : ℝ≥0) < p := by
    rw [(WithLp.linearEquiv 2 ℝ (ℝ × ℝ)).finrank_eq, finrank_prod, finrank_self]
    exact_mod_cast hp
  obtain ⟨f, hf, hu⟩ :=
    W1p.exists_continuousOn_closure_ae_eq_of_isLipschitzDomainWith hdim hΩ (isBounded_halfDisc r) u
  exact ⟨f, hf, hu, W1p.mem_halfDiscFlatTraceZeroSubmodule_iff_of_continuousOn _ hr hf hu⟩

end Morrey

end TauCeti

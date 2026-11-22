/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.LocallyConvex.WeakSpace
public import TauCeti.Analysis.Sobolev.LipschitzDomain.HalfDisc.SurfaceMeasure
public import TauCeti.Analysis.Sobolev.LipschitzDomain.Morrey
public import TauCeti.Analysis.Sobolev.W1p.Translation
import TauCeti.Analysis.Normed.Module.WeakSpace.Closure
import TauCeti.Geometry.Euclidean.Volume.Measure

/-!
# Flat traces on half-discs

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
(`TauCeti.euclideanHausdorffMeasure_restrict_halfDiscFlatSegment` in
`TauCeti.Analysis.Sobolev.LipschitzDomain.HalfDisc.SurfaceMeasure`), so a continuous function that
vanishes almost everywhere on the segment vanishes everywhere on it.

For `p = 2` the trace is genuinely needed: the function `log log (4 / |1 - z|)` of
`TauCeti.Analysis.Sobolev.W1p.LogLogTraceExample` lies in `W^{1,2}` of the disc but has no
continuous boundary value at `1`.

## Locality

If `|c| + ρ ≤ r`, translation by `(0, c)` maps the half-disc of radius `ρ` into the half-disc of
radius `r`, and its flat segment `[-ρ, ρ]` onto the subsegment `[c - ρ, c + ρ]` of `[-r, r]`.
The flat trace of the translated function `x ↦ u (x + (0, c))` is then the translate of the
flat trace of `u` (`TauCeti.W1p.halfDiscFlatTrace_translate_ae`). In particular the zero-trace
condition passes to every smaller and shifted half-disc, and it is local: a function has zero
trace on the flat segment as soon as every point of the open segment `(-r, r)` is the centre of
such a sub-half-disc on which the translated function has zero trace
(`TauCeti.W1p.mem_halfDiscFlatTraceZeroSubmodule_iff_forall_translate`). Totally real boundary
conditions on a relatively open subset of the closed upper half-plane can therefore be read off
on small half-discs around each real point.

## Main declarations

* `TauCeti.W1p.halfDiscFlatTrace`: the trace on the flat segment, a bounded linear map.
* `TauCeti.W1p.halfDiscFlatTrace_ae_eq`, `TauCeti.W1p.halfDiscFlatTrace_ae_eq_of_continuousOn`:
  it is the restriction of the frontier trace, and of a representative continuous up to the
  boundary.
* `TauCeti.W1p.halfDiscFlatTraceZeroSubmodule`: its kernel, the functions of zero trace on the
  flat segment (`TauCeti.W1p.mem_halfDiscFlatTraceZeroSubmodule_iff_halfDiscFlatTrace_ae_eq_zero`).
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

* `TauCeti.W1p.halfDiscFlatTrace_translate_ae`: the flat trace commutes with these translations;
  `TauCeti.W1p.halfDiscFlatTrace_restrictL_ae` is the centred case `c = 0`.
* `TauCeti.W1p.translate_mem_halfDiscFlatTraceZeroSubmodule_iff`: the translated function has
  zero trace exactly when the trace of `u` vanishes on the shifted subsegment.
* `TauCeti.W1p.translate_mem_halfDiscFlatTraceZeroSubmodule`,
  `TauCeti.W1p.restrictL_mem_halfDiscFlatTraceZeroSubmodule`: zero trace passes to smaller and
  shifted half-discs.
* `TauCeti.W1p.mem_halfDiscFlatTraceZeroSubmodule_of_forall_translate`,
  `TauCeti.W1p.mem_halfDiscFlatTraceZeroSubmodule_iff_forall_translate`: the local-to-global
  converse.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Appendix B.4
  (boundary conditions on the half-disc).
* L. C. Evans, *Partial Differential Equations*, 2nd ed., §5.5.
-/

public section

noncomputable section

open Bornology Filter MeasureTheory Metric Module Set TopologicalSpace
open scoped ENNReal NNReal Gradient

namespace TauCeti

/-! ### The trace condition on the flat segment -/

section Trace

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {r : ℝ}

/-- **The trace on the flat segment** of the half-disc, `W^{1,p}(halfDisc r) → Lᵖ(flat segment)`
for `p < ∞`: the boundary trace `TauCeti.W1p.frontierTrace`, for one choice of Lipschitz
constant, restricted to the flat segment. By `TauCeti.W1p.mem_halfDiscFlatTraceZeroSubmodule_iff`
its kernel does not depend on that choice. -/
def W1p.halfDiscFlatTrace (hp : p ≠ (∞ : ℝ≥0∞)) (r : ℝ) :
    W1p volume (halfDisc r) p →L[ℝ] Lp ℝ p
      (((μHE[finrank ℝ ℝ] : Measure (WithLp 2 (ℝ × ℝ))).restrict
        (frontier (halfDisc r : Set (WithLp 2 (ℝ × ℝ))))).restrict (halfDiscFlatSegment r)) :=
  (LpToLpRestrictCLM (WithLp 2 (ℝ × ℝ)) ℝ ℝ _ p (halfDiscFlatSegment r)).comp
    (W1p.frontierTrace hp (exists_isLipschitzDomainWith_halfDisc r).choose_spec
      (isBounded_halfDisc r))

/-- **Functions of zero trace on the flat segment.** The subspace of `W^{1,p}(halfDisc r)`,
`p < ∞`, of functions whose boundary trace vanishes almost everywhere on the flat segment: the
kernel of `TauCeti.W1p.halfDiscFlatTrace`. Imposed on the imaginary part of each component of a
`ℂⁿ`-valued map, it is the totally real boundary condition `ξ ∈ ℝⁿ` on the flat segment. -/
def W1p.halfDiscFlatTraceZeroSubmodule (hp : p ≠ (∞ : ℝ≥0∞)) (r : ℝ) :
    Submodule ℝ (W1p volume (halfDisc r) p) :=
  LinearMap.ker (W1p.halfDiscFlatTrace hp r).toLinearMap

/-- **The flat trace is the restricted frontier trace.** For any Lipschitz constant of the
half-disc, `TauCeti.W1p.halfDiscFlatTrace` agrees almost everywhere on the flat segment, for
surface measure, with the boundary trace `TauCeti.W1p.frontierTrace`. -/
theorem W1p.halfDiscFlatTrace_ae_eq (hp : p ≠ (∞ : ℝ≥0∞)) {L : ℝ≥0}
    (hΩ : (halfDisc r : Set (WithLp 2 (ℝ × ℝ))).IsLipschitzDomainWith L)
    (u : W1p volume (halfDisc r) p) :
    W1p.halfDiscFlatTrace hp r u =ᵐ[(μHE[1] : Measure (WithLp 2 (ℝ × ℝ))).restrict
      (halfDiscFlatSegment r)] W1p.frontierTrace hp hΩ (isBounded_halfDisc r) u := by
  rw [← congrArg ae (restrict_frontier_restrict_halfDiscFlatSegment r), W1p.halfDiscFlatTrace,
    ContinuousLinearMap.comp_apply,
    W1p.frontierTrace_eq_of_isLipschitzDomainWith hp _ hΩ (isBounded_halfDisc r)]
  exact LpToLpRestrictCLM_coeFn ℝ (halfDiscFlatSegment r) _

/-- **The flat trace of a function continuous up to the boundary is its restriction.** If
`u ∈ W^{1,p}(halfDisc r)` agrees almost everywhere with a function `f` continuous on the closed
half-disc, then `TauCeti.W1p.halfDiscFlatTrace` sends `u` to `f` almost everywhere on the flat
segment for surface measure. -/
theorem W1p.halfDiscFlatTrace_ae_eq_of_continuousOn (hp : p ≠ (∞ : ℝ≥0∞))
    {u : W1p volume (halfDisc r) p} {f : WithLp 2 (ℝ × ℝ) → ℝ}
    (hf : ContinuousOn f (closure (halfDisc r : Set (WithLp 2 (ℝ × ℝ)))))
    (hu : W1p.value u =ᵐ[volume.restrict (halfDisc r : Set (WithLp 2 (ℝ × ℝ)))] f) :
    W1p.halfDiscFlatTrace hp r u =ᵐ[(μHE[1] : Measure (WithLp 2 (ℝ × ℝ))).restrict
      (halfDiscFlatSegment r)] f := by
  obtain ⟨L, hΩ⟩ := exists_isLipschitzDomainWith_halfDisc r
  refine (W1p.halfDiscFlatTrace_ae_eq hp hΩ u).trans ?_
  rw [Filter.EventuallyEq, ← congrArg ae (restrict_frontier_restrict_halfDiscFlatSegment r)]
  exact ae_restrict_of_ae
    (W1p.frontierTrace_ae_eq_of_continuousOn hp hΩ (isBounded_halfDisc r) hf hu)

/-- A function lies in `TauCeti.W1p.halfDiscFlatTraceZeroSubmodule` exactly when its flat trace
`TauCeti.W1p.halfDiscFlatTrace` is zero. -/
@[simp]
theorem W1p.mem_halfDiscFlatTraceZeroSubmodule_iff_halfDiscFlatTrace_eq_zero
    (hp : p ≠ (∞ : ℝ≥0∞)) {u : W1p volume (halfDisc r) p} :
    u ∈ W1p.halfDiscFlatTraceZeroSubmodule hp r ↔ W1p.halfDiscFlatTrace hp r u = 0 :=
  LinearMap.mem_ker

/-- Membership in the flat zero-trace subspace is almost-everywhere vanishing of the flat
trace for normalized one-dimensional Hausdorff measure on the flat segment, for every real
radius. -/
theorem W1p.mem_halfDiscFlatTraceZeroSubmodule_iff_halfDiscFlatTrace_ae_eq_zero
    (hp : p ≠ (∞ : ℝ≥0∞)) {u : W1p volume (halfDisc r) p} :
    u ∈ W1p.halfDiscFlatTraceZeroSubmodule hp r ↔
      ∀ᵐ x ∂(μHE[1] : Measure (WithLp 2 (ℝ × ℝ))).restrict (halfDiscFlatSegment r),
        W1p.halfDiscFlatTrace hp r u x = 0 := by
  rw [W1p.mem_halfDiscFlatTraceZeroSubmodule_iff_halfDiscFlatTrace_eq_zero,
    Lp.eq_zero_iff_ae_eq_zero, Filter.EventuallyEq,
    congrArg ae (restrict_frontier_restrict_halfDiscFlatSegment r)]
  simp only [Pi.zero_apply]

/-- A function lies in `TauCeti.W1p.halfDiscFlatTraceZeroSubmodule` exactly when its trace, for
any Lipschitz constant of the half-disc, vanishes almost everywhere on the flat segment for
surface measure. -/
theorem W1p.mem_halfDiscFlatTraceZeroSubmodule_iff (hp : p ≠ (∞ : ℝ≥0∞))
    {L : ℝ≥0} (hΩ : (halfDisc r : Set (WithLp 2 (ℝ × ℝ))).IsLipschitzDomainWith L)
    {u : W1p volume (halfDisc r) p} :
    u ∈ W1p.halfDiscFlatTraceZeroSubmodule hp r ↔
      ∀ᵐ x ∂(μHE[1] : Measure (WithLp 2 (ℝ × ℝ))).restrict (halfDiscFlatSegment r),
        W1p.frontierTrace hp hΩ (isBounded_halfDisc r) u x = 0 := by
  rw [W1p.mem_halfDiscFlatTraceZeroSubmodule_iff_halfDiscFlatTrace_ae_eq_zero]
  have htr := W1p.halfDiscFlatTrace_ae_eq hp hΩ u
  constructor
  · intro h
    filter_upwards [htr, h] with x hx hx'
    rw [← hx, hx']
  · intro h
    filter_upwards [htr, h] with x hx hx'
    rw [hx, hx']

/-- **The zero-trace condition is closed** in `W^{1,p}(halfDisc r)`. -/
theorem W1p.isClosed_halfDiscFlatTraceZeroSubmodule (hp : p ≠ (∞ : ℝ≥0∞)) (r : ℝ) :
    IsClosed (W1p.halfDiscFlatTraceZeroSubmodule hp r : Set (W1p volume (halfDisc r) p)) :=
  (W1p.halfDiscFlatTrace hp r).isClosed_ker

/-- **The zero-trace condition is weakly closed**: its image in the weak topology of
`W^{1,p}(halfDisc r)` is closed, since it is a closed convex set. -/
theorem W1p.isClosed_toWeakSpace_halfDiscFlatTraceZeroSubmodule (hp : p ≠ (∞ : ℝ≥0∞)) (r : ℝ) :
    IsClosed (toWeakSpace ℝ (W1p volume (halfDisc r) p) ''
      (W1p.halfDiscFlatTraceZeroSubmodule hp r : Set (W1p volume (halfDisc r) p))) :=
  (W1p.halfDiscFlatTraceZeroSubmodule hp r).isClosed_toWeakSpace
    (W1p.isClosed_halfDiscFlatTraceZeroSubmodule hp r)

/-- **The pointwise reading of the zero-trace condition.** If `u ∈ W^{1,p}(halfDisc r)` agrees
almost everywhere with a function `f` continuous on the closed half-disc, then the trace of `u`
vanishes almost everywhere on the flat segment exactly when `f` vanishes at every point of the
flat segment. -/
theorem W1p.mem_halfDiscFlatTraceZeroSubmodule_iff_of_continuousOn (hp : p ≠ (∞ : ℝ≥0∞))
    (hr : 0 < r) {u : W1p volume (halfDisc r) p} {f : WithLp 2 (ℝ × ℝ) → ℝ}
    (hf : ContinuousOn f (closure (halfDisc r : Set (WithLp 2 (ℝ × ℝ)))))
    (hu : W1p.value u =ᵐ[volume.restrict (halfDisc r : Set (WithLp 2 (ℝ × ℝ)))] f) :
    u ∈ W1p.halfDiscFlatTraceZeroSubmodule hp r ↔ ∀ x ∈ halfDiscFlatSegment r, f x = 0 := by
  have htr := W1p.halfDiscFlatTrace_ae_eq_of_continuousOn hp hf hu
  rw [W1p.mem_halfDiscFlatTraceZeroSubmodule_iff_halfDiscFlatTrace_ae_eq_zero]
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
  obtain ⟨u, hu, -⟩ := W1p.exists_value_gradient_ae_eq_continuousLinearMap (mu := volume)
    (p := p) (isBounded_halfDisc r) (WithLp.fstL 2 ℝ ℝ ℝ)
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

/-! ## Locality of the flat trace -/

namespace TauCeti

variable {r ρ c : ℝ}

/-! ### Translating half-discs along the flat segment -/

/-- Under `|c| + ρ ≤ r`, translation by `(0, c)` carries surface measure on the flat segment of
radius `ρ` to surface measure on its image in the flat segment of radius `r`, for the measures of
the codomains of `TauCeti.W1p.halfDiscFlatTrace`. -/
private theorem measurePreserving_add_halfDiscFlatSegment (hc : |c| + ρ ≤ r) :
    MeasurePreserving (· + WithLp.toLp 2 ((0 : ℝ), c))
      (((μHE[finrank ℝ ℝ] : Measure (WithLp 2 (ℝ × ℝ))).restrict
        (frontier (halfDisc ρ : Set (WithLp 2 (ℝ × ℝ))))).restrict (halfDiscFlatSegment ρ))
      ((((μHE[finrank ℝ ℝ] : Measure (WithLp 2 (ℝ × ℝ))).restrict
        (frontier (halfDisc r : Set (WithLp 2 (ℝ × ℝ))))).restrict (halfDiscFlatSegment r)).restrict
          ((· + WithLp.toLp 2 ((0 : ℝ), c)) '' halfDiscFlatSegment ρ)) := by
  refine ⟨(continuous_id.add continuous_const).measurable, ?_⟩
  have hS : MeasurableSet ((· + WithLp.toLp 2 ((0 : ℝ), c)) '' halfDiscFlatSegment ρ) :=
    ((Homeomorph.addRight _).isClosedMap _ (isClosed_halfDiscFlatSegment ρ)).measurableSet
  rw [restrict_frontier_restrict_halfDiscFlatSegment,
    restrict_frontier_restrict_halfDiscFlatSegment, Measure.restrict_restrict hS,
    inter_eq_left.2 (image_subset_iff.2 (mapsTo_add_halfDiscFlatSegment hc)),
    (isometry_add_right (WithLp.toLp 2 ((0 : ℝ), c))).map_euclideanHausdorffMeasure_restrict]

/-- Under `|c| + ρ ≤ r`, sets of zero surface measure on the flat segment of radius `r` pull back
to sets of zero surface measure on the flat segment of radius `ρ` under translation by
`(0, c)`. -/
private theorem quasiMeasurePreserving_add_halfDiscFlatSegment (hc : |c| + ρ ≤ r) :
    QuasiMeasurePreserving (· + WithLp.toLp 2 ((0 : ℝ), c))
      ((μHE[1] : Measure (WithLp 2 (ℝ × ℝ))).restrict (halfDiscFlatSegment ρ))
      ((μHE[1] : Measure (WithLp 2 (ℝ × ℝ))).restrict (halfDiscFlatSegment r)) := by
  have h := (measurePreserving_add_halfDiscFlatSegment hc).quasiMeasurePreserving
  rw [restrict_frontier_restrict_halfDiscFlatSegment,
    restrict_frontier_restrict_halfDiscFlatSegment] at h
  exact h.mono_right Measure.restrict_le_self.absolutelyContinuous

/-! ### The flat trace of a translate -/

section Trace

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **The flat trace commutes with translation along the flat segment.** If `|c| + ρ ≤ r`, the
flat trace of the translate `x ↦ u (x + (0, c))` on `halfDisc ρ` is, almost everywhere on the flat
segment of radius `ρ`, the translate of the flat trace of `u` on `halfDisc r`. -/
theorem W1p.halfDiscFlatTrace_translate_ae (hp : p ≠ (∞ : ℝ≥0∞)) (hc : |c| + ρ ≤ r)
    (u : W1p volume (halfDisc r) p) :
    W1p.halfDiscFlatTrace hp ρ (W1p.translate (mapsTo_add_halfDisc hc) u) =ᵐ[
      (μHE[1] : Measure (WithLp 2 (ℝ × ℝ))).restrict (halfDiscFlatSegment ρ)]
      fun w => W1p.halfDiscFlatTrace hp r u (w + WithLp.toLp 2 ((0 : ℝ), c)) := by
  -- Both sides are bounded linear in `u` and agree on restrictions of test functions,
  -- which are dense in `W^{1,p}(halfDisc r)`.
  set h : WithLp 2 (ℝ × ℝ) := WithLp.toLp 2 ((0 : ℝ), c)
  set S := (· + h) '' halfDiscFlatSegment ρ
  have hτ := measurePreserving_add_halfDiscFlatSegment hc
  -- The right-hand side as a bounded linear operator in `u`.
  let B : W1p volume (halfDisc r) p →L[ℝ] Lp ℝ p
      (((μHE[finrank ℝ ℝ] : Measure (WithLp 2 (ℝ × ℝ))).restrict
        (frontier (halfDisc ρ : Set (WithLp 2 (ℝ × ℝ))))).restrict (halfDiscFlatSegment ρ)) :=
    (Lp.compMeasurePreservingₗᵢ ℝ (· + h) hτ).toContinuousLinearMap.comp
      ((LpToLpRestrictCLM (WithLp 2 (ℝ × ℝ)) ℝ ℝ _ p S).comp (W1p.halfDiscFlatTrace hp r))
  have hB (v : W1p volume (halfDisc r) p) :
      B v =ᵐ[(μHE[1] : Measure (WithLp 2 (ℝ × ℝ))).restrict (halfDiscFlatSegment ρ)]
        fun w => W1p.halfDiscFlatTrace hp r v (w + h) := by
    rw [← congrArg ae (restrict_frontier_restrict_halfDiscFlatSegment ρ)]
    exact (Lp.coeFn_compMeasurePreserving _ hτ).trans
      (hτ.quasiMeasurePreserving.ae_eq_comp (LpToLpRestrictCLM_coeFn ℝ S _))
  obtain ⟨L, hΩ⟩ := exists_isLipschitzDomainWith_halfDisc r
  have hAB : (W1p.halfDiscFlatTrace hp ρ).comp (W1p.translateL (mapsTo_add_halfDisc hc)) = B := by
    refine DFunLike.coe_injective <|
      (W1p.denseRange_restrictL_ofTestFunctionₗ_top hp hΩ (isBounded_halfDisc r)).equalizer
        (ContinuousLinearMap.continuous _) B.continuous (funext fun φ => ?_)
    simp only [Function.comp_apply, ContinuousLinearMap.comp_apply, W1p.translateL_apply]
    refine Lp.ext ?_
    have hv := W1p.value_restrictL_ofTestFunctionₗ_ae (mu := volume) (p := p)
      (le_top : halfDisc r ≤ ⊤) φ
    -- The value of the translate is the translated test function.
    have htr : W1p.value (W1p.translate (mapsTo_add_halfDisc hc)
          (W1p.restrictL (le_top : halfDisc r ≤ ⊤) (W1p.ofTestFunctionₗ volume ⊤ p φ)))
        =ᵐ[volume.restrict (halfDisc ρ : Set (WithLp 2 (ℝ × ℝ)))] fun x => φ (x + h) := by
      refine (W1p.value_translate_ae _ _).trans ?_
      have hmp := (measurePreserving_add_right volume h).quasiMeasurePreserving.ae
        ((ae_restrict_iff' (halfDisc r).isOpen.measurableSet).1 hv)
      filter_upwards [ae_restrict_of_ae hmp, ae_restrict_mem (halfDisc ρ).isOpen.measurableSet]
        with x hx hxρ
      exact hx (mapsTo_add_halfDisc hc hxρ)
    have hA := W1p.halfDiscFlatTrace_ae_eq_of_continuousOn hp
      (φ.continuous.comp (continuous_id.add continuous_const)).continuousOn htr
    have hφ := W1p.halfDiscFlatTrace_ae_eq_of_continuousOn hp φ.continuous.continuousOn hv
    have key := hA.trans <| Filter.EventuallyEq.trans
      ((quasiMeasurePreserving_add_halfDiscFlatSegment hc).ae_eq_comp hφ).symm (hB _).symm
    rwa [← congrArg ae (restrict_frontier_restrict_halfDiscFlatSegment ρ)] at key
  have hu := congrArg (· u) hAB
  simp only [ContinuousLinearMap.comp_apply, W1p.translateL_apply] at hu
  rw [hu]
  exact hB u

/-- **The flat trace of a restriction.** For `ρ ≤ r`, the flat trace of the restriction of `u` to
`halfDisc ρ` is the flat trace of `u`, almost everywhere on the flat segment of radius `ρ`. -/
theorem W1p.halfDiscFlatTrace_restrictL_ae (hp : p ≠ (∞ : ℝ≥0∞)) (hρr : ρ ≤ r)
    (u : W1p volume (halfDisc r) p) :
    W1p.halfDiscFlatTrace hp ρ (W1p.restrictL (halfDisc_mono hρr) u) =ᵐ[
      (μHE[1] : Measure (WithLp 2 (ℝ × ℝ))).restrict (halfDiscFlatSegment ρ)]
      W1p.halfDiscFlatTrace hp r u := by
  have hc : |(0 : ℝ)| + ρ ≤ r := by simpa using hρr
  have h0 : WithLp.toLp 2 ((0 : ℝ), (0 : ℝ)) = 0 :=
    WithLp.toLp_zero 2 (V := ℝ × ℝ)
  have heq : W1p.restrictL (halfDisc_mono hρr) u = W1p.translate (mapsTo_add_halfDisc hc) u := by
    refine W1p.ext_value (Lp.ext ((W1p.value_restrictL_ae _ u).trans ?_))
    refine Filter.EventuallyEq.trans ?_ (W1p.value_translate_ae _ u).symm
    simp only [h0, add_zero]
    rfl
  rw [heq]
  simpa only [h0, add_zero] using W1p.halfDiscFlatTrace_translate_ae hp hc u

/-- Almost everywhere on the flat segment, for surface measure, is almost everywhere on
`[-r, r]` along `t ↦ (0, t)`. -/
private theorem ae_restrict_halfDiscFlatSegment_iff {P : WithLp 2 (ℝ × ℝ) → Prop} :
    (∀ᵐ x ∂(μHE[1] : Measure (WithLp 2 (ℝ × ℝ))).restrict (halfDiscFlatSegment r), P x) ↔
      ∀ᵐ t ∂volume.restrict (Icc (-r) r), P (WithLp.toLp 2 ((0 : ℝ), t)) := by
  rw [euclideanHausdorffMeasure_restrict_halfDiscFlatSegment,
    (WithLp.isometry_toLp_prodMk_left 2 (β := ℝ) (0 : ℝ)).isClosedEmbedding.measurableEmbedding
      |>.ae_map_iff]

/-- **Zero trace on a shifted half-disc.** If `|c| + ρ ≤ r`, the translate `x ↦ u (x + (0, c))`
has zero trace on the flat segment of radius `ρ` exactly when `t ↦ trace(u) (0, t)` vanishes
almost everywhere for Lebesgue measure on the interval `[c - ρ, c + ρ]`. -/
theorem W1p.translate_mem_halfDiscFlatTraceZeroSubmodule_iff (hp : p ≠ (∞ : ℝ≥0∞))
    (hc : |c| + ρ ≤ r) {u : W1p volume (halfDisc r) p} :
    W1p.translate (mapsTo_add_halfDisc hc) u ∈ W1p.halfDiscFlatTraceZeroSubmodule hp ρ ↔
      ∀ᵐ t ∂volume.restrict (Icc (c - ρ) (c + ρ)),
        W1p.halfDiscFlatTrace hp r u (WithLp.toLp 2 ((0 : ℝ), t)) = 0 := by
  rw [W1p.mem_halfDiscFlatTraceZeroSubmodule_iff_halfDiscFlatTrace_ae_eq_zero,
    ae_restrict_halfDiscFlatSegment_iff]
  have hinterval : (· + c) '' Icc (-ρ) ρ = Icc (c - ρ) (c + ρ) := by
    rw [image_add_const_Icc, neg_add_eq_sub, add_comm ρ c]
  rw [← hinterval, ← ((measurePreserving_add_right volume c).restrict_image_emb
    (measurableEmbedding_addRight c) (Icc (-ρ) ρ)).map_eq,
    (measurableEmbedding_addRight c).ae_map_iff]
  have htr := W1p.halfDiscFlatTrace_translate_ae hp hc u
  simp only [Filter.EventuallyEq] at htr
  rw [ae_restrict_halfDiscFlatSegment_iff] at htr
  apply Filter.eventually_congr
  filter_upwards [htr] with t ht
  rw [ht]
  simp [← WithLp.toLp_add]

/-- **Zero trace passes to shifted half-discs.** If `u` has zero trace on the flat segment of
`halfDisc r` and `|c| + ρ ≤ r`, its translate `x ↦ u (x + (0, c))` has zero trace on the flat
segment of `halfDisc ρ`. -/
theorem W1p.translate_mem_halfDiscFlatTraceZeroSubmodule (hp : p ≠ (∞ : ℝ≥0∞))
    (hc : |c| + ρ ≤ r) {u : W1p volume (halfDisc r) p}
    (hu : u ∈ W1p.halfDiscFlatTraceZeroSubmodule hp r) :
    W1p.translate (mapsTo_add_halfDisc hc) u ∈ W1p.halfDiscFlatTraceZeroSubmodule hp ρ := by
  rw [W1p.mem_halfDiscFlatTraceZeroSubmodule_iff_halfDiscFlatTrace_ae_eq_zero]
  rw [W1p.mem_halfDiscFlatTraceZeroSubmodule_iff_halfDiscFlatTrace_ae_eq_zero] at hu
  filter_upwards [W1p.halfDiscFlatTrace_translate_ae hp hc u,
    (quasiMeasurePreserving_add_halfDiscFlatSegment hc).ae hu] with x hx hx'
  rw [hx, hx']

/-- **Zero trace passes to smaller half-discs.** If `u` has zero trace on the flat segment of
`halfDisc r` and `ρ ≤ r`, its restriction to `halfDisc ρ` has zero trace on the flat segment of
`halfDisc ρ`. -/
theorem W1p.restrictL_mem_halfDiscFlatTraceZeroSubmodule (hp : p ≠ (∞ : ℝ≥0∞)) (hρr : ρ ≤ r)
    {u : W1p volume (halfDisc r) p} (hu : u ∈ W1p.halfDiscFlatTraceZeroSubmodule hp r) :
    W1p.restrictL (halfDisc_mono hρr) u ∈ W1p.halfDiscFlatTraceZeroSubmodule hp ρ := by
  rw [W1p.mem_halfDiscFlatTraceZeroSubmodule_iff_halfDiscFlatTrace_ae_eq_zero]
  rw [W1p.mem_halfDiscFlatTraceZeroSubmodule_iff_halfDiscFlatTrace_ae_eq_zero] at hu
  filter_upwards [W1p.halfDiscFlatTrace_restrictL_ae hp hρr u,
    ae_restrict_of_ae_restrict_of_subset (halfDiscFlatSegment_mono hρr) hu] with x hx hx'
  rw [hx, hx']

/-! ### From small half-discs to the whole flat segment -/

/-- **The zero-trace condition is local.** If every point of the open flat segment `(-r, r)`
lies in a shifted subsegment `(c - ρ, c + ρ)`, with `|c| + ρ ≤ r`, on whose half-disc the
translate `x ↦ u (x + (0, c))` has zero trace, then `u` has zero trace on the flat segment of
`halfDisc r`. -/
theorem W1p.mem_halfDiscFlatTraceZeroSubmodule_of_forall_translate (hp : p ≠ (∞ : ℝ≥0∞))
    {u : W1p volume (halfDisc r) p}
    (H : ∀ t ∈ Ioo (-r) r, ∃ c ρ : ℝ, ∃ hc : |c| + ρ ≤ r, |t - c| < ρ ∧
      W1p.translate (mapsTo_add_halfDisc hc) u ∈ W1p.halfDiscFlatTraceZeroSubmodule hp ρ) :
    u ∈ W1p.halfDiscFlatTraceZeroSubmodule hp r := by
  rw [W1p.mem_halfDiscFlatTraceZeroSubmodule_iff_halfDiscFlatTrace_ae_eq_zero,
    ae_restrict_halfDiscFlatSegment_iff, ← Measure.restrict_congr_set Ioo_ae_eq_Icc]
  choose! c ρ hc hct hmem using H
  -- On each shifted subsegment the trace vanishes.
  have hpiece (t : Ioo (-r) r) : ∀ᵐ s ∂volume.restrict (Ioo (c t - ρ t) (c t + ρ t)),
      W1p.halfDiscFlatTrace hp r u (WithLp.toLp 2 ((0 : ℝ), s)) = 0 := by
    refine ae_restrict_of_ae_restrict_of_subset Ioo_subset_Icc_self ?_
    exact (W1p.translate_mem_halfDiscFlatTraceZeroSubmodule_iff hp (hc t t.property)).1
        (hmem t t.property)
  -- Countably many of the subsegments cover `(-r, r)`.
  obtain ⟨T, hT, hTU⟩ := isOpen_iUnion_countable
    (fun t : Ioo (-r) r => Ioo (c t - ρ t) (c t + ρ t)) fun _ => isOpen_Ioo
  refine ae_restrict_of_ae_restrict_of_subset (t := ⋃ t ∈ T, Ioo (c t - ρ t) (c t + ρ t))
    (fun t ht => ?_) ((ae_restrict_biUnion_iff _ hT _).2 fun t _ => hpiece t)
  rw [hTU, mem_iUnion]
  have := abs_sub_lt_iff.1 (hct t ht)
  exact ⟨⟨t, ht⟩, by constructor <;> linarith⟩

/-- **Zero trace on the flat segment is a local condition.** A function on `halfDisc r` has zero
trace on its flat segment exactly when every point of the open flat segment `(-r, r)` lies in a
shifted subsegment `(c - ρ, c + ρ)`, with `|c| + ρ ≤ r`, on whose half-disc the translate
`x ↦ u (x + (0, c))` has zero trace. -/
theorem W1p.mem_halfDiscFlatTraceZeroSubmodule_iff_forall_translate (hp : p ≠ (∞ : ℝ≥0∞))
    {u : W1p volume (halfDisc r) p} :
    u ∈ W1p.halfDiscFlatTraceZeroSubmodule hp r ↔
      ∀ t ∈ Ioo (-r) r, ∃ c ρ : ℝ, ∃ hc : |c| + ρ ≤ r, |t - c| < ρ ∧
        W1p.translate (mapsTo_add_halfDisc hc) u ∈ W1p.halfDiscFlatTraceZeroSubmodule hp ρ := by
  refine ⟨fun hu t ht => ?_, W1p.mem_halfDiscFlatTraceZeroSubmodule_of_forall_translate hp⟩
  have hc : |(0 : ℝ)| + r ≤ r := by simp
  exact ⟨0, r, hc, by simpa [abs_lt] using ht,
    W1p.translate_mem_halfDiscFlatTraceZeroSubmodule hp hc hu⟩

end Trace

end TauCeti

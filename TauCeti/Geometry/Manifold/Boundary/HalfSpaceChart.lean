/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Real
public import TauCeti.Geometry.Manifold.ExtChartAt
public import TauCeti.Topology.OpenPartialHomeomorph.Constructions
import TauCeti.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import TauCeti.Geometry.Manifold.MFDeriv.IsInvertible

/-!
# Half-space charts cut out by a sign condition

Let `e` be a chart of a space `M` with values in `ℝⁿ⁺¹`, and let `s` be a subset of `M` such that,
on the source of `e`, a point lies in `s` exactly when its zeroth coordinate is nonnegative. Then
`e` restricts to a chart `OpenPartialHomeomorph.halfSpaceChart` of `s`, modelled on the half-space
`EuclideanHalfSpace (n + 1)`. The transition maps between such charts are the transition maps of
the ambient charts, restricted to the half-space
(`OpenPartialHomeomorph.contDiffOn_halfSpaceChart_symm_trans`), so smooth ambient transitions give
a smooth atlas on `s`. This is how regular domains, such as the sublevels of a function at a
regular value, become manifolds with boundary.

The ambient `ℝⁿ⁺¹`-valued charts typically come from charts of a manifold with a boundaryless
model, read in the model vector space and moved by a homeomorphism
(`OpenPartialHomeomorph.extendTrans`, whose smooth transition maps are
`OpenPartialHomeomorph.contDiffOn_extendTrans_comp_symm`). Such charts, taken from the maximal
atlas and moved by `C^m` homeomorphisms with `C^m` inverses, are recorded by
`OpenPartialHomeomorph.IsExtendTransChart`. A charted space on `s` all of whose charts are
half-space restrictions of them is a `C^m` manifold with boundary
(`TauCeti.isManifold_of_forall_mem_atlas_halfSpaceChart`).

## Main declarations

* `OpenPartialHomeomorph.halfSpaceChart`, with its source, target, apply and inverse laws, and
  `OpenPartialHomeomorph.contDiffOn_halfSpaceChart_symm_trans`.
* `TauCeti.isManifold_of_forall_mem_atlas_halfSpaceChart`: an atlas of half-space
  restrictions of smoothly moved charts from the maximal atlas makes `s` a manifold with boundary.
* `TauCeti.contMDiff_subtypeVal_of_forall_mem_atlas_halfSpaceChart` and
  `TauCeti.isInvertible_mfderiv_subtypeVal_of_forall_mem_atlas_halfSpaceChart`: for such an atlas
  the inclusion `s → M` is smooth, with invertible derivative also at the boundary points of `s`.
  This is what transports orientations of `M` to `s`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, proof of Proposition 5.47 (charts of regular domains cut out by a defining
  function).
-/

public section

open Function Set
open scoped ContDiff Manifold

namespace OpenPartialHomeomorph

section HalfSpaceChart

variable {M : Type*} [TopologicalSpace M] {n : ℕ}
  {e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (n + 1)))} {s : Set M}

/-- Points of the target of `e` in the half-space come from `s`. -/
private theorem symm_mem_of_halfSpace (he : ∀ w ∈ e.source, w ∈ s ↔ 0 ≤ e w 0)
    {z : EuclideanHalfSpace (n + 1)} (hz : (𝓡∂ (n + 1)) z ∈ e.target) :
    e.symm ((𝓡∂ (n + 1)) z) ∈ s :=
  (he _ (e.map_target hz)).2 (by rw [e.right_inv hz]; exact z.2)

/-- Points of `s` are read by `e` in the half-space. -/
private theorem apply_symm_apply_halfSpace (he : ∀ w ∈ e.source, w ∈ s ↔ 0 ≤ e w 0) {w : M}
    (hw : w ∈ e.source) (hws : w ∈ s) :
    (𝓡∂ (n + 1)) ((𝓡∂ (n + 1)).symm (e w)) = e w :=
  (𝓡∂ (n + 1)).right_inv <| by
    rw [range_modelWithCornersEuclideanHalfSpace]; exact (he w hw).1 hws

private theorem leftInvOn_halfSpace_symm (t : Set (EuclideanSpace ℝ (Fin (n + 1)))) :
    LeftInvOn (𝓡∂ (n + 1)).symm (𝓡∂ (n + 1)) ((𝓡∂ (n + 1)) ⁻¹' t) :=
  fun z _ ↦ (𝓡∂ (n + 1)).left_inv z

variable (e) in
/-- An `ℝⁿ⁺¹`-valued chart `e` restricts to a half-space chart of a set `s` when, on the source of
`e`, a point lies in `s` exactly when its zeroth coordinate is nonnegative. The base point `x` only
witnesses that `s` is nonempty. -/
noncomputable def halfSpaceChart (he : ∀ w ∈ e.source, w ∈ s ↔ 0 ≤ e w 0) (x : s) :
    OpenPartialHomeomorph s (EuclideanHalfSpace (n + 1)) :=
  e.subtypeCoord s ⟨x⟩ (𝓡∂ (n + 1)) (𝓡∂ (n + 1)).symm (symm_mem_of_halfSpace he)
    (apply_symm_apply_halfSpace he) (leftInvOn_halfSpace_symm _) (𝓡∂ (n + 1)).continuous
    (𝓡∂ (n + 1)).continuous_symm.continuousOn

variable (he : ∀ w ∈ e.source, w ∈ s ↔ 0 ≤ e w 0)

/-- The source of the half-space chart is the part of `s` in the source of `e`. -/
@[simp]
theorem halfSpaceChart_source (x : s) :
    (e.halfSpaceChart he x).source = Subtype.val ⁻¹' e.source := by
  unfold halfSpaceChart
  exact OpenPartialHomeomorph.subtypeCoord_source ..

/-- The target of the half-space chart is the part of the half-space in the target of `e`. -/
@[simp]
theorem halfSpaceChart_target (x : s) :
    (e.halfSpaceChart he x).target = (𝓡∂ (n + 1)) ⁻¹' e.target := by
  unfold halfSpaceChart
  exact OpenPartialHomeomorph.subtypeCoord_target ..

/-- On its source, the half-space chart reads a point through `e`. -/
theorem coe_halfSpaceChart_apply (x : s) {w : s} (hw : (w : M) ∈ e.source) :
    (e.halfSpaceChart he x w).1 = e w := by
  unfold halfSpaceChart
  rw [OpenPartialHomeomorph.subtypeCoord_apply]
  exact apply_symm_apply_halfSpace he hw w.2

/-- On its target, the inverse half-space chart is the inverse of `e`. -/
theorem coe_halfSpaceChart_symm_apply (x : s) {z : EuclideanHalfSpace (n + 1)}
    (hz : z.1 ∈ e.target) : ((e.halfSpaceChart he x).symm z : M) = e.symm z.1 := by
  unfold halfSpaceChart
  exact OpenPartialHomeomorph.coe_subtypeCoord_symm_apply _ _ _ _ _ (symm_mem_of_halfSpace he)
    (apply_symm_apply_halfSpace he) _ _ _ hz

/-- The transition maps between half-space charts are those of the ambient charts, restricted to
the half-space. In particular they are `C^m` when the ambient transition maps are. -/
theorem contDiffOn_halfSpaceChart_symm_trans {m : ℕ∞ω}
    {e₁ e₂ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (n + 1)))}
    (he₁ : ∀ w ∈ e₁.source, w ∈ s ↔ 0 ≤ e₁ w 0) (he₂ : ∀ w ∈ e₂.source, w ∈ s ↔ 0 ≤ e₂ w 0)
    (x₁ x₂ : s) (h : ContDiffOn ℝ m (e₂ ∘ e₁.symm) (e₁.symm ≫ₕ e₂).source) :
    ContDiffOn ℝ m ((𝓡∂ (n + 1)) ∘ (e₁.halfSpaceChart he₁ x₁).symm ≫ₕ
        e₂.halfSpaceChart he₂ x₂ ∘ (𝓡∂ (n + 1)).symm)
      ((𝓡∂ (n + 1)).symm ⁻¹' ((e₁.halfSpaceChart he₁ x₁).symm ≫ₕ
        e₂.halfSpaceChart he₂ x₂).source ∩ range (𝓡∂ (n + 1))) := by
  -- On the half-space, the transition map is the ambient one.
  have key : ∀ v ∈ (𝓡∂ (n + 1)).symm ⁻¹' ((e₁.halfSpaceChart he₁ x₁).symm ≫ₕ
      e₂.halfSpaceChart he₂ x₂).source ∩ range (𝓡∂ (n + 1)),
      v ∈ (e₁.symm ≫ₕ e₂).source ∧ ((𝓡∂ (n + 1)) ∘ (e₁.halfSpaceChart he₁ x₁).symm ≫ₕ
        e₂.halfSpaceChart he₂ x₂ ∘ (𝓡∂ (n + 1)).symm) v = (e₂ ∘ e₁.symm) v := by
    rintro v ⟨⟨hv₁, hv₂⟩, hv⟩
    have hv' : ((𝓡∂ (n + 1)).symm v).1 = v := (𝓡∂ (n + 1)).right_inv hv
    simp only [OpenPartialHomeomorph.symm_symm] at hv₁ hv₂
    rw [halfSpaceChart_target, mem_preimage, modelWithCornersEuclideanHalfSpace_toFun, hv'] at hv₁
    rw [mem_preimage, halfSpaceChart_source, mem_preimage,
      coe_halfSpaceChart_symm_apply he₁ x₁ (by rwa [hv']), hv'] at hv₂
    refine ⟨⟨hv₁, hv₂⟩, ?_⟩
    simp only [comp_apply, OpenPartialHomeomorph.coe_trans,
      modelWithCornersEuclideanHalfSpace_toFun]
    rw [coe_halfSpaceChart_apply he₂ x₂ (by
      rwa [coe_halfSpaceChart_symm_apply he₁ x₁ (by rwa [hv']), hv']),
      coe_halfSpaceChart_symm_apply he₁ x₁ (by rwa [hv']), hv']
  exact (h.mono fun v hv ↦ (key v hv).1).congr fun v hv ↦ (key v hv).2

end HalfSpaceChart

end OpenPartialHomeomorph

namespace TauCeti

open OpenPartialHomeomorph

section IsManifold

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M]

/-- **Regular domains from half-space charts.** A charted space on a subset `s` of `M`, modelled on
the half-space `EuclideanHalfSpace (n + 1)`, all of whose charts are half-space restrictions
`OpenPartialHomeomorph.halfSpaceChart` of charts satisfying
`OpenPartialHomeomorph.IsExtendTransChart` for `C^m`, is a `C^m` manifold with boundary. -/
theorem isManifold_of_forall_mem_atlas_halfSpaceChart {m : ℕ∞ω} {n : ℕ} {s : Set M}
    [ChartedSpace (EuclideanHalfSpace (n + 1)) s]
    (h : ∀ e ∈ atlas (EuclideanHalfSpace (n + 1)) s,
      ∃ (e' : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (n + 1))))
        (he' : ∀ w ∈ e'.source, w ∈ s ↔ 0 ≤ e' w 0) (x : s),
        e'.IsExtendTransChart I m ∧ e = e'.halfSpaceChart he' x) :
    IsManifold (𝓡∂ (n + 1)) m s := by
  refine isManifold_of_contDiffOn _ _ _ fun e₁ e₂ h₁ h₂ ↦ ?_
  obtain ⟨_, he₁, x₁, hc₁, rfl⟩ := h e₁ h₁
  obtain ⟨_, he₂, x₂, hc₂, rfl⟩ := h e₂ h₂
  exact contDiffOn_halfSpaceChart_symm_trans he₁ he₂ x₁ x₂ (hc₁.contDiffOn_comp_symm hc₂)

variable {m : ℕ∞ω} {n : ℕ} {s : Set M} [ChartedSpace (EuclideanHalfSpace (n + 1)) s]

/-- Near a point `x` of `s`, the ambient chart `e` whose half-space restriction is the preferred
chart at `x` reads the points of `s` through the extended preferred chart. -/
private theorem exists_eventuallyEq_extChartAt_of_forall_mem_atlas_halfSpaceChart
    (h : ∀ e ∈ atlas (EuclideanHalfSpace (n + 1)) s,
      ∃ (e' : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (n + 1))))
        (he' : ∀ w ∈ e'.source, w ∈ s ↔ 0 ≤ e' w 0) (x : s),
        e'.IsExtendTransChart I m ∧ e = e'.halfSpaceChart he' x) (x : s) :
    ∃ e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (n + 1))),
      e.IsExtendTransChart I m ∧ (x : M) ∈ e.source ∧
        (e ∘ Subtype.val : s → EuclideanSpace ℝ (Fin (n + 1))) =ᶠ[nhds x]
          extChartAt (𝓡∂ (n + 1)) x := by
  obtain ⟨e, he, y, hc, hx⟩ := h _ (chart_mem_atlas _ x)
  have hsource (w : s) (hw : w ∈ (chartAt (EuclideanHalfSpace (n + 1)) x).source) :
      (w : M) ∈ e.source := by
    rw [hx, halfSpaceChart_source] at hw
    exact hw
  refine ⟨e, hc, hsource x (mem_chart_source _ x),
    Filter.eventually_of_mem (chart_source_mem_nhds (EuclideanHalfSpace (n + 1)) x)
      fun w hw ↦ ?_⟩
  simp only [extChartAt_coe, Function.comp_apply, modelWithCornersEuclideanHalfSpace_toFun, hx]
  rw [coe_halfSpaceChart_apply he y (hsource w hw)]

/-- **The inclusion of a regular domain is smooth.** If every chart of a charted space on a subset
`s` of `M`, modelled on the half-space `EuclideanHalfSpace (n + 1)`, is a half-space restriction of
a chart satisfying `OpenPartialHomeomorph.IsExtendTransChart` for `C^m`, then the inclusion
`s → M` is `C^m`, also at the boundary points of `s`. -/
theorem contMDiff_subtypeVal_of_forall_mem_atlas_halfSpaceChart
    (h : ∀ e ∈ atlas (EuclideanHalfSpace (n + 1)) s,
      ∃ (e' : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (n + 1))))
        (he' : ∀ w ∈ e'.source, w ∈ s ↔ 0 ≤ e' w 0) (x : s),
        e'.IsExtendTransChart I m ∧ e = e'.halfSpaceChart he' x) :
    ContMDiff (𝓡∂ (n + 1)) I m (Subtype.val : s → M) := by
  intro x
  obtain ⟨e, hce, hx, heq⟩ := exists_eventuallyEq_extChartAt_of_forall_mem_atlas_halfSpaceChart h x
  obtain ⟨c, Ψ, hc, -, hΨ, rfl⟩ := isExtendTransChart_iff.1 hce
  -- Near `x`, the inclusion is the inverse of `e` after the extended chart.
  have hval : (Subtype.val : s → M) =ᶠ[nhds x]
      (c.extendTrans I Ψ).symm ∘ extChartAt (𝓡∂ (n + 1)) x := by
    filter_upwards [heq, (continuous_subtype_val.continuousAt (x := x)).preimage_mem_nhds
      ((c.extendTrans I Ψ).open_source.mem_nhds hx)] with w hw hws
    rw [Function.comp_apply, ← hw, Function.comp_apply, (c.extendTrans I Ψ).left_inv hws]
  exact ((((contMDiffOn_extendTrans_symm c hc hΨ).contMDiffAt
    ((c.extendTrans I Ψ).open_target.mem_nhds ((c.extendTrans I Ψ).map_source hx))).comp_of_eq
      contMDiffAt_extChartAt heq.eq_of_nhds.symm).congr_of_eventuallyEq hval)

/-- **The inclusion of a regular domain has invertible derivative.** Under the hypotheses of
`TauCeti.contMDiff_subtypeVal_of_forall_mem_atlas_halfSpaceChart` with `m ≠ 0`, and when `M` is
modelled on a space of dimension `n + 1`, the manifold derivative of the inclusion `s → M` is
invertible at every point of `s`, including the boundary points, where the inclusion is not a
local diffeomorphism. -/
theorem isInvertible_mfderiv_subtypeVal_of_forall_mem_atlas_halfSpaceChart
    [FiniteDimensional ℝ E] (hn : Module.finrank ℝ E = n + 1) (hm : m ≠ 0)
    (h : ∀ e ∈ atlas (EuclideanHalfSpace (n + 1)) s,
      ∃ (e' : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (n + 1))))
        (he' : ∀ w ∈ e'.source, w ∈ s ↔ 0 ≤ e' w 0) (x : s),
        e'.IsExtendTransChart I m ∧ e = e'.halfSpaceChart he' x) (x : s) :
    (mfderiv (𝓡∂ (n + 1)) I (Subtype.val : s → M) x).IsInvertible := by
  obtain ⟨e, hce, hx, heq⟩ := exists_eventuallyEq_extChartAt_of_forall_mem_atlas_halfSpaceChart h x
  obtain ⟨c, Ψ, hc, hΨ, -, rfl⟩ := isExtendTransChart_iff.1 hce
  -- The ambient chart `e` composed with the inclusion is the extended chart of `s` near `x`,
  -- whose derivative at `x` is the identity.
  have he : MDifferentiableAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) (c.extendTrans I Ψ)
      (x : M) :=
    ((contMDiffOn_extendTrans c hc hΨ).contMDiffAt
      ((c.extendTrans I Ψ).open_source.mem_nhds hx)).mdifferentiableAt hm
  have hcomp : (mfderiv (𝓡∂ (n + 1)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
      ((c.extendTrans I Ψ) ∘ Subtype.val) x).IsInvertible := by
    have : IsManifold (𝓡∂ (n + 1)) 1 s :=
      have := isManifold_of_forall_mem_atlas_halfSpaceChart h
      IsManifold.of_le (ENat.one_le_iff_ne_zero_withTop.2 hm)
    rw [heq.mfderiv_eq, mfderiv_extChartAt_self]
    exact ⟨ContinuousLinearEquiv.refl ℝ _, rfl⟩
  exact (isInvertible_mfderiv_of_isInvertible_mfderiv_comp
    (by rw [finrank_euclideanSpace_fin, hn]) he
    ((contMDiff_subtypeVal_of_forall_mem_atlas_halfSpaceChart h x).mdifferentiableAt hm)
    hcomp).1

end IsManifold

end TauCeti

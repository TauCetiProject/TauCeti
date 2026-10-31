/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Real
public import TauCeti.Geometry.Manifold.ExtChartAt
public import TauCeti.Topology.OpenPartialHomeomorph.Constructions

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
(`OpenPartialHomeomorph.isManifold_of_forall_mem_atlas_halfSpaceChart`).

## Main declarations

* `OpenPartialHomeomorph.halfSpaceChart`, with its source, target, apply and inverse laws, and
  `OpenPartialHomeomorph.contDiffOn_halfSpaceChart_symm_trans`.
* `OpenPartialHomeomorph.IsExtendTransChart` and
  `OpenPartialHomeomorph.isManifold_of_forall_mem_atlas_halfSpaceChart`: an atlas of half-space
  restrictions of smoothly moved charts from the maximal atlas makes `s` a manifold with boundary.

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

section ExtendTrans

variable {𝕜 E F H M : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F] [TopologicalSpace H]
  [TopologicalSpace M] [ChartedSpace H M]

/-- `e` is a chart `c.extendTrans I Ψ`: a chart `c` of `M` from its maximal atlas for `C^m`, read in
the model vector space `E` and moved to `F` by a `C^m` homeomorphism `Ψ` with `C^m` inverse. The
transition maps between such charts are `C^m`
(`OpenPartialHomeomorph.contDiffOn_extendTrans_comp_symm`). -/
@[expose] def IsExtendTransChart (e : OpenPartialHomeomorph M F) (I : ModelWithCorners 𝕜 E H)
    [I.Boundaryless] (m : ℕ∞ω) : Prop :=
  ∃ (c : OpenPartialHomeomorph M H) (Ψ : E ≃ₜ F),
    c ∈ IsManifold.maximalAtlas I m M ∧ ContDiff 𝕜 m Ψ ∧ ContDiff 𝕜 m Ψ.symm ∧
      e = c.extendTrans I Ψ

end ExtendTrans

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
  obtain ⟨_, he₁, x₁, ⟨c₁, Ψ₁, hc₁, -, hΨ₁, rfl⟩, rfl⟩ := h e₁ h₁
  obtain ⟨_, he₂, x₂, ⟨c₂, Ψ₂, hc₂, hΨ₂, -, rfl⟩, rfl⟩ := h e₂ h₂
  exact contDiffOn_halfSpaceChart_symm_trans he₁ he₂ x₁ x₂
    (contDiffOn_extendTrans_comp_symm I hc₁ hc₂ hΨ₁ hΨ₂)

end IsManifold

end OpenPartialHomeomorph

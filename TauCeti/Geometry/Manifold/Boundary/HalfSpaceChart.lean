/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt
public import TauCeti.Geometry.Manifold.Boundary.Model
public import TauCeti.Topology.OpenPartialHomeomorph.Constructions

/-!
# Half-space charts cut out by a sign condition

Let `e` be a chart of a space `M` with values in `ℝⁿ⁺¹`, and let `s` be a subset of `M` such that,
on the source of `e`, a point lies in `s` exactly when its zeroth coordinate is nonnegative. Then
`e` restricts to a chart `OpenPartialHomeomorph.halfSpaceChart` of `s`, modelled on the half-space
`EuclideanHalfSpace (n + 1)`. The transition maps between such charts are the transition maps of
the ambient charts, restricted to the half-space
(`OpenPartialHomeomorph.contDiffOn_halfSpaceChart_trans_symm`), so smooth ambient transitions give
a smooth atlas on `s`. This is how regular domains, such as the sublevels of a function at a
regular value, become manifolds with boundary.

The ambient `ℝⁿ⁺¹`-valued charts typically come from charts `c` of a manifold with a boundaryless
model `I`, read in the model vector space and moved by a homeomorphism `Ψ`
(`OpenPartialHomeomorph.extendTrans`). When the charts lie in the maximal atlas and `Ψ` is smooth
with smooth inverse, their transition maps are smooth
(`OpenPartialHomeomorph.contDiffOn_extendTrans_comp_symm`).

Finally, `TauCeti.euclideanFinConsEquiv` places a normal coordinate in slot `0` of `ℝⁿ⁺¹` and
`k = n` tangential coordinates, reindexed along `k = n`, in slots `1, …, n`.

## Main declarations

* `OpenPartialHomeomorph.extendTrans` and `OpenPartialHomeomorph.contDiffOn_extendTrans_comp_symm`.
* `OpenPartialHomeomorph.halfSpaceChart`, with its source, target, apply and inverse laws, and
  `OpenPartialHomeomorph.contDiffOn_halfSpaceChart_trans_symm`.
* `TauCeti.euclideanFinConsEquiv`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, proof of Proposition 5.47 (charts of regular domains cut out by a defining
  function).
-/

public section

open Function Set
open scoped ContDiff Manifold

namespace OpenPartialHomeomorph

section ExtendTrans

variable {𝕜 E F H M : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [NormedAddCommGroup F] [TopologicalSpace H]
  [TopologicalSpace M]

/-- A chart `c` of `M`, read in the vector space `E` of a boundaryless model `I` and then moved to
`F` by a homeomorphism `Ψ`. Its coordinates are `Ψ ∘ c.extend I`. -/
noncomputable def extendTrans (c : OpenPartialHomeomorph M H) (I : ModelWithCorners 𝕜 E H)
    [I.Boundaryless] (Ψ : E ≃ₜ F) : OpenPartialHomeomorph M F :=
  (c.trans I.toHomeomorph.toOpenPartialHomeomorph).trans Ψ.toOpenPartialHomeomorph

variable (c : OpenPartialHomeomorph M H) (I : ModelWithCorners 𝕜 E H) [I.Boundaryless]
  (Ψ : E ≃ₜ F)

/-- The source of `c.extendTrans I Ψ` is the source of `c`. -/
@[simp]
theorem extendTrans_source : (c.extendTrans I Ψ).source = c.source := by
  simp [extendTrans, mfld_simps]

/-- The target of `c.extendTrans I Ψ` is the target of `c`, read in `E` and moved by `Ψ`. -/
@[simp]
theorem extendTrans_target :
    (c.extendTrans I Ψ).target = Ψ.symm ⁻¹' (I.symm ⁻¹' c.target) := by
  ext v
  simp [extendTrans, mfld_simps, ModelWithCorners.toHomeomorph_symm_apply]

/-- The chart `c.extendTrans I Ψ` reads a point through `c`, then `I`, then `Ψ`. -/
@[simp]
theorem extendTrans_apply (w : M) : c.extendTrans I Ψ w = Ψ (I (c w)) := by
  simp [extendTrans, mfld_simps, ModelWithCorners.toHomeomorph_apply]

/-- The inverse of `c.extendTrans I Ψ` is the inverse of `Ψ`, then of `I`, then of `c`. -/
@[simp]
theorem extendTrans_symm_apply (v : F) :
    (c.extendTrans I Ψ).symm v = c.symm (I.symm (Ψ.symm v)) := by
  simp [extendTrans, mfld_simps, ModelWithCorners.toHomeomorph_symm_apply]

/-- The transition map between two charts `c.extendTrans I Ψ` is `C^m` when `c` runs over the
maximal atlas of `M` and `Ψ` over homeomorphisms that are `C^m` with `C^m` inverses. -/
theorem contDiffOn_extendTrans_comp_symm [NormedSpace 𝕜 F] [ChartedSpace H M] {m : ℕ∞ω}
    {c₁ c₂ : OpenPartialHomeomorph M H} (hc₁ : c₁ ∈ IsManifold.maximalAtlas I m M)
    (hc₂ : c₂ ∈ IsManifold.maximalAtlas I m M) {Ψ₁ Ψ₂ : E ≃ₜ F}
    (hΨ₁ : ContDiff 𝕜 m Ψ₁.symm) (hΨ₂ : ContDiff 𝕜 m Ψ₂) :
    ContDiffOn 𝕜 m (c₂.extendTrans I Ψ₂ ∘ (c₁.extendTrans I Ψ₁).symm)
      ((c₁.extendTrans I Ψ₁).symm ≫ₕ c₂.extendTrans I Ψ₂).source := by
  have hmaps : MapsTo Ψ₁.symm ((c₁.extendTrans I Ψ₁).symm ≫ₕ c₂.extendTrans I Ψ₂).source
      (I.extendCoordChange c₁ c₂).source := by
    intro v hv
    simp only [extendTrans, mfld_simps, ModelWithCorners.toHomeomorph_symm_apply] at hv ⊢
    exact ⟨⟨by simp [I.range_eq_univ], hv.1⟩, hv.2⟩
  refine (hΨ₂.comp_contDiffOn ((I.contDiffOn_extendCoordChange hc₁ hc₂).comp
    hΨ₁.contDiffOn hmaps)).congr fun v _ ↦ ?_
  simp [mfld_simps]

end ExtendTrans

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
theorem contDiffOn_halfSpaceChart_trans_symm {m : ℕ∞ω}
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

/-- The continuous linear equivalence `(t, v) ↦ (t, v ∘ Fin.cast hk.symm)` of `ℝ × (Fin k → ℝ)`
with `ℝⁿ⁺¹`, for `k = n`: the scalar `t` is the normal coordinate in slot `0`, and `v`, reindexed
along `k = n` by `LinearEquiv.funCongrLeft`, gives the coordinates in slots `1, …, n`. It is the
boundary-normal identification `TauCeti.euclideanHalfSpaceBoundaryNormalEquiv n` after this
reindexing. -/
noncomputable def euclideanFinConsEquiv {k n : ℕ} (hk : k = n) :
    (ℝ × (Fin k → ℝ)) ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
  (ContinuousLinearEquiv.prodComm ℝ ℝ (Fin k → ℝ)).trans <|
    (((LinearEquiv.funCongrLeft ℝ ℝ (finCongr hk.symm)).toContinuousLinearEquiv.trans
      (EuclideanSpace.equiv (Fin n) ℝ).symm).prodCongr (ContinuousLinearEquiv.refl ℝ ℝ)).trans
    (euclideanHalfSpaceBoundaryNormalEquiv n)

/-- The zeroth coordinate of `TauCeti.euclideanFinConsEquiv` is the normal coordinate. -/
@[simp]
theorem euclideanFinConsEquiv_apply_zero {k n : ℕ} (hk : k = n) (p : ℝ × (Fin k → ℝ)) :
    euclideanFinConsEquiv hk p 0 = p.1 := by
  simp [euclideanFinConsEquiv]

/-- The coordinates of `TauCeti.euclideanFinConsEquiv` in slots `1, …, n` are the tangential
coordinates, reindexed along `k = n`. -/
@[simp]
theorem euclideanFinConsEquiv_apply_succ {k n : ℕ} (hk : k = n) (p : ℝ × (Fin k → ℝ))
    (i : Fin n) : euclideanFinConsEquiv hk p i.succ = p.2 (Fin.cast hk.symm i) := by
  simp [euclideanFinConsEquiv]

end TauCeti

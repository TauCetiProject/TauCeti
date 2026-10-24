/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.Charts
public import TauCeti.Geometry.Manifold.RegularValue.Scalar.Submersion

/-!
# Sublevels at regular values are manifolds with boundary

Let `f : M → ℝ` be a `C¹` function on a boundaryless manifold modelled on a real space `E` of
dimension `n + 1`, and let `a` be a regular value of `f`. Then the sublevel `{x | f x ≤ a}` carries
the atlas `TauCeti.sublevelChartedSpace`, modelled on the half-space `EuclideanHalfSpace (n + 1)`,
and it is a `C^m` manifold with boundary when `f` is `C^m`, `m ≥ 1`
(`TauCeti.isManifold_sublevel`). Its manifold boundary is the level `f⁻¹(a)`
(`TauCeti.boundary_sublevel`).

The preferred charts `TauCeti.sublevelChartAt` are of two kinds.

* **Face charts.** At a point `x` of the level `f⁻¹(a)`, the chart is the submersion chart
  `TauCeti.scalarSubmersionChartAt` of `f` at `x`, read in `ℝⁿ⁺¹` with the inward coordinate
  `a - f` in slot `0` and the tangential coordinates in slots `1, …, n`, placed by the
  boundary-normal identification `TauCeti.euclideanHalfSpaceBoundaryNormalEquiv`. Writing `D`
  for the derivative of `f` in the preferred extended chart at `x`, `P` for the chosen projection
  onto `ker D` and `K : ker D ≃ (Fin (dim E - 1) → ℝ)` for the identification used by the level
  atlas, the tangential coordinates of `w` are `K (P (extChartAt I x w - extChartAt I x x))`,
  reindexed by `Fin.cast` along `dim E - 1 = n` (`TauCeti.sublevelChartAt_apply_zero_of_eq` and
  `TauCeti.sublevelChartAt_apply_succ_of_eq`). On the level these are the coordinates of the level
  chart `TauCeti.scalarRegularLevelChartAt`
  (`TauCeti.sublevelChartAt_apply_succ_eq_scalarRegularLevelChartAt`).
* **Interior charts.** At a point `x` with `f x < a`, the chart is the preferred chart of `M`,
  restricted to `{f < a}`, read in `ℝⁿ⁺¹` through a fixed linear equivalence and recentred at `x`.
  It is then restricted to a ball of radius `r` contained in its target and translated by `2 r`
  in the zeroth coordinate, so that its image lies in the open half-space
  (`TauCeti.exists_sublevelChartAt_of_lt`).

Both kinds are restrictions of `ℝⁿ⁺¹`-valued charts of `M` on whose sources `f ≤ a` exactly when
the zeroth coordinate is nonnegative. Their transition maps are therefore restrictions of
transition maps of `M`, composed with smooth maps of the model spaces. No compactness of the
sublevel and no assumption on the critical points of `f` away from the level are needed.

## Main declarations

* `TauCeti.sublevelChartAt` and `TauCeti.sublevelChartedSpace`: the preferred charts and the atlas
  of a sublevel at a regular value.
* `TauCeti.sublevelFaceEquiv`: the linear part of the face charts, with the source, target, apply
  and inverse laws `TauCeti.sublevelChartAt_source_of_eq`, `TauCeti.sublevelChartAt_apply_of_eq`,
  `TauCeti.mem_sublevelChartAt_target_iff_of_eq` and `TauCeti.coe_sublevelChartAt_symm_apply_of_eq`.
* `TauCeti.isManifold_sublevel`: the sublevel is a `C^m` manifold with boundary.
* `TauCeti.boundary_sublevel` and `TauCeti.interior_sublevel`: its manifold boundary is the level
  `f⁻¹(a)`, and its manifold interior is `{x | f x < a}`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Proposition 5.47 (regular sublevel sets are regular domains).
* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  §3.
-/

public section

open Function Metric Module Set
open scoped ContDiff Manifold Topology

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] {f : M → ℝ} {a : ℝ}
  {n : ℕ}

namespace ScalarSublevel

variable (I) in
/-- A chart `c` of `M`, read in `E` and then moved to `ℝⁿ⁺¹` by a homeomorphism `Ψ`. -/
private noncomputable abbrev ambientChart [I.Boundaryless] (c : OpenPartialHomeomorph M H)
    (Ψ : E ≃ₜ EuclideanSpace ℝ (Fin (n + 1))) :
    OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (n + 1))) :=
  (c.trans I.toHomeomorph.toOpenPartialHomeomorph).trans Ψ.toOpenPartialHomeomorph

/-- The transition map between two charts `ambientChart I c Ψ` is `C^m` when `c` runs over the
maximal atlas of `M` and `Ψ` over smooth homeomorphisms with smooth inverses. -/
private theorem contDiffOn_ambientChart_trans_symm [I.Boundaryless] {m : ℕ∞ω}
    {c₁ c₂ : OpenPartialHomeomorph M H} (hc₁ : c₁ ∈ IsManifold.maximalAtlas I m M)
    (hc₂ : c₂ ∈ IsManifold.maximalAtlas I m M) {Ψ₁ Ψ₂ : E ≃ₜ EuclideanSpace ℝ (Fin (n + 1))}
    (hΨ₁ : ContDiff ℝ m Ψ₁.symm) (hΨ₂ : ContDiff ℝ m Ψ₂) :
    ContDiffOn ℝ m (ambientChart I c₂ Ψ₂ ∘ (ambientChart I c₁ Ψ₁).symm)
      ((ambientChart I c₁ Ψ₁).symm ≫ₕ ambientChart I c₂ Ψ₂).source := by
  have hmaps : MapsTo Ψ₁.symm ((ambientChart I c₁ Ψ₁).symm ≫ₕ ambientChart I c₂ Ψ₂).source
      (I.extendCoordChange c₁ c₂).source := by
    intro v hv
    simp only [mfld_simps, ModelWithCorners.toHomeomorph_symm_apply] at hv ⊢
    exact ⟨⟨by simp [I.range_eq_univ], hv.1⟩, hv.2⟩
  refine (hΨ₂.comp_contDiffOn ((I.contDiffOn_extendCoordChange hc₁ hc₂).comp
    hΨ₁.contDiffOn hmaps)).congr fun v _ ↦ ?_
  simp [mfld_simps]

section HalfSpaceChart

variable {e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (n + 1)))}
  (he : ∀ w ∈ e.source, f w ≤ a ↔ 0 ≤ e w 0)
include he

/-- Points of the target of `e` in the half-space come from the sublevel. -/
private theorem symm_mem_sublevel {z : EuclideanHalfSpace (n + 1)}
    (hz : (𝓡∂ (n + 1)) z ∈ e.target) : e.symm ((𝓡∂ (n + 1)) z) ∈ {x | f x ≤ a} :=
  (he _ (e.map_target hz)).2 (by rw [e.right_inv hz]; exact z.2)

/-- Points of the sublevel are read by `e` in the half-space. -/
private theorem apply_symm_apply_eq {w : M} (hw : w ∈ e.source) (hwa : w ∈ {x | f x ≤ a}) :
    (𝓡∂ (n + 1)) ((𝓡∂ (n + 1)).symm (e w)) = e w :=
  (𝓡∂ (n + 1)).right_inv <| by
    rw [range_modelWithCornersEuclideanHalfSpace]; exact (he w hw).1 hwa

omit he in
private theorem leftInvOn_symm (s : Set (EuclideanSpace ℝ (Fin (n + 1)))) :
    LeftInvOn (𝓡∂ (n + 1)).symm (𝓡∂ (n + 1)) ((𝓡∂ (n + 1)) ⁻¹' s) :=
  fun z _ ↦ (𝓡∂ (n + 1)).left_inv z

/-- An `ℝⁿ⁺¹`-valued chart `e` of `M` restricts to a half-space chart of the sublevel `{f ≤ a}`
when, on the source of `e`, a point lies in the sublevel exactly when its zeroth coordinate is
nonnegative. The base point `x` only witnesses that the sublevel is nonempty. -/
private noncomputable def halfSpaceChart (x : {x | f x ≤ a}) :
    OpenPartialHomeomorph {x | f x ≤ a} (EuclideanHalfSpace (n + 1)) :=
  e.subtypeCoord {x | f x ≤ a} ⟨x⟩ (𝓡∂ (n + 1)) (𝓡∂ (n + 1)).symm (symm_mem_sublevel he)
    (apply_symm_apply_eq he) (leftInvOn_symm _) (𝓡∂ (n + 1)).continuous
    (𝓡∂ (n + 1)).continuous_symm.continuousOn

private theorem halfSpaceChart_source (x : {x | f x ≤ a}) :
    (halfSpaceChart he x).source = Subtype.val ⁻¹' e.source := by
  unfold halfSpaceChart
  exact OpenPartialHomeomorph.subtypeCoord_source ..

private theorem halfSpaceChart_target (x : {x | f x ≤ a}) :
    (halfSpaceChart he x).target = (𝓡∂ (n + 1)) ⁻¹' e.target := by
  unfold halfSpaceChart
  exact OpenPartialHomeomorph.subtypeCoord_target ..

/-- On its source, the half-space chart reads a point through the ambient chart. -/
private theorem halfSpaceChart_apply (x : {x | f x ≤ a}) {w : {x | f x ≤ a}}
    (hw : (w : M) ∈ e.source) : (halfSpaceChart he x w).1 = e w := by
  unfold halfSpaceChart
  rw [OpenPartialHomeomorph.subtypeCoord_apply]
  exact apply_symm_apply_eq he hw w.2

/-- On its target, the inverse half-space chart is the inverse ambient chart. -/
private theorem coe_halfSpaceChart_symm_apply (x : {x | f x ≤ a})
    {z : EuclideanHalfSpace (n + 1)} (hz : z.1 ∈ e.target) :
    ((halfSpaceChart he x).symm z : M) = e.symm z.1 := by
  unfold halfSpaceChart
  exact OpenPartialHomeomorph.coe_subtypeCoord_symm_apply _ _ _ _ _ (symm_mem_sublevel he)
    (apply_symm_apply_eq he) _ _ _ hz

end HalfSpaceChart

/-- The transition maps between half-space charts are those of the ambient charts, restricted to
the half-space. -/
private theorem contDiffOn_halfSpaceChart_trans_symm {m : ℕ∞ω}
    {e₁ e₂ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (n + 1)))}
    (he₁ : ∀ w ∈ e₁.source, f w ≤ a ↔ 0 ≤ e₁ w 0) (he₂ : ∀ w ∈ e₂.source, f w ≤ a ↔ 0 ≤ e₂ w 0)
    (x₁ x₂ : {x | f x ≤ a}) (h : ContDiffOn ℝ m (e₂ ∘ e₁.symm) (e₁.symm ≫ₕ e₂).source) :
    ContDiffOn ℝ m ((𝓡∂ (n + 1)) ∘ (halfSpaceChart he₁ x₁).symm ≫ₕ halfSpaceChart he₂ x₂ ∘
        (𝓡∂ (n + 1)).symm)
      ((𝓡∂ (n + 1)).symm ⁻¹' ((halfSpaceChart he₁ x₁).symm ≫ₕ
        halfSpaceChart he₂ x₂).source ∩ range (𝓡∂ (n + 1))) := by
  -- On the half-space, the transition map is the ambient one.
  have key : ∀ v ∈ (𝓡∂ (n + 1)).symm ⁻¹' ((halfSpaceChart he₁ x₁).symm ≫ₕ
      halfSpaceChart he₂ x₂).source ∩ range (𝓡∂ (n + 1)),
      v ∈ (e₁.symm ≫ₕ e₂).source ∧ ((𝓡∂ (n + 1)) ∘ (halfSpaceChart he₁ x₁).symm ≫ₕ
        halfSpaceChart he₂ x₂ ∘ (𝓡∂ (n + 1)).symm) v = (e₂ ∘ e₁.symm) v := by
    rintro v ⟨⟨hv₁, hv₂⟩, hv⟩
    have hv' : ((𝓡∂ (n + 1)).symm v).1 = v := (𝓡∂ (n + 1)).right_inv hv
    simp only [OpenPartialHomeomorph.symm_symm] at hv₁ hv₂
    rw [halfSpaceChart_target, mem_preimage, modelWithCornersEuclideanHalfSpace_toFun, hv'] at hv₁
    rw [mem_preimage, halfSpaceChart_source, mem_preimage,
      coe_halfSpaceChart_symm_apply he₁ x₁ (by rwa [hv']), hv'] at hv₂
    refine ⟨⟨hv₁, hv₂⟩, ?_⟩
    simp only [comp_apply, OpenPartialHomeomorph.coe_trans,
      modelWithCornersEuclideanHalfSpace_toFun]
    rw [halfSpaceChart_apply he₂ x₂ (by rwa [coe_halfSpaceChart_symm_apply he₁ x₁ (by rwa [hv']),
      hv']), coe_halfSpaceChart_symm_apply he₁ x₁ (by rwa [hv']), hv']
  exact (h.mono fun v hv ↦ (key v hv).1).congr fun v hv ↦ (key v hv).2

section Interior

variable [I.Boundaryless] [FiniteDimensional ℝ E]

/-- The fixed linear identification of `E` with `ℝⁿ⁺¹` used by the interior charts. -/
private noncomputable abbrev modelEquiv (hn : finrank ℝ E = n + 1) :
    E ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
  ContinuousLinearEquiv.ofFinrankEq (by rw [hn, finrank_euclideanSpace_fin])

variable (I) in
/-- The preferred chart of `M` at `x`, read in `ℝⁿ⁺¹` through `modelEquiv` and recentred at `x`. -/
private noncomputable abbrev centredChart (hn : finrank ℝ E = n + 1) (x : M) :
    OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (n + 1))) :=
  ambientChart I (chartAt H x)
    ((Homeomorph.subRight (extChartAt I x x)).trans (modelEquiv hn).toHomeomorph)

private theorem centredChart_apply (hn : finrank ℝ E = n + 1) (x w : M) :
    centredChart I hn x w = modelEquiv hn (extChartAt I x w - extChartAt I x x) := by
  simp [mfld_simps, ModelWithCorners.toHomeomorph_apply]

private theorem centredChart_source (hn : finrank ℝ E = n + 1) (x : M) :
    (centredChart I hn x).source = (chartAt H x).source := by
  simp [mfld_simps]

/-- The recentred chart at a point of `{f < a}` maps the part of its source in `{f < a}` onto a
neighbourhood of `0`, which contains a ball about `0`. -/
private theorem exists_ball_subset_image (hf : Continuous f) (hn : finrank ℝ E = n + 1) {x : M}
    (hx : f x < a) :
    ∃ r > 0, ball 0 r ⊆ centredChart I hn x '' ((chartAt H x).source ∩ {w | f w < a}) := by
  refine Metric.isOpen_iff.1 ((centredChart I hn x).isOpen_image_of_subset_source
    ((chartAt H x).open_source.inter (isOpen_lt hf continuous_const))
    (by rw [centredChart_source]; exact inter_subset_left)) 0
    ⟨x, ⟨mem_chart_source H x, hx⟩, ?_⟩
  rw [centredChart_apply, sub_self, map_zero]

variable (I) in
/-- The radius of the ball in the target of the recentred chart used by the interior chart. -/
private noncomputable def interiorRadius (hf : Continuous f) (hn : finrank ℝ E = n + 1) {x : M}
    (hx : f x < a) : ℝ :=
  (exists_ball_subset_image (I := I) hf hn hx).choose

private theorem interiorRadius_pos (hf : Continuous f) (hn : finrank ℝ E = n + 1) {x : M}
    (hx : f x < a) : 0 < interiorRadius I hf hn hx :=
  (exists_ball_subset_image (I := I) hf hn hx).choose_spec.1

private theorem ball_interiorRadius_subset (hf : Continuous f) (hn : finrank ℝ E = n + 1)
    {x : M} (hx : f x < a) :
    ball 0 (interiorRadius I hf hn hx) ⊆
      centredChart I hn x '' ((chartAt H x).source ∩ {w | f w < a}) :=
  (exists_ball_subset_image (I := I) hf hn hx).choose_spec.2

variable (I) in
/-- The domain of the interior chart at `x`: the points of `{f < a}` which the recentred chart at
`x` sends into the ball of radius `interiorRadius`. -/
private noncomputable abbrev interiorDomain (hf : Continuous f) (hn : finrank ℝ E = n + 1)
    {x : M} (hx : f x < a) : Set M :=
  ((centredChart I hn x).source ∩ centredChart I hn x ⁻¹' ball 0 (interiorRadius I hf hn hx)) ∩
    {w | f w < a}

private theorem isOpen_interiorDomain (hf : Continuous f) (hn : finrank ℝ E = n + 1) {x : M}
    (hx : f x < a) : IsOpen (interiorDomain I hf hn hx) :=
  ((centredChart I hn x).isOpen_inter_preimage isOpen_ball).inter
    (isOpen_lt hf continuous_const)

variable (I) in
/-- The interior chart at a point `x` of `{f < a}`: the recentred chart at `x`, restricted to the
ball of radius `r = interiorRadius` and translated by `2 r` in the zeroth coordinate. -/
private noncomputable def interiorChart (hf : Continuous f) (hn : finrank ℝ E = n + 1) {x : M}
    (hx : f x < a) : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (n + 1))) :=
  ambientChart I ((chartAt H x).restr (interiorDomain I hf hn hx))
    (((Homeomorph.subRight (extChartAt I x x)).trans (modelEquiv hn).toHomeomorph).trans
      (Homeomorph.addRight (EuclideanSpace.single 0 (2 * interiorRadius I hf hn hx))))

private theorem interiorChart_apply (hf : Continuous f) (hn : finrank ℝ E = n + 1) {x : M}
    (hx : f x < a) (w : M) :
    interiorChart I hf hn hx w = centredChart I hn x w +
      EuclideanSpace.single 0 (2 * interiorRadius I hf hn hx) := by
  simp [interiorChart, centredChart_apply, mfld_simps, ModelWithCorners.toHomeomorph_apply]

private theorem interiorChart_source (hf : Continuous f) (hn : finrank ℝ E = n + 1) {x : M}
    (hx : f x < a) : (interiorChart I hf hn hx).source = interiorDomain I hf hn hx := by
  simp only [interiorChart, mfld_simps]
  rw [(isOpen_interiorDomain hf hn hx).interior_eq]
  refine inter_eq_right.2 fun w hw ↦ ?_
  have := hw.1.1
  rwa [centredChart_source] at this

/-- The zeroth coordinate of the interior chart is positive on its whole source. -/
private theorem interiorChart_apply_zero_pos (hf : Continuous f) (hn : finrank ℝ E = n + 1)
    {x : M} (hx : f x < a) {w : M} (hw : w ∈ (interiorChart I hf hn hx).source) :
    0 < interiorChart I hf hn hx w 0 := by
  rw [interiorChart_source] at hw
  have hlt : ‖centredChart I hn x w‖ < interiorRadius I hf hn hx := mem_ball_zero_iff.1 hw.1.2
  have h0 := (PiLp.norm_apply_le (centredChart I hn x w) 0).trans_lt hlt
  rw [interiorChart_apply]
  simp only [PiLp.add_apply, EuclideanSpace.single, PiLp.single_apply, ite_true]
  have h1 := neg_abs_le (centredChart I hn x w 0)
  rw [← Real.norm_eq_abs] at h1
  linarith [norm_nonneg (centredChart I hn x w 0)]

private theorem interiorChart_le_iff (hf : Continuous f) (hn : finrank ℝ E = n + 1) {x : M}
    (hx : f x < a) :
    ∀ w ∈ (interiorChart I hf hn hx).source, f w ≤ a ↔ 0 ≤ interiorChart I hf hn hx w 0 := by
  intro w hw
  refine iff_of_true ?_ (interiorChart_apply_zero_pos hf hn hx hw).le
  rw [interiorChart_source] at hw
  exact hw.2.le

end Interior

section Face

variable [I.Boundaryless] [FiniteDimensional ℝ E]

/-- The linear equivalence `(t, v) ↦ (-t, v ∘ Fin.cast)` of `ℝ × (Fin k → ℝ)` with `ℝⁿ⁺¹`,
for `k = n`: the boundary-normal identification `euclideanHalfSpaceBoundaryNormalEquiv n` with
normal coordinate `-t` and boundary coordinates `v`, reindexed along `k = n`. -/
private noncomputable def consEquiv {k : ℕ} (hk : k = n) :
    (ℝ × (Fin k → ℝ)) ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
  (ContinuousLinearEquiv.prodComm ℝ ℝ (Fin k → ℝ)).trans <|
    (((LinearEquiv.funCongrLeft ℝ ℝ (finCongr hk.symm)).toContinuousLinearEquiv.trans
      (EuclideanSpace.equiv (Fin n) ℝ).symm).prodCongr (ContinuousLinearEquiv.neg ℝ)).trans
    (euclideanHalfSpaceBoundaryNormalEquiv n)

private theorem consEquiv_apply_zero {k : ℕ} (hk : k = n) (p : ℝ × (Fin k → ℝ)) :
    consEquiv hk p 0 = -p.1 := by
  simp [consEquiv]

private theorem consEquiv_apply_succ {k : ℕ} (hk : k = n) (p : ℝ × (Fin k → ℝ)) (i : Fin n) :
    consEquiv hk p i.succ = p.2 (Fin.cast hk.symm i) := by
  simp [consEquiv]

end Face

end ScalarSublevel

open ScalarSublevel

section FaceEquiv

variable [I.Boundaryless] [FiniteDimensional ℝ E]

/-- The linear part `v ↦ (-D v, K (P v))` of the face chart of a sublevel at a regular point `x`
of `f`, with `-D v` in slot `0` and `K (P v)`, reindexed along `dim E - 1 = n`, in slots
`1, …, n` (`TauCeti.sublevelFaceEquiv_apply_zero`, `TauCeti.sublevelFaceEquiv_apply_succ`). Here
`D` is the derivative of `f` in the preferred extended chart at `x`, `P` the chosen projection onto
`ker D` and `K : ker D ≃ (Fin (dim E - 1) → ℝ)` the identification used by the level atlas. -/
noncomputable def sublevelFaceEquiv (hn : finrank ℝ E = n + 1) {x : M}
    (hx : IsRegularPoint I 𝓘(ℝ) f x) : E ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
  let D := fderiv ℝ (f ∘ (extChartAt I x).symm) (extChartAt I x x)
  (D.implicitCoordEquiv (LinearMap.range_eq_top.2 hx.surjective_fderiv_comp_extChartAt_symm)
      D.isFredholm_of_finiteDimensional.closedComplemented_ker).trans
    (((ContinuousLinearEquiv.refl ℝ ℝ).prodCongr
      (D.kerModelEquiv D.isFredholm_of_finiteDimensional.finite_ker
        hx.finrank_ker_fderiv_comp_extChartAt_symm)).trans (consEquiv (by omega)))

/-- The zeroth coordinate of `TauCeti.sublevelFaceEquiv` is `-D v`, where `D` is the derivative of
`f` in the preferred extended chart at `x`. -/
theorem sublevelFaceEquiv_apply_zero (hn : finrank ℝ E = n + 1) {x : M}
    (hx : IsRegularPoint I 𝓘(ℝ) f x) (v : E) :
    sublevelFaceEquiv hn hx v 0 = -fderiv ℝ (f ∘ (extChartAt I x).symm) (extChartAt I x x) v := by
  simp only [sublevelFaceEquiv, ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.prodCongr_apply, ContinuousLinearEquiv.refl_apply, consEquiv_apply_zero,
    ContinuousLinearMap.implicitCoordEquiv_apply]

/-- The coordinates of `TauCeti.sublevelFaceEquiv` in slots `1, …, n` are `K (P v)`, reindexed
along `dim E - 1 = n`, where `P` is the chosen projection onto the kernel of the preferred-chart
derivative `D` of `f` at `x` and `K` the identification of `ker D` used by the level atlas. -/
theorem sublevelFaceEquiv_apply_succ (hn : finrank ℝ E = n + 1) {x : M}
    (hx : IsRegularPoint I 𝓘(ℝ) f x) (v : E) (i : Fin n) :
    sublevelFaceEquiv hn hx v i.succ =
      let D := fderiv ℝ (f ∘ (extChartAt I x).symm) (extChartAt I x x)
      D.kerModelEquiv D.isFredholm_of_finiteDimensional.finite_ker
        hx.finrank_ker_fderiv_comp_extChartAt_symm
        (Classical.choose D.isFredholm_of_finiteDimensional.closedComplemented_ker v)
        (Fin.cast (by omega) i) := by
  simp only [sublevelFaceEquiv, ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.prodCongr_apply, ContinuousLinearEquiv.refl_apply, consEquiv_apply_succ,
    ContinuousLinearMap.implicitCoordEquiv_apply]

end FaceEquiv

namespace ScalarSublevel

section Face

variable [I.Boundaryless] [FiniteDimensional ℝ E]

variable (I) in
/-- The face chart at a regular point `x`: the submersion chart of `f` at `x`, read in `ℝⁿ⁺¹`
through `TauCeti.sublevelFaceEquiv`. -/
private noncomputable def faceChart (hn : finrank ℝ E = n + 1) {x : M}
    (hf : ContMDiffAt I 𝓘(ℝ) 1 f x) (hx : IsRegularPoint I 𝓘(ℝ) f x) :
    OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (n + 1))) :=
  ambientChart I (scalarSubmersionChartAt hf hx) (sublevelFaceEquiv hn hx).toHomeomorph

private theorem faceChart_source (hn : finrank ℝ E = n + 1) {x : M}
    (hf : ContMDiffAt I 𝓘(ℝ) 1 f x) (hx : IsRegularPoint I 𝓘(ℝ) f x) :
    (faceChart I hn hf hx).source = (scalarSubmersionChartAt hf hx).source := by
  simp [faceChart, mfld_simps]

private theorem faceChart_apply (hn : finrank ℝ E = n + 1) {x : M}
    (hf : ContMDiffAt I 𝓘(ℝ) 1 f x) (hx : IsRegularPoint I 𝓘(ℝ) f x) {w : M}
    (hw : w ∈ (chartAt H x).source) :
    faceChart I hn hf hx w =
      let D := fderiv ℝ (f ∘ (extChartAt I x).symm) (extChartAt I x x)
      consEquiv (by omega) (f w - f x,
        D.kerModelEquiv D.isFredholm_of_finiteDimensional.finite_ker
          hx.finrank_ker_fderiv_comp_extChartAt_symm
          (Classical.choose D.isFredholm_of_finiteDimensional.closedComplemented_ker
            (extChartAt I x w - extChartAt I x x))) := by
  have h := scalarSubmersionChartAt_extend_apply hf hx hw
  rw [OpenPartialHomeomorph.extend_coe, comp_apply] at h
  simp only [faceChart, OpenPartialHomeomorph.coe_trans, comp_apply,
    Homeomorph.toOpenPartialHomeomorph_apply, ModelWithCorners.toHomeomorph_apply,
    ContinuousLinearEquiv.coe_toHomeomorph, h, sublevelFaceEquiv, ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.prodCongr_apply,
    ContinuousLinearEquiv.refl_apply]

private theorem faceChart_le_iff (hn : finrank ℝ E = n + 1) {x : M}
    (hf : ContMDiffAt I 𝓘(ℝ) 1 f x) (hx : IsRegularPoint I 𝓘(ℝ) f x) (hxa : f x = a) :
    ∀ w ∈ (faceChart I hn hf hx).source, f w ≤ a ↔ 0 ≤ faceChart I hn hf hx w 0 := by
  intro w hw
  rw [faceChart_source, scalarSubmersionChartAt_source] at hw
  rw [faceChart_apply hn hf hx hw.1, consEquiv_apply_zero, hxa, neg_nonneg, sub_nonpos]

end Face

section Atlas

variable [I.Boundaryless] [FiniteDimensional ℝ E]

/-- The target of the interior chart is the ball of radius `r = interiorRadius` about the point
`2 r e₀` of `ℝⁿ⁺¹`. -/
private theorem interiorChart_target (hf : Continuous f) (hn : finrank ℝ E = n + 1) {x : M}
    (hx : f x < a) :
    (interiorChart I hf hn hx).target = ball (EuclideanSpace.single 0
      (2 * interiorRadius I hf hn hx)) (interiorRadius I hf hn hx) := by
  rw [← (interiorChart I hf hn hx).image_source_eq_target, interiorChart_source]
  ext v
  simp only [mem_image, interiorChart_apply, mem_ball, dist_eq_norm]
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [add_sub_cancel_right]
    exact mem_ball_zero_iff.1 hw.1.2
  · intro hv
    obtain ⟨w, ⟨hw, hwa⟩, hwv⟩ := ball_interiorRadius_subset hf hn hx (mem_ball_zero_iff.2 hv)
    refine ⟨w, ⟨⟨by rwa [centredChart_source], ?_⟩, hwa⟩, by rw [hwv, sub_add_cancel]⟩
    rw [mem_preimage, hwv, mem_ball_zero_iff]
    exact hv

end Atlas

end ScalarSublevel

open ScalarSublevel

variable [I.Boundaryless] [FiniteDimensional ℝ E] (hf : ContMDiff I 𝓘(ℝ) 1 f)
  (hreg : IsRegularValue I 𝓘(ℝ) f a) (hn : finrank ℝ E = n + 1)

/-- The preferred chart at a point `x` of the sublevel `{f ≤ a}` of a `C¹` function at a regular
value `a`, modelled on the half-space `EuclideanHalfSpace (n + 1)`, where `n + 1 = dim E`.

At a point of the level `f⁻¹(a)` it is the face chart: the submersion chart of `f` at `x`, with
the inward coordinate `a - f` in slot `0` and the tangential coordinates of the level chart in
slots `1, …, n` (`TauCeti.sublevelChartAt_apply_zero_of_eq`,
`TauCeti.sublevelChartAt_apply_succ_of_eq`). At a point of `{f < a}` it is an interior chart,
whose target is a ball in the open half-space (`TauCeti.exists_sublevelChartAt_of_lt`). -/
noncomputable def sublevelChartAt (x : {x | f x ≤ a}) :
    OpenPartialHomeomorph {x | f x ≤ a} (EuclideanHalfSpace (n + 1)) :=
  if hx : f x < a then halfSpaceChart (interiorChart_le_iff (I := I) hf.continuous hn hx) x
  else
    have hxa : f x = a := le_antisymm x.2 (not_lt.1 hx)
    halfSpaceChart (faceChart_le_iff hn hf.contMDiffAt (hreg.isRegularPoint hxa) hxa) x

private theorem sublevelChartAt_of_lt {x : {x | f x ≤ a}} (hx : f x < a) :
    sublevelChartAt hf hreg hn x =
      halfSpaceChart (interiorChart_le_iff (I := I) hf.continuous hn hx) x :=
  dite_eq_left hx

private theorem sublevelChartAt_of_eq {x : {x | f x ≤ a}} (hx : f x = a) :
    sublevelChartAt hf hreg hn x =
      halfSpaceChart (faceChart_le_iff hn hf.contMDiffAt (hreg.isRegularPoint hx) hx) x :=
  dite_eq_right hx.not_lt

/-- Every point of the sublevel lies in the source of its preferred chart. -/
theorem mem_sublevelChartAt_source (x : {x | f x ≤ a}) :
    x ∈ (sublevelChartAt hf hreg hn x).source := by
  have hxa : f x ≤ a := x.2
  rcases hxa.lt_or_eq with hx | hx
  · rw [sublevelChartAt_of_lt hf hreg hn hx, halfSpaceChart_source, mem_preimage,
      interiorChart_source]
    refine ⟨⟨by rw [centredChart_source]; exact mem_chart_source H _, ?_⟩, hx⟩
    rw [mem_preimage, centredChart_apply, sub_self, map_zero]
    exact mem_ball_self (interiorRadius_pos hf.continuous hn hx)
  · rw [sublevelChartAt_of_eq hf hreg hn hx, halfSpaceChart_source, mem_preimage,
      faceChart_source]
    exact mem_scalarSubmersionChartAt_source _ _

/-- The atlas of the sublevel `{f ≤ a}` of a `C¹` function at a regular value `a`, modelled on the
half-space `EuclideanHalfSpace (n + 1)`, where `n + 1 = dim E`, with preferred charts
`TauCeti.sublevelChartAt`. -/
@[irreducible]
noncomputable def sublevelChartedSpace :
    ChartedSpace (EuclideanHalfSpace (n + 1)) {x | f x ≤ a} where
  atlas := range (sublevelChartAt hf hreg hn)
  chartAt := sublevelChartAt hf hreg hn
  mem_chart_source := mem_sublevelChartAt_source hf hreg hn
  chart_mem_atlas := mem_range_self

/-- The installed preferred charts are `TauCeti.sublevelChartAt`. -/
@[simp]
theorem sublevelChartedSpace_chartAt (x : {x | f x ≤ a}) :
    @chartAt (EuclideanHalfSpace (n + 1)) _ {x | f x ≤ a} _ (sublevelChartedSpace hf hreg hn) x =
      sublevelChartAt hf hreg hn x := by
  unfold sublevelChartedSpace
  rfl

/-- The installed atlas consists exactly of the preferred charts. -/
@[simp]
theorem sublevelChartedSpace_atlas :
    @atlas (EuclideanHalfSpace (n + 1)) _ {x | f x ≤ a} _ (sublevelChartedSpace hf hreg hn) =
      range (sublevelChartAt hf hreg hn) := by
  unfold atlas sublevelChartedSpace
  rfl

section Face

variable {x : {x | f x ≤ a}} (hx : f x = a)
include hx

/-- The source of the preferred chart at a point `x` of the level `f⁻¹(a)` is the part of the
sublevel in the source of the submersion chart of `f` at `x`. -/
theorem sublevelChartAt_source_of_eq :
    (sublevelChartAt hf hreg hn x).source =
      Subtype.val ⁻¹' (scalarSubmersionChartAt hf.contMDiffAt (hreg.isRegularPoint hx)).source := by
  rw [sublevelChartAt_of_eq hf hreg hn hx, halfSpaceChart_source, faceChart_source]

/-- At a point `x` of the level `f⁻¹(a)`, the preferred chart reads a point of its source in the
extended submersion chart of `f` at `x`, followed by `TauCeti.sublevelFaceEquiv`. -/
theorem sublevelChartAt_apply_of_eq {w : {x | f x ≤ a}}
    (hw : w ∈ (sublevelChartAt hf hreg hn x).source) :
    (sublevelChartAt hf hreg hn x w).1 = sublevelFaceEquiv hn (hreg.isRegularPoint hx)
      ((scalarSubmersionChartAt hf.contMDiffAt (hreg.isRegularPoint hx)).extend I w) := by
  rw [sublevelChartAt_source_of_eq hf hreg hn hx, mem_preimage] at hw
  rw [sublevelChartAt_of_eq hf hreg hn hx, halfSpaceChart_apply _ _ (by rwa [faceChart_source])]
  simp [faceChart, mfld_simps, ModelWithCorners.toHomeomorph_apply]

/-- At a point `x` of the level `f⁻¹(a)`, a point `z` of the half-space lies in the target of the
preferred chart exactly when `TauCeti.sublevelFaceEquiv` sends it back into the target of the
extended submersion chart of `f` at `x`. -/
theorem mem_sublevelChartAt_target_iff_of_eq (z : EuclideanHalfSpace (n + 1)) :
    z ∈ (sublevelChartAt hf hreg hn x).target ↔
      (sublevelFaceEquiv hn (hreg.isRegularPoint hx)).symm z.1 ∈
        ((scalarSubmersionChartAt hf.contMDiffAt (hreg.isRegularPoint hx)).extend I).target := by
  rw [sublevelChartAt_of_eq hf hreg hn hx, halfSpaceChart_target, mem_preimage,
    OpenPartialHomeomorph.extend_target, I.range_eq_univ, inter_univ]
  simp [faceChart, mfld_simps, ModelWithCorners.toHomeomorph_symm_apply]

/-- At a point `x` of the level `f⁻¹(a)`, the inverse of the preferred chart is the inverse of
`TauCeti.sublevelFaceEquiv` followed by the inverse extended submersion chart of `f` at `x`. -/
theorem coe_sublevelChartAt_symm_apply_of_eq {z : EuclideanHalfSpace (n + 1)}
    (hz : z ∈ (sublevelChartAt hf hreg hn x).target) :
    ((sublevelChartAt hf hreg hn x).symm z : M) =
      ((scalarSubmersionChartAt hf.contMDiffAt (hreg.isRegularPoint hx)).extend I).symm
        ((sublevelFaceEquiv hn (hreg.isRegularPoint hx)).symm z.1) := by
  rw [sublevelChartAt_of_eq hf hreg hn hx] at hz ⊢
  rw [halfSpaceChart_target, mem_preimage, modelWithCornersEuclideanHalfSpace_toFun] at hz
  rw [coe_halfSpaceChart_symm_apply _ _ hz]
  simp [faceChart, mfld_simps, ModelWithCorners.toHomeomorph_symm_apply]

/-- At a point `x` of the level `f⁻¹(a)`, the zeroth coordinate of the preferred chart is the
inward coordinate `a - f`. -/
theorem sublevelChartAt_apply_zero_of_eq {w : {x | f x ≤ a}}
    (hw : w ∈ (sublevelChartAt hf hreg hn x).source) :
    (sublevelChartAt hf hreg hn x w).1 0 = a - f w := by
  rw [sublevelChartAt_source_of_eq hf hreg hn hx, mem_preimage,
    scalarSubmersionChartAt_source] at hw
  rw [sublevelChartAt_of_eq hf hreg hn hx, halfSpaceChart_apply _ _ (by
      rw [faceChart_source, scalarSubmersionChartAt_source]; exact hw),
    faceChart_apply hn _ _ hw.1, consEquiv_apply_zero, hx, neg_sub]

/-- At a point `x` of the level `f⁻¹(a)`, the coordinates of the preferred chart in slots
`1, …, n` are the tangential coordinates `K (P (extChartAt I x w - extChartAt I x x))`, reindexed
along `dim E - 1 = n`. Here `D` is the derivative of `f` in the preferred extended chart at `x`,
`P` the chosen projection onto `ker D` and `K : ker D ≃ (Fin (dim E - 1) → ℝ)` the identification
used by the level atlas. -/
theorem sublevelChartAt_apply_succ_of_eq {w : {x | f x ≤ a}}
    (hw : w ∈ (sublevelChartAt hf hreg hn x).source) (i : Fin n) :
    (sublevelChartAt hf hreg hn x w).1 i.succ =
      let D := fderiv ℝ (f ∘ (extChartAt I (x : M)).symm) (extChartAt I (x : M) x)
      D.kerModelEquiv D.isFredholm_of_finiteDimensional.finite_ker
        (hreg.isRegularPoint hx).finrank_ker_fderiv_comp_extChartAt_symm
        (Classical.choose D.isFredholm_of_finiteDimensional.closedComplemented_ker
          (extChartAt I (x : M) w - extChartAt I (x : M) x)) (Fin.cast (by omega) i) := by
  rw [sublevelChartAt_source_of_eq hf hreg hn hx, mem_preimage,
    scalarSubmersionChartAt_source] at hw
  rw [sublevelChartAt_of_eq hf hreg hn hx, halfSpaceChart_apply _ _ (by
      rw [faceChart_source, scalarSubmersionChartAt_source]; exact hw),
    faceChart_apply hn _ _ hw.1, consEquiv_apply_succ]

/-- **On the level, the tangential coordinates are those of the level chart.** At a point `x` of
the level `f⁻¹(a)`, the coordinates in slots `1, …, n` of the preferred chart of the sublevel at a
point `w` of the level are the coordinates of the preferred level chart
`TauCeti.scalarRegularLevelChartAt` at `x`, reindexed along `dim E - 1 = n`. -/
theorem sublevelChartAt_apply_succ_eq_scalarRegularLevelChartAt {w : {x | f x ≤ a}}
    (hw : w ∈ (sublevelChartAt hf hreg hn x).source) (hwa : f w = a) (i : Fin n) :
    (sublevelChartAt hf hreg hn x w).1 i.succ =
      scalarRegularLevelChartAt (fun y _ ↦ hf.contMDiffAt) hreg ⟨x, hx⟩ ⟨w, hwa⟩
        (Fin.cast (by omega) i) := by
  rw [sublevelChartAt_apply_succ_of_eq hf hreg hn hx hw, scalarRegularLevelChartAt_apply]

end Face

/-- At a point `x` of `{f < a}`, the preferred chart of the sublevel is an interior chart: for some
`r > 0` its target is the ball of radius `r` about the point `2 r e₀` of the open half-space, its
source lies in `{f < a}`, and it reads a point `w` as `T (extChartAt I x w - extChartAt I x x)`,
translated by `2 r e₀`, for a fixed linear equivalence `T : E ≃ ℝⁿ⁺¹`. -/
theorem exists_sublevelChartAt_of_lt {x : {x | f x ≤ a}} (hx : f x < a) :
    ∃ r > 0, (sublevelChartAt hf hreg hn x).target =
        (𝓡∂ (n + 1)) ⁻¹' ball (EuclideanSpace.single 0 (2 * r)) r ∧
      ∀ w ∈ (sublevelChartAt hf hreg hn x).source, f w < a ∧
        (sublevelChartAt hf hreg hn x w).1 =
          ContinuousLinearEquiv.ofFinrankEq (𝕜 := ℝ) (E := E)
              (F := EuclideanSpace ℝ (Fin (n + 1))) (by rw [hn, finrank_euclideanSpace_fin])
            (extChartAt I (x : M) w - extChartAt I (x : M) x) +
          EuclideanSpace.single 0 (2 * r) := by
  refine ⟨interiorRadius I hf.continuous hn hx, interiorRadius_pos hf.continuous hn hx, ?_,
    fun w hw ↦ ?_⟩
  · rw [sublevelChartAt_of_lt hf hreg hn hx, halfSpaceChart_target, interiorChart_target]
  · rw [sublevelChartAt_of_lt hf hreg hn hx, halfSpaceChart_source, mem_preimage] at hw
    rw [sublevelChartAt_of_lt hf hreg hn hx, halfSpaceChart_apply _ _ hw, interiorChart_apply,
      centredChart_apply]
    rw [interiorChart_source] at hw
    exact ⟨hw.2, rfl⟩

/-- Each preferred chart of the sublevel restricts a chart of `M` from its maximal atlas, read in
`ℝⁿ⁺¹` by a smooth homeomorphism with smooth inverse. -/
private theorem exists_sublevelChartAt_eq_halfSpaceChart {m : ℕ∞ω} [IsManifold I m M]
    (hm : 1 ≤ m) (hfm : ContMDiff I 𝓘(ℝ) m f) (x : {x | f x ≤ a}) :
    ∃ (c : OpenPartialHomeomorph M H) (Ψ : E ≃ₜ EuclideanSpace ℝ (Fin (n + 1)))
      (he : ∀ w ∈ (ambientChart I c Ψ).source, f w ≤ a ↔ 0 ≤ ambientChart I c Ψ w 0),
      c ∈ IsManifold.maximalAtlas I m M ∧ ContDiff ℝ m Ψ ∧ ContDiff ℝ m Ψ.symm ∧
        sublevelChartAt (hfm.of_le hm) hreg hn x = halfSpaceChart he x := by
  have hxa : f x ≤ a := x.2
  rcases hxa.lt_or_eq with hx | hx
  · refine ⟨_, _, interiorChart_le_iff (I := I) (hfm.of_le hm).continuous hn hx,
      restr_mem_maximalAtlas _ (IsManifold.chart_mem_maximalAtlas _)
        (isOpen_interiorDomain _ hn hx), ?_, ?_, sublevelChartAt_of_lt _ hreg hn hx⟩
    · exact ((modelEquiv hn).contDiff.comp (contDiff_id.sub contDiff_const)).add contDiff_const
    · convert ((modelEquiv hn).symm.contDiff.comp (contDiff_id.sub (contDiff_const
        (c := EuclideanSpace.single 0 (2 * interiorRadius I (hfm.of_le hm).continuous hn hx))))).add
        (contDiff_const (c := extChartAt I (x : M) x)) using 1
      ext1 v
      simp [Homeomorph.addRight_symm, sub_eq_add_neg]
  · exact ⟨_, _, faceChart_le_iff hn _ (hreg.isRegularPoint hx) hx,
      scalarSubmersionChartAt_mem_maximalAtlas _ _ hm fun y _ ↦ hfm.contMDiffAt,
      (sublevelFaceEquiv hn (hreg.isRegularPoint hx)).contDiff,
      (sublevelFaceEquiv hn (hreg.isRegularPoint hx)).symm.contDiff,
      sublevelChartAt_of_eq _ hreg hn hx⟩

/-- **A sublevel at a regular value is a manifold with boundary.** If `f` is `C^m`, `m ≥ 1`, and
`a` is a regular value of `f`, then the sublevel `{x | f x ≤ a}` is a `C^m` manifold with boundary
for its preferred atlas `TauCeti.sublevelChartedSpace`, modelled on the half-space
`EuclideanHalfSpace (n + 1)`, where `n + 1 = dim E`. -/
theorem isManifold_sublevel {m : ℕ∞ω} [IsManifold I m M] (hm : 1 ≤ m)
    (hfm : ContMDiff I 𝓘(ℝ) m f) :
    letI := sublevelChartedSpace (hfm.of_le hm) hreg hn
    IsManifold (𝓡∂ (n + 1)) m {x | f x ≤ a} := by
  let := sublevelChartedSpace (hfm.of_le hm) hreg hn
  refine isManifold_of_contDiffOn _ _ _ ?_
  rw [sublevelChartedSpace_atlas]
  rintro _ _ ⟨x₁, rfl⟩ ⟨x₂, rfl⟩
  obtain ⟨c₁, Ψ₁, he₁, hc₁, -, hΨ₁, h₁⟩ :=
    exists_sublevelChartAt_eq_halfSpaceChart hreg hn hm hfm x₁
  obtain ⟨c₂, Ψ₂, he₂, hc₂, hΨ₂, -, h₂⟩ :=
    exists_sublevelChartAt_eq_halfSpaceChart hreg hn hm hfm x₂
  rw [h₁, h₂]
  exact contDiffOn_halfSpaceChart_trans_symm he₁ he₂ x₁ x₂
    (contDiffOn_ambientChart_trans_symm hc₁ hc₂ hΨ₁ hΨ₂)

/-- **The boundary of a sublevel at a regular value is the level.** If `f` is `C^m`, `m ≥ 1`, and
`a` is a regular value of `f`, then the manifold boundary of the sublevel `{x | f x ≤ a}`, for its
preferred atlas, is the level `f⁻¹(a)`. -/
theorem boundary_sublevel {m : ℕ∞ω} [IsManifold I m M] (hm : 1 ≤ m)
    (hfm : ContMDiff I 𝓘(ℝ) m f) :
    letI := sublevelChartedSpace (hfm.of_le hm) hreg hn
    (𝓡∂ (n + 1)).boundary {x | f x ≤ a} = {x : {x | f x ≤ a} | f x = a} := by
  let := sublevelChartedSpace (hfm.of_le hm) hreg hn
  have := isManifold_sublevel hreg hn hm hfm
  ext x
  rw [ModelWithCorners.mem_boundary_euclideanHalfSpace_iff_of_mem_atlas
    (ENat.one_le_iff_ne_zero_withTop.1 hm) (chart_mem_atlas _ x) (mem_chart_source _ x),
    sublevelChartedSpace_chartAt, mem_ofPred_eq]
  have hxa : f x ≤ a := x.2
  rcases hxa.lt_or_eq with hx | hx
  · obtain ⟨r, hr, -, happly⟩ := exists_sublevelChartAt_of_lt (hfm.of_le hm) hreg hn hx
    rw [(happly x (mem_sublevelChartAt_source _ hreg hn x)).2, sub_self, map_zero, zero_add]
    simp only [EuclideanSpace.single, PiLp.single_apply, ite_true]
    exact iff_of_false (by positivity) hx.ne
  · rw [sublevelChartAt_apply_zero_of_eq _ hreg hn hx (mem_sublevelChartAt_source _ hreg hn x),
      hx, sub_self]
    exact iff_of_true rfl rfl

/-- The manifold interior of the sublevel `{x | f x ≤ a}` at a regular value `a` of a `C^m`
function, `m ≥ 1`, for its preferred atlas, is the strict sublevel `{x | f x < a}`. -/
theorem interior_sublevel {m : ℕ∞ω} [IsManifold I m M] (hm : 1 ≤ m)
    (hfm : ContMDiff I 𝓘(ℝ) m f) :
    letI := sublevelChartedSpace (hfm.of_le hm) hreg hn
    (𝓡∂ (n + 1)).interior {x | f x ≤ a} = {x : {x | f x ≤ a} | f x < a} := by
  let := sublevelChartedSpace (hfm.of_le hm) hreg hn
  rw [← ModelWithCorners.compl_boundary, boundary_sublevel hreg hn hm hfm]
  ext x
  have hxa : f x ≤ a := x.2
  simp only [mem_compl_iff, mem_ofPred_eq]
  exact ⟨fun h ↦ hxa.lt_of_ne h, ne_of_lt⟩

end TauCeti

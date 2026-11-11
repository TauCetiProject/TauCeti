/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Cell.Annulus
import TauCeti.AlgebraicTopology.Disk.Annulus

/-!
# Extending a homotopy of small Morse discs to the characteristic maps

Let `ψ₀` and `ψ₁` be two normal-form charts of the same index `k` at a critical level `c`, in which
`f = c - Σ_{j < k} yⱼ² + Σ_{j ≥ k} yⱼ²`, with characteristic maps
`χ₀, χ₁ : (D^k, ∂D^k) → (M_{c+ε}, M_{c-ε})`, `χ(w) = ψ⁻¹(√ε • (w, 0))`, and let `g` be a linear
isometry of `ℝᵏ`. Milnor's comparison of the cells attached by the two charts first compares
only small discs: for a radius `0 < d ≤ 1` one constructs a homotopy `G` from `χ₁` to `χ₀ ∘ g` on
the disc `‖w‖ ≤ d` which stays in `M_{c+ε}` and keeps the small boundary sphere `‖w‖ = d` in
`M_{c-εd²}`. This file shows that such a homotopy of small discs extends to a homotopy of maps of
pairs `K : χ₁ ≃ χ₀ ∘ g` on the whole disc, keeping the boundary sphere in the lower sublevel
`M_{c-ε}` (`TauCeti.exists_homotopy_morseCharacteristicMap_of_innerDisc`), provided the band
`f⁻¹[c - ε, c - εd²]` is compact and free of critical points. This is the homotopy of pairs that
the change-of-chart comparison, the reattachment map `TauCeti.morseCellReattachment`, takes as
input.

The construction follows Milnor. Let `R` deform `M_{c-εd²}` onto `M_{c-ε}` across the band
(`TauCeti.exists_sublevelDeformation`). Write a point of the annulus `d ≤ ‖w‖ ≤ 1` of the disc
as `(d + (1 - d) s) • θ` with `s ∈ [0, 1]` and `θ` on the unit sphere. The homotopy has three
stages; on the small disc the first and last are constant in time, and the second is `G`:

* on the annulus, deform the annulus of `χ₁` to the retraction track `(s, θ) ↦ R (s, χ₁ (d θ))`
  of its inner circle (`ContinuousMap.HomotopyRel.annulusToTrack`), keeping `χ₁` on the small
  disc;
* move the small disc by `G`, together with the retraction track of its boundary circle
  (`ContinuousMap.Homotopy.retractionTrackHomotopy`);
* undo the first stage for the annulus of `χ₀ ∘ g`.

On the seam `‖w‖ = d` the pieces agree because `R` starts at the identity, and on the outer
sphere every stage stays in `M_{c-ε}`: the annulus deformation does by construction, and the
track has reached the end of `R` there. No overlap of the whole characteristic discs of the two
charts is used.

## Main results

* `TauCeti.exists_homotopy_morseCharacteristicMap_of_innerDisc_of_homotopyRel`: a homotopy of the
  small discs of two Morse charts, keeping their boundary spheres in `M_{c-εd²}`, extends to a
  homotopy of maps of pairs between the characteristic maps, given a deformation of `M_{c-εd²}`
  into `M_{c-ε}` fixing `M_{c-ε}`.
* `TauCeti.exists_homotopy_morseCharacteristicMap_of_innerDisc`: the same when `M` is a manifold
  and the band `f⁻¹[c - ε, c - εd²]` is compact and free of critical points, which supplies the
  deformation.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  §3, Remark 3.3.
-/

public section

noncomputable section

universe u

open Set Metric Topology unitInterval CategoryTheory
open scoped ContDiff Manifold

namespace TauCeti

section Stages

variable {M : Type u} [TopologicalSpace M] {f : M → ℝ} {c ε : ℝ} {n k : ℕ} (d : I)
  {r : C({x : M | f x ≤ c - ε * (d : ℝ) ^ 2}, {x : M | f x ≤ c - ε * (d : ℝ) ^ 2})}
  (R : (ContinuousMap.id _).HomotopyRel r {x | f x.val ≤ c - ε}) (hr : ∀ x, f (r x).val ≤ c - ε)
  (hk : k ≤ n) (hε : 0 ≤ ε) (hd : 0 < d)

/-- The bounds kept by every stage: the disc goes into `M_{c+ε}` and its boundary into
`M_{c-ε}`. -/
private def StageBound (f : M → ℝ) (c ε : ℝ) (m : C(TopCat.disk.{u} k, M)) : Prop :=
  (∀ w, f (m w) ≤ c + ε) ∧ ∀ s, f (m (TopCat.diskBoundaryInclusion k s)) ≤ c - ε

/-- The characteristic map `w ↦ χ (g w)` of a chart, as a map into `M`. -/
private def cellMapComp (ψ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hball : closedBall 0 √ε ⊆ ψ.target)
    (g : EuclideanSpace ℝ (Fin k) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin k)) :
    C(TopCat.disk.{u} k, M) where
  toFun w := ψ.morseCellMap hk ε (g w.down)
  continuous_toFun := (ψ.continuousOn_morseCellMap hball hk).comp_continuous (by fun_prop)
    fun w ↦ by
      rw [mem_closedBall_zero_iff, g.norm_map]
      exact mem_closedBall_zero_iff.1 w.down.2

private theorem cellMapComp_apply (ψ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hball : closedBall 0 √ε ⊆ ψ.target)
    (g : EuclideanSpace ℝ (Fin k) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin k)) (w : TopCat.disk.{u} k) :
    cellMapComp hk ψ hball g w = ψ.morseCellMap hk ε (g w.down) :=
  (rfl)

/-- The Morse annulus of a chart, precomposed with a linear isometry on the sphere. -/
private def gAnnulus (ψ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hball : closedBall 0 √ε ⊆ ψ.target)
    (hf : ∀ y ∈ ψ.source, f y = c + ∑ j, (if j.val < k then -1 else 1) * ψ y j ^ 2)
    (g : EuclideanSpace ℝ (Fin k) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin k)) :
    C(I × TopCat.diskBoundary.{u} k, {x : M | f x ≤ c - ε * (d : ℝ) ^ 2}) :=
  (ψ.morseAnnulusMap hk hε hball hf d).comp
    (ContinuousMap.prodMap (ContinuousMap.id I) g.diskBoundaryMap.hom)

private theorem coe_gAnnulus_apply (ψ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hball : closedBall 0 √ε ⊆ ψ.target)
    (hf : ∀ y ∈ ψ.source, f y = c + ∑ j, (if j.val < k then -1 else 1) * ψ y j ^ 2)
    (g : EuclideanSpace ℝ (Fin k) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin k)) (s : I)
    (θ : TopCat.diskBoundary.{u} k) :
    (gAnnulus d hk hε ψ hball hf g (s, θ) : M) =
      ψ.morseCellMap hk ε (g (((d : ℝ) + (1 - d) * s) • θ.down)) := by
  have h : 1 - (1 - (d : ℝ)) * (1 - s) = d + (1 - d) * s := by ring
  simp [gAnnulus, OpenPartialHomeomorph.coe_morseAnnulusMap_apply, h]

variable {d}

omit [TopologicalSpace M] in
include hε in
/-- The sublevel `M_{c-εd²}` lies in `M_{c+ε}`. -/
private theorem le_of_mem_sublevel (x : {x : M | f x ≤ c - ε * (d : ℝ) ^ 2}) : f x ≤ c + ε :=
  x.2.trans ((sub_le_self _ (by positivity)).trans (le_add_of_nonneg_right hε))

variable (ψ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
  (hball : closedBall 0 √ε ⊆ ψ.target)
  (hf : ∀ y ∈ ψ.source, f y = c + ∑ j, (if j.val < k then -1 else 1) * ψ y j ^ 2)
  (g : EuclideanSpace ℝ (Fin k) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin k))

include hball hf in
/-- The outer circle of the annulus lies in the lower sublevel `M_{c-ε}`. -/
private theorem gAnnulus_one_mem (θ : TopCat.diskBoundary.{u} k) :
    gAnnulus d hk hε ψ hball hf g (1, θ) ∈ {x | f x.val ≤ c - ε} := by
  rw [mem_ofPred_eq, coe_gAnnulus_apply, Set.Icc.coe_one, mul_one, add_sub_cancel, one_smul]
  exact (OpenPartialHomeomorph.apply_morseCellMap_of_norm_eq_one hball hf hk hε
    ((g.norm_map _).trans (mem_sphere_zero_iff_norm.1 θ.down.2))).le

/-- The first stage for a chart `ψ` and an isometry `g`: on the small disc it is `χ ∘ g`, and on
the annulus it deforms the annulus of `χ ∘ g` to the retraction track of its inner circle. -/
private def chartStage : C(I × TopCat.disk.{u} k, M) :=
  TopCat.discGlue (unitInterval.coe_pos.2 hd)
    ⟨fun p ↦ ψ.morseCellMap hk ε (g p.2),
      (ψ.continuousOn_morseCellMap hball hk).comp_continuous (by fun_prop) fun p ↦ by
        rw [mem_closedBall_zero_iff, g.norm_map]
        exact (mem_closedBall_zero_iff.1 p.2.2).trans d.2.2⟩
    ⟨fun p ↦ (R.annulusToTrack hr (gAnnulus d hk hε ψ hball hf g)
        (gAnnulus_one_mem hk hε ψ hball hf g) (ContinuousMap.id I) rfl rfl p : M), by fun_prop⟩
    fun t θ ↦ by
      have h := ((R.annulusToTrack hr (gAnnulus d hk hε ψ hball hf g)
        (gAnnulus_one_mem hk hε ψ hball hf g) (ContinuousMap.id I) rfl rfl).prop t).1 θ
      simp only [ContinuousMap.HomotopyWith.coe_toHomotopy,
        ContinuousMap.Homotopy.curry_apply] at h
      simp [h, coe_gAnnulus_apply]

/-- On the small disc the first stage is `χ ∘ g` at all times. -/
private theorem chartStage_of_norm_le (t : I) {w : TopCat.disk.{u} k} (hw : ‖w.down.1‖ ≤ d) :
    chartStage R hr hk hε hd ψ hball hf g (t, w) = ψ.morseCellMap hk ε (g w.down.1) :=
  TopCat.discGlue_apply_of_norm_le _ _ _ _ _ hw

/-- On the annulus the first stage is the deformation of the annulus to the retraction track,
read in annulus coordinates. -/
private theorem chartStage_of_le_norm (t : I) {w : TopCat.disk.{u} k} (hw : d ≤ ‖w.down.1‖) :
    chartStage R hr hk hε hd ψ hball hf g (t, w) =
      (R.annulusToTrack hr (gAnnulus d hk hε ψ hball hf g) (gAnnulus_one_mem hk hε ψ hball hf g)
        (ContinuousMap.id I) rfl rfl
        (t, TopCat.annulusParam d w, TopCat.annulusDir (unitInterval.coe_pos.2 hd) ⟨w, hw⟩) : M) :=
  TopCat.discGlue_apply_of_le_norm _ _ _ _ _ hw

/-- Every stage map takes values in `M_{c+ε}`. -/
private theorem chartStage_le (q : I × TopCat.disk.{u} k) :
    f (chartStage R hr hk hε hd ψ hball hf g q) ≤ c + ε := by
  rw [chartStage]
  refine TopCat.discGlue_mem (S := {x | f x ≤ c + ε}) _ _ _ _ (fun q ↦ ?_) (fun q ↦ ?_) _
  · exact (OpenPartialHomeomorph.apply_morseCellMap_le hball hf hk hε
      ((g.norm_map _).trans_le ((mem_closedBall_zero_iff.1 q.2.2).trans d.2.2))).trans
      (le_add_of_nonneg_right hε)
  · exact le_of_mem_sublevel hε _

/-- Every stage map sends the boundary sphere into `M_{c-ε}`. -/
private theorem chartStage_boundary_le (t : I) (s : TopCat.diskBoundary.{u} k) :
    f (chartStage R hr hk hε hd ψ hball hf g (t, TopCat.diskBoundaryInclusion k s)) ≤ c - ε := by
  rw [chartStage]
  refine TopCat.discGlue_mem_of_norm_eq_one (S := {x | f x ≤ c - ε}) _ _ _ _ (fun _ v hv ↦ ?_)
    (fun _ θ ↦ ?_) _ (TopCat.norm_diskBoundaryInclusion s)
  · exact (OpenPartialHomeomorph.apply_morseCellMap_of_norm_eq_one hball hf hk hε
      ((g.norm_map _).trans hv)).le
  · exact ((R.annulusToTrack hr _ _ _ rfl rfl).prop _).2 θ

/-- The first stage as a homotopy keeping the bounds `TauCeti.StageBound`. -/
private def chartStageHomotopy :
    ContinuousMap.HomotopyWith (cellMapComp hk ψ hball g)
      ((chartStage R hr hk hε hd ψ hball hf g).curry 1) (StageBound f c ε) where
  toFun := chartStage R hr hk hε hd ψ hball hf g
  continuous_toFun := (chartStage R hr hk hε hd ψ hball hf g).continuous
  map_zero_left w := by
    rw [cellMapComp_apply]
    rcases le_total ‖w.down.1‖ d with hw | hw
    · exact chartStage_of_norm_le R hr hk hε hd ψ hball hf g 0 hw
    · rw [chartStage_of_le_norm R hr hk hε hd ψ hball hf g 0 hw,
        ContinuousMap.HomotopyWith.apply_zero, coe_gAnnulus_apply,
        TopCat.add_one_sub_mul_annulusParam_smul_annulusDir _ d.2.2 ⟨w, hw⟩]
  map_one_left _ := rfl
  prop' t := ⟨fun w ↦ chartStage_le R hr hk hε hd ψ hball hf g (t, w),
    fun s ↦ chartStage_boundary_le R hr hk hε hd ψ hball hf g t s⟩

end Stages

section Middle

variable {M : Type u} [TopologicalSpace M] {f : M → ℝ} {c ε : ℝ} {n k : ℕ} {d : I}
  {r : C({x : M | f x ≤ c - ε * (d : ℝ) ^ 2}, {x : M | f x ≤ c - ε * (d : ℝ) ^ 2})}
  (R : (ContinuousMap.id _).HomotopyRel r {x | f x.val ≤ c - ε}) (hr : ∀ x, f (r x).val ≤ c - ε)
  (hk : k ≤ n) (hε : 0 ≤ ε) (hd : 0 < d)
  {ψ₀ ψ₁ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
  (hball₀ : closedBall 0 √ε ⊆ ψ₀.target) (hball₁ : closedBall 0 √ε ⊆ ψ₁.target)
  (hf₀ : ∀ y ∈ ψ₀.source, f y = c + ∑ j, (if j.val < k then -1 else 1) * ψ₀ y j ^ 2)
  (hf₁ : ∀ y ∈ ψ₁.source, f y = c + ∑ j, (if j.val < k then -1 else 1) * ψ₁ y j ^ 2)
  (g : EuclideanSpace ℝ (Fin k) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin k))
  (G : C(I × closedBall (0 : EuclideanSpace ℝ (Fin k)) d, M))
  (hG₀ : ∀ w, G (0, w) = ψ₁.morseCellMap hk ε w)
  (hG₁ : ∀ w, G (1, w) = ψ₀.morseCellMap hk ε (g w))
  (hGf : ∀ t w, f (G (t, w)) ≤ c + ε)
  (hGd : ∀ t (w : closedBall (0 : EuclideanSpace ℝ (Fin k)) d),
    ‖(w : EuclideanSpace ℝ (Fin k))‖ = d → f (G (t, w)) ≤ c - ε * (d : ℝ) ^ 2)

/-- The homotopy `G` restricted to the inner circles, as a homotopy in `M_{c-εd²}` between the
inner circles of the annuli of `χ₁` and `χ₀ ∘ g`. -/
private def circleHomotopy :
    ContinuousMap.Homotopy
      ⟨fun θ ↦ gAnnulus d hk hε ψ₁ hball₁ hf₁ (.refl ℝ _) (0, θ), by fun_prop⟩
      ⟨fun θ ↦ gAnnulus d hk hε ψ₀ hball₀ hf₀ g (0, θ), by fun_prop⟩ where
  toFun p := ⟨G (p.1, ⟨(d : ℝ) • p.2.down.1, TopCat.smul_diskBoundary_mem_closedBall d.2.1 p.2⟩),
    hGd _ _ (by rw [norm_smul, mem_sphere_zero_iff_norm.1 p.2.down.2, Real.norm_of_nonneg d.2.1,
      mul_one])⟩
  continuous_toFun := by fun_prop
  map_zero_left θ := Subtype.ext (by simp [hG₀, coe_gAnnulus_apply])
  map_one_left θ := Subtype.ext (by simp [hG₁, coe_gAnnulus_apply])

private theorem coe_circleHomotopy_apply (p : I × TopCat.diskBoundary.{u} k) :
    (circleHomotopy hk hε hball₀ hball₁ hf₀ hf₁ g G hG₀ hG₁ hGd p : M) =
      G (p.1, ⟨(d : ℝ) • p.2.down.1, TopCat.smul_diskBoundary_mem_closedBall d.2.1 p.2⟩) :=
  (rfl)

/-- The second stage: move the small disc by `G`, together with the retraction tracks of its
boundary circles. -/
private def middleStage : C(I × TopCat.disk.{u} k, M) :=
  TopCat.discGlue (unitInterval.coe_pos.2 hd) G
    ⟨fun p ↦ (R.toHomotopy.retractionTrackHomotopy (ContinuousMap.id I)
      (circleHomotopy hk hε hball₀ hball₁ hf₀ hf₁ g G hG₀ hG₁ hGd) p : M), by fun_prop⟩
    fun t θ ↦ by
      simp only [ContinuousMap.coe_mk, ContinuousMap.Homotopy.retractionTrackHomotopy_apply,
        ContinuousMap.id_apply, ContinuousMap.Homotopy.apply_zero, coe_circleHomotopy_apply]

/-- On the small disc the second stage is `G`. -/
private theorem middleStage_of_norm_le (t : I) {w : TopCat.disk.{u} k} (hw : ‖w.down.1‖ ≤ d) :
    middleStage R hk hε hd hball₀ hball₁ hf₀ hf₁ g G hG₀ hG₁ hGd (t, w) =
      G (t, ⟨w.down.1, mem_closedBall_zero_iff.2 hw⟩) :=
  TopCat.discGlue_apply_of_norm_le _ _ _ _ _ hw

/-- On the annulus the second stage is the retraction track of `G` on the inner circle, read in
annulus coordinates. -/
private theorem middleStage_of_le_norm (t : I) {w : TopCat.disk.{u} k} (hw : d ≤ ‖w.down.1‖) :
    middleStage R hk hε hd hball₀ hball₁ hf₀ hf₁ g G hG₀ hG₁ hGd (t, w) =
      (R.toHomotopy.retractionTrackHomotopy (ContinuousMap.id I)
        (circleHomotopy hk hε hball₀ hball₁ hf₀ hf₁ g G hG₀ hG₁ hGd)
        (t, TopCat.annulusParam d w, TopCat.annulusDir (unitInterval.coe_pos.2 hd) ⟨w, hw⟩) : M) :=
  TopCat.discGlue_apply_of_le_norm _ _ _ _ _ hw

include hGf in
private theorem middleStage_le (q : I × TopCat.disk.{u} k) :
    f (middleStage R hk hε hd hball₀ hball₁ hf₀ hf₁ g G hG₀ hG₁ hGd q) ≤ c + ε := by
  rw [middleStage]
  exact TopCat.discGlue_mem (S := {x | f x ≤ c + ε}) _ _ _ _ (fun q ↦ hGf _ _)
    (fun q ↦ le_of_mem_sublevel hε _) _

include hr in
private theorem middleStage_boundary_le (t : I) (s : TopCat.diskBoundary.{u} k) :
    f (middleStage R hk hε hd hball₀ hball₁ hf₀ hf₁ g G hG₀ hG₁ hGd
      (t, TopCat.diskBoundaryInclusion k s)) ≤ c - ε := by
  rw [middleStage]
  refine TopCat.discGlue_mem_of_norm_eq_one (S := {x | f x ≤ c - ε}) _ _ _ _ (fun _ v hv ↦ ?_)
    (fun _ θ ↦ ?_) _ (TopCat.norm_diskBoundaryInclusion s)
  · -- A unit vector of the small disc forces `d = 1`.
    have hd₁ : (d : ℝ) = 1 :=
      le_antisymm d.2.2 (hv ▸ mem_closedBall_zero_iff.1 v.2)
    simpa [hd₁] using hGd _ v (hv.trans hd₁.symm)
  · exact R.toHomotopy.retractionTrackHomotopy_one_mem (B := {x | f x.val ≤ c - ε}) hr rfl _ _ θ

/-- The second stage as a homotopy keeping the bounds `TauCeti.StageBound`, from the end of the
first stage for `ψ₁` to the end of the first stage for `ψ₀` and `g`. -/
private def middleStageHomotopy :
    ContinuousMap.HomotopyWith
      ((chartStage R hr hk hε hd ψ₁ hball₁ hf₁ (.refl ℝ _)).curry 1)
      ((chartStage R hr hk hε hd ψ₀ hball₀ hf₀ g).curry 1) (StageBound f c ε) where
  toFun := middleStage R hk hε hd hball₀ hball₁ hf₀ hf₁ g G hG₀ hG₁ hGd
  continuous_toFun := (middleStage R hk hε hd hball₀ hball₁ hf₀ hf₁ g G hG₀ hG₁ hGd).continuous
  map_zero_left w := by
    rw [ContinuousMap.curry_apply]
    rcases le_total ‖w.down.1‖ d with hw | hw
    · rw [middleStage_of_norm_le (hw := hw), chartStage_of_norm_le (hw := hw), hG₀,
        LinearIsometryEquiv.coe_refl, id]
    · rw [middleStage_of_le_norm (hw := hw), chartStage_of_le_norm (hw := hw)]
      simp
  map_one_left w := by
    rw [ContinuousMap.curry_apply]
    rcases le_total ‖w.down.1‖ d with hw | hw
    · rw [middleStage_of_norm_le (hw := hw), chartStage_of_norm_le (hw := hw), hG₁]
    · rw [middleStage_of_le_norm (hw := hw), chartStage_of_le_norm (hw := hw)]
      simp
  prop' t := ⟨fun w ↦ middleStage_le R hk hε hd hball₀ hball₁ hf₀ hf₁ g G hG₀ hG₁ hGf hGd (t, w),
    fun s ↦ middleStage_boundary_le R hr hk hε hd hball₀ hball₁ hf₀ hf₁ g G hG₀ hG₁ hGd t s⟩

end Middle

section Topological

variable {M : Type u} [TopologicalSpace M] {f : M → ℝ} {c ε : ℝ} {n k : ℕ}

/-- **A homotopy of small Morse discs extends to the characteristic maps, given a deformation of
the band.** Let `ψ₀` and `ψ₁` be charts with values in `ℝⁿ` in which
`f = c - Σ_{j < k} yⱼ² + Σ_{j ≥ k} yⱼ²`, whose targets contain the closed ball of radius `√ε`, with
characteristic maps `χ₀` and `χ₁`, and let `g` be a linear isometry of `ℝᵏ`. Let `0 < d ≤ 1`, and
let `R` be a homotopy from the identity of `M_{c-εd²}` to a self-map `r` with values in `M_{c-ε}`,
fixing `M_{c-ε}`. Suppose that `G` is a homotopy, on the disc `‖w‖ ≤ d`, from `w ↦ χ₁ w` to
`w ↦ χ₀ (g w)`, with values in `M_{c+ε}`, which keeps the sphere `‖w‖ = d` in `M_{c-εd²}`. Then
`χ₁` is homotopic to `χ₀ ∘ g` as a map of pairs `(D^k, ∂D^k) → (M_{c+ε}, M_{c-ε})`: the homotopy
keeps the boundary sphere in `M_{c-ε}`. -/
theorem exists_homotopy_morseCharacteristicMap_of_innerDisc_of_homotopyRel
    {ψ₀ ψ₁ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))} (hk : k ≤ n) (hε : 0 ≤ ε)
    (hball₀ : closedBall 0 √ε ⊆ ψ₀.target) (hball₁ : closedBall 0 √ε ⊆ ψ₁.target)
    (hf₀ : ∀ y ∈ ψ₀.source, f y = c + ∑ j, (if j.val < k then -1 else 1) * ψ₀ y j ^ 2)
    (hf₁ : ∀ y ∈ ψ₁.source, f y = c + ∑ j, (if j.val < k then -1 else 1) * ψ₁ y j ^ 2)
    (g : EuclideanSpace ℝ (Fin k) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin k)) {d : I} (hd : 0 < d)
    {r : C({x : M | f x ≤ c - ε * (d : ℝ) ^ 2}, {x : M | f x ≤ c - ε * (d : ℝ) ^ 2})}
    (R : (ContinuousMap.id _).HomotopyRel r {x | f x.val ≤ c - ε})
    (hr : ∀ x, f (r x).val ≤ c - ε)
    (G : C(I × closedBall (0 : EuclideanSpace ℝ (Fin k)) d, M))
    (hG₀ : ∀ w, G (0, w) = ψ₁.morseCellMap hk ε w)
    (hG₁ : ∀ w, G (1, w) = ψ₀.morseCellMap hk ε (g w))
    (hGf : ∀ t w, f (G (t, w)) ≤ c + ε)
    (hGd : ∀ t (w : closedBall (0 : EuclideanSpace ℝ (Fin k)) d),
      ‖(w : EuclideanSpace ℝ (Fin k))‖ = d → f (G (t, w)) ≤ c - ε * (d : ℝ) ^ 2) :
    ∃ K : (ψ₁.morseCharacteristicMap hk hε hball₁ hf₁).hom.Homotopy
        (g.diskMap ≫ ψ₀.morseCharacteristicMap hk hε hball₀ hf₀).hom,
      ∀ t (s : TopCat.diskBoundary.{u} k), f (K (t, TopCat.diskBoundaryInclusion k s)) ≤ c - ε := by
  -- Deform the annulus of `χ₁`, move the small disc with its tracks, and undo the annulus
  -- deformation for `χ₀ ∘ g`.
  let K := (chartStageHomotopy R hr hk hε hd ψ₁ hball₁ hf₁ (.refl ℝ _)).trans
    ((middleStageHomotopy R hr hk hε hd hball₀ hball₁ hf₀ hf₁ g G hG₀ hG₁ hGf hGd).trans
      (chartStageHomotopy R hr hk hε hd ψ₀ hball₀ hf₀ g).symm)
  exact ⟨{ toFun p := ⟨K p, (K.prop p.1).1 p.2⟩
           continuous_toFun := K.continuous.subtype_mk _
           map_zero_left w := Subtype.ext ((K.apply_zero w).trans (by
             rw [cellMapComp_apply, OpenPartialHomeomorph.coe_morseCharacteristicMap_apply,
               LinearIsometryEquiv.coe_refl, id]))
           map_one_left w := Subtype.ext ((K.apply_one w).trans (by
             rw [cellMapComp_apply, TopCat.hom_comp, ContinuousMap.comp_apply,
               OpenPartialHomeomorph.coe_morseCharacteristicMap_apply,
               LinearIsometryEquiv.coe_diskMap_apply_down])) }, fun t s ↦ (K.prop t).2 s⟩

end Topological

section Main

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {Iₘ : ModelWithCorners ℝ E H} [Iₘ.Boundaryless]
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold Iₘ ∞ M] [T2Space M]
  {f : M → ℝ} {c ε : ℝ} {n k : ℕ}

/-- **A homotopy of small Morse discs extends to the characteristic maps.** Let `ψ₀` and `ψ₁` be
charts with values in `ℝⁿ` in which `f = c - Σ_{j < k} yⱼ² + Σ_{j ≥ k} yⱼ²`, whose targets contain
the closed ball of radius `√ε`, with characteristic maps `χ₀` and `χ₁`, and let `g` be a linear
isometry of `ℝᵏ`. Let `0 < d ≤ 1` be such that the band `f⁻¹[c - ε, c - εd²]` is compact and free
of critical points. Suppose that `G` is a homotopy, on the disc `‖w‖ ≤ d`, from `w ↦ χ₁ w` to
`w ↦ χ₀ (g w)`, with values in `M_{c+ε}`, which keeps the sphere `‖w‖ = d` in `M_{c-εd²}`. Then
`χ₁` is homotopic to `χ₀ ∘ g` as a map of pairs `(D^k, ∂D^k) → (M_{c+ε}, M_{c-ε})`: the homotopy
keeps the boundary sphere in `M_{c-ε}`. -/
theorem exists_homotopy_morseCharacteristicMap_of_innerDisc (hf : ContMDiff Iₘ 𝓘(ℝ) ∞ f)
    {ψ₀ ψ₁ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))} (hk : k ≤ n) (hε : 0 ≤ ε)
    (hball₀ : closedBall 0 √ε ⊆ ψ₀.target) (hball₁ : closedBall 0 √ε ⊆ ψ₁.target)
    (hf₀ : ∀ y ∈ ψ₀.source, f y = c + ∑ j, (if j.val < k then -1 else 1) * ψ₀ y j ^ 2)
    (hf₁ : ∀ y ∈ ψ₁.source, f y = c + ∑ j, (if j.val < k then -1 else 1) * ψ₁ y j ^ 2)
    (g : EuclideanSpace ℝ (Fin k) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin k)) {d : I} (hd : 0 < d)
    (hcompact : IsCompact (f ⁻¹' Icc (c - ε) (c - ε * (d : ℝ) ^ 2)))
    (hreg : ∀ x, c - ε ≤ f x → f x ≤ c - ε * (d : ℝ) ^ 2 → mfderiv Iₘ 𝓘(ℝ) f x ≠ 0)
    (G : C(I × closedBall (0 : EuclideanSpace ℝ (Fin k)) d, M))
    (hG₀ : ∀ w, G (0, w) = ψ₁.morseCellMap hk ε w)
    (hG₁ : ∀ w, G (1, w) = ψ₀.morseCellMap hk ε (g w))
    (hGf : ∀ t w, f (G (t, w)) ≤ c + ε)
    (hGd : ∀ t (w : closedBall (0 : EuclideanSpace ℝ (Fin k)) d),
      ‖(w : EuclideanSpace ℝ (Fin k))‖ = d → f (G (t, w)) ≤ c - ε * (d : ℝ) ^ 2) :
    ∃ K : (ψ₁.morseCharacteristicMap hk hε hball₁ hf₁).hom.Homotopy
        (g.diskMap ≫ ψ₀.morseCharacteristicMap hk hε hball₀ hf₀).hom,
      ∀ t (s : TopCat.diskBoundary.{u} k), f (K (t, TopCat.diskBoundaryInclusion k s)) ≤ c - ε := by
  have hab : c - ε ≤ c - ε * (d : ℝ) ^ 2 := by
    have := pow_le_one₀ d.2.1 d.2.2 (n := 2)
    nlinarith
  obtain ⟨r, -, ⟨R⟩⟩ := exists_sublevelDeformation hf hab hcompact hreg
  refine exists_homotopy_morseCharacteristicMap_of_innerDisc_of_homotopyRel hk hε hball₀ hball₁ hf₀
    hf₁ g hd R.symm (fun x ↦ ?_) G hG₀ hG₁ hGf hGd
  rw [ContinuousMap.comp_apply, coe_sublevelInclusion_apply]
  exact (r x).2

end Main

end TauCeti

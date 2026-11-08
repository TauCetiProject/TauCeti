/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Cell.Annulus
import TauCeti.AlgebraicTopology.Disk.RadialPush

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
the change-of-chart comparison `TauCeti.morseChartChange` and the reattachment map
`TauCeti.morseCellReattachment` take as input.

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

* `TauCeti.exists_homotopy_morseCharacteristicMap_of_innerDisc`: a homotopy of the small discs
  of two Morse charts, keeping their boundary spheres in `M_{c-εd²}`, extends to a homotopy of maps
  of pairs between the characteristic maps.

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

section DiscGlue

variable {P Y : Type*} [TopologicalSpace P] [TopologicalSpace Y] {k : ℕ} {d : ℝ}

/-- The radial parameter `s ∈ [0, 1]` of a point `w = (d + (1 - d) s) • θ` of the annulus
`d ≤ ‖w‖ ≤ 1` of the disc. -/
private def annulusParam (d : ℝ) (w : TopCat.disk.{u} k) : I :=
  projIcc 0 1 zero_le_one ((‖w.down.1‖ - d) / (1 - d))

private theorem continuous_annulusParam : Continuous (annulusParam.{u} (k := k) d) :=
  continuous_projIcc.comp (((continuous_norm.comp
    (continuous_subtype_val.comp continuous_uliftDown)).sub continuous_const).div_const _)

/-- The direction `w / ‖w‖` of a point `w` of the annulus `d ≤ ‖w‖` of the disc, for `0 < d`: the
end of the radial push `TauCeti.TopCat.diskRadialPush` with radius `d`. -/
private def annulusDir (hd : 0 < d) (w : {w : TopCat.disk.{u} k // d ≤ ‖w.down.1‖}) :
    TopCat.diskBoundary.{u} k :=
  ULift.up ⟨(TopCat.diskRadialPush k hd.le (1, w.1)).down.1,
    mem_sphere_zero_iff_norm.2 (TopCat.norm_diskRadialPush_one hd w.2)⟩

private theorem continuous_annulusDir (hd : 0 < d) : Continuous (annulusDir.{u} (k := k) hd) :=
  continuous_uliftUp.comp ((continuous_subtype_val.comp (continuous_uliftDown.comp
    ((TopCat.diskRadialPush k hd.le).continuous.comp
      (continuous_const.prodMk continuous_subtype_val)))).subtype_mk _)

private theorem coe_annulusDir (hd : 0 < d) (w : {w : TopCat.disk.{u} k // d ≤ ‖w.down.1‖}) :
    ((annulusDir hd w).down : EuclideanSpace ℝ (Fin k)) = ‖w.1.down.1‖⁻¹ • w.1.down.1 :=
  TopCat.coe_diskRadialPush_one_of_le_norm hd w.2

/-- The radius `d + (1 - d) s` of the annulus coordinates of `w` is the norm of `w`. -/
private theorem annulusRadius_eq (hd₁ : d ≤ 1) {w : TopCat.disk.{u} k} (hw : d ≤ ‖w.down.1‖) :
    d + (1 - d) * (annulusParam d w : ℝ) = ‖w.down.1‖ := by
  have hw₁ : ‖w.down.1‖ ≤ 1 := mem_closedBall_zero_iff.1 w.down.2
  rcases hd₁.lt_or_eq with hd₁ | rfl
  · have h₀ : 0 ≤ (‖w.down.1‖ - d) / (1 - d) := div_nonneg (by linarith) (by linarith)
    have h₁ : (‖w.down.1‖ - d) / (1 - d) ≤ 1 := (div_le_one (by linarith)).2 (by linarith)
    rw [annulusParam, coe_projIcc, min_eq_right h₁, max_eq_right h₀]
    field_simp
    ring
  · rw [le_antisymm hw₁ hw]
    ring

/-- A point of the annulus is recovered from its annulus coordinates. -/
private theorem annulusRadius_smul_annulusDir (hd : 0 < d) (hd₁ : d ≤ 1)
    (w : {w : TopCat.disk.{u} k // d ≤ ‖w.down.1‖}) :
    (d + (1 - d) * (annulusParam d w.1 : ℝ)) • ((annulusDir hd w).down : EuclideanSpace ℝ (Fin k)) =
      w.1.down.1 := by
  rw [annulusRadius_eq hd₁ w.2, coe_annulusDir, smul_smul,
    mul_inv_cancel₀ (hd.trans_le w.2).ne', one_smul]

/-- On the seam `‖w‖ = d` the radial parameter vanishes. -/
private theorem annulusParam_of_norm_eq {w : TopCat.disk.{u} k} (hw : ‖w.down.1‖ = d) :
    annulusParam d w = 0 :=
  projIcc_of_le_left _ (by rw [hw, sub_self, zero_div])

/-- On the boundary sphere the radial parameter is `1`, for `d < 1`. -/
private theorem annulusParam_of_norm_eq_one (hd₁ : d < 1) {w : TopCat.disk.{u} k}
    (hw : ‖w.down.1‖ = 1) : annulusParam d w = 1 :=
  projIcc_of_right_le _ (by rw [hw, div_self (by linarith)])

private theorem norm_smul_diskBoundary_le (hd : 0 ≤ d) (θ : TopCat.diskBoundary.{u} k) :
    d • (θ.down : EuclideanSpace ℝ (Fin k)) ∈ closedBall (0 : EuclideanSpace ℝ (Fin k)) d := by
  rw [mem_closedBall_zero_iff, norm_smul, mem_sphere_zero_iff_norm.1 θ.down.2,
    Real.norm_of_nonneg hd, mul_one]

/-- The function underlying `TauCeti.discGlue`. -/
private def discGlueFun (hd : 0 < d) (A : C(P × closedBall (0 : EuclideanSpace ℝ (Fin k)) d, Y))
    (B : C(P × (I × TopCat.diskBoundary.{u} k), Y)) (q : P × TopCat.disk.{u} k) : Y :=
  if h : ‖q.2.down.1‖ ≤ d then A (q.1, ⟨q.2.down.1, mem_closedBall_zero_iff.2 h⟩)
  else B (q.1, annulusParam d q.2, annulusDir hd ⟨q.2, (not_le.1 h).le⟩)

private theorem discGlueFun_of_norm_le (hd : 0 < d)
    (A : C(P × closedBall (0 : EuclideanSpace ℝ (Fin k)) d, Y))
    (B : C(P × (I × TopCat.diskBoundary.{u} k), Y)) (p : P) {w : TopCat.disk.{u} k}
    (hw : ‖w.down.1‖ ≤ d) :
    discGlueFun hd A B (p, w) = A (p, ⟨w.down.1, mem_closedBall_zero_iff.2 hw⟩) :=
  dite_eq_left hw

private theorem discGlueFun_of_le_norm (hd : 0 < d)
    (A : C(P × closedBall (0 : EuclideanSpace ℝ (Fin k)) d, Y))
    (B : C(P × (I × TopCat.diskBoundary.{u} k), Y))
    (hAB : ∀ p θ, B (p, 0, θ) = A (p, ⟨d • θ.down.1, norm_smul_diskBoundary_le hd.le θ⟩))
    (p : P) {w : TopCat.disk.{u} k} (hw : d ≤ ‖w.down.1‖) :
    discGlueFun hd A B (p, w) = B (p, annulusParam d w, annulusDir hd ⟨w, hw⟩) := by
  by_cases h : ‖w.down.1‖ ≤ d
  · -- On the seam both pieces are given by `A`.
    have hwd : ‖w.down.1‖ = d := le_antisymm h hw
    rw [discGlueFun_of_norm_le hd A B p h, annulusParam_of_norm_eq hwd, hAB]
    congr 2
    refine Subtype.ext ?_
    simp only [coe_annulusDir, ← hwd, smul_smul, mul_inv_cancel₀ (hd.trans_le hw).ne', one_smul]
  · exact dite_eq_right h

/-- Glue a map on the ball of radius `d` of the disc to a map on the annulus `d ≤ ‖w‖ ≤ 1`, given
in the coordinates `(s, θ)` of the point `(d + (1 - d) s) • θ`, when the two agree on the seam. -/
private def discGlue (hd : 0 < d) (A : C(P × closedBall (0 : EuclideanSpace ℝ (Fin k)) d, Y))
    (B : C(P × (I × TopCat.diskBoundary.{u} k), Y))
    (hAB : ∀ p θ, B (p, 0, θ) = A (p, ⟨d • θ.down.1, norm_smul_diskBoundary_le hd.le θ⟩)) :
    C(P × TopCat.disk.{u} k, Y) where
  toFun := discGlueFun hd A B
  continuous_toFun := by
    have hn : Continuous fun q : P × TopCat.disk.{u} k ↦ ‖q.2.down.1‖ :=
      continuous_norm.comp (continuous_subtype_val.comp (continuous_uliftDown.comp continuous_snd))
    have hs : ContinuousOn (discGlueFun hd A B) {q | ‖q.2.down.1‖ ≤ d} := by
      rw [continuousOn_iff_continuous_domRestrict]
      have he : domRestrict {q | ‖q.2.down.1‖ ≤ d} (discGlueFun hd A B) =
          fun q ↦ A (q.1.1, ⟨q.1.2.down.1, mem_closedBall_zero_iff.2 q.2⟩) :=
        funext fun q ↦ discGlueFun_of_norm_le hd A B _ q.2
      rw [he]
      exact A.continuous.comp (by fun_prop)
    have ht : ContinuousOn (discGlueFun hd A B) {q | d ≤ ‖q.2.down.1‖} := by
      rw [continuousOn_iff_continuous_domRestrict]
      have he : domRestrict {q | d ≤ ‖q.2.down.1‖} (discGlueFun hd A B) =
          fun q ↦ B (q.1.1, annulusParam d q.1.2, annulusDir hd ⟨q.1.2, q.2⟩) :=
        funext fun q ↦ discGlueFun_of_le_norm hd A B hAB _ q.2
      rw [he]
      have := continuous_annulusParam.{u} (k := k) (d := d)
      have := continuous_annulusDir.{u} (k := k) hd
      exact B.continuous.comp (by fun_prop)
    rw [← continuousOn_univ]
    convert hs.union_of_isClosed ht (isClosed_le hn continuous_const)
      (isClosed_le continuous_const hn)
    ext q
    simp [le_total]

private theorem discGlue_apply_of_norm_le (hd : 0 < d)
    (A : C(P × closedBall (0 : EuclideanSpace ℝ (Fin k)) d, Y))
    (B : C(P × (I × TopCat.diskBoundary.{u} k), Y))
    (hAB : ∀ p θ, B (p, 0, θ) = A (p, ⟨d • θ.down.1, norm_smul_diskBoundary_le hd.le θ⟩))
    (p : P) {w : TopCat.disk.{u} k} (hw : ‖w.down.1‖ ≤ d) :
    discGlue hd A B hAB (p, w) = A (p, ⟨w.down.1, mem_closedBall_zero_iff.2 hw⟩) :=
  discGlueFun_of_norm_le hd A B p hw

private theorem discGlue_apply_of_le_norm (hd : 0 < d)
    (A : C(P × closedBall (0 : EuclideanSpace ℝ (Fin k)) d, Y))
    (B : C(P × (I × TopCat.diskBoundary.{u} k), Y))
    (hAB : ∀ p θ, B (p, 0, θ) = A (p, ⟨d • θ.down.1, norm_smul_diskBoundary_le hd.le θ⟩))
    (p : P) {w : TopCat.disk.{u} k} (hw : d ≤ ‖w.down.1‖) :
    discGlue hd A B hAB (p, w) = B (p, annulusParam d w, annulusDir hd ⟨w, hw⟩) :=
  discGlueFun_of_le_norm hd A B hAB p hw

/-- A glued map takes values in a set containing all values of both pieces. -/
private theorem discGlue_mem (hd : 0 < d)
    (A : C(P × closedBall (0 : EuclideanSpace ℝ (Fin k)) d, Y))
    (B : C(P × (I × TopCat.diskBoundary.{u} k), Y))
    (hAB : ∀ p θ, B (p, 0, θ) = A (p, ⟨d • θ.down.1, norm_smul_diskBoundary_le hd.le θ⟩))
    {S : Set Y} (hA : ∀ q, A q ∈ S) (hB : ∀ q, B q ∈ S) (q : P × TopCat.disk.{u} k) :
    discGlue hd A B hAB q ∈ S := by
  rcases le_total ‖q.2.down.1‖ d with hw | hw
  · rw [discGlue_apply_of_norm_le hd A B hAB q.1 hw]
    exact hA _
  · rw [discGlue_apply_of_le_norm hd A B hAB q.1 hw]
    exact hB _

/-- On the boundary sphere, a glued map takes values in a set containing the values of the inner
piece on the unit sphere and of the outer piece on the outer circle `s = 1`. -/
private theorem discGlue_mem_of_norm_eq_one (hd : 0 < d)
    (A : C(P × closedBall (0 : EuclideanSpace ℝ (Fin k)) d, Y))
    (B : C(P × (I × TopCat.diskBoundary.{u} k), Y))
    (hAB : ∀ p θ, B (p, 0, θ) = A (p, ⟨d • θ.down.1, norm_smul_diskBoundary_le hd.le θ⟩))
    {S : Set Y} (hA : ∀ p (v : closedBall (0 : EuclideanSpace ℝ (Fin k)) d),
      ‖(v : EuclideanSpace ℝ (Fin k))‖ = 1 → A (p, v) ∈ S)
    (hB : ∀ p θ, B (p, 1, θ) ∈ S) (p : P) {w : TopCat.disk.{u} k} (hw : ‖w.down.1‖ = 1) :
    discGlue hd A B hAB (p, w) ∈ S := by
  by_cases h : ‖w.down.1‖ ≤ d
  · rw [discGlue_apply_of_norm_le hd A B hAB p h]
    exact hA _ _ hw
  · have hd₁ : d < 1 := hw ▸ not_le.1 h
    rw [discGlue_apply_of_le_norm hd A B hAB p (not_le.1 h).le,
      annulusParam_of_norm_eq_one hd₁ hw]
    exact hB _ _

end DiscGlue

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

private theorem norm_diskBoundaryInclusion (s : TopCat.diskBoundary.{u} k) :
    ‖(TopCat.diskBoundaryInclusion k s).down.1‖ = 1 :=
  (mem_range_diskBoundaryInclusion_iff _).1 (mem_range_self s)

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

include hd in
private theorem dPos : 0 < (d : ℝ) := hd

/-- The first stage for a chart `ψ` and an isometry `g`: on the small disc it is `χ ∘ g`, and on
the annulus it deforms the annulus of `χ ∘ g` to the retraction track of its inner circle. -/
private def chartStage : C(I × TopCat.disk.{u} k, M) :=
  discGlue (dPos hd)
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

/-- Every stage map takes values in `M_{c+ε}`. -/
private theorem chartStage_le (q : I × TopCat.disk.{u} k) :
    f (chartStage R hr hk hε hd ψ hball hf g q) ≤ c + ε := by
  rw [chartStage]
  refine discGlue_mem (S := {x | f x ≤ c + ε}) _ _ _ _ (fun q ↦ ?_) (fun q ↦ ?_) _
  · exact (OpenPartialHomeomorph.apply_morseCellMap_le hball hf hk hε
      ((g.norm_map _).trans_le ((mem_closedBall_zero_iff.1 q.2.2).trans d.2.2))).trans
      (le_add_of_nonneg_right hε)
  · exact le_of_mem_sublevel hε _

/-- Every stage map sends the boundary sphere into `M_{c-ε}`. -/
private theorem chartStage_boundary_le (t : I) (s : TopCat.diskBoundary.{u} k) :
    f (chartStage R hr hk hε hd ψ hball hf g (t, TopCat.diskBoundaryInclusion k s)) ≤ c - ε := by
  rw [chartStage]
  refine discGlue_mem_of_norm_eq_one (S := {x | f x ≤ c - ε}) _ _ _ _ (fun _ v hv ↦ ?_)
    (fun _ θ ↦ ?_) _ (norm_diskBoundaryInclusion s)
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
    rcases le_total ‖w.down.1‖ d with hw | hw
    · rw [chartStage, discGlue_apply_of_norm_le _ _ _ _ _ hw, cellMapComp_apply]
      simp
    · rw [chartStage, discGlue_apply_of_le_norm _ _ _ _ _ hw, cellMapComp_apply]
      simp only [ContinuousMap.coe_mk, ContinuousMap.HomotopyWith.apply_zero, coe_gAnnulus_apply,
        annulusRadius_smul_annulusDir (dPos hd) d.2.2 ⟨w, hw⟩]
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
  toFun p := ⟨G (p.1, ⟨(d : ℝ) • p.2.down.1, norm_smul_diskBoundary_le d.2.1 p.2⟩),
    hGd _ _ (by rw [norm_smul, mem_sphere_zero_iff_norm.1 p.2.down.2, Real.norm_of_nonneg d.2.1,
      mul_one])⟩
  continuous_toFun := by fun_prop
  map_zero_left θ := Subtype.ext (by simp [hG₀, coe_gAnnulus_apply])
  map_one_left θ := Subtype.ext (by simp [hG₁, coe_gAnnulus_apply])

private theorem coe_circleHomotopy_apply (p : I × TopCat.diskBoundary.{u} k) :
    (circleHomotopy hk hε hball₀ hball₁ hf₀ hf₁ g G hG₀ hG₁ hGd p : M) =
      G (p.1, ⟨(d : ℝ) • p.2.down.1, norm_smul_diskBoundary_le d.2.1 p.2⟩) :=
  (rfl)

/-- The second stage: move the small disc by `G`, together with the retraction tracks of its
boundary circles. -/
private def middleStage : C(I × TopCat.disk.{u} k, M) :=
  discGlue (dPos hd) G
    ⟨fun p ↦ (R.toHomotopy.retractionTrackHomotopy (ContinuousMap.id I)
      (circleHomotopy hk hε hball₀ hball₁ hf₀ hf₁ g G hG₀ hG₁ hGd) p : M), by fun_prop⟩
    fun t θ ↦ by
      simp only [ContinuousMap.coe_mk, ContinuousMap.Homotopy.retractionTrackHomotopy_apply,
        ContinuousMap.id_apply, ContinuousMap.Homotopy.apply_zero, coe_circleHomotopy_apply]

include hGf in
private theorem middleStage_le (q : I × TopCat.disk.{u} k) :
    f (middleStage R hk hε hd hball₀ hball₁ hf₀ hf₁ g G hG₀ hG₁ hGd q) ≤ c + ε := by
  rw [middleStage]
  exact discGlue_mem (S := {x | f x ≤ c + ε}) _ _ _ _ (fun q ↦ hGf _ _)
    (fun q ↦ le_of_mem_sublevel hε _) _

include hr in
private theorem middleStage_boundary_le (t : I) (s : TopCat.diskBoundary.{u} k) :
    f (middleStage R hk hε hd hball₀ hball₁ hf₀ hf₁ g G hG₀ hG₁ hGd
      (t, TopCat.diskBoundaryInclusion k s)) ≤ c - ε := by
  rw [middleStage]
  refine discGlue_mem_of_norm_eq_one (S := {x | f x ≤ c - ε}) _ _ _ _ (fun _ v hv ↦ ?_)
    (fun _ θ ↦ ?_) _ (norm_diskBoundaryInclusion s)
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
    rcases le_total ‖w.down.1‖ d with hw | hw
    · rw [middleStage, chartStage, ContinuousMap.curry_apply,
        discGlue_apply_of_norm_le _ _ _ _ _ hw, discGlue_apply_of_norm_le _ _ _ _ _ hw]
      simp [hG₀]
    · rw [middleStage, chartStage, ContinuousMap.curry_apply,
        discGlue_apply_of_le_norm _ _ _ _ _ hw, discGlue_apply_of_le_norm _ _ _ _ _ hw]
      simp
  map_one_left w := by
    rcases le_total ‖w.down.1‖ d with hw | hw
    · rw [middleStage, chartStage, ContinuousMap.curry_apply,
        discGlue_apply_of_norm_le _ _ _ _ _ hw, discGlue_apply_of_norm_le _ _ _ _ _ hw]
      simp [hG₁]
    · rw [middleStage, chartStage, ContinuousMap.curry_apply,
        discGlue_apply_of_le_norm _ _ _ _ _ hw, discGlue_apply_of_le_norm _ _ _ _ _ hw]
      simp
  prop' t := ⟨fun w ↦ middleStage_le R hk hε hd hball₀ hball₁ hf₀ hf₁ g G hG₀ hG₁ hGf hGd (t, w),
    fun s ↦ middleStage_boundary_le R hr hk hε hd hball₀ hball₁ hf₀ hf₁ g G hG₀ hG₁ hGd t s⟩

end Middle

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
  have hr : ∀ x, f ((sublevelInclusion f _ _ hab).comp r x).val ≤ c - ε := fun x ↦ by
    rw [ContinuousMap.comp_apply, coe_sublevelInclusion_apply]
    exact (r x).2
  -- Deform the annulus of `χ₁`, move the small disc with its tracks, and undo the annulus
  -- deformation for `χ₀ ∘ g`.
  let K := (chartStageHomotopy R.symm hr hk hε hd ψ₁ hball₁ hf₁ (.refl ℝ _)).trans
    ((middleStageHomotopy R.symm hr hk hε hd hball₀ hball₁ hf₀ hf₁ g G hG₀ hG₁ hGf hGd).trans
      (chartStageHomotopy R.symm hr hk hε hd ψ₀ hball₀ hf₀ g).symm)
  exact ⟨{ toFun p := ⟨K p, (K.prop p.1).1 p.2⟩
           continuous_toFun := K.continuous.subtype_mk _
           map_zero_left w := Subtype.ext ((K.apply_zero w).trans (by
             rw [cellMapComp_apply, OpenPartialHomeomorph.coe_morseCharacteristicMap_apply,
               LinearIsometryEquiv.coe_refl, id]))
           map_one_left w := Subtype.ext ((K.apply_one w).trans (by
             rw [cellMapComp_apply, TopCat.hom_comp, ContinuousMap.comp_apply,
               OpenPartialHomeomorph.coe_morseCharacteristicMap_apply,
               LinearIsometryEquiv.coe_diskMap_apply_down])) }, fun t s ↦ (K.prop t).2 s⟩

end Main

end TauCeti

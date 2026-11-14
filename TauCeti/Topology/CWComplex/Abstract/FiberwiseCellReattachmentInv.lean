/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.CWComplex.Abstract.FiberwiseCellAttachment
import TauCeti.Analysis.InnerProductSpace.LinearIsometry

/-!
# The inverse of a fiberwise reattachment map

Let `E : (P × A) ∪_{α₁} ⨆ᵢ (P × D^{k i}) → (P × A) ∪_{α₀} ⨆ᵢ (P × D^{k i})` be the fiberwise
reattachment map (`TauCeti.fiberwiseCellReattachment`) of self-maps `h i` of `P × D^{k i}` over `P`
and of homotopies `K i : χ₁ i ≃ χ₀ i ∘ (p, h i)` keeping the boundary spheres in `A`.
When each `h i (p, ·)` is a linear isometry `e i p` of the disc, as for the polar factors in
Milnor's comparison of two charts, `E` is a homotopy equivalence over `P` relative to `P × A`. Its
inverse (`TauCeti.fiberwiseCellReattachmentInv`) is the reattachment map of the inverse isometries
`(e i p)⁻¹` and of the reversed homotopies `(t, (p, x)) ↦ K i (1 - t, (p, (e i p)⁻¹ x))`, and both
composites are homotopic to the identity relative to `P × A` through maps over `P`
(`TauCeti.exists_homotopyRel_fiberwiseCellReattachment_comp_fiberwiseCellReattachmentInv`,
`TauCeti.exists_homotopyRel_fiberwiseCellReattachmentInv_comp_fiberwiseCellReattachment`). On the
`i`-th cell, `E` followed by its inverse is `x ↦ 4x` on the disc of radius `1/4`, while on the
annulus `1/4 ≤ ‖x‖` it runs out along `K i` and back. Contracting this out-and-back track, and then
undoing the radial push of radius `1/4`, gives the homotopy. The construction uses no left inverse
of the comparison map `Φ₀`.

The inverse is natural in the parameter space
(`TauCeti.fiberwiseCellReattachmentInv_comp_fiberwiseCellAttachmentMap`), and, like `E`, it is
compatible with the comparison maps up to a homotopy over `P` relative to `P × A`
(`TauCeti.fiberwiseCellReattachmentInvHomotopy`, from `Φ₁ ∘ E⁻¹` to `Φ₀`).

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Lemma 3.6 and Remark 3.3.
-/

public section

noncomputable section

open CategoryTheory Limits Set Metric unitInterval

universe u

namespace TauCeti

variable {P Y : Type u} [TopologicalSpace P] [TopologicalSpace Y] {A : Set Y} {ι : Type u}
  {k : ι → ℕ}

/-- The time `(1 - u) · min (3s) ((3 - 3s) / 2)`: for fixed `u` a tent in `s`, vanishing at both
ends, peaking at `s = 1/3`, and vanishing identically at `u = 1`. -/
private def reattachmentLoopTime (u s : I) : I :=
  projIcc 0 1 zero_le_one ((1 - (u : ℝ)) * min (3 * (s : ℝ)) ((3 - 3 * (s : ℝ)) / 2))

private theorem continuous_reattachmentLoopTime :
    Continuous fun q : I × I ↦ reattachmentLoopTime q.1 q.2 :=
  continuous_projIcc.comp ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
    ((continuous_const.mul (continuous_subtype_val.comp continuous_snd)).min
      ((continuous_const.sub (continuous_const.mul
        (continuous_subtype_val.comp continuous_snd))).div_const _)))

private theorem coe_reattachmentLoopTime (u s : I) :
    (reattachmentLoopTime u s : ℝ) = (1 - (u : ℝ)) * min (3 * (s : ℝ)) ((3 - 3 * (s : ℝ)) / 2) := by
  have hu₀ : 0 ≤ (u : ℝ) := u.2.1
  have hu₁ : (u : ℝ) ≤ 1 := u.2.2
  have hs₀ : 0 ≤ (s : ℝ) := s.2.1
  have hs₁ : (s : ℝ) ≤ 1 := s.2.2
  have hm₀ : 0 ≤ min (3 * (s : ℝ)) ((3 - 3 * (s : ℝ)) / 2) := le_min (by linarith) (by linarith)
  have hm₁ : min (3 * (s : ℝ)) ((3 - 3 * (s : ℝ)) / 2) ≤ 1 := by
    rcases le_or_gt (s : ℝ) (1 / 3) with h | h
    · exact (min_le_left _ _).trans (by linarith)
    · exact (min_le_right _ _).trans (by linarith)
  have h₀ : 0 ≤ (1 - (u : ℝ)) * min (3 * (s : ℝ)) ((3 - 3 * (s : ℝ)) / 2) :=
    mul_nonneg (by linarith) hm₀
  have h₁ : (1 - (u : ℝ)) * min (3 * (s : ℝ)) ((3 - 3 * (s : ℝ)) / 2) ≤ 1 :=
    (mul_le_of_le_one_left hm₀ (by linarith)).trans hm₁
  rw [reattachmentLoopTime, projIcc_of_mem _ ⟨h₀, h₁⟩]

private theorem reattachmentLoopTime_zero_right (u : I) : reattachmentLoopTime u 0 = 0 :=
  Subtype.ext (by rw [coe_reattachmentLoopTime]; norm_num)

private theorem reattachmentLoopTime_one_right (u : I) : reattachmentLoopTime u 1 = 0 :=
  Subtype.ext (by rw [coe_reattachmentLoopTime]; norm_num)

private theorem reattachmentLoopTime_one_left (s : I) : reattachmentLoopTime 1 s = 0 :=
  Subtype.ext (by rw [coe_reattachmentLoopTime]; norm_num)

/-- At `u = 0` and a point `w` of the annulus `1/4 ≤ ‖w‖`, the time is the tent `4‖w‖ - 1` on
`‖w‖ ≤ 1/2` and `2 - 2‖w‖` on `1/2 ≤ ‖w‖`, that is, `min (4‖w‖ - 1) (2 - 2‖w‖)`. -/
private theorem coe_reattachmentLoopTime_zero_annulusParam {n : ℕ} {w : TopCat.disk.{u} n}
    (hw : 1 / 4 ≤ ‖w.down.1‖) :
    (reattachmentLoopTime 0 (TopCat.annulusParam (1 / 4) w) : ℝ) =
      min (4 * ‖w.down.1‖ - 1) (2 - 2 * ‖w.down.1‖) := by
  have h := TopCat.add_one_sub_mul_annulusParam (by norm_num : (1 / 4 : ℝ) ≤ 1) hw
  rw [coe_reattachmentLoopTime, Icc.coe_zero, sub_zero, one_mul]
  congr 1 <;> linarith

variable (α : ∀ i, C(P × TopCat.diskBoundary.{u} (k i), A))

/-- The inclusion of the ball of radius `1/4` into the disk. -/
private def quarterBallInclusion (n : ℕ) :
    C(closedBall (0 : EuclideanSpace ℝ (Fin n)) (1 / 4), TopCat.disk.{u} n) :=
  ⟨fun v ↦ (ULift.up ⟨v.1, closedBall_subset_closedBall (by norm_num) v.2⟩ : TopCat.disk.{u} n),
    continuous_uliftUp.comp (continuous_subtype_val.subtype_mk _)⟩

@[simp]
private theorem coe_quarterBallInclusion_apply_down {n : ℕ}
    (v : closedBall (0 : EuclideanSpace ℝ (Fin n)) (1 / 4)) :
    ((quarterBallInclusion.{u} n v).down : EuclideanSpace ℝ (Fin n)) = v :=
  rfl

/-- The radial push of radius `1/4` at time `1` of the point `(1/4) θ` of the disk is `θ`. -/
private theorem diskRadialPush_one_quarterBallInclusion {n : ℕ} (θ : TopCat.diskBoundary.{u} n) :
    TopCat.diskRadialPush.{u} n (by norm_num : (0 : ℝ) ≤ 1 / 4) (1, quarterBallInclusion n
      ⟨(1 / 4 : ℝ) • θ.down.1, TopCat.smul_diskBoundary_mem_closedBall (by norm_num) θ⟩) =
      TopCat.diskBoundaryInclusion n θ := by
  have hθ := TopCat.smul_diskBoundary_mem_closedBall.{u} (by norm_num : (0 : ℝ) ≤ 1 / 4) θ
  have hx : ‖((quarterBallInclusion.{u} n ⟨(1 / 4 : ℝ) • θ.down.1, hθ⟩).down :
      EuclideanSpace ℝ (Fin n))‖ ≤ 1 / 4 := by
    rw [coe_quarterBallInclusion_apply_down]
    exact mem_closedBall_zero_iff.1 hθ
  refine ULift.ext (Subtype.ext ?_)
  rw [TopCat.coe_diskRadialPush_one_of_norm_le _ hx, TopCat.coe_diskBoundaryInclusion_apply_down,
    coe_quarterBallInclusion_apply_down, smul_smul]
  norm_num

/-- The inner piece of `TauCeti.reattachmentLoop`: `(p, v) ↦ (p, 4v)` in the `i`-th cell, written
with the radial push of radius `1/4`. -/
private def reattachmentLoopInner (i : ι) :
    C((I × P) × closedBall (0 : EuclideanSpace ℝ (Fin (k i))) (1 / 4), fiberwiseCellAttachment α) :=
  ⟨fun q ↦ fiberwiseCellAttachmentCell α i (q.1.2, TopCat.diskRadialPush (k i)
      (by norm_num : (0 : ℝ) ≤ 1 / 4) (1, quarterBallInclusion (k i) q.2)),
    (fiberwiseCellAttachmentCell α i).hom.continuous.comp
      ((continuous_snd.comp continuous_fst).prodMk
      ((TopCat.diskRadialPush (k i) (by norm_num : (0 : ℝ) ≤ 1 / 4)).continuous.comp
        (continuous_const.prodMk ((quarterBallInclusion (k i)).continuous.comp continuous_snd))))⟩

variable {α} in
/-- The outer piece of `TauCeti.reattachmentLoop`: `(s, θ)` goes along the track `H` of `θ` for the
time `reattachmentLoopTime u s`, read in `P × A`. -/
private def reattachmentLoopOuter (i : ι) (H : C(I × (P × TopCat.diskBoundary.{u} (k i)), A)) :
    C((I × P) × (I × TopCat.diskBoundary.{u} (k i)), fiberwiseCellAttachment α) :=
  ⟨fun q ↦ fiberwiseCellAttachmentIncl α
      (q.1.2, H (reattachmentLoopTime q.1.1 q.2.1, (q.1.2, q.2.2))),
    (fiberwiseCellAttachmentIncl α).hom.continuous.comp ((continuous_snd.comp continuous_fst).prodMk
      (H.continuous.comp ((continuous_reattachmentLoopTime.comp
        ((continuous_fst.comp continuous_fst).prodMk (continuous_fst.comp continuous_snd))).prodMk
        ((continuous_snd.comp continuous_fst).prodMk (continuous_snd.comp continuous_snd)))))⟩

/-- **The loop homotopy on a cell.** For a track `H : I × (P × ∂D^{k i}) → A` starting at the
attaching map `α i`, this is the map `I × (P × D^{k i}) → (P × A) ∪_α ⨆ᵢ (P × D^{k i})` sending
`(u, (p, w))` to the point `(p, 4w)` of the `i`-th cell when `‖w‖ ≤ 1/4`, and, when
`‖w‖ = 1/4 + 3s/4` with `s ∈ [0, 1]`, to the point `(p, H((1 - u) τ(s), (p, w/‖w‖)))` of `P × A`,
where `τ(s) = min (3s) ((3 - 3s)/2)`. At `u = 1` it is the `i`-th cell composed with the radial
push of radius `1/4`. -/
private def reattachmentLoop (i : ι) (H : C(I × (P × TopCat.diskBoundary.{u} (k i)), A))
    (hH : ∀ p s, H (0, (p, s)) = α i (p, s)) :
    C(I × (P × TopCat.disk.{u} (k i)), fiberwiseCellAttachment α) :=
  (TopCat.discGlue (by norm_num : (0 : ℝ) < 1 / 4) (reattachmentLoopInner α i)
    (reattachmentLoopOuter i H) fun q θ ↦ by
      simp only [reattachmentLoopOuter, reattachmentLoopInner, ContinuousMap.coe_mk,
        reattachmentLoopTime_zero_right, hH, diskRadialPush_one_quarterBallInclusion]
      exact (fiberwiseCellAttachmentCell_diskBoundaryInclusion α i q.2 θ).symm).comp
    ⟨fun q ↦ ((q.1, q.2.1), q.2.2),
      (continuous_fst.prodMk (continuous_fst.comp continuous_snd)).prodMk
        (continuous_snd.comp continuous_snd)⟩

variable {α}

section Loop

variable {i : ι} {H : C(I × (P × TopCat.diskBoundary.{u} (k i)), A)}
  {hH : ∀ p s, H (0, (p, s)) = α i (p, s)}

private theorem reattachmentLoop_of_norm_le (t : I) (p : P) {w : TopCat.disk.{u} (k i)}
    (hw : ‖w.down.1‖ ≤ 1 / 4) :
    reattachmentLoop α i H hH (t, (p, w)) = fiberwiseCellAttachmentCell α i
      (p, TopCat.diskRadialPush (k i) (by norm_num : (0 : ℝ) ≤ 1 / 4) (1, w)) := by
  rw [reattachmentLoop, ContinuousMap.comp_apply]
  exact TopCat.discGlue_apply_of_norm_le _ _ _ _ (t, p) hw

private theorem reattachmentLoop_of_le_norm (t : I) (p : P) {w : TopCat.disk.{u} (k i)}
    (hw : 1 / 4 ≤ ‖w.down.1‖) :
    reattachmentLoop α i H hH (t, (p, w)) = fiberwiseCellAttachmentIncl α
      (p, H (reattachmentLoopTime t (TopCat.annulusParam (1 / 4) w),
        (p, TopCat.annulusDir (by norm_num) ⟨w, hw⟩))) := by
  rw [reattachmentLoop, ContinuousMap.comp_apply]
  exact TopCat.discGlue_apply_of_le_norm _ _ _ _ (t, p) hw

/-- On the boundary spheres the loop homotopy is the attaching map at all times. -/
private theorem reattachmentLoop_diskBoundaryInclusion (t : I) (p : P)
    (s : TopCat.diskBoundary.{u} (k i)) :
    reattachmentLoop α i H hH (t, (p, TopCat.diskBoundaryInclusion (k i) s)) =
      fiberwiseCellAttachmentIncl α (p, α i (p, s)) := by
  have hw : 1 / 4 ≤ ‖(TopCat.diskBoundaryInclusion (k i) s).down.1‖ := by
    rw [TopCat.norm_diskBoundaryInclusion]
    norm_num
  rw [reattachmentLoop_of_le_norm t p hw, TopCat.annulusDir_diskBoundaryInclusion,
    TopCat.annulusParam_of_norm_eq_one (by norm_num) (TopCat.norm_diskBoundaryInclusion s),
    reattachmentLoopTime_one_right, hH]

/-- At time `1` the loop homotopy is the `i`-th cell composed with the radial push of radius
`1/4`. -/
private theorem reattachmentLoop_one (p : P) (w : TopCat.disk.{u} (k i)) :
    reattachmentLoop α i H hH (1, (p, w)) = fiberwiseCellAttachmentCell α i
      (p, TopCat.diskRadialPush (k i) (by norm_num : (0 : ℝ) ≤ 1 / 4) (1, w)) := by
  rcases le_total ‖w.down.1‖ (1 / 4) with hw | hw
  · exact reattachmentLoop_of_norm_le 1 p hw
  · rw [reattachmentLoop_of_le_norm 1 p hw, reattachmentLoopTime_one_left, hH,
      ← fiberwiseCellAttachmentCell_diskBoundaryInclusion, TopCat.diskBoundaryInclusion_annulusDir]

/-- The loop homotopy lies over `P`. -/
private theorem fiberwiseCellAttachmentProj_reattachmentLoop (t : I) (p : P)
    (w : TopCat.disk.{u} (k i)) :
    fiberwiseCellAttachmentProj α (reattachmentLoop α i H hH (t, (p, w))) = p := by
  rcases le_total ‖w.down.1‖ (1 / 4) with hw | hw
  · rw [reattachmentLoop_of_norm_le t p hw, fiberwiseCellAttachmentProj_fiberwiseCellAttachmentCell]
  · rw [reattachmentLoop_of_le_norm t p hw, fiberwiseCellAttachmentProj_fiberwiseCellAttachmentIncl]

end Loop

/-- **The loop homotopy followed by the radial unpush.** For a track `H` of the attaching map
`α i`, a homotopy over `P` from the loop homotopy at time `0` to the `i`-th cell, constant on the
boundary spheres. -/
private theorem exists_reattachmentLoopCylinder (i : ι)
    (H : C(I × (P × TopCat.diskBoundary.{u} (k i)), A)) (hH : ∀ p s, H (0, (p, s)) = α i (p, s)) :
    ∃ C : C(I × (P × TopCat.disk.{u} (k i)), fiberwiseCellAttachment α),
      (∀ x, C (0, x) = reattachmentLoop α i H hH (0, x)) ∧
      (∀ x, C (1, x) = fiberwiseCellAttachmentCell α i x) ∧
      (∀ t p s, C (t, (p, TopCat.diskBoundaryInclusion (k i) s)) =
        fiberwiseCellAttachmentIncl α (p, α i (p, s))) ∧
      ∀ t x, fiberwiseCellAttachmentProj α (C (t, x)) = x.1 := by
  have hr : (0 : ℝ) ≤ 1 / 4 := by norm_num
  let F₀ : C(P × TopCat.disk.{u} (k i), fiberwiseCellAttachment α) :=
    ⟨fun x ↦ reattachmentLoop α i H hH (0, x),
      (reattachmentLoop α i H hH).continuous.comp (continuous_const.prodMk continuous_id)⟩
  let F₁ : C(P × TopCat.disk.{u} (k i), fiberwiseCellAttachment α) :=
    ⟨fun x ↦ fiberwiseCellAttachmentCell α i (x.1, TopCat.diskRadialPush (k i) hr (1, x.2)),
      (fiberwiseCellAttachmentCell α i).hom.continuous.comp (continuous_fst.prodMk
        ((TopCat.diskRadialPush (k i) hr).continuous.comp
          (continuous_const.prodMk continuous_snd)))⟩
  let Θ₁ : F₀.Homotopy F₁ :=
    { toFun := reattachmentLoop α i H hH
      continuous_toFun := (reattachmentLoop α i H hH).continuous
      map_zero_left := fun _ ↦ rfl
      map_one_left := fun x ↦ reattachmentLoop_one x.1 x.2 }
  let Θ₂ : F₁.Homotopy (fiberwiseCellAttachmentCell α i).hom :=
    { toFun := fun q ↦ fiberwiseCellAttachmentCell α i
        (q.2.1, TopCat.diskRadialPush (k i) hr (σ q.1, q.2.2))
      continuous_toFun := (fiberwiseCellAttachmentCell α i).hom.continuous.comp
        ((continuous_fst.comp continuous_snd).prodMk
          ((TopCat.diskRadialPush (k i) hr).continuous.comp
            ((continuous_symm.comp continuous_fst).prodMk (continuous_snd.comp continuous_snd))))
      map_zero_left := fun x ↦ by simp [F₁]
      map_one_left := fun x ↦ by simp [TopCat.diskRadialPush_zero] }
  refine ⟨(Θ₁.trans Θ₂).toContinuousMap, fun x ↦ (Θ₁.trans Θ₂).apply_zero x,
    fun x ↦ (Θ₁.trans Θ₂).apply_one x, fun t p s ↦ ?_, fun t x ↦ ?_⟩
  · rw [ContinuousMap.Homotopy.coe_toContinuousMap, ContinuousMap.Homotopy.trans_apply]
    split_ifs
    · exact reattachmentLoop_diskBoundaryInclusion (hH := hH) _ p s
    · -- Unfold the local homotopy `Θ₂`: the cell composed with the reversed radial push.
      change fiberwiseCellAttachmentCell α i (p, TopCat.diskRadialPush (k i) hr (_, _)) = _
      rw [TopCat.diskRadialPush_diskBoundaryInclusion (by norm_num) (by norm_num),
        fiberwiseCellAttachmentCell_diskBoundaryInclusion]
  · rw [ContinuousMap.Homotopy.coe_toContinuousMap, ContinuousMap.Homotopy.trans_apply]
    split_ifs
    · exact fiberwiseCellAttachmentProj_reattachmentLoop (hH := hH) _ x.1 x.2
    · exact fiberwiseCellAttachmentProj_fiberwiseCellAttachmentCell α i _


section Composite

variable (α₀ α₁ : ∀ i, C(P × TopCat.diskBoundary.{u} (k i), A))
  (χ₀ χ₁ : ∀ i, C(P × TopCat.disk.{u} (k i), Y))
  (hχ₀ : ∀ i p s, χ₀ i (p, TopCat.diskBoundaryInclusion (k i) s) = α₀ i (p, s))
  (hχ₁ : ∀ i p s, χ₁ i (p, TopCat.diskBoundaryInclusion (k i) s) = α₁ i (p, s))
  (h h' : ∀ i, C(P × TopCat.disk.{u} (k i), TopCat.disk.{u} (k i)))
  (hh : ∀ i p, MapsTo (fun w ↦ h i (p, w)) (range (TopCat.diskBoundaryInclusion (k i)))
    (range (TopCat.diskBoundaryInclusion (k i))))
  (hh' : ∀ i p, MapsTo (fun w ↦ h' i (p, w)) (range (TopCat.diskBoundaryInclusion (k i)))
    (range (TopCat.diskBoundaryInclusion (k i))))
  (K : ∀ i, (χ₁ i).Homotopy ((χ₀ i).comp (ContinuousMap.fst.prodMk (h i))))
  (hK : ∀ i t p s, K i (t, (p, TopCat.diskBoundaryInclusion (k i) s)) ∈ A)
  (K' : ∀ i, (χ₀ i).Homotopy ((χ₁ i).comp (ContinuousMap.fst.prodMk (h' i))))
  (hK' : ∀ i t p s, K' i (t, (p, TopCat.diskBoundaryInclusion (k i) s)) ∈ A)
  (e : ∀ i, P → EuclideanSpace ℝ (Fin (k i)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (k i)))
  (he : ∀ i p w, ((h i (p, w)).down : EuclideanSpace ℝ (Fin (k i))) = e i p w.down)
  (he' : ∀ i p w, ((h' i (p, w)).down : EuclideanSpace ℝ (Fin (k i))) = (e i p).symm w.down)
  (hKK' : ∀ i t x, K' i (t, x) = K i (σ t, (x.1, h' i x)))

/-- The track `(t, (p, s)) ↦ K i (t, (p, s))` of the boundary spheres in `A`. -/
private def reattachmentTrack (i : ι) : C(I × (P × TopCat.diskBoundary.{u} (k i)), A) :=
  ⟨fun q ↦ ⟨K i (q.1, (q.2.1, TopCat.diskBoundaryInclusion (k i) q.2.2)), hK i _ _ _⟩,
    ((K i).continuous.comp (continuous_fst.prodMk ((continuous_fst.comp continuous_snd).prodMk
      ((TopCat.diskBoundaryInclusion (k i)).hom.continuous.comp
        (continuous_snd.comp continuous_snd))))).subtype_mk _⟩

private theorem reattachmentTrack_apply (i : ι) (q : I × (P × TopCat.diskBoundary.{u} (k i))) :
    reattachmentTrack χ₀ χ₁ h K hK i q =
      ⟨K i (q.1, (q.2.1, TopCat.diskBoundaryInclusion (k i) q.2.2)), hK i _ _ _⟩ :=
  rfl

include hχ₁ in
private theorem reattachmentTrack_zero (i : ι) (p : P) (s : TopCat.diskBoundary.{u} (k i)) :
    reattachmentTrack χ₀ χ₁ h K hK i (0, (p, s)) = α₁ i (p, s) :=
  Subtype.ext ((K i).apply_zero _ |>.trans (hχ₁ i p s))

include he he' hKK' in
/-- On the `i`-th cell, the composite of the two reattachment maps is the loop homotopy at time
`0`, built on the track of the boundary spheres along `K i`. -/
private theorem fiberwiseCellReattachment_fiberwiseCellReattachment_fiberwiseCellAttachmentCell
    (i : ι) (p : P) (w : TopCat.disk.{u} (k i)) :
    fiberwiseCellReattachment α₁ α₀ χ₁ χ₀ hχ₁ hχ₀ h' hh' K' hK'
        (fiberwiseCellReattachment α₀ α₁ χ₀ χ₁ hχ₀ hχ₁ h hh K hK
          (fiberwiseCellAttachmentCell α₁ i (p, w))) =
      reattachmentLoop α₁ i (reattachmentTrack χ₀ χ₁ h K hK i)
        (reattachmentTrack_zero α₁ χ₀ χ₁ hχ₁ h K hK i) (0, (p, w)) := by
  -- the norm of `h i (p, v)` is that of `v`
  have hnorm : ∀ v : TopCat.disk.{u} (k i), ‖(h i (p, v)).down.1‖ = ‖v.down.1‖ := fun v ↦ by
    rw [he, LinearIsometryEquiv.norm_map]
  rcases le_total ‖w.down.1‖ (1 / 2) with hw₂ | hw₂
  · rw [fiberwiseCellReattachment_fiberwiseCellAttachmentCell_of_norm_le α₀ α₁ χ₀ χ₁ hχ₀ hχ₁ h hh K
      hK i p hw₂ (TopCat.coe_reattachmentRadial_of_norm_le hw₂)]
    have hv : ‖(h i (p, TopCat.reattachmentRadial w)).down.1‖ = 2 * ‖w.down.1‖ := by
      rw [hnorm, TopCat.coe_reattachmentRadial_of_norm_le hw₂, norm_smul, Real.norm_two]
    rcases le_total ‖w.down.1‖ (1 / 4) with hw₄ | hw₄
    · -- On the ball of radius `1/4` the composite is `x ↦ 4x`.
      have hv₂ : ‖(h i (p, TopCat.reattachmentRadial w)).down.1‖ ≤ 1 / 2 := by
        rw [hv]
        linarith
      rw [fiberwiseCellReattachment_fiberwiseCellAttachmentCell_of_norm_le α₁ α₀ χ₁ χ₀ hχ₁ hχ₀ h'
        hh' K' hK' i p hv₂ (TopCat.coe_reattachmentRadial_of_norm_le hv₂),
        reattachmentLoop_of_norm_le 0 p hw₄]
      congr 2
      refine ULift.ext (Subtype.ext ?_)
      simp only [he', he, TopCat.coe_reattachmentRadial_of_norm_le hv₂,
        TopCat.coe_reattachmentRadial_of_norm_le hw₂,
        TopCat.coe_diskRadialPush_one_of_norm_le _ hw₄, map_smul,
        LinearIsometryEquiv.symm_apply_apply, smul_smul]
      norm_num
    · -- On the annulus `1/4 ≤ ‖x‖ ≤ 1/2` the composite runs out along `K i` and back.
      have hv₂ : 1 / 2 ≤ ‖(h i (p, TopCat.reattachmentRadial w)).down.1‖ := by
        rw [hv]
        linarith
      have ht := coe_reattachmentLoopTime_zero_annulusParam hw₄
      rw [min_eq_left (by linarith)] at ht
      rw [fiberwiseCellReattachment_fiberwiseCellAttachmentCell_of_le_norm α₁ α₀ χ₁ χ₀ hχ₁ hχ₀ h'
        hh' K' hK' i p hv₂ (t := σ (reattachmentLoopTime 0 (TopCat.annulusParam (1 / 4) w)))
        (by rw [coe_symm_eq, ht, hv]; ring) (s := TopCat.annulusDir (by norm_num) ⟨_, hv₂⟩)
        (TopCat.coe_annulusDir _ _), reattachmentLoop_of_le_norm 0 p hw₄]
      congr 2
      rw [reattachmentTrack_apply, Subtype.mk.injEq, hKK', symm_symm]
      congr 3
      refine ULift.ext (Subtype.ext ?_)
      simp only [he', he, TopCat.coe_diskBoundaryInclusion_apply_down, TopCat.coe_annulusDir,
        TopCat.coe_reattachmentRadial_of_norm_le hw₂, LinearIsometryEquiv.norm_map, norm_smul,
        Real.norm_two, map_smul, LinearIsometryEquiv.symm_apply_apply, smul_smul]
      congr 1
      field_simp
  · -- On the annulus `1/2 ≤ ‖x‖` the composite runs back along `K i`.
    have ht := coe_reattachmentLoopTime_zero_annulusParam (by linarith : 1 / 4 ≤ ‖w.down.1‖)
    rw [min_eq_right (by linarith)] at ht
    rw [fiberwiseCellReattachment_fiberwiseCellAttachmentCell_of_le_norm α₀ α₁ χ₀ χ₁ hχ₀ hχ₁ h hh K
      hK i p hw₂ (t := reattachmentLoopTime 0 (TopCat.annulusParam (1 / 4) w)) ht
      (s := TopCat.annulusDir (by norm_num : (0 : ℝ) < 1 / 4) ⟨w, by linarith⟩)
      (TopCat.coe_annulusDir _ _),
      fiberwiseCellReattachment_fiberwiseCellAttachmentIncl,
      reattachmentLoop_of_le_norm 0 p (by linarith), reattachmentTrack_apply]

include he he' hKK' in
/-- **Reattaching back along the reversed homotopy undoes a reattachment, over `P` and relative to
`P × A`.** Let `h i (p, ·)` act on the disc by linear isometries `e i p`, let `h' i (p, ·)` act by
their inverses, and let `K' i (t, (p, x)) = K i (1 - t, (p, h' i (p, x)))`. Then the fiberwise
reattachment map of `(h, K)` followed by that of `(h', K')` is homotopic to the identity relative to
`P × A`, through maps over `P`. -/
private theorem exists_homotopyRel_fiberwiseCellReattachment_comp_fiberwiseCellReattachment_id :
    ∃ G : (fiberwiseCellReattachment α₀ α₁ χ₀ χ₁ hχ₀ hχ₁ h hh K hK ≫
        fiberwiseCellReattachment α₁ α₀ χ₁ χ₀ hχ₁ hχ₀ h' hh' K' hK').hom.HomotopyRel
        (ContinuousMap.id _) (range (fiberwiseCellAttachmentIncl α₁)),
      ∀ t y, fiberwiseCellAttachmentProj α₁ (G (t, y)) = fiberwiseCellAttachmentProj α₁ y := by
  choose C hC₀ hC₁ hCb hCp using fun i ↦ exists_reattachmentLoopCylinder (α := α₁) i
    (reattachmentTrack χ₀ χ₁ h K hK i) (reattachmentTrack_zero α₁ χ₀ χ₁ hχ₁ h K hK i)
  have hE : ∀ x, (fiberwiseCellReattachment α₀ α₁ χ₀ χ₁ hχ₀ hχ₁ h hh K hK ≫
      fiberwiseCellReattachment α₁ α₀ χ₁ χ₀ hχ₁ hχ₀ h' hh' K' hK').hom
        (fiberwiseCellAttachmentIncl α₁ x) = fiberwiseCellAttachmentIncl α₁ x := fun x ↦ by
    rw [TopCat.hom_comp, ContinuousMap.comp_apply,
      fiberwiseCellReattachment_fiberwiseCellAttachmentIncl,
      fiberwiseCellReattachment_fiberwiseCellAttachmentIncl]
  refine ⟨{ toFun := fiberwiseCellAttachmentCylinderDesc α₁
              ((fiberwiseCellAttachmentIncl α₁).hom.comp ContinuousMap.snd) C hCb
            continuous_toFun := (fiberwiseCellAttachmentCylinderDesc α₁ _ C hCb).continuous
            map_zero_left := fun y ↦ ?_
            map_one_left := fun y ↦ ?_
            prop' := ?_ }, fun t y ↦ ?_⟩
  · refine fiberwiseCellAttachment_induction α₁ (fun x ↦ ?_) (fun i x ↦ ?_) y
    · exact (fiberwiseCellAttachmentCylinderDesc_fiberwiseCellAttachmentIncl α₁ _ C hCb 0 x).trans
        (hE x).symm
    · refine (fiberwiseCellAttachmentCylinderDesc_fiberwiseCellAttachmentCell α₁ _ C hCb 0 i
        x).trans ?_
      rw [hC₀, TopCat.hom_comp, ContinuousMap.comp_apply,
        fiberwiseCellReattachment_fiberwiseCellReattachment_fiberwiseCellAttachmentCell α₀ α₁ χ₀ χ₁
          hχ₀ hχ₁ h h' hh hh' K hK K' hK' e he he' hKK' i x.1 x.2]
  · refine fiberwiseCellAttachment_induction α₁ (fun x ↦ ?_) (fun i x ↦ ?_) y
    · exact fiberwiseCellAttachmentCylinderDesc_fiberwiseCellAttachmentIncl α₁ _ C hCb 1 x
    · exact (fiberwiseCellAttachmentCylinderDesc_fiberwiseCellAttachmentCell α₁ _ C hCb 1 i
        x).trans (hC₁ i x)
  · rintro t _ ⟨x, rfl⟩
    exact (fiberwiseCellAttachmentCylinderDesc_fiberwiseCellAttachmentIncl α₁ _ C hCb t x).trans
      (hE x).symm
  · refine fiberwiseCellAttachment_induction α₁ (fun x ↦ ?_) (fun i x ↦ ?_) y
    · exact congrArg (fiberwiseCellAttachmentProj α₁)
        (fiberwiseCellAttachmentCylinderDesc_fiberwiseCellAttachmentIncl α₁ _ C hCb t x)
    · exact (congrArg (fiberwiseCellAttachmentProj α₁)
        (fiberwiseCellAttachmentCylinderDesc_fiberwiseCellAttachmentCell α₁ _ C hCb t i x)).trans
        ((hCp i t x).trans (fiberwiseCellAttachmentProj_fiberwiseCellAttachmentCell α₁ i x).symm)

end Composite

section Inv

variable (α₀ α₁ : ∀ i, C(P × TopCat.diskBoundary.{u} (k i), A))
  (χ₀ χ₁ : ∀ i, C(P × TopCat.disk.{u} (k i), Y))
  (hχ₀ : ∀ i p s, χ₀ i (p, TopCat.diskBoundaryInclusion (k i) s) = α₀ i (p, s))
  (hχ₁ : ∀ i p s, χ₁ i (p, TopCat.diskBoundaryInclusion (k i) s) = α₁ i (p, s))
  (h : ∀ i, C(P × TopCat.disk.{u} (k i), TopCat.disk.{u} (k i)))
  (hh : ∀ i p, MapsTo (fun w ↦ h i (p, w)) (range (TopCat.diskBoundaryInclusion (k i)))
    (range (TopCat.diskBoundaryInclusion (k i))))
  (K : ∀ i, (χ₁ i).Homotopy ((χ₀ i).comp (ContinuousMap.fst.prodMk (h i))))
  (hK : ∀ i t p s, K i (t, (p, TopCat.diskBoundaryInclusion (k i) s)) ∈ A)
  (e : ∀ i, P → EuclideanSpace ℝ (Fin (k i)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (k i)))
  (he : ∀ i p w, ((h i (p, w)).down : EuclideanSpace ℝ (Fin (k i))) = e i p w.down)

include h he in
/-- The family `(p, w) ↦ (e i p)⁻¹ w` of inverse isometries of the disc. It is continuous because
`p ↦ e i p v` is, being `p ↦ c • h i (p, c⁻¹ v)` for `c = ‖v‖ + 1`
(`TauCeti.continuous_linearIsometryEquiv_symm_apply`). -/
private def fiberwiseDiskInv (i : ι) : C(P × TopCat.disk.{u} (k i), TopCat.disk.{u} (k i)) where
  toFun x := (ULift.up ⟨(e i x.1).symm x.2.down.1, by
    rw [mem_closedBall_zero_iff, LinearIsometryEquiv.norm_map]
    exact mem_closedBall_zero_iff.1 x.2.down.2⟩ : TopCat.disk.{u} (k i))
  continuous_toFun := by
    have hcont : ∀ v, Continuous fun p ↦ e i p v := fun v ↦ by
      have hc : (0 : ℝ) < ‖v‖ + 1 := by positivity
      have hu : (‖v‖ + 1)⁻¹ • v ∈ closedBall (0 : EuclideanSpace ℝ (Fin (k i))) 1 := by
        rw [mem_closedBall_zero_iff, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hc.le),
          inv_mul_le_iff₀ hc]
        linarith
      have hcu : Continuous fun p ↦ e i p ((‖v‖ + 1)⁻¹ • v) :=
        (continuous_subtype_val.comp (continuous_uliftDown.comp ((h i).continuous.comp
          (continuous_id.prodMk continuous_const)))).congr fun p ↦ he i p (ULift.up ⟨_, hu⟩)
      exact (hcu.const_smul (‖v‖ + 1)).congr fun p ↦ by
        rw [Pi.smul_apply, ← map_smul, smul_inv_smul₀ hc.ne']
    exact continuous_uliftUp.comp (((continuous_linearIsometryEquiv_symm_apply hcont).comp
      (continuous_fst.prodMk (continuous_subtype_val.comp
        (continuous_uliftDown.comp continuous_snd)))).subtype_mk _)

private theorem coe_fiberwiseDiskInv_apply_down (i : ι) (x : P × TopCat.disk.{u} (k i)) :
    ((fiberwiseDiskInv h e he i x).down : EuclideanSpace ℝ (Fin (k i))) = (e i x.1).symm x.2.down :=
  rfl

private theorem apply_fiberwiseDiskInv (i : ι) (p : P) (w : TopCat.disk.{u} (k i)) :
    h i (p, fiberwiseDiskInv h e he i (p, w)) = w :=
  ULift.ext (Subtype.ext (by rw [he, coe_fiberwiseDiskInv_apply_down,
    LinearIsometryEquiv.apply_symm_apply]))

private theorem fiberwiseDiskInv_apply (i : ι) (p : P) (w : TopCat.disk.{u} (k i)) :
    fiberwiseDiskInv h e he i (p, h i (p, w)) = w :=
  ULift.ext (Subtype.ext (by rw [coe_fiberwiseDiskInv_apply_down, he,
    LinearIsometryEquiv.symm_apply_apply]))

private theorem mapsTo_fiberwiseDiskInv (i : ι) (p : P) :
    MapsTo (fun w ↦ fiberwiseDiskInv h e he i (p, w)) (range (TopCat.diskBoundaryInclusion (k i)))
      (range (TopCat.diskBoundaryInclusion (k i))) := by
  rintro _ ⟨s, rfl⟩
  rw [mem_range_diskBoundaryInclusion_iff, coe_fiberwiseDiskInv_apply_down,
    LinearIsometryEquiv.norm_map]
  exact TopCat.norm_diskBoundaryInclusion s

/-- The reversed homotopy `(t, (p, x)) ↦ K i (1 - t, (p, (e i p)⁻¹ x))` from `χ₀ i` to
`χ₁ i ∘ (p, (e i p)⁻¹)`. -/
private def fiberwiseReversedHomotopy (i : ι) :
    (χ₀ i).Homotopy ((χ₁ i).comp (ContinuousMap.fst.prodMk (fiberwiseDiskInv h e he i))) where
  toFun q := K i (σ q.1, (q.2.1, fiberwiseDiskInv h e he i q.2))
  continuous_toFun := (K i).continuous.comp ((continuous_symm.comp continuous_fst).prodMk
    ((continuous_fst.comp continuous_snd).prodMk
      ((fiberwiseDiskInv h e he i).continuous.comp continuous_snd)))
  map_zero_left x := by
    rw [symm_zero, (K i).apply_one, ContinuousMap.comp_apply, ContinuousMap.prod_eval,
      ContinuousMap.fst_apply, apply_fiberwiseDiskInv]
  map_one_left x := by
    rw [symm_one, (K i).apply_zero, ContinuousMap.comp_apply, ContinuousMap.prod_eval,
      ContinuousMap.fst_apply]

private theorem fiberwiseReversedHomotopy_apply (i : ι) (t : I)
    (x : P × TopCat.disk.{u} (k i)) :
    fiberwiseReversedHomotopy χ₀ χ₁ h K e he i (t, x) =
      K i (σ t, (x.1, fiberwiseDiskInv h e he i x)) :=
  rfl

include hK in
private theorem fiberwiseReversedHomotopy_mem (i : ι) (t : I) (p : P)
    (s : TopCat.diskBoundary.{u} (k i)) :
    fiberwiseReversedHomotopy χ₀ χ₁ h K e he i
      (t, (p, TopCat.diskBoundaryInclusion (k i) s)) ∈ A := by
  obtain ⟨s', hs'⟩ := mapsTo_fiberwiseDiskInv h e he i p ⟨s, rfl⟩
  rw [fiberwiseReversedHomotopy_apply]
  simp only at hs'
  rw [← hs']
  exact hK i _ p s'

/-- **The inverse of a fiberwise reattachment map** along isometries of the discs. When `h i (p, ·)`
is a linear isometry `e i p` of the disc for every `p`, this is the fiberwise reattachment map
`(P × A) ∪_{α₀} ⨆ᵢ (P × D^{k i}) → (P × A) ∪_{α₁} ⨆ᵢ (P × D^{k i})` of the inverse isometries
`(e i p)⁻¹` and the reversed homotopies `(t, (p, x)) ↦ K i (1 - t, (p, (e i p)⁻¹ x))` from `χ₀ i`
to `χ₁ i ∘ (p, (e i p)⁻¹)`. It is a homotopy inverse of `TauCeti.fiberwiseCellReattachment` over
`P`, relative to `P × A`
(`TauCeti.exists_homotopyRel_fiberwiseCellReattachment_comp_fiberwiseCellReattachmentInv`,
`TauCeti.exists_homotopyRel_fiberwiseCellReattachmentInv_comp_fiberwiseCellReattachment`). -/
def fiberwiseCellReattachmentInv : fiberwiseCellAttachment α₀ ⟶ fiberwiseCellAttachment α₁ :=
  fiberwiseCellReattachment α₁ α₀ χ₁ χ₀ hχ₁ hχ₀ (fiberwiseDiskInv h e he)
    (mapsTo_fiberwiseDiskInv h e he) (fiberwiseReversedHomotopy χ₀ χ₁ h K e he)
    (fiberwiseReversedHomotopy_mem χ₀ χ₁ h K hK e he)

/-- The inverse of a fiberwise reattachment map is the identity on `P × A`. -/
@[simp]
theorem fiberwiseCellReattachmentInv_fiberwiseCellAttachmentIncl (x : P × A) :
    fiberwiseCellReattachmentInv α₀ α₁ χ₀ χ₁ hχ₀ hχ₁ h K hK e he
        (fiberwiseCellAttachmentIncl α₀ x) = fiberwiseCellAttachmentIncl α₁ x :=
  fiberwiseCellReattachment_fiberwiseCellAttachmentIncl _ _ _ _ _ _ _ _ _ _ x

/-- The inverse of a fiberwise reattachment map lies over `P`. -/
@[simp]
theorem fiberwiseCellAttachmentProj_fiberwiseCellReattachmentInv
    (y : fiberwiseCellAttachment α₀) :
    fiberwiseCellAttachmentProj α₁
        (fiberwiseCellReattachmentInv α₀ α₁ χ₀ χ₁ hχ₀ hχ₁ h K hK e he y) =
      fiberwiseCellAttachmentProj α₀ y :=
  fiberwiseCellAttachmentProj_fiberwiseCellReattachment _ _ _ _ _ _ _ _ _ _ y

/-- On the disc of radius `1/2` of the `i`-th cell over `p`, the inverse of a fiberwise
reattachment map is `x ↦ (e i p)⁻¹ (2x)`, read in the `i`-th cell over `p`. -/
theorem fiberwiseCellReattachmentInv_fiberwiseCellAttachmentCell_of_norm_le (i : ι) (p : P)
    {w v : TopCat.disk.{u} (k i)} (hw : ‖w.down.1‖ ≤ 1 / 2)
    (hv : v.down.1 = (e i p).symm ((2 : ℝ) • w.down.1)) :
    fiberwiseCellReattachmentInv α₀ α₁ χ₀ χ₁ hχ₀ hχ₁ h K hK e he
        (fiberwiseCellAttachmentCell α₀ i (p, w)) =
      fiberwiseCellAttachmentCell α₁ i (p, v) := by
  rw [fiberwiseCellReattachmentInv, fiberwiseCellReattachment_fiberwiseCellAttachmentCell_of_norm_le
    _ _ _ _ _ _ _ _ _ _ i p hw (TopCat.coe_reattachmentRadial_of_norm_le hw)]
  refine congrArg (fun v ↦ fiberwiseCellAttachmentCell α₁ i (p, v)) (ULift.ext (Subtype.ext ?_))
  rw [coe_fiberwiseDiskInv_apply_down, TopCat.coe_reattachmentRadial_of_norm_le hw, hv]

/-- Outside the disc of radius `1/2` of the `i`-th cell over `p`, the inverse of a fiberwise
reattachment map is `x ↦ K i (2‖x‖ - 1, (p, (e i p)⁻¹ (x/‖x‖)))`, read in `P × A`. -/
theorem fiberwiseCellReattachmentInv_fiberwiseCellAttachmentCell_of_le_norm (i : ι) (p : P)
    {w : TopCat.disk.{u} (k i)} (hw : 1 / 2 ≤ ‖w.down.1‖) {t : I}
    (ht : (t : ℝ) = 2 * ‖w.down.1‖ - 1) {s : TopCat.diskBoundary.{u} (k i)}
    (hs : s.down.1 = (e i p).symm (‖w.down.1‖⁻¹ • w.down.1)) :
    fiberwiseCellReattachmentInv α₀ α₁ χ₀ χ₁ hχ₀ hχ₁ h K hK e he
        (fiberwiseCellAttachmentCell α₀ i (p, w)) =
      fiberwiseCellAttachmentIncl α₁ (p, ⟨K i (t, (p, TopCat.diskBoundaryInclusion (k i) s)),
        hK i t p s⟩) := by
  rw [fiberwiseCellReattachmentInv, fiberwiseCellReattachment_fiberwiseCellAttachmentCell_of_le_norm
    _ _ _ _ _ _ _ _ _ _ i p hw (t := σ t) (by rw [coe_symm_eq, ht]; ring)
    (s := TopCat.annulusDir (by norm_num : (0 : ℝ) < 1 / 2) ⟨w, hw⟩) (TopCat.coe_annulusDir _ _)]
  refine congrArg (fun a ↦ fiberwiseCellAttachmentIncl α₁ (p, a)) (Subtype.ext ?_)
  rw [Subtype.coe_mk, fiberwiseReversedHomotopy_apply, symm_symm]
  refine congrArg (fun v ↦ K i (t, (p, v))) (ULift.ext (Subtype.ext ?_))
  rw [coe_fiberwiseDiskInv_apply_down, TopCat.coe_diskBoundaryInclusion_apply_down,
    TopCat.coe_annulusDir, TopCat.coe_diskBoundaryInclusion_apply_down, hs]

include he in
/-- **`E` followed by its inverse is homotopic to the identity over `P`, relative to `P × A`.** -/
theorem exists_homotopyRel_fiberwiseCellReattachment_comp_fiberwiseCellReattachmentInv :
    ∃ G : (fiberwiseCellReattachment α₀ α₁ χ₀ χ₁ hχ₀ hχ₁ h hh K hK ≫
        fiberwiseCellReattachmentInv α₀ α₁ χ₀ χ₁ hχ₀ hχ₁ h K hK e he).hom.HomotopyRel
        (ContinuousMap.id _) (range (fiberwiseCellAttachmentIncl α₁)),
      ∀ t y, fiberwiseCellAttachmentProj α₁ (G (t, y)) = fiberwiseCellAttachmentProj α₁ y :=
  exists_homotopyRel_fiberwiseCellReattachment_comp_fiberwiseCellReattachment_id α₀ α₁ χ₀ χ₁ hχ₀ hχ₁
    h (fiberwiseDiskInv h e he) hh (mapsTo_fiberwiseDiskInv h e he) K hK
    (fiberwiseReversedHomotopy χ₀ χ₁ h K e he)
    (fiberwiseReversedHomotopy_mem χ₀ χ₁ h K hK e he) e he
    (fun i p w ↦ coe_fiberwiseDiskInv_apply_down h e he i (p, w))
    (fiberwiseReversedHomotopy_apply χ₀ χ₁ h K e he)

include he in
/-- **The inverse followed by `E` is homotopic to the identity over `P`, relative to `P × A`.** -/
theorem exists_homotopyRel_fiberwiseCellReattachmentInv_comp_fiberwiseCellReattachment :
    ∃ G : (fiberwiseCellReattachmentInv α₀ α₁ χ₀ χ₁ hχ₀ hχ₁ h K hK e he ≫
        fiberwiseCellReattachment α₀ α₁ χ₀ χ₁ hχ₀ hχ₁ h hh K hK).hom.HomotopyRel
        (ContinuousMap.id _) (range (fiberwiseCellAttachmentIncl α₀)),
      ∀ t y, fiberwiseCellAttachmentProj α₀ (G (t, y)) = fiberwiseCellAttachmentProj α₀ y :=
  exists_homotopyRel_fiberwiseCellReattachment_comp_fiberwiseCellReattachment_id α₁ α₀ χ₁ χ₀ hχ₁ hχ₀
    (fiberwiseDiskInv h e he) h (mapsTo_fiberwiseDiskInv h e he) hh
    (fiberwiseReversedHomotopy χ₀ χ₁ h K e he)
    (fiberwiseReversedHomotopy_mem χ₀ χ₁ h K hK e he) K hK (fun i p ↦ (e i p).symm)
    (fun i p w ↦ coe_fiberwiseDiskInv_apply_down h e he i (p, w))
    (fun i p w ↦ by rw [LinearIsometryEquiv.symm_symm]; exact he i p w)
    fun i t x ↦ by rw [fiberwiseReversedHomotopy_apply, symm_symm, fiberwiseDiskInv_apply]

/-- **`Φ₁ ∘ E⁻¹` is homotopic to `Φ₀` over `P`, relative to `P × A`.** The homotopy from the
inverse of a fiberwise reattachment map followed by the comparison map `Φ₁` to the comparison map
`Φ₀`: it is `TauCeti.fiberwiseCellReattachmentHomotopy` for the reattachment data of the inverse. It
fixes the points of `P × A` and lies over `P` at all times
(`TauCeti.fst_fiberwiseCellReattachmentInvHomotopy`). -/
def fiberwiseCellReattachmentInvHomotopy :
    (fiberwiseCellReattachmentInv α₀ α₁ χ₀ χ₁ hχ₀ hχ₁ h K hK e he ≫
        fiberwiseCellComparison α₁ χ₁ hχ₁).hom.HomotopyRel
      (fiberwiseCellComparison α₀ χ₀ hχ₀).hom (range (fiberwiseCellAttachmentIncl α₀)) :=
  fiberwiseCellReattachmentHomotopy α₁ α₀ χ₁ χ₀ hχ₁ hχ₀ (fiberwiseDiskInv h e he)
    (mapsTo_fiberwiseDiskInv h e he) (fiberwiseReversedHomotopy χ₀ χ₁ h K e he)
    (fiberwiseReversedHomotopy_mem χ₀ χ₁ h K hK e he)

/-- The homotopy from `Φ₁ ∘ E⁻¹` to `Φ₀` is constant on `P × A`. -/
@[simp]
theorem fiberwiseCellReattachmentInvHomotopy_fiberwiseCellAttachmentIncl (t : I) (x : P × A) :
    fiberwiseCellReattachmentInvHomotopy α₀ α₁ χ₀ χ₁ hχ₀ hχ₁ h K hK e he
        (t, fiberwiseCellAttachmentIncl α₀ x) = (x.1, (x.2 : Y)) :=
  fiberwiseCellReattachmentHomotopy_fiberwiseCellAttachmentIncl _ _ _ _ _ _ _ _ _ _ t x

/-- The homotopy from `Φ₁ ∘ E⁻¹` to `Φ₀` lies over `P` at all times. -/
@[simp]
theorem fst_fiberwiseCellReattachmentInvHomotopy (t : I) (y : fiberwiseCellAttachment α₀) :
    (fiberwiseCellReattachmentInvHomotopy α₀ α₁ χ₀ χ₁ hχ₀ hχ₁ h K hK e he (t, y)).1 =
      fiberwiseCellAttachmentProj α₀ y :=
  fst_fiberwiseCellReattachmentHomotopy _ _ _ _ _ _ _ _ _ _ t y

section BaseChange

variable {P' : Type u} [TopologicalSpace P'] (g : C(P', P))
  (α₀' α₁' : ∀ i, C(P' × TopCat.diskBoundary.{u} (k i), A))
  (χ₀' χ₁' : ∀ i, C(P' × TopCat.disk.{u} (k i), Y))
  (hχ₀' : ∀ i p s, χ₀' i (p, TopCat.diskBoundaryInclusion (k i) s) = α₀' i (p, s))
  (hχ₁' : ∀ i p s, χ₁' i (p, TopCat.diskBoundaryInclusion (k i) s) = α₁' i (p, s))
  (h' : ∀ i, C(P' × TopCat.disk.{u} (k i), TopCat.disk.{u} (k i)))
  (K' : ∀ i, (χ₁' i).Homotopy ((χ₀' i).comp (ContinuousMap.fst.prodMk (h' i))))
  (hK' : ∀ i t p s, K' i (t, (p, TopCat.diskBoundaryInclusion (k i) s)) ∈ A)
  (e' : ∀ i, P' → EuclideanSpace ℝ (Fin (k i)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (k i)))
  (he' : ∀ i p w, ((h' i (p, w)).down : EuclideanSpace ℝ (Fin (k i))) = e' i p w.down)
  (hα₀ : ∀ i p s, α₀' i (p, s) = α₀ i (g p, s)) (hα₁ : ∀ i p s, α₁' i (p, s) = α₁ i (g p, s))

/-- **The inverse of a fiberwise reattachment map is natural in the parameter space.** For data
restricted along a continuous map `g : P' → P`, with isometries `e' i p = e i (g p)` and homotopies
`K' i (t, (p, x)) = K i (t, (g p, x))`, the inverse over `P'` followed by the map of fiberwise
adjunction spaces over `g` is the map over `g` followed by the inverse over `P`. -/
theorem fiberwiseCellReattachmentInv_comp_fiberwiseCellAttachmentMap
    (he'e : ∀ i p, e' i p = e i (g p))
    (hK'K : ∀ i t p x, K' i (t, (p, x)) = K i (t, (g p, x))) :
    fiberwiseCellReattachmentInv α₀' α₁' χ₀' χ₁' hχ₀' hχ₁' h' K' hK' e' he' ≫
        fiberwiseCellAttachmentMap g α₁ α₁' hα₁ =
      fiberwiseCellAttachmentMap g α₀ α₀' hα₀ ≫
        fiberwiseCellReattachmentInv α₀ α₁ χ₀ χ₁ hχ₀ hχ₁ h K hK e he := by
  have hd : ∀ i p x, fiberwiseDiskInv h' e' he' i (p, x) = fiberwiseDiskInv h e he i (g p, x) :=
    fun i p x ↦ ULift.ext (Subtype.ext (by
      rw [coe_fiberwiseDiskInv_apply_down, coe_fiberwiseDiskInv_apply_down, he'e]))
  exact fiberwiseCellReattachment_comp_fiberwiseCellAttachmentMap g α₁ α₀ χ₁ χ₀ hχ₁ hχ₀ _
    (mapsTo_fiberwiseDiskInv h e he) _ (fiberwiseReversedHomotopy_mem χ₀ χ₁ h K hK e he)
    α₁' α₀' χ₁' χ₀' hχ₁' hχ₀' _ (mapsTo_fiberwiseDiskInv h' e' he') _
    (fiberwiseReversedHomotopy_mem χ₀' χ₁' h' K' hK' e' he') hα₁ hα₀ hd fun i t p x ↦ by
      rw [fiberwiseReversedHomotopy_apply, fiberwiseReversedHomotopy_apply, hK'K, hd]

end BaseChange

end Inv

end TauCeti

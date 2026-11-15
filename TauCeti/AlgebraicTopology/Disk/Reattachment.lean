/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Disk.Annulus

/-!
# The disc-to-cylinder map of a cell reattachment

Comparing two attachments of a cell along homotopic attaching maps uses a map from the disc
`D^k` to the cylinder `I × D^k` (Milnor, *Morse Theory*, Lemma 3.6). Its time coordinate
`TauCeti.TopCat.reattachmentTime` is `1` on the disc of radius `1/2` and `2 - 2‖x‖` on the annulus
`1/2 ≤ ‖x‖`, and its radial coordinate `TauCeti.TopCat.reattachmentRadial` is `2x` on the disc of
radius `1/2` and `x / ‖x‖` on the annulus. Reading a homotopy `K : I × D^k → Y` of characteristic
maps along `x ↦ (reattachmentTime x, reattachmentRadial x)` gives the composite of a reattachment
map with the comparison map of the target attachment.

The straight-line homotopy `TauCeti.TopCat.reattachmentPath` in the convex cylinder joins this map
to `x ↦ (0, x)` and fixes the boundary sphere, where both maps are `x ↦ (0, x)`. Read through `K`,
it is the homotopy relative to the attached base from that composite to the comparison map of the
source attachment.

Following a reattachment map by the reattachment map along the reversed homotopy shrinks the cell
to the disc of radius `1/4` and runs the boundary homotopy forwards and then backwards in the
annulus `1/4 ≤ ‖x‖ ≤ 1`. Read in a cell with a collar of radius `1/2` attached along the boundary
homotopy, this composite is the map `x ↦ 2x` for `‖x‖ ≤ 1/2` and `x ↦ (3/2 - ‖x‖) • x/‖x‖` for
`1/2 ≤ ‖x‖`. The radial homotopy `TauCeti.TopCat.reattachmentFoldPath` joins it to `x ↦ x/2`,
which is the identity of the cell, and fixes the boundary sphere: it folds the collar away.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Lemma 3.6.
-/

public section

noncomputable section

open Metric unitInterval

universe u

namespace TauCeti.TopCat

variable {k : ℕ}

/-- The radial part `x ↦ x / max(1/2, ‖x‖)` of the disc-to-cylinder map of a reattachment: it is
`2x` on the disc of radius `1/2` and `x / ‖x‖` outside it. It is the end of the radial push
`TauCeti.TopCat.diskRadialPush` with radius `1/2`. -/
def reattachmentRadial (w : TopCat.disk.{u} k) : TopCat.disk.{u} k :=
  diskRadialPush k (by norm_num : (0 : ℝ) ≤ 1 / 2) (1, w)

theorem reattachmentRadial_def (w : TopCat.disk.{u} k) :
    reattachmentRadial w = diskRadialPush k (by norm_num : (0 : ℝ) ≤ 1 / 2) (1, w) :=
  (rfl)

theorem continuous_reattachmentRadial : Continuous (reattachmentRadial.{u} (k := k)) :=
  (diskRadialPush k _).continuous.comp (continuous_const.prodMk continuous_id)

theorem coe_reattachmentRadial_of_norm_le {w : TopCat.disk.{u} k} (hw : ‖w.down.1‖ ≤ 1 / 2) :
    (reattachmentRadial w).down.1 = (2 : ℝ) • w.down.1 := by
  rw [reattachmentRadial, coe_diskRadialPush_one_of_norm_le _ hw]
  norm_num

theorem coe_reattachmentRadial_of_le_norm {w : TopCat.disk.{u} k} (hw : 1 / 2 ≤ ‖w.down.1‖) :
    (reattachmentRadial w).down.1 = ‖w.down.1‖⁻¹ • w.down.1 :=
  coe_diskRadialPush_one_of_le_norm (by norm_num) hw

/-- On the annulus `1/2 ≤ ‖x‖`, the radial part of `x` is its direction `x / ‖x‖` on the boundary
sphere. -/
theorem reattachmentRadial_of_le_norm {w : TopCat.disk.{u} k} (hw : 1 / 2 ≤ ‖w.down.1‖) :
    reattachmentRadial w = TopCat.diskBoundaryInclusion k (annulusDir (by norm_num) ⟨w, hw⟩) :=
  (diskBoundaryInclusion_annulusDir _ ⟨w, hw⟩).symm

/-- The point `(1/2) • θ` of the disc, for `θ` on the boundary sphere, has radial part `θ`. -/
theorem reattachmentRadial_half_smul (θ : TopCat.diskBoundary.{u} k)
    (hθ : (1 / 2 : ℝ) • θ.down.1 ∈ closedBall (0 : EuclideanSpace ℝ (Fin k)) 1) :
    reattachmentRadial (ULift.up ⟨(1 / 2 : ℝ) • θ.down.1, hθ⟩) =
      TopCat.diskBoundaryInclusion k θ := by
  have hθ' : ‖(1 / 2 : ℝ) • θ.down.1‖ ≤ 1 / 2 :=
    mem_closedBall_zero_iff.1 (smul_diskBoundary_mem_closedBall (by norm_num) θ)
  refine ULift.ext (Subtype.ext ?_)
  rw [coe_reattachmentRadial_of_norm_le (w := ULift.up ⟨(1 / 2 : ℝ) • θ.down.1, hθ⟩) hθ',
    smul_smul, mul_one_div_cancel two_ne_zero, one_smul]
  exact (TopCat.coe_diskBoundaryInclusion_apply_down _ _).symm

/-- The time part `x ↦ 2 - 2‖x‖`, clamped to `[0, 1]`, of the disc-to-cylinder map of a
reattachment: the reversed radial parameter of the annulus `1/2 ≤ ‖x‖`. It is `1` on the disc of
radius `1/2` and `0` on the boundary sphere. -/
def reattachmentTime (w : TopCat.disk.{u} k) : I :=
  σ (annulusParam (1 / 2) w)

theorem reattachmentTime_def (w : TopCat.disk.{u} k) :
    reattachmentTime w = σ (annulusParam (1 / 2) w) :=
  (rfl)

theorem continuous_reattachmentTime : Continuous (reattachmentTime.{u} (k := k)) :=
  continuous_symm.comp continuous_annulusParam

theorem reattachmentTime_of_norm_le {w : TopCat.disk.{u} k} (hw : ‖w.down.1‖ ≤ 1 / 2) :
    reattachmentTime w = 1 := by
  rw [reattachmentTime, annulusParam_of_norm_le (by norm_num) hw, symm_zero]

theorem coe_reattachmentTime_of_le_norm {w : TopCat.disk.{u} k} (hw : 1 / 2 ≤ ‖w.down.1‖) :
    (reattachmentTime w : ℝ) = 2 - 2 * ‖w.down.1‖ := by
  have h := add_one_sub_mul_annulusParam (by norm_num : (1 / 2 : ℝ) ≤ 1) hw
  rw [reattachmentTime, coe_symm_eq]
  linarith

@[simp]
theorem reattachmentTime_diskBoundaryInclusion (s : TopCat.diskBoundary.{u} k) :
    reattachmentTime (TopCat.diskBoundaryInclusion k s) = 0 := by
  rw [reattachmentTime, annulusParam_of_norm_eq_one (by norm_num) (norm_diskBoundaryInclusion s),
    symm_one]

/-- The straight-line homotopy in the cylinder `I × D^k` from
`x ↦ (reattachmentTime x, reattachmentRadial x)` at time `0` to `x ↦ (0, x)` at time `1`. Its disc
coordinate is the radial push `TauCeti.TopCat.diskRadialPush` with radius `1/2`, run backwards. -/
def reattachmentPath (p : TopCat.disk.{u} k × I) : I × TopCat.disk.{u} k :=
  (⟨(1 - (p.2 : ℝ)) * reattachmentTime p.1, mul_mem (symm p.2).2 (reattachmentTime p.1).2⟩,
    diskRadialPush k (by norm_num : (0 : ℝ) ≤ 1 / 2) (σ p.2, p.1))

theorem coe_fst_reattachmentPath (p : TopCat.disk.{u} k × I) :
    ((reattachmentPath p).1 : ℝ) = (1 - (p.2 : ℝ)) * reattachmentTime p.1 :=
  (rfl)

theorem snd_reattachmentPath (p : TopCat.disk.{u} k × I) :
    (reattachmentPath p).2 = diskRadialPush k (by norm_num : (0 : ℝ) ≤ 1 / 2) (σ p.2, p.1) :=
  (rfl)

theorem continuous_reattachmentPath : Continuous (reattachmentPath.{u} (k := k)) := by
  have hs : Continuous fun p : TopCat.disk.{u} k × I ↦ (p.2 : ℝ) :=
    continuous_subtype_val.comp continuous_snd
  exact .prodMk ((((continuous_const.sub hs).mul (continuous_subtype_val.comp
    (continuous_reattachmentTime.comp continuous_fst))).subtype_mk _))
    ((diskRadialPush k _).continuous.comp
      ((continuous_symm.comp continuous_snd).prodMk continuous_fst))

@[simp]
theorem reattachmentPath_zero (w : TopCat.disk.{u} k) :
    reattachmentPath (w, 0) = (reattachmentTime w, reattachmentRadial w) := by
  refine Prod.ext (Subtype.ext ?_) ?_ <;> simp [reattachmentPath, reattachmentRadial]

@[simp]
theorem reattachmentPath_one (w : TopCat.disk.{u} k) : reattachmentPath (w, 1) = (0, w) := by
  refine Prod.ext (Subtype.ext ?_) ?_ <;> simp [reattachmentPath]

@[simp]
theorem reattachmentPath_diskBoundaryInclusion (s : TopCat.diskBoundary.{u} k) (t : I) :
    reattachmentPath (TopCat.diskBoundaryInclusion k s, t) =
      (0, TopCat.diskBoundaryInclusion k s) := by
  refine Prod.ext (Subtype.ext ?_) ?_
  · simp [reattachmentPath, reattachmentTime_diskBoundaryInclusion]
  · exact diskRadialPush_diskBoundaryInclusion (by norm_num) (by norm_num) _ s

section Fold

/-- The radial scale factor of `TauCeti.TopCat.reattachmentFoldPath` at time `s` and radius `r`. -/
private def reattachmentFoldScale (s r : ℝ) : ℝ :=
  (1 - s) * min 2 ((3 / 2 - r) / max r (1 / 2)) + s / 2

private theorem reattachmentFoldScale_nonneg {s r : ℝ} (hs : s ∈ I) (hr : r ≤ 1) :
    0 ≤ reattachmentFoldScale s r := by
  have : 0 ≤ min 2 ((3 / 2 - r) / max r (1 / 2)) :=
    le_min zero_le_two (div_nonneg (by linarith) (by positivity))
  unfold reattachmentFoldScale
  nlinarith [hs.1, hs.2]

private theorem reattachmentFoldScale_mul_le {s r : ℝ} (hs : s ∈ I) (hr₀ : 0 ≤ r) (hr : r ≤ 1) :
    reattachmentFoldScale s r * r ≤ 1 := by
  set φ := min 2 ((3 / 2 - r) / max r (1 / 2))
  have hφr : φ * r ≤ 1 := by
    rcases le_total r (1 / 2) with h | h
    · nlinarith [min_le_left 2 ((3 / 2 - r) / max r (1 / 2))]
    · have hle : φ ≤ (3 / 2 - r) / r := (min_le_right _ _).trans_eq (by rw [max_eq_left h])
      have : φ * r ≤ 3 / 2 - r := by
        rwa [le_div_iff₀ (by linarith)] at hle
      linarith
  unfold reattachmentFoldScale
  nlinarith [hs.1, hs.2]

/-- The radial homotopy of the disc from the map `x ↦ 2x` for `‖x‖ ≤ 1/2` and
`x ↦ (3/2 - ‖x‖) • x/‖x‖` for `1/2 ≤ ‖x‖`, at time `0`, to the map `x ↦ x/2`, at time `1`. Every
stage sends the boundary sphere to the sphere of radius `1/2` by `x ↦ x/2`. -/
def reattachmentFoldPath (q : I × TopCat.disk.{u} k) : TopCat.disk.{u} k :=
  ULift.up ⟨reattachmentFoldScale q.1 ‖q.2.down.1‖ • q.2.down.1, by
    have hr := mem_closedBall_zero_iff.1 q.2.down.2
    rw [mem_closedBall_zero_iff, norm_smul,
      Real.norm_of_nonneg (reattachmentFoldScale_nonneg q.1.2 hr)]
    exact reattachmentFoldScale_mul_le q.1.2 (norm_nonneg _) hr⟩

theorem continuous_reattachmentFoldPath : Continuous (reattachmentFoldPath.{u} (k := k)) := by
  have hx : Continuous fun q : I × TopCat.disk.{u} k ↦ (q.2.down.1 : EuclideanSpace ℝ (Fin k)) :=
    continuous_subtype_val.comp (continuous_uliftDown.comp continuous_snd)
  have hr := continuous_norm.comp hx
  have hs : Continuous fun q : I × TopCat.disk.{u} k ↦ (q.1 : ℝ) :=
    continuous_subtype_val.comp continuous_fst
  have hm : Continuous fun q : I × TopCat.disk.{u} k ↦ reattachmentFoldScale q.1 ‖q.2.down.1‖ :=
    ((continuous_const.sub hs).mul (continuous_const.min ((continuous_const.sub hr).div
      (hr.max continuous_const) fun q ↦ (lt_max_of_lt_right (by norm_num)).ne'))).add
      (hs.div_const _)
  exact continuous_uliftUp.comp ((hm.smul hx).subtype_mk _)

/-- At time `0`, the fold path is `x ↦ 2x` on the disc of radius `1/2`. -/
theorem coe_reattachmentFoldPath_zero_of_norm_le {w : TopCat.disk.{u} k}
    (hw : ‖w.down.1‖ ≤ 1 / 2) : (reattachmentFoldPath (0, w)).down.1 = (2 : ℝ) • w.down.1 := by
  have : 2 ≤ (3 / 2 - ‖w.down.1‖) / max ‖w.down.1‖ (1 / 2) := by
    rw [max_eq_right hw, le_div_iff₀ (by norm_num)]
    linarith
  simp only [reattachmentFoldPath, reattachmentFoldScale, Set.Icc.coe_zero, min_eq_left this]
  norm_num

/-- At time `0`, the fold path is `x ↦ (3/2 - ‖x‖) • x/‖x‖` outside the disc of radius `1/2`. -/
theorem coe_reattachmentFoldPath_zero_of_le_norm {w : TopCat.disk.{u} k}
    (hw : 1 / 2 ≤ ‖w.down.1‖) :
    (reattachmentFoldPath (0, w)).down.1 = ((3 / 2 - ‖w.down.1‖) / ‖w.down.1‖) • w.down.1 := by
  have : (3 / 2 - ‖w.down.1‖) / ‖w.down.1‖ ≤ 2 := by
    rw [div_le_iff₀ (by linarith)]
    linarith
  simp only [reattachmentFoldPath, reattachmentFoldScale, Set.Icc.coe_zero, max_eq_left hw,
    min_eq_right this]
  norm_num

/-- At time `1`, the fold path is `x ↦ x/2`. -/
theorem coe_reattachmentFoldPath_one (w : TopCat.disk.{u} k) :
    (reattachmentFoldPath (1, w)).down.1 = (1 / 2 : ℝ) • w.down.1 := by
  simp only [reattachmentFoldPath, reattachmentFoldScale, Set.Icc.coe_one]
  norm_num

/-- On the boundary sphere, the fold path is `x ↦ x/2` at all times. -/
theorem coe_reattachmentFoldPath_diskBoundaryInclusion (t : I) (s : TopCat.diskBoundary.{u} k) :
    (reattachmentFoldPath (t, TopCat.diskBoundaryInclusion k s)).down.1 =
      (1 / 2 : ℝ) • (TopCat.diskBoundaryInclusion k s).down.1 := by
  have : min (2 : ℝ) ((3 / 2 - 1) / max 1 (1 / 2)) = 1 / 2 := by norm_num
  simp only [reattachmentFoldPath, reattachmentFoldScale, norm_diskBoundaryInclusion, this]
  ring_nf

end Fold

end TauCeti.TopCat

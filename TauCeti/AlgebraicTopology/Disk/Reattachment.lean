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

Composing two reattachment maps reparametrizes the disc radially. The straight-line homotopy
`TauCeti.TopCat.composeRadialHomotopy` joins the radial map sending the radii `1/4` and `1/2` to
`1/2` and `3/4` to the identity and fixes the boundary sphere.

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

theorem coe_reattachmentRadial_of_norm_le {w : TopCat.disk.{u} k} (hw : ‖w.down.val‖ ≤ 1 / 2) :
    (reattachmentRadial w).down.val = (2 : ℝ) • w.down.val := by
  rw [reattachmentRadial, coe_diskRadialPush_one_of_norm_le _ hw]
  norm_num

theorem coe_reattachmentRadial_of_le_norm {w : TopCat.disk.{u} k} (hw : 1 / 2 ≤ ‖w.down.val‖) :
    (reattachmentRadial w).down.val = ‖w.down.val‖⁻¹ • w.down.val :=
  coe_diskRadialPush_one_of_le_norm (by norm_num) hw

/-- On the annulus `1/2 ≤ ‖x‖`, the radial part of `x` is its direction `x / ‖x‖` on the boundary
sphere. -/
theorem reattachmentRadial_of_le_norm {w : TopCat.disk.{u} k} (hw : 1 / 2 ≤ ‖w.down.val‖) :
    reattachmentRadial w = TopCat.diskBoundaryInclusion k (annulusDir (by norm_num) ⟨w, hw⟩) :=
  (diskBoundaryInclusion_annulusDir _ ⟨w, hw⟩).symm

/-- The point `(1/2) • θ` of the disc, for `θ` on the boundary sphere, has radial part `θ`. -/
theorem reattachmentRadial_half_smul (θ : TopCat.diskBoundary.{u} k)
    (hθ : (1 / 2 : ℝ) • θ.down.val ∈ closedBall (0 : EuclideanSpace ℝ (Fin k)) 1) :
    reattachmentRadial (ULift.up ⟨(1 / 2 : ℝ) • θ.down.val, hθ⟩) =
      TopCat.diskBoundaryInclusion k θ := by
  have hθ' : ‖(1 / 2 : ℝ) • θ.down.val‖ ≤ 1 / 2 :=
    mem_closedBall_zero_iff.1 (smul_diskBoundary_mem_closedBall (by norm_num) θ)
  refine ULift.ext (Subtype.ext ?_)
  rw [coe_reattachmentRadial_of_norm_le (w := ULift.up ⟨(1 / 2 : ℝ) • θ.down.val, hθ⟩) hθ',
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

theorem reattachmentTime_of_norm_le {w : TopCat.disk.{u} k} (hw : ‖w.down.val‖ ≤ 1 / 2) :
    reattachmentTime w = 1 := by
  rw [reattachmentTime, annulusParam_of_norm_le (by norm_num) hw, symm_zero]

theorem coe_reattachmentTime_of_le_norm {w : TopCat.disk.{u} k} (hw : 1 / 2 ≤ ‖w.down.val‖) :
    (reattachmentTime w : ℝ) = 2 - 2 * ‖w.down.val‖ := by
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
  (⟨(1 - (p.2 : ℝ)) * reattachmentTime p.1, mul_mem (symm p.2).property
      (reattachmentTime p.1).property⟩,
    diskRadialPush k (by norm_num : (0 : ℝ) ≤ 1 / 2) (σ p.2, p.1))

theorem coe_fst_reattachmentPath (p : TopCat.disk.{u} k × I) :
    ((reattachmentPath p).1 : ℝ) = (1 - (p.2 : ℝ)) * reattachmentTime p.1 :=
  (rfl)

theorem snd_reattachmentPath (p : TopCat.disk.{u} k × I) :
    (reattachmentPath p).2 = diskRadialPush k (by norm_num : (0 : ℝ) ≤ 1 / 2) (σ p.2, p.1) :=
  (rfl)

theorem continuous_reattachmentPath : Continuous (reattachmentPath.{u} (k := k)) := by
  have hs : Continuous fun p : TopCat.disk.{u} k × I ↦ (p.2 : ℝ) :=
    continuous_subtypeVal.comp continuous_snd
  exact .prodMk ((((continuous_const.sub hs).mul (continuous_subtypeVal.comp
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

/-! ### The radial reparametrization for composing two reattachments -/

/-- The radial factor of the reparametrization of the disc used to compare a composite of two
reattachment maps with a single one: with `m = max r (1/4)`, it is `min (m + 1/4) ((m + 1)/2) / m`.
A vector of norm `r` is scaled by `2` when `r ≤ 1/4`, to norm `r + 1/4` when `1/4 ≤ r ≤ 1/2`, and
to norm `(r + 1)/2` when `1/2 ≤ r`. -/
def composeRadialFactor (r : ℝ) : ℝ :=
  min (max r (1 / 4) + 1 / 4) ((max r (1 / 4) + 1) / 2) / max r (1 / 4)

theorem composeRadialFactor_def (r : ℝ) :
    composeRadialFactor r =
      min (max r (1 / 4) + 1 / 4) ((max r (1 / 4) + 1) / 2) / max r (1 / 4) :=
  (rfl)

private theorem quarter_le_max (r : ℝ) : (1 / 4 : ℝ) ≤ max r (1 / 4) :=
  le_max_right _ _

theorem continuous_composeRadialFactor : Continuous composeRadialFactor := by
  have hm : Continuous fun r : ℝ ↦ max r (1 / 4) := continuous_id.max continuous_const
  exact (((hm.add continuous_const).min ((hm.add continuous_const).div_const _))).div hm
    fun r ↦ (lt_of_lt_of_le (by norm_num) (quarter_le_max r)).ne'

theorem composeRadialFactor_pos (r : ℝ) : 0 < composeRadialFactor r := by
  have := quarter_le_max r
  exact div_pos (lt_min (by linarith) (by linarith)) (by linarith)

theorem composeRadialFactor_of_le_quarter {r : ℝ} (hr : r ≤ 1 / 4) :
    composeRadialFactor r = 2 := by
  rw [composeRadialFactor, max_eq_right hr]
  norm_num

theorem composeRadialFactor_mul_of_quarter_le_of_le_half {r : ℝ} (h₁ : 1 / 4 ≤ r)
    (h₂ : r ≤ 1 / 2) :
    composeRadialFactor r * r = r + 1 / 4 := by
  rw [composeRadialFactor, max_eq_left h₁, min_eq_left (by linarith),
    div_mul_cancel₀ _ (by linarith : r ≠ 0)]

theorem composeRadialFactor_mul_of_half_le {r : ℝ} (h : 1 / 2 ≤ r) :
    composeRadialFactor r * r = (r + 1) / 2 := by
  rw [composeRadialFactor, max_eq_left (by linarith), min_eq_right (by linarith),
    div_mul_cancel₀ _ (by linarith : r ≠ 0)]

@[simp]
theorem composeRadialFactor_one : composeRadialFactor 1 = 1 := by
  have h := composeRadialFactor_mul_of_half_le (by norm_num : (1 / 2 : ℝ) ≤ 1)
  rw [mul_one] at h
  rw [h]
  norm_num

private theorem composeRadialFactor_mul_le_one {r : ℝ} (h₁ : r ≤ 1) :
    composeRadialFactor r * r ≤ 1 := by
  rcases le_total r (1 / 4) with h | h
  · rw [composeRadialFactor_of_le_quarter h]
    linarith
  rcases le_total r (1 / 2) with h' | h'
  · rw [composeRadialFactor_mul_of_quarter_le_of_le_half h h']
    linarith
  · rw [composeRadialFactor_mul_of_half_le h']
    linarith

private theorem norm_composeRadialHomotopy_le (t : I) (x : TopCat.disk.{u} k) :
    ‖((1 - (t : ℝ)) * composeRadialFactor ‖x.down.val‖ + t) • x.down.val‖ ≤ 1 := by
  have hx : ‖x.down.val‖ ≤ 1 := mem_closedBall_zero_iff.1 x.down.property
  have hc := (composeRadialFactor_pos ‖x.down.val‖).le
  have hcr := composeRadialFactor_mul_le_one hx
  have ht₀ := t.property.1
  have ht₁ := t.property.2
  rw [norm_smul, Real.norm_of_nonneg (by nlinarith)]
  nlinarith

variable (k) in
/-- The straight-line homotopy `(t, x) ↦ ((1 - t) c(‖x‖) + t) • x` of the disc, for the radial
factor `c` of `TauCeti.TopCat.composeRadialFactor`: it starts at the radial reparametrization
sending the radii `1/4` and `1/2` to `1/2` and `3/4`, ends at the identity, and fixes the boundary
sphere. -/
def composeRadialHomotopy : C(I × TopCat.disk.{u} k, TopCat.disk.{u} k) where
  toFun q := ULift.up ⟨((1 - (q.1 : ℝ)) * composeRadialFactor ‖q.2.down.val‖ + q.1) • q.2.down.val,
    mem_closedBall_zero_iff.2 (norm_composeRadialHomotopy_le q.1 q.2)⟩
  continuous_toFun := by
    have hx : Continuous fun q : I × TopCat.disk.{u} k ↦
        (q.2.down.val : EuclideanSpace ℝ (Fin k)) :=
      continuous_subtypeVal.comp (continuous_uliftDown.comp continuous_snd)
    have ht : Continuous fun q : I × TopCat.disk.{u} k ↦ (q.1 : ℝ) :=
      continuous_subtypeVal.comp continuous_fst
    exact continuous_uliftUp.comp ((((continuous_const.sub ht).mul
      (continuous_composeRadialFactor.comp hx.norm)).add ht).smul hx |>.subtype_mk _)

theorem coe_composeRadialHomotopy_apply_down (t : I) (x : TopCat.disk.{u} k) :
    ((composeRadialHomotopy k (t, x)).down : EuclideanSpace ℝ (Fin k)) =
      ((1 - (t : ℝ)) * composeRadialFactor ‖x.down.val‖ + t) • x.down.val :=
  (rfl)

theorem coe_composeRadialHomotopy_zero_apply_down (x : TopCat.disk.{u} k) :
    ((composeRadialHomotopy k (0, x)).down : EuclideanSpace ℝ (Fin k)) =
      composeRadialFactor ‖x.down.val‖ • x.down.val := by
  rw [coe_composeRadialHomotopy_apply_down]
  simp

@[simp]
theorem composeRadialHomotopy_one (x : TopCat.disk.{u} k) : composeRadialHomotopy k (1, x) = x :=
  ULift.ext (Subtype.ext ((coe_composeRadialHomotopy_apply_down 1 x).trans (by simp)))

@[simp]
theorem composeRadialHomotopy_diskBoundaryInclusion (t : I) (s : TopCat.diskBoundary.{u} k) :
    composeRadialHomotopy k (t, TopCat.diskBoundaryInclusion k s) =
      TopCat.diskBoundaryInclusion k s := by
  refine ULift.ext (Subtype.ext ((coe_composeRadialHomotopy_apply_down t _).trans ?_))
  rw [norm_diskBoundaryInclusion, composeRadialFactor_one]
  simp

theorem norm_composeRadialHomotopy_zero (x : TopCat.disk.{u} k) :
    ‖(composeRadialHomotopy k (0, x)).down.val‖ =
      composeRadialFactor ‖x.down.val‖ * ‖x.down.val‖ := by
  rw [coe_composeRadialHomotopy_zero_apply_down, norm_smul,
    Real.norm_of_nonneg (composeRadialFactor_pos _).le]

/-- The radial reparametrization preserves the direction of every vector. -/
theorem inv_norm_smul_composeRadialHomotopy_zero (x : TopCat.disk.{u} k) :
    ‖(composeRadialHomotopy k (0, x)).down.val‖⁻¹ • (composeRadialHomotopy k (0, x)).down.val =
      ‖x.down.val‖⁻¹ • x.down.val := by
  rw [norm_composeRadialHomotopy_zero, coe_composeRadialHomotopy_zero_apply_down, smul_smul,
    mul_inv_rev, mul_assoc, inv_mul_cancel₀ (composeRadialFactor_pos _).ne', mul_one]

end TauCeti.TopCat

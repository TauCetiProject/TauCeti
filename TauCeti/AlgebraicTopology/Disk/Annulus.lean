/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Disk.RadialPush

/-!
# Annulus coordinates on the Euclidean disk

For `0 < d ≤ 1`, a point `w` of the annulus `d ≤ ‖w‖ ≤ 1` of the disk `TopCat.disk k` is
`(d + (1 - d) s) • θ` for a radial parameter `s ∈ [0, 1]` (`TauCeti.TopCat.annulusParam`) and a
direction `θ` on the boundary sphere (`TauCeti.TopCat.annulusDir`). A map on the ball of radius `d`
and a map on the annulus, given in these coordinates, glue to a map on the whole disk when they
agree on the seam `‖w‖ = d` (`TauCeti.TopCat.discGlue`). This is how a homotopy of a small disc
is combined with a deformation of the surrounding annulus, as in cell reattachment arguments.

## Main declarations

* `TauCeti.TopCat.annulusParam`, `TauCeti.TopCat.annulusDir`: the annulus coordinates.
* `TauCeti.TopCat.add_one_sub_mul_annulusParam_smul_annulusDir`: a point of the annulus is
  recovered from its coordinates.
* `TauCeti.TopCat.smallDiskIncl`: the inclusion of the ball of radius `d ≤ 1` into the disk.
* `TauCeti.TopCat.annulusPoint`: the point of the annulus with given coordinates, as a continuous
  map, and `TauCeti.TopCat.annulusPoint_annulusParam_annulusDir`,
  `TauCeti.TopCat.annulusParam_annulusPoint`, `TauCeti.TopCat.annulusDir_annulusPoint`: it is
  inverse to the coordinates.
  Its inner circle is the sphere of radius `d` (`TauCeti.TopCat.annulusPoint_zero`) and its outer
  circle is the boundary sphere (`TauCeti.TopCat.annulusPoint_one`).
* `TauCeti.TopCat.discGlue`: the gluing of a map on the ball of radius `d` and a map on the
  annulus, with a parameter space `P`.
-/

public section

noncomputable section

open Set Metric unitInterval

universe u

namespace TauCeti.TopCat

variable {P Y : Type*} [TopologicalSpace P] [TopologicalSpace Y] {k : ℕ} {d : ℝ}

/-- The radial parameter `s ∈ [0, 1]` of a point `w = (d + (1 - d) s) • θ` of the annulus
`d ≤ ‖w‖ ≤ 1` of the disk. -/
def annulusParam (d : ℝ) (w : TopCat.disk.{u} k) : I :=
  projIcc 0 1 zero_le_one ((‖w.down.1‖ - d) / (1 - d))

@[continuity, fun_prop]
theorem continuous_annulusParam : Continuous (annulusParam.{u} (k := k) d) :=
  continuous_projIcc.comp (((continuous_norm.comp
    (continuous_subtype_val.comp continuous_uliftDown)).sub continuous_const).div_const _)

/-- The direction `w / ‖w‖` of a point `w` of the annulus `d ≤ ‖w‖` of the disk, for `0 < d`: the
end of the radial push `TauCeti.TopCat.diskRadialPush` with radius `d`. -/
def annulusDir (hd : 0 < d) (w : {w : TopCat.disk.{u} k // d ≤ ‖w.down.1‖}) :
    TopCat.diskBoundary.{u} k :=
  ULift.up ⟨(diskRadialPush k hd.le (1, w.1)).down.1,
    mem_sphere_zero_iff_norm.2 (norm_diskRadialPush_one hd w.2)⟩

@[continuity, fun_prop]
theorem continuous_annulusDir (hd : 0 < d) : Continuous (annulusDir.{u} (k := k) hd) :=
  continuous_uliftUp.comp ((continuous_subtype_val.comp (continuous_uliftDown.comp
    ((diskRadialPush k hd.le).continuous.comp
      (continuous_const.prodMk continuous_subtype_val)))).subtype_mk _)

/-- The direction of `w` is `w / ‖w‖`. -/
theorem coe_annulusDir (hd : 0 < d) (w : {w : TopCat.disk.{u} k // d ≤ ‖w.down.1‖}) :
    ((annulusDir hd w).down : EuclideanSpace ℝ (Fin k)) = ‖w.1.down.1‖⁻¹ • w.1.down.1 :=
  coe_diskRadialPush_one_of_le_norm hd w.2

/-- Viewed in the disk, the direction of `w` is the end of the radial push with radius `d`. -/
theorem diskBoundaryInclusion_annulusDir (hd : 0 < d)
    (w : {w : TopCat.disk.{u} k // d ≤ ‖w.down.1‖}) :
    TopCat.diskBoundaryInclusion k (annulusDir hd w) = diskRadialPush k hd.le (1, w.1) :=
  ULift.ext (Subtype.ext (TopCat.coe_diskBoundaryInclusion_apply_down k _))

/-- The direction of a point of the boundary sphere is the point itself. -/
@[simp]
theorem annulusDir_diskBoundaryInclusion (hd : 0 < d) (s : TopCat.diskBoundary.{u} k)
    (hs : d ≤ ‖(TopCat.diskBoundaryInclusion k s).down.1‖) :
    annulusDir hd ⟨TopCat.diskBoundaryInclusion k s, hs⟩ = s := by
  refine ULift.ext (Subtype.ext ?_)
  rw [coe_annulusDir, norm_diskBoundaryInclusion, inv_one, one_smul]
  exact (TopCat.coe_diskBoundaryInclusion_apply_down k s).symm

/-- The radius `d + (1 - d) s` of the annulus coordinates of `w` is the norm of `w`. -/
theorem add_one_sub_mul_annulusParam (hd₁ : d ≤ 1) {w : TopCat.disk.{u} k}
    (hw : d ≤ ‖w.down.1‖) : d + (1 - d) * (annulusParam d w : ℝ) = ‖w.down.1‖ := by
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
theorem add_one_sub_mul_annulusParam_smul_annulusDir (hd : 0 < d) (hd₁ : d ≤ 1)
    (w : {w : TopCat.disk.{u} k // d ≤ ‖w.down.1‖}) :
    (d + (1 - d) * (annulusParam d w.1 : ℝ)) • ((annulusDir hd w).down : EuclideanSpace ℝ (Fin k)) =
      w.1.down.1 := by
  rw [add_one_sub_mul_annulusParam hd₁ w.2, coe_annulusDir, smul_smul,
    mul_inv_cancel₀ (hd.trans_le w.2).ne', one_smul]

/-- On the seam `‖w‖ = d` the radial parameter vanishes. -/
theorem annulusParam_of_norm_eq {w : TopCat.disk.{u} k} (hw : ‖w.down.1‖ = d) :
    annulusParam d w = 0 :=
  projIcc_of_le_left _ (by rw [hw, sub_self, zero_div])

/-- Inside the ball of radius `d` the radial parameter vanishes, for `d ≤ 1`. -/
theorem annulusParam_of_norm_le (hd₁ : d ≤ 1) {w : TopCat.disk.{u} k} (hw : ‖w.down.1‖ ≤ d) :
    annulusParam d w = 0 :=
  projIcc_of_le_left _ (div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith))

/-- On the boundary sphere the radial parameter is `1`, for `d < 1`. -/
theorem annulusParam_of_norm_eq_one (hd₁ : d < 1) {w : TopCat.disk.{u} k}
    (hw : ‖w.down.1‖ = 1) : annulusParam d w = 1 :=
  projIcc_of_right_le _ (by rw [hw, div_self (by linarith)])

/-- The point `d • θ` of a point `θ` of the boundary sphere lies in the ball of radius `d`. -/
theorem smul_diskBoundary_mem_closedBall (hd : 0 ≤ d) (θ : TopCat.diskBoundary.{u} k) :
    d • (θ.down : EuclideanSpace ℝ (Fin k)) ∈ closedBall (0 : EuclideanSpace ℝ (Fin k)) d := by
  rw [mem_closedBall_zero_iff, norm_smul, mem_sphere_zero_iff_norm.1 θ.down.2,
    Real.norm_of_nonneg hd, mul_one]

/-- The inclusion of the closed ball of radius `d ≤ 1` into the unit disk. -/
def smallDiskIncl (hd₁ : d ≤ 1) :
    C(closedBall (0 : EuclideanSpace ℝ (Fin k)) d, TopCat.disk.{u} k) where
  toFun w := ⟨⟨w.1, closedBall_subset_closedBall hd₁ w.2⟩⟩
  continuous_toFun := continuous_uliftUp.comp (continuous_subtype_val.subtype_mk _)

@[simp]
theorem smallDiskIncl_apply (hd₁ : d ≤ 1) (w : closedBall (0 : EuclideanSpace ℝ (Fin k)) d) :
    smallDiskIncl.{u} hd₁ w = ⟨⟨w.1, closedBall_subset_closedBall hd₁ w.2⟩⟩ :=
  (rfl)

/-- A point of the disk in the ball of radius `d` comes from that ball. -/
theorem smallDiskIncl_mk (hd₁ : d ≤ 1) {w : TopCat.disk.{u} k} (hw : w.down.1 ∈ closedBall 0 d) :
    smallDiskIncl hd₁ ⟨w.down.1, hw⟩ = w :=
  (rfl)

/-- The radius `d + (1 - d) s` of the annulus coordinates is at least `d`. -/
private theorem le_add_one_sub_mul (hd₁ : d ≤ 1) (s : I) : d ≤ d + (1 - d) * s :=
  le_add_of_nonneg_right (mul_nonneg (sub_nonneg.2 hd₁) s.2.1)

/-- The norm of `(d + (1 - d) s) • θ` is `d + (1 - d) s`. -/
private theorem norm_add_one_sub_mul_smul (hd₀ : 0 ≤ d) (hd₁ : d ≤ 1)
    (p : I × TopCat.diskBoundary.{u} k) :
    ‖(d + (1 - d) * p.1) • (p.2.down : EuclideanSpace ℝ (Fin k))‖ = d + (1 - d) * p.1 := by
  rw [norm_smul, mem_sphere_zero_iff_norm.1 p.2.down.2, mul_one,
    Real.norm_of_nonneg (hd₀.trans (le_add_one_sub_mul hd₁ p.1))]

/-- The point `(d + (1 - d) s) • θ` of the annulus `d ≤ ‖w‖ ≤ 1` of the disk with annulus
coordinates `(s, θ)`, for `0 ≤ d ≤ 1`. For `0 < d < 1` it is inverse to the annulus coordinates
(`TauCeti.TopCat.annulusPoint_annulusParam_annulusDir`, `TauCeti.TopCat.annulusParam_annulusPoint`,
`TauCeti.TopCat.annulusDir_annulusPoint`). -/
def annulusPoint (hd₀ : 0 ≤ d) (hd₁ : d ≤ 1) : C(I × TopCat.diskBoundary.{u} k, TopCat.disk.{u} k)
    where
  toFun p := ⟨⟨(d + (1 - d) * p.1) • p.2.down.1, mem_closedBall_zero_iff.2
    ((norm_add_one_sub_mul_smul hd₀ hd₁ p).trans_le (by nlinarith [p.1.2.2]))⟩⟩
  continuous_toFun := continuous_uliftUp.comp (Continuous.subtype_mk (by fun_prop) _)

@[simp]
theorem coe_annulusPoint_apply_down (hd₀ : 0 ≤ d) (hd₁ : d ≤ 1)
    (p : I × TopCat.diskBoundary.{u} k) :
    ((annulusPoint hd₀ hd₁ p).down : EuclideanSpace ℝ (Fin k)) =
      (d + (1 - d) * p.1) • (p.2.down : EuclideanSpace ℝ (Fin k)) :=
  (rfl)

/-- The annulus point with coordinates `(s, θ)` has norm `d + (1 - d) s`. -/
theorem norm_annulusPoint (hd₀ : 0 ≤ d) (hd₁ : d ≤ 1) (p : I × TopCat.diskBoundary.{u} k) :
    ‖(annulusPoint hd₀ hd₁ p).down.1‖ = d + (1 - d) * p.1 :=
  norm_add_one_sub_mul_smul hd₀ hd₁ p

/-- The outer circle `s = 1` of the annulus is the boundary sphere. -/
@[simp]
theorem annulusPoint_one (hd₀ : 0 ≤ d) (hd₁ : d ≤ 1) (θ : TopCat.diskBoundary.{u} k) :
    annulusPoint hd₀ hd₁ (1, θ) = TopCat.diskBoundaryInclusion k θ :=
  ULift.ext (Subtype.ext (by
    rw [coe_annulusPoint_apply_down, TopCat.coe_diskBoundaryInclusion_apply_down, Icc.coe_one,
      mul_one, add_sub_cancel, one_smul]))

/-- The inner circle `s = 0` of the annulus is the sphere of radius `d`. -/
@[simp]
theorem annulusPoint_zero (hd₀ : 0 ≤ d) (hd₁ : d ≤ 1) (θ : TopCat.diskBoundary.{u} k) :
    annulusPoint hd₀ hd₁ (0, θ) =
      smallDiskIncl hd₁ ⟨d • θ.down.1, smul_diskBoundary_mem_closedBall hd₀ θ⟩ :=
  ULift.ext (Subtype.ext (by simp))

/-- A point of the annulus is the annulus point of its annulus coordinates. -/
@[simp]
theorem annulusPoint_annulusParam_annulusDir (hd : 0 < d) (hd₁ : d ≤ 1)
    (w : {w : TopCat.disk.{u} k // d ≤ ‖w.down.1‖}) :
    annulusPoint hd.le hd₁ (annulusParam d w.1, annulusDir hd w) = w.1 :=
  ULift.ext (Subtype.ext ((coe_annulusPoint_apply_down _ _ _).trans
    (add_one_sub_mul_annulusParam_smul_annulusDir hd hd₁ w)))

/-- The radial parameter of the annulus point with coordinates `(s, θ)` is `s`, for `d < 1`. -/
@[simp]
theorem annulusParam_annulusPoint (hd₀ : 0 ≤ d) (hd₁ : d < 1) (p : I × TopCat.diskBoundary.{u} k) :
    annulusParam d (annulusPoint hd₀ hd₁.le p) = p.1 := by
  have h : (‖(annulusPoint hd₀ hd₁.le p).down.1‖ - d) / (1 - d) = p.1 := by
    rw [norm_annulusPoint, add_sub_cancel_left, mul_div_cancel_left₀ _ (sub_ne_zero.2 hd₁.ne')]
  rw [annulusParam, h, projIcc_val]

/-- The direction of the annulus point with coordinates `(s, θ)` is `θ`, for `0 < d`. -/
@[simp]
theorem annulusDir_annulusPoint (hd : 0 < d) (hd₁ : d ≤ 1) (p : I × TopCat.diskBoundary.{u} k)
    (hp : d ≤ ‖(annulusPoint hd.le hd₁ p).down.1‖) :
    annulusDir hd ⟨annulusPoint hd.le hd₁ p, hp⟩ = p.2 := by
  refine ULift.ext (Subtype.ext ?_)
  rw [coe_annulusDir, norm_annulusPoint, coe_annulusPoint_apply_down, smul_smul,
    inv_mul_cancel₀ (hd.trans_le (le_add_one_sub_mul hd₁ p.1)).ne', one_smul]

/-- The function underlying `TauCeti.TopCat.discGlue`. -/
private def discGlueFun (hd : 0 < d) (A : C(P × closedBall (0 : EuclideanSpace ℝ (Fin k)) d, Y))
    (B : C(P × (I × TopCat.diskBoundary.{u} k), Y)) (q : P × TopCat.disk.{u} k) :
    Y :=
  if h : ‖q.2.down.1‖ ≤ d then A (q.1, ⟨q.2.down.1, mem_closedBall_zero_iff.2 h⟩)
  else B (q.1, annulusParam d q.2, annulusDir hd ⟨q.2, (not_le.1 h).le⟩)

private theorem discGlueFun_of_norm_le (hd : 0 < d)
    (A : C(P × closedBall (0 : EuclideanSpace ℝ (Fin k)) d, Y))
    (B : C(P × (I × TopCat.diskBoundary.{u} k), Y)) (p : P)
    {w : TopCat.disk.{u} k} (hw : ‖w.down.1‖ ≤ d) :
    discGlueFun hd A B (p, w) = A (p, ⟨w.down.1, mem_closedBall_zero_iff.2 hw⟩) :=
  dite_eq_left hw

private theorem discGlueFun_of_le_norm (hd : 0 < d)
    (A : C(P × closedBall (0 : EuclideanSpace ℝ (Fin k)) d, Y))
    (B : C(P × (I × TopCat.diskBoundary.{u} k), Y))
    (hAB : ∀ p θ, B (p, 0, θ) = A (p, ⟨d • θ.down.1, smul_diskBoundary_mem_closedBall hd.le θ⟩))
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

/-- Glue a map on the ball of radius `d` of the disk to a map on the annulus `d ≤ ‖w‖ ≤ 1`, given
in the coordinates `(s, θ)` of the point `(d + (1 - d) s) • θ`, when the two agree on the seam.
Both maps may depend continuously on a parameter in `P`. -/
def discGlue (hd : 0 < d) (A : C(P × closedBall (0 : EuclideanSpace ℝ (Fin k)) d, Y))
    (B : C(P × (I × TopCat.diskBoundary.{u} k), Y))
    (hAB : ∀ p θ, B (p, 0, θ) = A (p, ⟨d • θ.down.1, smul_diskBoundary_mem_closedBall hd.le θ⟩)) :
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
      exact B.continuous.comp (by fun_prop)
    rw [← continuousOn_univ]
    convert hs.union_of_isClosed ht (isClosed_le hn continuous_const)
      (isClosed_le continuous_const hn)
    ext q
    simp [le_total]

/-- On the ball of radius `d` a glued map is its inner piece. -/
theorem discGlue_apply_of_norm_le (hd : 0 < d)
    (A : C(P × closedBall (0 : EuclideanSpace ℝ (Fin k)) d, Y))
    (B : C(P × (I × TopCat.diskBoundary.{u} k), Y))
    (hAB : ∀ p θ, B (p, 0, θ) = A (p, ⟨d • θ.down.1, smul_diskBoundary_mem_closedBall hd.le θ⟩))
    (p : P) {w : TopCat.disk.{u} k} (hw : ‖w.down.1‖ ≤ d) :
    discGlue hd A B hAB (p, w) = A (p, ⟨w.down.1, mem_closedBall_zero_iff.2 hw⟩) :=
  discGlueFun_of_norm_le hd A B p hw

/-- On the annulus `d ≤ ‖w‖` a glued map is its outer piece, read in annulus coordinates. -/
theorem discGlue_apply_of_le_norm (hd : 0 < d)
    (A : C(P × closedBall (0 : EuclideanSpace ℝ (Fin k)) d, Y))
    (B : C(P × (I × TopCat.diskBoundary.{u} k), Y))
    (hAB : ∀ p θ, B (p, 0, θ) = A (p, ⟨d • θ.down.1, smul_diskBoundary_mem_closedBall hd.le θ⟩))
    (p : P) {w : TopCat.disk.{u} k} (hw : d ≤ ‖w.down.1‖) :
    discGlue hd A B hAB (p, w) = B (p, annulusParam d w, annulusDir hd ⟨w, hw⟩) :=
  discGlueFun_of_le_norm hd A B hAB p hw

/-- A glued map takes values in a set containing all values of both pieces. -/
theorem discGlue_mem (hd : 0 < d)
    (A : C(P × closedBall (0 : EuclideanSpace ℝ (Fin k)) d, Y))
    (B : C(P × (I × TopCat.diskBoundary.{u} k), Y))
    (hAB : ∀ p θ, B (p, 0, θ) = A (p, ⟨d • θ.down.1, smul_diskBoundary_mem_closedBall hd.le θ⟩))
    {S : Set Y} (hA : ∀ q, A q ∈ S) (hB : ∀ q, B q ∈ S) (q : P × TopCat.disk.{u} k) :
    discGlue hd A B hAB q ∈ S := by
  rcases le_total ‖q.2.down.1‖ d with hw | hw
  · rw [discGlue_apply_of_norm_le hd A B hAB q.1 hw]
    exact hA _
  · rw [discGlue_apply_of_le_norm hd A B hAB q.1 hw]
    exact hB _

/-- On the boundary sphere, a glued map takes values in a set containing the values of the inner
piece on the unit sphere and of the outer piece on the outer circle `s = 1`. -/
theorem discGlue_mem_of_norm_eq_one (hd : 0 < d)
    (A : C(P × closedBall (0 : EuclideanSpace ℝ (Fin k)) d, Y))
    (B : C(P × (I × TopCat.diskBoundary.{u} k), Y))
    (hAB : ∀ p θ, B (p, 0, θ) = A (p, ⟨d • θ.down.1, smul_diskBoundary_mem_closedBall hd.le θ⟩))
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

end TauCeti.TopCat

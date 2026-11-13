/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Disk.RadialPush

/-!
# Gluing a homotopy of the disk from an inner disk and a collar

Fix `0 < d < 1`. The disk `D^k` is the union of the ball of radius `d` and the collar
`d ≤ ‖x‖ ≤ 1`, which is parametrized by `I × ∂D^k` through `(s, θ) ↦ (d + (1 - d) s) • θ`. A
homotopy `inner` of maps out of `D^k` and a homotopy `outer` of maps out of the annulus
`I × ∂D^k` that agree along the seam, `outer (t, 0, θ) = inner (t, θ)`, glue to a homotopy
`TauCeti.TopCat.diskCollar` of maps out of `D^k`: at the point `d • y` it is `inner (t, y)`, and at
the point `(d + (1 - d) s) • θ` it is `outer (t, s, θ)`. On the boundary sphere it is the outer
edge `outer (t, 1, θ)` of the annulus.

This is how a deformation of a disk is assembled from a deformation of a smaller concentric disk
and a deformation of the surrounding annulus, as in the comparison of the characteristic maps of
Morse cells in J. Milnor, *Morse Theory*, Princeton University Press, 1963, §3, Remark 3.3.

## Main declarations

* `TauCeti.TopCat.diskCollar`: the glued homotopy.
* `TauCeti.TopCat.diskCollar_apply_of_eq_smul` and
  `TauCeti.TopCat.diskCollar_apply_of_eq_smul_sphere`: its values on the inner disk and on the
  collar.
* `TauCeti.TopCat.diskCollar_diskBoundaryInclusion`: its values on the boundary sphere.
* `TauCeti.TopCat.apply_diskCollar_eq_of_radial`: a glued homotopy at a given time is a given map
  of the disk when its two pieces are that map read in the two parametrizations.
-/

public section

noncomputable section

universe u

open Set Metric Topology unitInterval

namespace TauCeti.TopCat

variable {X : Type*} [TopologicalSpace X] {k : ℕ} {d : ℝ}

/-- The point `x / max d ‖x‖` of the disk: `d⁻¹ • x` on the ball of radius `d` and `x / ‖x‖` on
the collar `d ≤ ‖x‖`. -/
private def collarRadial (hd : 0 < d) (w : _root_.TopCat.disk.{u} k) :
    _root_.TopCat.disk.{u} k :=
  diskRadialPush k hd.le (1, w)

private theorem continuous_collarRadial (hd : 0 < d) :
    Continuous (collarRadial.{u} (k := k) hd) :=
  (diskRadialPush k _).continuous.comp (continuous_const.prodMk continuous_id)

private theorem coe_collarRadial_of_norm_le (hd : 0 < d) {w : _root_.TopCat.disk.{u} k}
    (hw : ‖w.down.1‖ ≤ d) : (collarRadial hd w).down.1 = d⁻¹ • w.down.1 :=
  coe_diskRadialPush_one_of_norm_le hd.le hw

/-- The point `x / ‖x‖` of the boundary sphere, for a point `x` of the collar `d ≤ ‖x‖`. -/
private def collarSphere (hd : 0 < d) (w : {w : _root_.TopCat.disk.{u} k // d ≤ ‖w.down.1‖}) :
    _root_.TopCat.diskBoundary.{u} k :=
  ULift.up ⟨(collarRadial hd w.1).down.1,
    mem_sphere_zero_iff_norm.2 (norm_diskRadialPush_one hd w.2)⟩

private theorem continuous_collarSphere (hd : 0 < d) :
    Continuous (collarSphere.{u} (k := k) hd) :=
  continuous_uliftUp.comp ((continuous_subtype_val.comp (continuous_uliftDown.comp
    ((continuous_collarRadial hd).comp continuous_subtype_val))).subtype_mk _)

private theorem diskBoundaryInclusion_collarSphere (hd : 0 < d)
    (w : {w : _root_.TopCat.disk.{u} k // d ≤ ‖w.down.1‖}) :
    _root_.TopCat.diskBoundaryInclusion k (collarSphere hd w) = collarRadial hd w.1 :=
  ULift.ext (Subtype.ext (coe_diskBoundaryInclusion_apply_down k _))

/-- The radial coordinate `(‖x‖ - d) / (1 - d)` of the collar, clamped to `[0, 1]`. -/
private def collarTime (d : ℝ) (w : _root_.TopCat.disk.{u} k) : I :=
  projIcc 0 1 zero_le_one ((‖w.down.1‖ - d) / (1 - d))

private theorem continuous_collarTime : Continuous (collarTime.{u} (k := k) d) :=
  continuous_projIcc.comp (((continuous_norm.comp (continuous_subtype_val.comp
    continuous_uliftDown)).sub continuous_const).div_const _)

private theorem collarTime_of_norm_eq {w : _root_.TopCat.disk.{u} k} (hw : ‖w.down.1‖ = d) :
    collarTime d w = 0 :=
  projIcc_of_le_left _ (by rw [hw, sub_self, zero_div])

private theorem coe_collarTime_of_le_norm (hd1 : d < 1) {w : _root_.TopCat.disk.{u} k}
    (hw : d ≤ ‖w.down.1‖) : (collarTime d w : ℝ) = (‖w.down.1‖ - d) / (1 - d) := by
  have hw₁ : ‖w.down.1‖ ≤ 1 := mem_closedBall_zero_iff.1 w.down.2
  rw [collarTime, coe_projIcc, min_eq_right ?_, max_eq_right ?_]
  · exact div_nonneg (by linarith) (by linarith)
  · rw [div_le_one (by linarith)]
    linarith

private theorem coe_collarSphere (hd : 0 < d)
    (w : {w : _root_.TopCat.disk.{u} k // d ≤ ‖w.down.1‖}) :
    (collarSphere hd w).down.1 = ‖w.1.down.1‖⁻¹ • w.1.down.1 :=
  coe_diskRadialPush_one_of_le_norm hd w.2

/-- The glued map: `inner (t, x / d)` on the ball of radius `d` and
`outer (t, (‖x‖ - d) / (1 - d), x / ‖x‖)` on the collar `d ≤ ‖x‖`. -/
private def diskCollarFun (hd : 0 < d) (inner : C(I × _root_.TopCat.disk.{u} k, X))
    (outer : C(I × (I × _root_.TopCat.diskBoundary.{u} k), X))
    (p : I × _root_.TopCat.disk.{u} k) : X :=
  if hw : d ≤ ‖p.2.down.1‖ then outer (p.1, collarTime d p.2, collarSphere hd ⟨p.2, hw⟩)
  else inner (p.1, collarRadial hd p.2)

private theorem diskCollarFun_of_norm_le (hd : 0 < d)
    {inner : C(I × _root_.TopCat.disk.{u} k, X)}
    {outer : C(I × (I × _root_.TopCat.diskBoundary.{u} k), X)}
    (hseam : ∀ t θ, outer (t, 0, θ) = inner (t, _root_.TopCat.diskBoundaryInclusion k θ))
    {p : I × _root_.TopCat.disk.{u} k} (hp : ‖p.2.down.1‖ ≤ d) :
    diskCollarFun hd inner outer p = inner (p.1, collarRadial hd p.2) := by
  rw [diskCollarFun]
  split_ifs with hw
  · rw [collarTime_of_norm_eq (le_antisymm hp hw), hseam, diskBoundaryInclusion_collarSphere]
  · rfl

private theorem continuous_diskCollarFun (hd : 0 < d)
    {inner : C(I × _root_.TopCat.disk.{u} k, X)}
    {outer : C(I × (I × _root_.TopCat.diskBoundary.{u} k), X)}
    (hseam : ∀ t θ, outer (t, 0, θ) = inner (t, _root_.TopCat.diskBoundaryInclusion k θ)) :
    Continuous (diskCollarFun hd inner outer) := by
  set F := diskCollarFun hd inner outer
  have hinner : Continuous fun p : I × _root_.TopCat.disk.{u} k ↦
      inner (p.1, collarRadial hd p.2) :=
    inner.continuous.comp (continuous_fst.prodMk ((continuous_collarRadial hd).comp
      continuous_snd))
  have houter : ContinuousOn F {p | d ≤ ‖p.2.down.1‖} := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hF : domRestrict {p : I × _root_.TopCat.disk.{u} k | d ≤ ‖p.2.down.1‖} F = fun p ↦
        outer (p.1.1, collarTime d p.1.2, collarSphere hd ⟨p.1.2, p.2⟩) :=
      funext fun p ↦ dite_eq_left p.2
    rw [hF]
    exact outer.continuous.comp ((continuous_fst.comp continuous_subtype_val).prodMk
      ((continuous_collarTime.comp (continuous_snd.comp continuous_subtype_val)).prodMk
        ((continuous_collarSphere hd).comp
          ((continuous_snd.comp continuous_subtype_val).subtype_mk _))))
  have hF : F = fun p ↦ if d ≤ ‖p.2.down.1‖ then F p else inner (p.1, collarRadial hd p.2) := by
    funext p
    split_ifs with hw
    · rfl
    · exact dite_eq_right hw
  rw [hF]
  exact continuous_if_le continuous_const (continuous_norm.comp (continuous_subtype_val.comp
    (continuous_uliftDown.comp continuous_snd))) houter hinner.continuousOn
    fun p hp ↦ diskCollarFun_of_norm_le hd hseam hp.symm.le

/-- Glue a homotopy `inner` of maps out of the disk, placed on the ball of radius `d` by
`y ↦ d • y`, to a homotopy `outer` of maps out of the annulus `I × ∂D^k`, placed on the collar
`d ≤ ‖x‖` by `(s, θ) ↦ (d + (1 - d) s) • θ`. The two must agree along the seam `‖x‖ = d`. -/
def diskCollar (hd : 0 < d) (inner : C(I × _root_.TopCat.disk.{u} k, X))
    (outer : C(I × (I × _root_.TopCat.diskBoundary.{u} k), X))
    (hseam : ∀ t θ, outer (t, 0, θ) = inner (t, _root_.TopCat.diskBoundaryInclusion k θ)) :
    C(I × _root_.TopCat.disk.{u} k, X) :=
  ⟨diskCollarFun hd inner outer, continuous_diskCollarFun hd hseam⟩

private theorem diskCollar_apply (hd : 0 < d) (inner : C(I × _root_.TopCat.disk.{u} k, X))
    (outer : C(I × (I × _root_.TopCat.diskBoundary.{u} k), X))
    (hseam : ∀ t θ, outer (t, 0, θ) = inner (t, _root_.TopCat.diskBoundaryInclusion k θ))
    (p : I × _root_.TopCat.disk.{u} k) :
    diskCollar hd inner outer hseam p = diskCollarFun hd inner outer p :=
  rfl

variable (hd : 0 < d) (inner : C(I × _root_.TopCat.disk.{u} k, X))
  (outer : C(I × (I × _root_.TopCat.diskBoundary.{u} k), X))
  (hseam : ∀ t θ, outer (t, 0, θ) = inner (t, _root_.TopCat.diskBoundaryInclusion k θ))

/-- On the inner disk, the glued homotopy at the point `d • y` is `inner (t, y)`. -/
theorem diskCollar_apply_of_eq_smul {t : I} {w y : _root_.TopCat.disk.{u} k}
    (h : w.down.1 = d • y.down.1) : diskCollar hd inner outer hseam (t, w) = inner (t, y) := by
  have hy : ‖y.down.1‖ ≤ 1 := mem_closedBall_zero_iff.1 y.down.2
  have hw : ‖w.down.1‖ ≤ d := by
    rw [h, norm_smul, Real.norm_of_nonneg hd.le]
    exact mul_le_of_le_one_right hd.le hy
  rw [diskCollar_apply, diskCollarFun_of_norm_le hd hseam (p := (t, w)) hw]
  refine congrArg _ (Prod.ext rfl (ULift.ext (Subtype.ext ?_)))
  rw [coe_collarRadial_of_norm_le hd hw, h, smul_smul, inv_mul_cancel₀ hd.ne', one_smul]

/-- On the collar, the glued homotopy at the point `(d + (1 - d) s) • θ` is `outer (t, s, θ)`. -/
theorem diskCollar_apply_of_eq_smul_sphere (hd1 : d < 1) {t s : I}
    {w : _root_.TopCat.disk.{u} k} {θ : _root_.TopCat.diskBoundary.{u} k}
    (h : w.down.1 = (d + (1 - d) * s) • θ.down.1) :
    diskCollar hd inner outer hseam (t, w) = outer (t, s, θ) := by
  have hθ : ‖θ.down.1‖ = 1 := mem_sphere_zero_iff_norm.1 θ.down.2
  have hr : 0 < d + (1 - d) * s := by nlinarith [s.2.1]
  have hw : ‖w.down.1‖ = d + (1 - d) * s := by
    rw [h, norm_smul, hθ, mul_one, Real.norm_of_nonneg hr.le]
  have hdw : d ≤ ‖w.down.1‖ := by rw [hw]; nlinarith [s.2.1]
  have htime : collarTime d w = s := Subtype.ext <| by
    rw [coe_collarTime_of_le_norm hd1 hdw, hw, add_sub_cancel_left,
      mul_div_cancel_left₀ _ (by linarith)]
  have hsphere : collarSphere hd ⟨w, hdw⟩ = θ := ULift.ext <| Subtype.ext <| by
    rw [coe_collarSphere, hw, h, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
  rw [diskCollar_apply, diskCollarFun, dite_eq_left hdw, htime, hsphere]

/-- On the boundary sphere, the glued homotopy is the outer edge of the annulus. -/
theorem diskCollar_diskBoundaryInclusion (hd1 : d < 1) (t : I)
    (θ : _root_.TopCat.diskBoundary.{u} k) :
    diskCollar hd inner outer hseam (t, _root_.TopCat.diskBoundaryInclusion k θ) =
      outer (t, 1, θ) :=
  diskCollar_apply_of_eq_smul_sphere hd inner outer hseam hd1 (by
    rw [coe_diskBoundaryInclusion_apply_down, Set.Icc.coe_one, mul_one, add_sub_cancel,
      one_smul])

/-- A glued homotopy at time `t`, read through `v`, is a given map `Φ` of the disk when its inner
piece reads as `y ↦ Φ (d • y)` and its outer piece as `(s, θ) ↦ Φ ((d + (1 - d) s) • θ)`. -/
theorem apply_diskCollar_eq_of_radial (hd1 : d < 1) {Z : Type*} (v : X → Z)
    {Φ : EuclideanSpace ℝ (Fin k) → Z} {t : I}
    (hi : ∀ y : _root_.TopCat.disk.{u} k, v (inner (t, y)) = Φ (d • y.down.1))
    (ho : ∀ s (θ : _root_.TopCat.diskBoundary.{u} k),
      v (outer (t, s, θ)) = Φ ((d + (1 - d) * s) • θ.down.1))
    (w : _root_.TopCat.disk.{u} k) : v (diskCollar hd inner outer hseam (t, w)) = Φ w.down.1 := by
  by_cases hw : ‖w.down.1‖ ≤ d
  · let y : _root_.TopCat.disk.{u} k := collarRadial hd w
    have hwy : w.down.1 = d • y.down.1 := by
      rw [coe_collarRadial_of_norm_le hd hw, smul_smul, mul_inv_cancel₀ hd.ne', one_smul]
    rw [diskCollar_apply_of_eq_smul hd inner outer hseam hwy, hi, ← hwy]
  · have hdw : d ≤ ‖w.down.1‖ := (not_le.1 hw).le
    have hwθ : w.down.1 = (d + (1 - d) * collarTime d w) • (collarSphere hd ⟨w, hdw⟩).down.1 := by
      rw [coe_collarTime_of_le_norm hd1 hdw, coe_collarSphere, mul_div_cancel₀ _ (by linarith),
        add_sub_cancel, smul_smul, mul_inv_cancel₀ (by linarith), one_smul]
    rw [diskCollar_apply_of_eq_smul_sphere hd inner outer hseam hd1 hwθ, ho, ← hwθ]

end TauCeti.TopCat

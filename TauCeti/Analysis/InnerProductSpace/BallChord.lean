/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Continuous
public import Mathlib.Analysis.Normed.Group.BallSphere
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Order.Interval.Set.Defs
public import TauCeti.Analysis.InnerProductSpace.Reflection

/-!
# The unit ball swept out by chords parallel to a unit vector

Let `p` be a unit vector of a real inner product space `E`. Every point `y` of the closed unit ball
of `E` lies on the chord through `y` parallel to `p`, whose two ends are a point `x` of the unit
sphere with `⟪x, p⟫ ≥ 0` and its reflection in the hyperplane `(ℝ ∙ p)ᗮ`. Off the equator, the
points of the sphere orthogonal to `p`, the chord is nondegenerate, so the closed ball minus the
equator is a product: an open hemisphere times the interval `[-1, 1]`.

`TauCeti.chordPoint p x t = x - (1 - t) ⟪x, p⟫ p` is the point at height `t` on the chord through
`x`: its component along `p` is `t ⟪x, p⟫` and its component orthogonal to `p` is that of `x`, so
for `x` on the sphere it runs from the reflection of `x` (at `t = -1`) to `x` (at `t = 1`).
`TauCeti.hemisphereChord p` is the resulting homeomorphism from the open hemisphere
`{x | 0 < ⟪x, p⟫}` times `[-1, 1]` onto the closed ball minus the equator, that is onto the points
`y` with `‖y‖² - ⟪y, p⟫² < 1`; this set is open in the closed ball
(`TauCeti.isOpenEmbedding_hemisphereChord`).

In these coordinates the union of the chords through the points of an arc `A` in the open
hemisphere is the product `A × [-1, 1]`, a disc whose boundary is `A` followed by its reflection
in `(ℝ ∙ p)ᗮ`. This is the slice disc bounded by the connected sum of a knot with its reverse
mirror image.

## Main definitions

* `TauCeti.chordPoint p x t`: the point at height `t` on the chord through `x` parallel to `p`.
* `TauCeti.hemisphereChord p`: the open hemisphere around `p` times `[-1, 1]` is homeomorphic to
  the closed unit ball minus the equator, by `(x, t) ↦ chordPoint p x t`.

## Main results

* `TauCeti.inner_chordPoint`, `TauCeti.norm_chordPoint_sq`: the height and the norm of a point on a
  chord.
* `TauCeti.norm_chordPoint_eq_one_iff`: off the equator, a chord meets the sphere only at its two
  ends `t = ±1`.
* `TauCeti.isOpenEmbedding_hemisphereChord`: the chord parametrization is an open embedding into
  the closed unit ball.
-/

public section

noncomputable section

open Metric Set Topology
open scoped RealInnerProductSpace

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (p : sphere (0 : E) 1)

/-- The point at height `t` on the chord through `x` parallel to the unit vector `p`:
`x - (1 - t) ⟪x, p⟫ p`. Its component along `p` is `t ⟪x, p⟫` (`TauCeti.inner_chordPoint`) and its
component orthogonal to `p` is that of `x`. -/
def chordPoint (x : E) (t : ℝ) : E :=
  x - ((1 - t) * ⟪x, (p : E)⟫) • (p : E)

theorem chordPoint_def (x : E) (t : ℝ) :
    chordPoint p x t = x - ((1 - t) * ⟪x, (p : E)⟫) • (p : E) :=
  (rfl)

/-- The chord through `x` is continuous in `x` and in the height. -/
@[fun_prop]
theorem _root_.Continuous.chordPoint {X : Type*} [TopologicalSpace X] {f : X → E} {g : X → ℝ}
    (hf : Continuous f) (hg : Continuous g) : Continuous fun x ↦ chordPoint p (f x) (g x) := by
  unfold TauCeti.chordPoint
  fun_prop

private theorem inner_self_coe : ⟪(p : E), (p : E)⟫ = 1 := by
  rw [real_inner_self_eq_norm_sq, norm_eq_of_mem_sphere p, one_pow]

/-- The component along `p` of the point at height `t` on the chord through `x` is `t ⟪x, p⟫`. -/
@[simp]
theorem inner_chordPoint (x : E) (t : ℝ) : ⟪chordPoint p x t, (p : E)⟫ = t * ⟪x, (p : E)⟫ := by
  rw [chordPoint, inner_sub_left, real_inner_smul_left, inner_self_coe]
  ring

/-- The top `t = 1` of the chord through `x` is `x`. -/
@[simp]
theorem chordPoint_one (x : E) : chordPoint p x 1 = x := by
  simp [chordPoint]

/-- The bottom `t = -1` of the chord through `x` is the reflection of `x` in the hyperplane
`(ℝ ∙ p)ᗮ`. -/
theorem chordPoint_neg_one (x : E) : chordPoint p x (-1) = (ℝ ∙ (p : E))ᗮ.reflection x := by
  rw [reflection_orthogonal_singleton_apply (norm_eq_of_mem_sphere p), real_inner_comm, chordPoint]
  norm_num

/-- The point at height `t` on the chord through a unit vector `x` has squared norm
`1 - (1 - t²) ⟪x, p⟫²`. -/
theorem norm_chordPoint_sq {x : E} (hx : ‖x‖ = 1) (t : ℝ) :
    ‖chordPoint p x t‖ ^ 2 = 1 - (1 - t ^ 2) * ⟪x, (p : E)⟫ ^ 2 := by
  rw [chordPoint, norm_sub_sq_real, real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs,
    sq_abs, norm_eq_of_mem_sphere p, hx]
  ring

/-- The chord through a unit vector stays in the closed unit ball for heights in `[-1, 1]`. -/
theorem norm_chordPoint_le_one {x : E} (hx : ‖x‖ = 1) {t : ℝ} (ht : t ^ 2 ≤ 1) :
    ‖chordPoint p x t‖ ≤ 1 := by
  have h := norm_chordPoint_sq p hx t
  refine (pow_le_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 ?_
  nlinarith [mul_nonneg (sub_nonneg.2 ht) (sq_nonneg ⟪x, (p : E)⟫)]

/-- **A chord off the equator meets the sphere only at its ends.** For a unit vector `x` with
`⟪x, p⟫ ≠ 0`, the point at height `t` on the chord through `x` is a unit vector exactly when
`t = ±1`. -/
theorem norm_chordPoint_eq_one_iff {x : E} (hx : ‖x‖ = 1) (hxp : ⟪x, (p : E)⟫ ≠ 0) (t : ℝ) :
    ‖chordPoint p x t‖ = 1 ↔ t ^ 2 = 1 := by
  rw [← pow_left_inj₀ (norm_nonneg _) zero_le_one two_ne_zero, norm_chordPoint_sq p hx, one_pow]
  constructor
  · intro h
    have h' : (1 - t ^ 2) * ⟪x, (p : E)⟫ ^ 2 = 0 := by linarith
    rcases mul_eq_zero.1 h' with h' | h'
    · linarith
    · exact absurd (pow_eq_zero_iff two_ne_zero |>.1 h') hxp
  · intro h
    rw [h]
    ring

/-- The half-length `√(1 - ‖y‖² + ⟪y, p⟫²)` of the chord through `y` parallel to `p`, which is the
height `⟪x, p⟫` of its upper end `x`. -/
private def chordRadius (y : E) : ℝ :=
  √(1 - ‖y‖ ^ 2 + ⟪y, (p : E)⟫ ^ 2)

private theorem chordRadius_pos {y : E} (hy : ‖y‖ ^ 2 - ⟪y, (p : E)⟫ ^ 2 < 1) :
    0 < chordRadius p y :=
  Real.sqrt_pos.2 (by linarith)

private theorem chordRadius_sq {y : E} (hy : ‖y‖ ^ 2 - ⟪y, (p : E)⟫ ^ 2 < 1) :
    chordRadius p y ^ 2 = 1 - ‖y‖ ^ 2 + ⟪y, (p : E)⟫ ^ 2 :=
  Real.sq_sqrt (by linarith)

/-- The upper end `y + (r - ⟪y, p⟫) p` of the chord through `y`, with `r` its half-length. -/
private def chordTop (y : E) : E :=
  y + (chordRadius p y - ⟪y, (p : E)⟫) • (p : E)

private theorem inner_chordTop (y : E) : ⟪chordTop p y, (p : E)⟫ = chordRadius p y := by
  rw [chordTop, inner_add_left, real_inner_smul_left, inner_self_coe]
  ring

private theorem norm_chordTop {y : E} (hy : ‖y‖ ^ 2 - ⟪y, (p : E)⟫ ^ 2 < 1) :
    ‖chordTop p y‖ = 1 := by
  rw [← pow_left_inj₀ (norm_nonneg _) zero_le_one two_ne_zero, chordTop, norm_add_sq_real,
    real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, norm_eq_of_mem_sphere p]
  have := chordRadius_sq p hy
  nlinarith

/-- **The closed unit ball off the equator is swept out by the chords parallel to `p`.** The map
`(x, t) ↦ x - (1 - t) ⟪x, p⟫ p` is a homeomorphism from the open hemisphere `{x | 0 < ⟪x, p⟫}`
of the unit sphere times `[-1, 1]` onto the points `y` of the closed unit ball with
`‖y‖² - ⟪y, p⟫² < 1`, that is off the equator `{y | ‖y‖ = 1, ⟪y, p⟫ = 0}`. The inverse sends `y`
to the upper end `x` of its chord and to its height `⟪y, p⟫ / ⟪x, p⟫`. -/
def hemisphereChord :
    {x : sphere (0 : E) 1 // 0 < ⟪(x : E), (p : E)⟫} × Icc (-1 : ℝ) 1 ≃ₜ
      {y : closedBall (0 : E) 1 // ‖(y : E)‖ ^ 2 - ⟪(y : E), (p : E)⟫ ^ 2 < 1} where
  toFun q := ⟨⟨chordPoint p q.1.1 q.2, mem_closedBall_zero_iff.2 <|
      norm_chordPoint_le_one p (norm_eq_of_mem_sphere _) (by nlinarith [q.2.2.1, q.2.2.2])⟩, by
    simp only
    rw [norm_chordPoint_sq p (norm_eq_of_mem_sphere _), inner_chordPoint]
    nlinarith [mul_pos q.1.2 q.1.2]⟩
  invFun y :=
    (⟨⟨chordTop p y, mem_sphere_zero_iff_norm.2 (norm_chordTop p y.2)⟩, by
        simpa only [inner_chordTop] using chordRadius_pos p y.2⟩,
      ⟨⟪(y : E), (p : E)⟫ / chordRadius p y, by
        have hr := chordRadius_pos p y.2
        have hle : |⟪(y : E), (p : E)⟫| ≤ chordRadius p y := Real.abs_le_sqrt <| by
          nlinarith [pow_le_one₀ (norm_nonneg _) (mem_closedBall_zero_iff.1 y.1.2) (n := 2)]
        refine ⟨(le_div_iff₀ hr).2 ?_, (div_le_one hr).2 ?_⟩ <;>
          linarith [abs_le.1 hle]⟩)
  left_inv q := by
    obtain ⟨⟨⟨x, hx⟩, hxp⟩, ⟨t, ht⟩⟩ := q
    have hx' : ‖x‖ = 1 := mem_sphere_zero_iff_norm.1 hx
    have hy : ‖chordPoint p x t‖ ^ 2 - ⟪chordPoint p x t, (p : E)⟫ ^ 2 < 1 := by
      rw [norm_chordPoint_sq p hx', inner_chordPoint]
      nlinarith [mul_pos hxp hxp]
    -- The half-length of the chord through `chordPoint p x t` is the height of `x`.
    have hr : chordRadius p (chordPoint p x t) = ⟪x, (p : E)⟫ := by
      rw [chordRadius, norm_chordPoint_sq p hx', inner_chordPoint]
      rw [show 1 - (1 - (1 - t ^ 2) * ⟪x, (p : E)⟫ ^ 2) + (t * ⟪x, (p : E)⟫) ^ 2 =
        ⟪x, (p : E)⟫ ^ 2 by ring, Real.sqrt_sq hxp.le]
    refine Prod.ext (Subtype.ext (Subtype.ext ?_)) (Subtype.ext ?_)
    · dsimp only
      rw [chordTop, hr, inner_chordPoint, chordPoint]
      module
    · dsimp only
      rw [hr, inner_chordPoint]
      field_simp [hxp.ne']
  right_inv y := by
    obtain ⟨⟨y, hy⟩, hyp⟩ := y
    have hr := chordRadius_pos p hyp
    refine Subtype.ext (Subtype.ext ?_)
    dsimp only
    rw [chordPoint, inner_chordTop, show (1 - ⟪y, (p : E)⟫ / chordRadius p y) * chordRadius p y =
      chordRadius p y - ⟪y, (p : E)⟫ by field_simp, chordTop, add_sub_cancel_right]
  continuous_toFun := by
    fun_prop
  continuous_invFun := by
    have hr : Continuous fun y : {y : closedBall (0 : E) 1 //
        ‖(y : E)‖ ^ 2 - ⟪(y : E), (p : E)⟫ ^ 2 < 1} ↦ chordRadius p (y : E) := by
      unfold chordRadius
      fun_prop
    refine .prodMk (.subtype_mk (.subtype_mk ?_ _) _) (.subtype_mk ?_ _)
    · unfold chordTop
      fun_prop
    · exact .div (by fun_prop) hr fun y ↦ (chordRadius_pos p y.2).ne'

/-- `TauCeti.hemisphereChord p` sends `(x, t)` to the point at height `t` on the chord through
`x`. -/
@[simp]
theorem coe_hemisphereChord_apply
    (q : {x : sphere (0 : E) 1 // 0 < ⟪(x : E), (p : E)⟫} × Icc (-1 : ℝ) 1) :
    ((hemisphereChord p q : closedBall (0 : E) 1) : E) = chordPoint p q.1.1 q.2 :=
  (rfl)

/-- The inverse of `TauCeti.hemisphereChord p` sends `y` to the upper end
`y + (√(1 - ‖y‖² + ⟪y, p⟫²) - ⟪y, p⟫) p` of its chord. -/
@[simp]
theorem coe_hemisphereChord_symm_apply_fst
    (y : {y : closedBall (0 : E) 1 // ‖(y : E)‖ ^ 2 - ⟪(y : E), (p : E)⟫ ^ 2 < 1}) :
    ((((hemisphereChord p).symm y).1 : sphere (0 : E) 1) : E) =
      (y : E) + (√(1 - ‖(y : E)‖ ^ 2 + ⟪(y : E), (p : E)⟫ ^ 2) - ⟪(y : E), (p : E)⟫) • (p : E) :=
  (rfl)

/-- The inverse of `TauCeti.hemisphereChord p` sends `y` to its height
`⟪y, p⟫ / √(1 - ‖y‖² + ⟪y, p⟫²)` on its chord. -/
@[simp]
theorem coe_hemisphereChord_symm_apply_snd
    (y : {y : closedBall (0 : E) 1 // ‖(y : E)‖ ^ 2 - ⟪(y : E), (p : E)⟫ ^ 2 < 1}) :
    (((hemisphereChord p).symm y).2 : ℝ) =
      ⟪(y : E), (p : E)⟫ / √(1 - ‖(y : E)‖ ^ 2 + ⟪(y : E), (p : E)⟫ ^ 2) :=
  (rfl)

/-- The points of the closed unit ball off the equator form an open subset. -/
theorem isOpen_setOf_norm_sq_sub_inner_sq_lt_one :
    IsOpen {y : closedBall (0 : E) 1 | ‖(y : E)‖ ^ 2 - ⟪(y : E), (p : E)⟫ ^ 2 < 1} :=
  isOpen_lt (by fun_prop) continuous_const

/-- The chord parametrization of the closed unit ball off the equator is an open embedding into
the closed unit ball. -/
theorem isOpenEmbedding_hemisphereChord :
    IsOpenEmbedding fun q : {x : sphere (0 : E) 1 // 0 < ⟪(x : E), (p : E)⟫} × Icc (-1 : ℝ) 1 ↦
      (hemisphereChord p q : closedBall (0 : E) 1) :=
  (isOpen_setOf_norm_sq_sub_inner_sq_lt_one p).isOpenEmbedding_subtypeVal.comp
    (hemisphereChord p).isOpenEmbedding

end TauCeti

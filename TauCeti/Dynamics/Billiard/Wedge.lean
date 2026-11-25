/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Billiard.SideReflection
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Data.Set.Card
import Mathlib.Topology.Algebra.Order.Floor
import TauCeti.Algebra.Order.Floor.Ring
import TauCeti.Analysis.Complex.Circle.Basic

/-!
# Unfolding billiard trajectories in a wedge

Let `α > 0` (the corners of billiard tables have `α < 2π`). The wedge of angle `α` is the closed
sector `W_α` of `ℂ` with vertex `0` between the rays through `1` and `exp(iα)`. A billiard
trajectory in `W_α` is unfolded into a straight line of the plane: cut the plane, viewed through a
continuous choice of polar angle `θ ∈ ℝ`, into the sectors `S_k = {kα ≤ θ ≤ (k+1)α}`, `k ∈ ℤ`, and
fold `S_k` onto `W_α` by the isometry `sectorFold α k`, the rotation by `-kα` for even `k` and the
reflection `σ` in the line at angle `(k+1)α/2` for odd `k`. Consecutive folds agree on the common
ray of their sectors, and `sectorFold α (k + 1)` is `sectorFold α k` followed by the reflection in a
side of the wedge (`sectorFold_succ`). So a straight line `t ↦ p + t·u` with `p = |p| exp(iψ)`,
folded sector by sector, moves continuously and in a straight line inside the wedge, and its
direction changes by the side reflection exactly when the line crosses one of the rays `θ = kα`: it
is the billiard trajectory with initial state `(p, u)`. The real angle `ψ`, rather than `p` alone,
fixes the lift of the polar angle and hence the indexing of the sectors; the trajectory starts at
`p` when `ψ ∈ [0, α)`.

A line avoiding the vertex sees it under a total angle `π`: along the line, the polar angle stays in
an open interval of length `π` and takes each value at most once. Hence the line crosses at most
`⌈π/α⌉` of the rays `θ = kα`, and the billiard trajectory of a state whose line avoids the vertex
makes at most `⌈π/α⌉` reflections (the corner bound). For `α = π/2` and `α = 2π/3` this is `2`,
and for the reflex angle `α = 3π/2` it is `1`.

## Main definitions

* `TauCeti.Billiard.wedge α`: the closed wedge of angle `α`.
* `TauCeti.Billiard.sectorFold α k`: the isometry folding the `k`-th sector onto the wedge.
* `TauCeti.Billiard.unfoldedAngle ψ p u t`: the polar angle of `p + t·u` equal to `ψ` at `t = 0`,
  continuous when `ψ` is a polar angle of `p` and the line avoids the vertex.
* `TauCeti.Billiard.wedgeTrajectory α ψ p u t` and `TauCeti.Billiard.wedgeDirection α ψ p u t`:
  the position and direction at time `t` of the billiard trajectory in the wedge, by unfolding.
* `TauCeti.Billiard.wedgeReflectionTimes α ψ p u`: the times at which the trajectory reflects.

## Main results

* `TauCeti.Billiard.sectorFold_succ`: consecutive folds differ by a side reflection.
* `TauCeti.Billiard.wedgeTrajectory_mem_wedge`: the folded trajectory stays in the wedge.
* `TauCeti.Billiard.continuous_wedgeTrajectory`: the folded trajectory is continuous.
* `TauCeti.Billiard.wedgeSector_eq_of_disjoint` and `TauCeti.Billiard.wedgeTrajectory_eq_add_smul`:
  between reflections it moves in a straight line at unit speed with constant direction.
* `TauCeti.Billiard.wedgeSector_eq_add_one_or_eq_sub_one` and
  `TauCeti.Billiard.wedgeDirection_eq_directionReflection`: across a reflection time the sector
  changes by one and the direction is reflected in a side (the reflection law).
* `TauCeti.Billiard.encard_wedgeReflectionTimes_le`: the corner bound, at most `⌈π/α⌉`
  reflections.

## References

* S. Tabachnikov, *Geometry and Billiards*, Chapter 7.
-/

public section

noncomputable section

open Complex ComplexConjugate Set

namespace TauCeti.Billiard

/-! ### The wedge and its folds -/

/-- **The wedge of angle `α`.** The closed sector of `ℂ` with vertex `0` between the rays through
`1` and `exp(iα)`, the points `r · exp(iψ)` with `r ≥ 0` and `0 ≤ ψ ≤ α`. -/
def wedge (α : ℝ) : Set ℂ :=
  {z | ∃ r : ℝ, 0 ≤ r ∧ ∃ ψ ∈ Icc 0 α, z = r * exp (ψ * I)}

theorem mem_wedge_iff {α : ℝ} {z : ℂ} :
    z ∈ wedge α ↔ ∃ r : ℝ, 0 ≤ r ∧ ∃ ψ ∈ Icc 0 α, z = r * exp (ψ * I) :=
  Iff.rfl

/-- **The fold of the `k`-th sector.** The linear isometry carrying the sector
`{kα ≤ θ ≤ (k+1)α}` onto the wedge: the rotation by `-kα` for even `k`, and the reflection in the
line at angle `(k+1)α/2` for odd `k`. -/
def sectorFold (α : ℝ) (k : ℤ) : ℂ ≃ₗᵢ[ℝ] ℂ :=
  if Even k then rotation (Circle.exp (-(k * α))) else sideReflection (Circle.exp ((k + 1) * α / 2))

/-- The polar angle of the image of `exp(iθ)` under `sectorFold α k`: `θ - kα` for even `k` and
`(k+1)α - θ` for odd `k`. -/
def foldAngle (α : ℝ) (k : ℤ) (θ : ℝ) : ℝ :=
  if Even k then θ - k * α else (k + 1) * α - θ

/-- The side of the wedge reflected in when the unfolded line passes from the `k`-th to the
`(k+1)`-st sector: the side through `exp(iα)` for even `k` and the side through `1` for odd `k`. -/
def wedgeSide (α : ℝ) (k : ℤ) : Circle :=
  if Even k then Circle.exp α else 1

theorem sectorFold_of_even (α : ℝ) {k : ℤ} (hk : Even k) :
    sectorFold α k = rotation (Circle.exp (-(k * α))) :=
  ite_eq_left hk

theorem sectorFold_of_odd (α : ℝ) {k : ℤ} (hk : Odd k) :
    sectorFold α k = sideReflection (Circle.exp ((k + 1) * α / 2)) :=
  ite_eq_right (Int.not_even_iff_odd.2 hk)

theorem foldAngle_of_even (α : ℝ) {k : ℤ} (hk : Even k) (θ : ℝ) : foldAngle α k θ = θ - k * α :=
  ite_eq_left hk

theorem foldAngle_of_odd (α : ℝ) {k : ℤ} (hk : Odd k) (θ : ℝ) :
    foldAngle α k θ = (k + 1) * α - θ :=
  ite_eq_right (Int.not_even_iff_odd.2 hk)

theorem wedgeSide_of_even (α : ℝ) {k : ℤ} (hk : Even k) : wedgeSide α k = Circle.exp α :=
  ite_eq_left hk

theorem wedgeSide_of_odd (α : ℝ) {k : ℤ} (hk : Odd k) : wedgeSide α k = 1 :=
  ite_eq_right (Int.not_even_iff_odd.2 hk)

theorem sectorFold_ofReal_mul_exp (α : ℝ) (k : ℤ) (r θ : ℝ) :
    sectorFold α k (r * exp (θ * I)) = r * exp (foldAngle α k θ * I) := by
  rcases Int.even_or_odd k with hk | hk
  · simp only [sectorFold_of_even α hk, foldAngle_of_even α hk, rotation_apply, Circle.coe_exp,
      mul_left_comm _ (r : ℂ), ← Complex.exp_add]
    push_cast
    ring_nf
  · simp only [sectorFold_of_odd α hk, foldAngle_of_odd α hk, sideReflection_apply,
      Circle.coe_exp, map_mul, conj_ofReal, ← Complex.exp_conj, conj_I, ← Complex.exp_natCast_mul,
      mul_left_comm _ (r : ℂ), ← Complex.exp_add]
    push_cast
    ring_nf

theorem foldAngle_mem_Icc {α : ℝ} {k : ℤ} {θ : ℝ} (hθ : θ ∈ Icc (k * α) ((k + 1) * α)) :
    foldAngle α k θ ∈ Icc 0 α := by
  unfold foldAngle
  split_ifs <;> constructor <;> linarith [hθ.1, hθ.2]

/-- The fold of the `k`-th sector maps it into the wedge. -/
theorem sectorFold_mem_wedge {α : ℝ} {k : ℤ} {r θ : ℝ} (hr : 0 ≤ r)
    (hθ : θ ∈ Icc (k * α) ((k + 1) * α)) : sectorFold α k (r * exp (θ * I)) ∈ wedge α :=
  ⟨r, hr, foldAngle α k θ, foldAngle_mem_Icc hθ, sectorFold_ofReal_mul_exp α k r θ⟩

@[simp]
theorem sectorFold_zero (α : ℝ) : sectorFold α 0 = LinearIsometryEquiv.refl ℝ ℂ := by
  ext z
  simp [sectorFold]

/-- The fold angles of consecutive sectors agree on their common ray `θ = (k+1)α`. -/
theorem foldAngle_succ_add_one_mul (α : ℝ) (k : ℤ) :
    foldAngle α (k + 1) ((k + 1) * α) = foldAngle α k ((k + 1) * α) := by
  rcases Int.even_or_odd k with hk | hk
  · rw [foldAngle_of_odd α hk.add_one, foldAngle_of_even α hk]
    push_cast
    ring
  · rw [foldAngle_of_even α hk.add_one, foldAngle_of_odd α hk]
    push_cast
    ring

/-- Consecutive folds agree on the common ray `θ = (k+1)α` of their sectors. -/
theorem sectorFold_succ_ofReal_mul_exp (α : ℝ) (k : ℤ) (r : ℝ) :
    sectorFold α (k + 1) (r * exp (((k + 1 : ℤ) * α : ℝ) * I)) =
      sectorFold α k (r * exp (((k + 1 : ℤ) * α : ℝ) * I)) := by
  rw [sectorFold_ofReal_mul_exp, sectorFold_ofReal_mul_exp, Int.cast_add, Int.cast_one,
    foldAngle_succ_add_one_mul]

/-- The fold of the `k`-th sector maps the direction of its ray `θ = (k+1)α` to the side
`wedgeSide α k` of the wedge. -/
theorem sectorFold_exp_succ (α : ℝ) (k : ℤ) :
    sectorFold α k (exp (((k + 1 : ℤ) * α : ℝ) * I)) = wedgeSide α k := by
  have h := sectorFold_ofReal_mul_exp α k 1 ((k + 1 : ℤ) * α)
  rw [ofReal_one, one_mul, one_mul] at h
  rw [h, wedgeSide, foldAngle]
  split_ifs
  · rw [Circle.coe_exp]
    push_cast
    ring_nf
  · push_cast
    simp

/-- **Unfolding law.** The fold of the `(k+1)`-st sector is the fold of the `k`-th sector followed
by the reflection in the side `wedgeSide α k` of the wedge. -/
theorem sectorFold_succ (α : ℝ) (k : ℤ) :
    sectorFold α (k + 1) = (sectorFold α k).trans (sideReflection (wedgeSide α k)) := by
  ext z
  rw [LinearIsometryEquiv.trans_apply, sideReflection_apply]
  rcases Int.even_or_odd k with hk | hk
  · rw [sectorFold_of_odd α hk.add_one, sectorFold_of_even α hk, wedgeSide_of_even α hk,
      sideReflection_apply, rotation_apply, map_mul, ← Circle.coe_inv_eq_conj, ← Circle.exp_neg,
      Circle.coe_exp, Circle.coe_exp, Circle.coe_exp, ← mul_assoc, ← Complex.exp_natCast_mul,
      ← Complex.exp_natCast_mul, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  · rw [sectorFold_of_even α hk.add_one, sectorFold_of_odd α hk, wedgeSide_of_odd α hk,
      rotation_apply, sideReflection_apply, map_mul, Complex.conj_conj, Circle.coe_one, one_pow,
      one_mul, map_pow, ← Circle.coe_inv_eq_conj, ← Circle.exp_neg, Circle.coe_exp,
      Circle.coe_exp, ← Complex.exp_natCast_mul]
    congr 2
    push_cast
    ring

/-- The pointwise form of `sectorFold_succ`. -/
theorem sectorFold_succ_apply (α : ℝ) (k : ℤ) (z : ℂ) :
    sectorFold α (k + 1) z = sideReflection (wedgeSide α k) (sectorFold α k z) := by
  rw [sectorFold_succ, LinearIsometryEquiv.trans_apply]

/-- On the closed sector `kα ≤ θ ≤ (k+1)α`, the fold angle of the sector `⌊θ/α⌋` of `θ` is that of
the `k`-th sector: at `θ = (k+1)α` the two folds agree. -/
theorem foldAngle_floor_div_eq_of_mem_Icc {α : ℝ} (hα : 0 < α) {k : ℤ} {θ : ℝ}
    (hθ : θ ∈ Icc (k * α) ((k + 1) * α)) : foldAngle α ⌊θ / α⌋ θ = foldAngle α k θ := by
  rcases hθ.2.lt_or_eq with hlt | rfl
  · rw [Int.floor_eq_iff.2 ⟨(le_div_iff₀ hα).2 hθ.1, (div_lt_iff₀ hα).2 hlt⟩]
  · rw [mul_div_cancel_right₀ _ hα.ne', ← Int.cast_one, ← Int.cast_add, Int.floor_intCast,
      Int.cast_add, Int.cast_one, foldAngle_succ_add_one_mul]

theorem continuous_foldAngle (α : ℝ) (k : ℤ) : Continuous (foldAngle α k) := by
  rcases Int.even_or_odd k with hk | hk
  · simp only [funext (foldAngle_of_even α hk)]
    fun_prop
  · simp only [funext (foldAngle_of_odd α hk)]
    fun_prop

private theorem continuous_foldAngle_floor_div_of_pos {α : ℝ} (hα : 0 < α) :
    Continuous fun θ ↦ foldAngle α ⌊θ / α⌋ θ := by
  refine continuous_iff_continuousAt.2 fun x ↦ continuousAt_iff_continuous_left_right.2 ⟨?_, ?_⟩
  · -- on the left of `x`, the sector `⌈x/α⌉ - 1`, closed at its upper end
    set k := ⌈x / α⌉ - 1
    have h₁ : (k : ℝ) * α < x := by
      rw [← lt_div_iff₀ hα]
      push_cast [k]
      linarith [Int.ceil_lt_add_one (x / α)]
    have h₂ : x ≤ (k + 1) * α := by
      rw [← div_le_iff₀ hα]
      push_cast [k]
      linarith [Int.le_ceil (x / α)]
    refine (continuous_foldAngle α k).continuousWithinAt.congr_of_eventuallyEq ?_
      (foldAngle_floor_div_eq_of_mem_Icc hα ⟨h₁.le, h₂⟩)
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Ioi_mem_nhds h₁)] with y hy hy'
    exact foldAngle_floor_div_eq_of_mem_Icc hα ⟨le_of_lt hy', le_trans hy h₂⟩
  · -- on the right of `x`, the sector `⌊x/α⌋`
    set k := ⌊x / α⌋
    have h₁ : (k : ℝ) * α ≤ x := (le_div_iff₀ hα).1 (Int.floor_le _)
    have h₂ : x < (k + 1) * α := (div_lt_iff₀ hα).1 (Int.lt_floor_add_one _)
    refine (continuous_foldAngle α k).continuousWithinAt.congr_of_eventuallyEq ?_
      (foldAngle_floor_div_eq_of_mem_Icc hα ⟨h₁, h₂.le⟩)
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds h₂)] with y hy hy'
    exact foldAngle_floor_div_eq_of_mem_Icc hα ⟨h₁.trans hy, le_of_lt hy'⟩

/-- **The folded angle is continuous.** The angle `θ` folded by the fold of its sector `⌊θ/α⌋` is a
continuous (triangle wave) function of `θ`, because consecutive folds agree on their common ray. -/
theorem continuous_foldAngle_floor_div (α : ℝ) : Continuous fun θ ↦ foldAngle α ⌊θ / α⌋ θ := by
  rcases lt_trichotomy α 0 with hα | rfl | hα
  · -- reflect `θ ↦ -θ` to reduce to the step `-α > 0`
    refine ((continuous_foldAngle_floor_div_of_pos (neg_pos.2 hα)).comp continuous_neg).neg.congr
      fun θ ↦ ?_
    simp only [Pi.neg_apply, Function.comp_apply]
    rw [neg_div_neg_eq]
    rcases Int.even_or_odd ⌊θ / α⌋ with hk | hk
    · rw [foldAngle_of_even _ hk, foldAngle_of_even _ hk]
      ring
    · rw [foldAngle_of_odd _ hk, foldAngle_of_odd _ hk]
      ring
  · simpa [foldAngle] using continuous_id'
  · exact continuous_foldAngle_floor_div_of_pos hα

/-! ### The unfolded line -/

/-- **The unfolded polar angle.** Writing `p + t · u = u · (conj u · p + t)`, the angle
`ψ + arg (conj u · p + t) - arg (conj u · p)`, equal to `ψ` at `t = 0`. When `ψ` is a polar angle
of `p` and the line `t ↦ p + t · u` avoids the vertex `0`, it is the continuous choice of polar
angle of `p + t · u` along the line (`add_mul_eq_norm_mul_exp`, `continuous_unfoldedAngle`);
otherwise it is just this formula. -/
def unfoldedAngle (ψ : ℝ) (p : ℂ) (u : Circle) (t : ℝ) : ℝ :=
  ψ + arg (conj (u : ℂ) * p + t) - arg (conj (u : ℂ) * p)

theorem unfoldedAngle_def (ψ : ℝ) (p : ℂ) (u : Circle) (t : ℝ) :
    unfoldedAngle ψ p u t = ψ + arg (conj (u : ℂ) * p + t) - arg (conj (u : ℂ) * p) :=
  (rfl)

/-- **Polar form of the unfolded line.** If `p ≠ 0` has polar angle `ψ`, then
`p + t · u = ‖p + t · u‖ · exp(i · unfoldedAngle ψ p u t)`. -/
theorem add_mul_eq_norm_mul_exp {ψ : ℝ} {p : ℂ} (u : Circle) (hp0 : p ≠ 0)
    (hp : p = ‖p‖ * exp (ψ * I)) (t : ℝ) :
    p + t * u = ‖p + t * u‖ * exp (unfoldedAngle ψ p u t * I) := by
  set w := conj (u : ℂ) * p with hw
  have hpw : p = u * w := by
    rw [hw, ← mul_assoc, u.coe_mul_conj_self, one_mul]
  have hnorm : ‖w‖ = ‖p‖ := by simp [hw]
  have hr : (‖p‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hp0
  have hu : (u : ℂ) = exp ((ψ - arg w : ℝ) * I) := by
    have h1 : (u : ℂ) * (‖p‖ * exp (arg w * I)) = ‖p‖ * exp (ψ * I) := by
      rw [← hnorm, norm_mul_exp_arg_mul_I, ← hpw, hnorm, ← hp]
    have h2 : (u : ℂ) * exp (arg w * I) = exp (ψ * I) := by
      apply mul_left_cancel₀ hr
      linear_combination h1
    rw [ofReal_sub, sub_mul, Complex.exp_sub, ← h2, mul_div_cancel_right₀ _ (Complex.exp_ne_zero _)]
  have hn : ‖p + t * u‖ = ‖w + t‖ := by
    rw [Circle.add_mul_coe_eq_coe_mul_conj_mul_add, norm_mul, Circle.norm_coe, one_mul]
  rw [hn, Circle.add_mul_coe_eq_coe_mul_conj_mul_add, ← hw, hu, unfoldedAngle, ← hw]
  conv_lhs => rw [← norm_mul_exp_arg_mul_I (w + t)]
  rw [mul_left_comm, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- At time `0` the unfolded angle is `ψ`. -/
@[simp]
theorem unfoldedAngle_zero (ψ : ℝ) (p : ℂ) (u : Circle) : unfoldedAngle ψ p u 0 = ψ := by
  simp [unfoldedAngle]

/-- If the line avoids the vertex, the unfolded angle takes each value at most once. -/
theorem unfoldedAngle_injective {ψ : ℝ} {p : ℂ} {u : Circle} (hs : (conj (u : ℂ) * p).im ≠ 0) :
    Function.Injective (unfoldedAngle ψ p u) := by
  intro t₁ t₂ h
  set w := conj (u : ℂ) * p
  have harg : arg (w + t₁) = arg (w + t₂) := by
    simp only [unfoldedAngle] at h
    linarith
  have hn : ‖w + t₁‖ = ‖w + t₂‖ := by
    have e₁ := congrArg Complex.im (norm_mul_exp_arg_mul_I (w + t₁))
    have e₂ := congrArg Complex.im (norm_mul_exp_arg_mul_I (w + t₂))
    rw [harg] at e₁
    simp only [add_im, ofReal_im, add_zero, im_ofReal_mul, exp_ofReal_mul_I_im] at e₁ e₂
    have hsin : Real.sin (arg (w + t₂)) ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at e₂
      exact hs e₂.symm
    exact mul_right_cancel₀ hsin (e₁.trans e₂.symm)
  have hw : w + t₁ = w + t₂ := by
    rw [← norm_mul_exp_arg_mul_I (w + t₁), ← norm_mul_exp_arg_mul_I (w + t₂), hn, harg]
  exact_mod_cast add_left_cancel hw

/-- If the line avoids the vertex, its unfolded angle stays in an open interval of length `π`:
the line sees the vertex under the angle `π`. -/
theorem exists_unfoldedAngle_mem_Ioo {ψ : ℝ} {p : ℂ} {u : Circle}
    (hs : (conj (u : ℂ) * p).im ≠ 0) :
    ∃ c : ℝ, ∀ t, unfoldedAngle ψ p u t ∈ Ioo c (c + Real.pi) := by
  set w := conj (u : ℂ) * p
  rcases hs.lt_or_gt with hneg | hpos
  · refine ⟨ψ - arg w - Real.pi, fun t ↦ ?_⟩
    have h1 : arg (w + t) < 0 := arg_neg_iff.2 (by simpa using hneg)
    have h2 := neg_pi_lt_arg (w + t)
    simp only [unfoldedAngle, mem_Ioo]
    constructor <;> linarith
  · refine ⟨ψ - arg w, fun t ↦ ?_⟩
    have him : 0 < (w + t).im := by simpa using hpos
    have h1 : 0 ≤ arg (w + t) := arg_nonneg_iff.2 him.le
    have h1' : arg (w + t) ≠ 0 := fun h0 ↦ him.ne' (arg_eq_zero_iff.1 h0).2
    have h2 : arg (w + t) < Real.pi := arg_lt_pi_iff.2 (Or.inr him.ne')
    simp only [unfoldedAngle, mem_Ioo]
    constructor
    · linarith [lt_of_le_of_ne h1 (Ne.symm h1')]
    · linarith

/-- If the line avoids the vertex, the unfolded angle is continuous. -/
theorem continuous_unfoldedAngle {ψ : ℝ} {p : ℂ} {u : Circle}
    (hs : (conj (u : ℂ) * p).im ≠ 0) : Continuous (unfoldedAngle ψ p u) := by
  have harg : Continuous fun t : ℝ ↦ arg (conj (u : ℂ) * p + t) := by
    rw [continuous_iff_continuousAt]
    intro t
    refine (continuousAt_arg ?_).comp (by fun_prop)
    exact Or.inr (by simpa using hs)
  unfold unfoldedAngle
  fun_prop

/-! ### The billiard trajectory in the wedge -/

/-- The index of the sector `{kα ≤ θ < (k+1)α}` containing the unfolded angle at time `t`. -/
def wedgeSector (α ψ : ℝ) (p : ℂ) (u : Circle) (t : ℝ) : ℤ :=
  ⌊unfoldedAngle ψ p u t / α⌋

theorem wedgeSector_def (α ψ : ℝ) (p : ℂ) (u : Circle) (t : ℝ) :
    wedgeSector α ψ p u t = ⌊unfoldedAngle ψ p u t / α⌋ :=
  (rfl)

/-- For `α > 0`, the trajectory is in the `k`-th sector at time `t` exactly when its unfolded
angle lies in `[kα, (k+1)α)`. -/
theorem wedgeSector_eq_iff {α ψ : ℝ} {p : ℂ} {u : Circle} {t : ℝ} {k : ℤ} (hα : 0 < α) :
    wedgeSector α ψ p u t = k ↔ unfoldedAngle ψ p u t ∈ Ico (k * α) ((k + 1) * α) := by
  rw [wedgeSector, Int.floor_eq_iff, le_div_iff₀ hα, div_lt_iff₀ hα, mem_Ico]

/-- **The billiard trajectory in the wedge**, by unfolding: the point `p + t · u` of the unfolded
line, folded onto the wedge by the fold of its sector. When `ψ ∈ [0, α)` is a
polar angle of `p` and the line avoids the vertex, it is the billiard trajectory of `(p, u)`
(`wedgeTrajectory_zero`, `continuous_wedgeTrajectory`, `wedgeTrajectory_eq_add_smul`,
`wedgeDirection_eq_directionReflection`); for another polar angle `ψ` it is the billiard trajectory
of the folded state, and otherwise it is just this formula. -/
def wedgeTrajectory (α ψ : ℝ) (p : ℂ) (u : Circle) (t : ℝ) : ℂ :=
  sectorFold α (wedgeSector α ψ p u t) (p + t * u)

theorem wedgeTrajectory_def (α ψ : ℝ) (p : ℂ) (u : Circle) (t : ℝ) :
    wedgeTrajectory α ψ p u t = sectorFold α (wedgeSector α ψ p u t) (p + t * u) :=
  (rfl)

/-- **The direction of the billiard trajectory in the wedge** at time `t`: the direction `u` of
the unfolded line, folded by the fold of the current sector. -/
def wedgeDirection (α ψ : ℝ) (p : ℂ) (u : Circle) (t : ℝ) : Circle :=
  ⟨sectorFold α (wedgeSector α ψ p u t) u, mem_sphere_zero_iff_norm.2 (by simp)⟩

@[simp]
theorem coe_wedgeDirection (α ψ : ℝ) (p : ℂ) (u : Circle) (t : ℝ) :
    (wedgeDirection α ψ p u t : ℂ) = sectorFold α (wedgeSector α ψ p u t) u :=
  (rfl)

/-- **The reflection times** of the billiard trajectory in the wedge: the times at which the
unfolded line crosses one of the rays `θ = kα`, where the folded trajectory meets a side. -/
def wedgeReflectionTimes (α ψ : ℝ) (p : ℂ) (u : Circle) : Set ℝ :=
  {t | ∃ k : ℤ, unfoldedAngle ψ p u t = k * α}

theorem mem_wedgeReflectionTimes_iff {α ψ : ℝ} {p : ℂ} {u : Circle} {t : ℝ} :
    t ∈ wedgeReflectionTimes α ψ p u ↔ ∃ k : ℤ, unfoldedAngle ψ p u t = k * α :=
  Iff.rfl

theorem wedgeSector_zero {α ψ : ℝ} (p : ℂ) (u : Circle) (hψ : ψ ∈ Ico 0 α) :
    wedgeSector α ψ p u 0 = 0 := by
  have hα : 0 < α := hψ.1.trans_lt hψ.2
  rw [wedgeSector, unfoldedAngle_zero, Int.floor_eq_iff]
  constructor
  · simpa using div_nonneg hψ.1 hα.le
  · simpa using (div_lt_one hα).2 hψ.2

/-- For `ψ ∈ [0, α)` the unfolding starts in the sector `0`, so the trajectory starts at `p`. -/
theorem wedgeTrajectory_zero {α ψ : ℝ} (p : ℂ) (u : Circle) (hψ : ψ ∈ Ico 0 α) :
    wedgeTrajectory α ψ p u 0 = p := by
  simp [wedgeTrajectory, wedgeSector_zero p u hψ]

/-- For `ψ ∈ [0, α)` the unfolding starts in the sector `0`, so the trajectory starts with
direction `u`. -/
theorem wedgeDirection_zero {α ψ : ℝ} (p : ℂ) (u : Circle) (hψ : ψ ∈ Ico 0 α) :
    wedgeDirection α ψ p u 0 = u := by
  ext
  simp [wedgeSector_zero p u hψ]

/-- **Polar form of the trajectory.** If `p ≠ 0` has polar angle `ψ`, the trajectory at time `t`
is `‖p + t · u‖ · exp(i φ)`, where `φ` is the unfolded angle folded by the fold of its sector. -/
theorem wedgeTrajectory_eq_norm_mul_exp {α ψ : ℝ} {p : ℂ} (u : Circle) (hp0 : p ≠ 0)
    (hp : p = ‖p‖ * exp (ψ * I)) (t : ℝ) :
    wedgeTrajectory α ψ p u t = ‖p + t * u‖ *
      exp (foldAngle α (wedgeSector α ψ p u t) (unfoldedAngle ψ p u t) * I) := by
  rw [wedgeTrajectory]
  nth_rewrite 1 [add_mul_eq_norm_mul_exp u hp0 hp t]
  rw [sectorFold_ofReal_mul_exp]

/-- **The trajectory is continuous.** If `ψ` is a polar angle of `p` and the line avoids the
vertex, the folded trajectory does not jump at the reflection times, because consecutive folds
agree on the common ray of their sectors. -/
theorem continuous_wedgeTrajectory {α ψ : ℝ} {p : ℂ} {u : Circle}
    (hs : (conj (u : ℂ) * p).im ≠ 0) (hp : p = ‖p‖ * exp (ψ * I)) :
    Continuous (wedgeTrajectory α ψ p u) := by
  have hp0 : p ≠ 0 := by
    rintro rfl
    simp at hs
  have hθ := (continuous_foldAngle_floor_div α).comp (continuous_unfoldedAngle (ψ := ψ) hs)
  simp only [funext (wedgeTrajectory_eq_norm_mul_exp (α := α) u hp0 hp), wedgeSector]
  exact (continuous_ofReal.comp (by fun_prop)).mul
    (Complex.continuous_exp.comp ((continuous_ofReal.comp hθ).mul continuous_const))

/-- **The trajectory stays in the wedge.** -/
theorem wedgeTrajectory_mem_wedge {α ψ : ℝ} {p : ℂ} (u : Circle) (hα : 0 < α) (hp0 : p ≠ 0)
    (hp : p = ‖p‖ * exp (ψ * I)) (t : ℝ) : wedgeTrajectory α ψ p u t ∈ wedge α := by
  rw [wedgeTrajectory, add_mul_eq_norm_mul_exp u hp0 hp t]
  apply sectorFold_mem_wedge (norm_nonneg _)
  set θ := unfoldedAngle ψ p u t
  have h1 := Int.floor_le (θ / α)
  have h2 := Int.lt_floor_add_one (θ / α)
  rw [wedgeSector]
  constructor
  · rwa [le_div_iff₀ hα] at h1
  · rw [div_lt_iff₀ hα] at h2
    linarith

/-- **Straight motion between reflections.** While the trajectory stays in one sector of the
unfolding, it moves in a straight line at unit speed. -/
theorem wedgeTrajectory_eq_add_smul {α ψ : ℝ} {p : ℂ} {u : Circle} {t₁ t₂ : ℝ}
    (h : wedgeSector α ψ p u t₁ = wedgeSector α ψ p u t₂) :
    wedgeTrajectory α ψ p u t₂ =
      wedgeTrajectory α ψ p u t₁ + (t₂ - t₁) • (wedgeDirection α ψ p u t₁ : ℂ) := by
  simp only [wedgeTrajectory, coe_wedgeDirection, h]
  rw [← map_smul, ← map_add]
  congr 1
  rw [real_smul, ofReal_sub]
  ring

/-- While the trajectory stays in one sector of the unfolding, its direction is constant. -/
theorem wedgeDirection_eq_of_wedgeSector_eq {α ψ : ℝ} {p : ℂ} {u : Circle} {t₁ t₂ : ℝ}
    (h : wedgeSector α ψ p u t₁ = wedgeSector α ψ p u t₂) :
    wedgeDirection α ψ p u t₂ = wedgeDirection α ψ p u t₁ := by
  ext
  simp only [coe_wedgeDirection, h]

/-- **The sector changes only at reflection times.** If no reflection happens in `[t₁, t₂]`, the
trajectory stays in one sector of the unfolding, so it moves in a straight line by
`wedgeTrajectory_eq_add_smul`. -/
theorem wedgeSector_eq_of_disjoint {α ψ : ℝ} {p : ℂ} {u : Circle} (hα : 0 < α)
    (hs : (conj (u : ℂ) * p).im ≠ 0) {t₁ t₂ : ℝ} (ht : t₁ ≤ t₂)
    (hdisj : Disjoint (Icc t₁ t₂) (wedgeReflectionTimes α ψ p u)) :
    wedgeSector α ψ p u t₁ = wedgeSector α ψ p u t₂ := by
  refine floor_div_eq_of_forall_intCast_mul_notMem_uIcc hα fun m hm ↦ ?_
  obtain ⟨t, ht', hθt⟩ := intermediate_value_uIcc (continuous_unfoldedAngle hs).continuousOn hm
  rw [uIcc_of_le ht] at ht'
  exact disjoint_left.1 hdisj ht' ⟨m, hθt⟩

/-- If `t₀` is the only reflection time between `t` and `t₀`, every multiple of `α` between the
unfolded angles at `t` and at `t₀` is the angle at `t₀`. -/
private theorem intCast_mul_eq_of_mem_uIcc {α ψ : ℝ} {p : ℂ} {u : Circle}
    (hs : (conj (u : ℂ) * p).im ≠ 0) {t t₀ : ℝ}
    (huniq : ∀ s ∈ uIcc t t₀, s ∈ wedgeReflectionTimes α ψ p u → s = t₀) {m : ℤ}
    (hm : (m : ℝ) * α ∈ uIcc (unfoldedAngle ψ p u t) (unfoldedAngle ψ p u t₀)) :
    (m : ℝ) * α = unfoldedAngle ψ p u t₀ := by
  obtain ⟨s, hs', hθs⟩ := intermediate_value_uIcc (continuous_unfoldedAngle hs).continuousOn hm
  rw [← hθs, huniq s hs' ⟨m, hθs⟩]

/-- Before the only reflection time `t₀` between `t` and `t₀`, at which the unfolded angle is
`kα`, an angle below `kα` is in the sector `k - 1`. -/
private theorem wedgeSector_eq_sub_one_of_lt {α ψ : ℝ} {p : ℂ} {u : Circle} (hα : 0 < α)
    (hs : (conj (u : ℂ) * p).im ≠ 0) {t t₀ : ℝ} {k : ℤ} (hk : unfoldedAngle ψ p u t₀ = k * α)
    (huniq : ∀ s ∈ uIcc t t₀, s ∈ wedgeReflectionTimes α ψ p u → s = t₀)
    (hlt : unfoldedAngle ψ p u t < k * α) : wedgeSector α ψ p u t = k - 1 := by
  rw [wedgeSector_eq_iff hα, mem_Ico]
  push_cast
  refine ⟨not_lt.1 fun h ↦ ?_, by linarith⟩
  have := intCast_mul_eq_of_mem_uIcc hs huniq (m := k - 1)
    (by rw [hk]; push_cast; exact mem_uIcc_of_le h.le (by linarith))
  push_cast at this
  linarith

/-- After the only reflection time `t₀` between `t` and `t₀`, at which the unfolded angle is
`kα`, an angle above `kα` is in the sector `k`. -/
private theorem wedgeSector_eq_of_gt {α ψ : ℝ} {p : ℂ} {u : Circle} (hα : 0 < α)
    (hs : (conj (u : ℂ) * p).im ≠ 0) {t t₀ : ℝ} {k : ℤ} (hk : unfoldedAngle ψ p u t₀ = k * α)
    (huniq : ∀ s ∈ uIcc t t₀, s ∈ wedgeReflectionTimes α ψ p u → s = t₀)
    (hgt : k * α < unfoldedAngle ψ p u t) : wedgeSector α ψ p u t = k := by
  rw [wedgeSector_eq_iff hα, mem_Ico]
  refine ⟨hgt.le, not_le.1 fun h ↦ ?_⟩
  have := intCast_mul_eq_of_mem_uIcc hs huniq (m := k + 1)
    (by rw [hk]; push_cast; exact mem_uIcc_of_ge (by linarith) h)
  push_cast at this
  linarith

/-- Across a reflection time `t₀` at which the unfolded angle is `kα`, the only one in
`[t₁, t₂]`, the trajectory passes between the sectors `k - 1` and `k`. -/
private theorem wedgeSector_of_mem_wedgeReflectionTimes {α ψ : ℝ} {p : ℂ} {u : Circle}
    (hα : 0 < α) (hs : (conj (u : ℂ) * p).im ≠ 0) {t₁ t₀ t₂ : ℝ} (h₁ : t₁ < t₀) (h₂ : t₀ < t₂)
    {k : ℤ} (hk : unfoldedAngle ψ p u t₀ = k * α)
    (huniq : ∀ s ∈ Icc t₁ t₂, s ∈ wedgeReflectionTimes α ψ p u → s = t₀) :
    wedgeSector α ψ p u t₁ = k - 1 ∧ wedgeSector α ψ p u t₂ = k ∨
      wedgeSector α ψ p u t₁ = k ∧ wedgeSector α ψ p u t₂ = k - 1 := by
  have hu₁ : ∀ s ∈ uIcc t₁ t₀, s ∈ wedgeReflectionTimes α ψ p u → s = t₀ := fun s hs' ↦
    huniq s (Icc_subset_Icc le_rfl h₂.le (uIcc_of_le h₁.le ▸ hs'))
  have hu₂ : ∀ s ∈ uIcc t₂ t₀, s ∈ wedgeReflectionTimes α ψ p u → s = t₀ := fun s hs' ↦
    huniq s (Icc_subset_Icc h₁.le le_rfl (uIcc_of_ge h₂.le ▸ hs'))
  rcases (continuous_unfoldedAngle hs).strictMono_of_inj (unfoldedAngle_injective (ψ := ψ) hs) with
    hθ | hθ
  · exact Or.inl ⟨wedgeSector_eq_sub_one_of_lt hα hs hk hu₁ (hk ▸ hθ h₁),
      wedgeSector_eq_of_gt hα hs hk hu₂ (hk ▸ hθ h₂)⟩
  · exact Or.inr ⟨wedgeSector_eq_of_gt hα hs hk hu₁ (hk ▸ hθ h₁),
      wedgeSector_eq_sub_one_of_lt hα hs hk hu₂ (hk ▸ hθ h₂)⟩

/-- **The sector changes by one at a reflection.** If `t₀` is the only reflection time in
`[t₁, t₂]` and `t₁ < t₀ < t₂`, the trajectory passes into a neighbouring sector of the
unfolding. -/
theorem wedgeSector_eq_add_one_or_eq_sub_one {α ψ : ℝ} {p : ℂ} {u : Circle} (hα : 0 < α)
    (hs : (conj (u : ℂ) * p).im ≠ 0) {t₁ t₀ t₂ : ℝ} (h₁ : t₁ < t₀) (h₂ : t₀ < t₂)
    (h₀ : t₀ ∈ wedgeReflectionTimes α ψ p u)
    (huniq : ∀ s ∈ Icc t₁ t₂, s ∈ wedgeReflectionTimes α ψ p u → s = t₀) :
    wedgeSector α ψ p u t₂ = wedgeSector α ψ p u t₁ + 1 ∨
      wedgeSector α ψ p u t₂ = wedgeSector α ψ p u t₁ - 1 := by
  obtain ⟨k, hk⟩ := h₀
  rcases wedgeSector_of_mem_wedgeReflectionTimes hα hs h₁ h₂ hk huniq with
    ⟨e₁, e₂⟩ | ⟨e₁, e₂⟩
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

/-- **The reflection law.** If `t₀` is the only reflection time in `[t₁, t₂]`, with
`t₁ < t₀ < t₂`, and the unfolded angle at `t₀` is `kα`, then the direction of the trajectory after
the reflection is the direction before it, reflected in the side `wedgeSide α (k - 1)` of the
wedge: the side through `exp(iα)` for odd `k` and the side through `1` for even `k`. -/
theorem wedgeDirection_eq_directionReflection {α ψ : ℝ} {p : ℂ} {u : Circle} (hα : 0 < α)
    (hs : (conj (u : ℂ) * p).im ≠ 0) {t₁ t₀ t₂ : ℝ} (h₁ : t₁ < t₀) (h₂ : t₀ < t₂) {k : ℤ}
    (hk : unfoldedAngle ψ p u t₀ = k * α)
    (huniq : ∀ s ∈ Icc t₁ t₂, s ∈ wedgeReflectionTimes α ψ p u → s = t₀) :
    wedgeDirection α ψ p u t₂ =
      directionReflection (wedgeSide α (k - 1)) (wedgeDirection α ψ p u t₁) := by
  have hfold := sectorFold_succ_apply α (k - 1) u
  rw [sub_add_cancel] at hfold
  ext
  rw [coe_directionReflection, coe_wedgeDirection, coe_wedgeDirection]
  rcases wedgeSector_of_mem_wedgeReflectionTimes hα hs h₁ h₂ hk huniq with
    ⟨e₁, e₂⟩ | ⟨e₁, e₂⟩
  · rw [e₁, e₂, hfold]
  · rw [e₁, e₂, hfold, sideReflection_sideReflection]

/-! ### The corner bound -/

/-- **The corner bound.** In a wedge of angle `α > 0`, a billiard trajectory whose unfolded line
avoids the vertex makes at most `⌈π/α⌉` reflections. -/
theorem encard_wedgeReflectionTimes_le {α ψ : ℝ} {p : ℂ} {u : Circle} (hα : 0 < α)
    (hs : (conj (u : ℂ) * p).im ≠ 0) :
    (wedgeReflectionTimes α ψ p u).encard ≤ ⌈Real.pi / α⌉₊ := by
  obtain ⟨c, hc⟩ := exists_unfoldedAngle_mem_Ioo (ψ := ψ) hs
  have hinj := unfoldedAngle_injective (ψ := ψ) hs
  refine (encard_le_encard_of_injOn (f := fun t ↦ ⌊unfoldedAngle ψ p u t / α⌋) ?_ ?_).trans
    (encard_setOf_intCast_mul_mem_Ioo_le hα c Real.pi)
  · rintro t ⟨k, hk⟩
    simp only [mem_ofPred_eq, hk, mul_div_cancel_right₀ _ hα.ne', Int.floor_intCast]
    exact hk ▸ hc t
  · rintro t₁ ⟨k₁, hk₁⟩ t₂ ⟨k₂, hk₂⟩ h
    simp only [hk₁, hk₂, mul_div_cancel_right₀ _ hα.ne', Int.floor_intCast] at h
    exact hinj (by rw [hk₁, hk₂, h])

/-! #### Checks -/

/-- `⌈π/α⌉₊ = 2` for `α = π/2`, so `encard_wedgeReflectionTimes_le` gives at most `2` reflections
in a right-angled corner. -/
theorem natCeil_pi_div_pi_div_two : ⌈Real.pi / (Real.pi / 2)⌉₊ = 2 := by
  rw [show Real.pi / (Real.pi / 2) = 2 by field_simp]
  exact Nat.ceil_ofNat 2

/-- `⌈π/α⌉₊ = ⌈3/2⌉₊ = 2` for `α = 2π/3`, so `encard_wedgeReflectionTimes_le` gives at most `2`
reflections in a corner of angle `2π/3`. -/
theorem natCeil_pi_div_two_pi_div_three : ⌈Real.pi / (2 * Real.pi / 3)⌉₊ = 2 := by
  rw [show Real.pi / (2 * Real.pi / 3) = 3 / 2 by field_simp, Nat.ceil_eq_iff (by norm_num)]
  norm_num

/-- `⌈π/α⌉₊ = ⌈2/3⌉₊ = 1` for `α = 3π/2`, so `encard_wedgeReflectionTimes_le` gives at most `1`
reflection in a reflex corner of angle `3π/2`. -/
theorem natCeil_pi_div_three_pi_div_two : ⌈Real.pi / (3 * Real.pi / 2)⌉₊ = 1 := by
  rw [show Real.pi / (3 * Real.pi / 2) = 2 / 3 by field_simp, Nat.ceil_eq_iff (by norm_num)]
  norm_num

/-- In the square corner, the state at `ε(1 + i)` with direction `-(1 + i)/√2` does not avoid the
vertex: its line reaches `0` at time `√2 ε`, so the corner bound does not apply to it. -/
theorem square_corner_reaches_vertex (ε : ℝ) {u : Circle} (hu : (u : ℂ) = -(1 + I) / √2) :
    (conj (u : ℂ) * (ε * (1 + I))).im = 0 ∧ ε * (1 + I) + ((√2 * ε : ℝ) : ℂ) * u = 0 := by
  have h2 : (√2 : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 two_pos).ne'
  constructor
  · rw [hu, map_div₀, map_neg, map_add, map_one, conj_I, conj_ofReal]
    field_simp
    simp [Complex.mul_im, Complex.div_im]
  · rw [hu]
    push_cast
    field_simp
    ring

end TauCeti.Billiard

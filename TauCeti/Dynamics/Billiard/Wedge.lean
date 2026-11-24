/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Billiard.SideReflection
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Data.Set.Card
import Mathlib.Data.Int.Interval
import Mathlib.Topology.Algebra.Order.Floor

/-!
# Unfolding billiard trajectories in a wedge

Let `α > 0` (the corners of billiard tables have `α < 2π`). The wedge of angle `α` is the closed
sector `W_α` of `ℂ` with vertex `0` between the rays through `1` and `exp(iα)`. A billiard
trajectory in `W_α` is unfolded into a straight line of the plane: cut the plane, viewed through a
continuous choice of polar angle `θ ∈ ℝ`, into the sectors `S_k = {kα ≤ θ ≤ (k+1)α}`, `k ∈ ℤ`, and
fold `S_k` onto `W_α` by the isometry `sectorFold α k`, the rotation by `-kα` for even `k` and the
reflection `σ` in the line at angle `(k+1)α/2` for odd `k`. Consecutive folds agree on the common
ray of their sectors, and `sectorFold α (k + 1)` is `sectorFold α k` followed by the reflection in a
side of the wedge (`sectorFold_succ`). So a straight line `t ↦ p + t·u`, folded sector by sector,
moves in a straight line inside the wedge, and its direction changes by the side reflection exactly
when the line crosses one of the rays `θ = kα`: it is the billiard trajectory with initial state
`(p, u)`.

A line avoiding the vertex sees it under a total angle `π`: along the line, the polar angle stays in
an open interval of length `π` and takes each value at most once. Hence the line crosses at most
`⌈π/α⌉` of the rays `θ = kα`, and the billiard trajectory of a state whose line avoids the vertex
makes at most `⌈π/α⌉` reflections (the corner bound). For `α = π/2` and `α = 2π/3` this is `2`,
and for the reflex angle `α = 3π/2` it is `1`.

## Main definitions

* `TauCeti.Billiard.wedge α`: the closed wedge of angle `α`.
* `TauCeti.Billiard.sectorFold α k`: the isometry folding the `k`-th sector onto the wedge.
* `TauCeti.Billiard.unfoldedAngle ψ p u t`: the continuous polar angle of `p + t·u`, equal to `ψ`
  at `t = 0`.
* `TauCeti.Billiard.wedgeTrajectory α ψ p u t` and `TauCeti.Billiard.wedgeDirection α ψ p u t`:
  the position and direction at time `t` of the billiard trajectory in the wedge, by unfolding.
* `TauCeti.Billiard.wedgeReflectionTimes α ψ p u`: the times at which the trajectory reflects.

## Main results

* `TauCeti.Billiard.sectorFold_succ`: consecutive folds differ by a side reflection.
* `TauCeti.Billiard.wedgeTrajectory_mem_wedge`: the folded trajectory stays in the wedge.
* `TauCeti.Billiard.wedgeSector_eq_of_disjoint` and `TauCeti.Billiard.wedgeTrajectory_eq_add_smul`:
  between reflections it moves in a straight line at unit speed with constant direction.
* `TauCeti.Billiard.sectorFold_succ_apply`: at a reflection the direction is reflected in a side.
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

theorem sectorFold_ofReal_mul_exp (α : ℝ) (k : ℤ) (r θ : ℝ) :
    sectorFold α k (r * exp (θ * I)) = r * exp (foldAngle α k θ * I) := by
  unfold sectorFold foldAngle
  split_ifs with hk
  · rw [rotation_apply, Circle.coe_exp, mul_left_comm, ← Complex.exp_add]
    push_cast
    ring_nf
  · rw [sideReflection_apply, Circle.coe_exp, map_mul, conj_ofReal, ← Complex.exp_conj,
      map_mul, conj_ofReal, conj_I, mul_left_comm, ← Complex.exp_natCast_mul, ← Complex.exp_add]
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

/-- Consecutive folds agree on the common ray `θ = (k+1)α` of their sectors. -/
theorem sectorFold_succ_ofReal_mul_exp (α : ℝ) (k : ℤ) (r : ℝ) :
    sectorFold α (k + 1) (r * exp (((k + 1 : ℤ) * α : ℝ) * I)) =
      sectorFold α k (r * exp (((k + 1 : ℤ) * α : ℝ) * I)) := by
  rw [sectorFold_ofReal_mul_exp, sectorFold_ofReal_mul_exp]
  congr 3
  unfold foldAngle
  rcases Int.even_or_odd k with hk | hk
  · have : ¬ Even (k + 1) := by simpa [Int.even_add_one] using hk
    simp only [this, hk, ↓reduceIte]
    push_cast
    ring
  · have : Even (k + 1) := hk.add_one
    have hk' : ¬ Even k := Int.not_even_iff_odd.2 hk
    simp only [this, hk', ↓reduceIte]
    push_cast
    ring

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
  unfold sectorFold wedgeSide
  rcases Int.even_or_odd k with hk | hk
  · have : ¬ Even (k + 1) := by simpa [Int.even_add_one] using hk
    simp only [this, hk, ↓reduceIte]
    rw [sideReflection_apply, rotation_apply, map_mul,
      ← Circle.coe_inv_eq_conj, ← Circle.exp_neg, Circle.coe_exp, Circle.coe_exp, Circle.coe_exp,
      ← mul_assoc, ← Complex.exp_natCast_mul, ← Complex.exp_natCast_mul, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  · have : Even (k + 1) := hk.add_one
    have hk' : ¬ Even k := Int.not_even_iff_odd.2 hk
    simp only [this, hk', ↓reduceIte]
    rw [rotation_apply, sideReflection_apply, map_mul, Complex.conj_conj, Circle.coe_one, one_pow,
      one_mul, map_pow, ← Circle.coe_inv_eq_conj, ← Circle.exp_neg, Circle.coe_exp,
      Circle.coe_exp, ← Complex.exp_natCast_mul]
    congr 2
    push_cast
    ring

/-! ### The unfolded line -/

/-- **The unfolded polar angle.** Along the line `t ↦ p + t · u`, the continuous choice of polar
angle that equals `ψ` at `t = 0`. Writing `p + t · u = u · (conj u · p + t)`, it is
`ψ + arg (conj u · p + t) - arg (conj u · p)`. -/
def unfoldedAngle (ψ : ℝ) (p : ℂ) (u : Circle) (t : ℝ) : ℝ :=
  ψ + arg (conj (u : ℂ) * p + t) - arg (conj (u : ℂ) * p)

private theorem conj_mul_self (u : Circle) : conj (u : ℂ) * u = 1 := by
  rw [← Circle.coe_inv_eq_conj, ← Circle.coe_mul, inv_mul_cancel, Circle.coe_one]

private theorem add_mul_eq (p : ℂ) (u : Circle) (t : ℝ) :
    p + t * u = u * (conj (u : ℂ) * p + t) := by
  linear_combination (-p) * conj_mul_self u

/-- The line `t ↦ p + t · u` avoids the vertex `0` exactly when `conj u · p` is not real. -/
theorem im_conj_mul_ne_zero_iff (p : ℂ) (u : Circle) :
    (conj (u : ℂ) * p).im ≠ 0 ↔ ∀ t : ℝ, p + t * u ≠ 0 := by
  simp only [add_mul_eq, ne_eq, mul_eq_zero, Circle.coe_ne_zero, false_or]
  constructor
  · intro h t ht
    apply h
    simpa using congrArg Complex.im ht
  · intro h him
    apply h (-(conj (u : ℂ) * p).re)
    apply Complex.ext <;> simp [him]

/-- **Polar form of the unfolded line.** If `p ≠ 0` has polar angle `ψ`, then
`p + t · u = ‖p + t · u‖ · exp(i · unfoldedAngle ψ p u t)`. -/
theorem add_mul_eq_norm_mul_exp {ψ : ℝ} {p : ℂ} (u : Circle) (hp0 : p ≠ 0)
    (hp : p = ‖p‖ * exp (ψ * I)) (t : ℝ) :
    p + t * u = ‖p + t * u‖ * exp (unfoldedAngle ψ p u t * I) := by
  set w := conj (u : ℂ) * p with hw
  have hpw : p = u * w := by
    rw [hw, ← mul_assoc, mul_comm (u : ℂ), conj_mul_self, one_mul]
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
    rw [add_mul_eq, norm_mul, Circle.norm_coe, one_mul]
  rw [hn, add_mul_eq, ← hw, hu, unfoldedAngle, ← hw]
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

/-- **The billiard trajectory in the wedge**, by unfolding: the point `p + t · u` of the unfolded
line, folded onto the wedge by the fold of its sector. -/
def wedgeTrajectory (α ψ : ℝ) (p : ℂ) (u : Circle) (t : ℝ) : ℂ :=
  sectorFold α (wedgeSector α ψ p u t) (p + t * u)

/-- **The direction of the billiard trajectory in the wedge** at time `t`: the direction `u` of
the unfolded line, folded by the fold of the current sector. -/
def wedgeDirection (α ψ : ℝ) (p : ℂ) (u : Circle) (t : ℝ) : ℂ :=
  sectorFold α (wedgeSector α ψ p u t) u

/-- **The reflection times** of the billiard trajectory in the wedge: the times at which the
unfolded line crosses one of the rays `θ = kα`, where the folded trajectory meets a side. -/
def wedgeReflectionTimes (α ψ : ℝ) (p : ℂ) (u : Circle) : Set ℝ :=
  {t | ∃ k : ℤ, unfoldedAngle ψ p u t = k * α}

theorem wedgeSector_zero {α ψ : ℝ} (p : ℂ) (u : Circle) (hψ : ψ ∈ Ico 0 α) :
    wedgeSector α ψ p u 0 = 0 := by
  have hα : 0 < α := hψ.1.trans_lt hψ.2
  rw [wedgeSector, unfoldedAngle_zero, Int.floor_eq_iff]
  constructor
  · simpa using div_nonneg hψ.1 hα.le
  · simpa using (div_lt_one hα).2 hψ.2

/-- The trajectory of a state `(p, u)` with `p` in the wedge, off the side through `exp(iα)`,
starts at `p` with direction `u`. -/
theorem wedgeTrajectory_zero {α ψ : ℝ} (p : ℂ) (u : Circle) (hψ : ψ ∈ Ico 0 α) :
    wedgeTrajectory α ψ p u 0 = p ∧ wedgeDirection α ψ p u 0 = u := by
  simp [wedgeTrajectory, wedgeDirection, wedgeSector_zero p u hψ]

/-- The direction of the trajectory is a unit vector. -/
theorem norm_wedgeDirection (α ψ : ℝ) (p : ℂ) (u : Circle) (t : ℝ) :
    ‖wedgeDirection α ψ p u t‖ = 1 := by
  simp [wedgeDirection]

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
unfolding, it moves in a straight line at unit speed with constant direction. -/
theorem wedgeTrajectory_eq_add_smul {α ψ : ℝ} {p : ℂ} {u : Circle} {t₁ t₂ : ℝ}
    (h : wedgeSector α ψ p u t₁ = wedgeSector α ψ p u t₂) :
    wedgeTrajectory α ψ p u t₂ =
        wedgeTrajectory α ψ p u t₁ + (t₂ - t₁) • wedgeDirection α ψ p u t₁ ∧
      wedgeDirection α ψ p u t₂ = wedgeDirection α ψ p u t₁ := by
  refine ⟨?_, by simp only [wedgeDirection, h]⟩
  simp only [wedgeTrajectory, wedgeDirection, h]
  rw [← map_smul, ← map_add]
  congr 1
  rw [real_smul, ofReal_sub]
  ring

/-- **The reflection law.** When the unfolded line passes from the `k`-th sector to the next, the
direction of the folded trajectory is reflected in the side `wedgeSide α k` of the wedge. -/
theorem sectorFold_succ_apply (α : ℝ) (k : ℤ) (z : ℂ) :
    sectorFold α (k + 1) z = sideReflection (wedgeSide α k) (sectorFold α k z) := by
  rw [sectorFold_succ, LinearIsometryEquiv.trans_apply]

/-- **The sector changes only at reflection times.** If no reflection happens in `[t₁, t₂]`, the
trajectory stays in one sector of the unfolding, so it moves in a straight line by
`wedgeTrajectory_eq_add_smul`. -/
theorem wedgeSector_eq_of_disjoint {α ψ : ℝ} {p : ℂ} {u : Circle} (hα : 0 < α)
    (hs : (conj (u : ℂ) * p).im ≠ 0) {t₁ t₂ : ℝ} (ht : t₁ ≤ t₂)
    (hdisj : Disjoint (Icc t₁ t₂) (wedgeReflectionTimes α ψ p u)) :
    wedgeSector α ψ p u t₁ = wedgeSector α ψ p u t₂ := by
  set θ := unfoldedAngle ψ p u
  have hθ : ContinuousOn θ (Icc t₁ t₂) := (continuous_unfoldedAngle hs).continuousOn
  have hnot : ∀ m : ℤ, (m : ℝ) * α ∉ θ '' Icc t₁ t₂ := by
    rintro m ⟨t, ht, hm⟩
    exact Set.disjoint_left.1 hdisj ht ⟨m, hm⟩
  have key : ∀ a b : ℝ, ∀ m : ℤ, a ≤ m * α → m * α ≤ b →
      (θ t₁ = a ∧ θ t₂ = b ∨ θ t₁ = b ∧ θ t₂ = a) → False := by
    rintro a b m ha hb (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact hnot m (intermediate_value_Icc ht hθ ⟨h1 ▸ ha, h2 ▸ hb⟩)
    · exact hnot m (intermediate_value_Icc' ht hθ ⟨h2 ▸ ha, h1 ▸ hb⟩)
  simp only [wedgeSector]
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · set m := ⌊θ t₁ / α⌋ + 1
    have h1 : θ t₁ < m * α := by
      have := Int.lt_floor_add_one (θ t₁ / α)
      rw [div_lt_iff₀ hα] at this
      push_cast [m]
      linarith
    have h2 : (m : ℝ) * α ≤ θ t₂ := by
      have := Int.floor_le (θ t₂ / α)
      rw [le_div_iff₀ hα] at this
      have hm : (m : ℝ) ≤ ⌊θ t₂ / α⌋ := by exact_mod_cast hlt
      nlinarith
    exact key _ _ m h1.le h2 (Or.inl ⟨rfl, rfl⟩)
  · set m := ⌊θ t₂ / α⌋ + 1
    have h1 : θ t₂ < m * α := by
      have := Int.lt_floor_add_one (θ t₂ / α)
      rw [div_lt_iff₀ hα] at this
      push_cast [m]
      linarith
    have h2 : (m : ℝ) * α ≤ θ t₁ := by
      have := Int.floor_le (θ t₁ / α)
      rw [le_div_iff₀ hα] at this
      have hm : (m : ℝ) ≤ ⌊θ t₁ / α⌋ := by exact_mod_cast hlt
      nlinarith
    exact key _ _ m h1.le h2 (Or.inr ⟨rfl, rfl⟩)

/-! ### The corner bound -/

/-- An open interval of length `π` contains at most `⌈π/α⌉` multiples of `α > 0`. -/
theorem encard_setOf_mul_mem_Ioo_le {α : ℝ} (hα : 0 < α) (c : ℝ) :
    {k : ℤ | (k : ℝ) * α ∈ Ioo c (c + Real.pi)}.encard ≤ ⌈Real.pi / α⌉₊ := by
  have hsub : {k : ℤ | (k : ℝ) * α ∈ Ioo c (c + Real.pi)} ⊆
      (Finset.Ioo ⌊c / α⌋ ⌈(c + Real.pi) / α⌉ : Set ℤ) := by
    rintro k ⟨h1, h2⟩
    simp only [Finset.coe_Ioo, mem_Ioo]
    constructor
    · rw [Int.floor_lt, div_lt_iff₀ hα]
      exact h1
    · rw [Int.lt_ceil, lt_div_iff₀ hα]
      exact h2
  refine (encard_le_encard hsub).trans ?_
  rw [encard_coe_eq_coe_finsetCard, Int.card_Ioo]
  have hceil : ⌈(c + Real.pi) / α⌉ ≤ ⌈c / α⌉ + ⌈Real.pi / α⌉ := by
    rw [add_div]
    exact Int.ceil_add_le _ _
  have hfl : ⌈c / α⌉ ≤ ⌊c / α⌋ + 1 := Int.ceil_le_floor_add_one _
  have : (⌈(c + Real.pi) / α⌉ - ⌊c / α⌋ - 1).toNat ≤ ⌈Real.pi / α⌉₊ := by
    rw [← Int.ceil_toNat]
    exact Int.toNat_le_toNat (by omega)
  exact_mod_cast this

/-- **The corner bound.** In a wedge of angle `α > 0`, a billiard trajectory whose unfolded line
avoids the vertex makes at most `⌈π/α⌉` reflections. -/
theorem encard_wedgeReflectionTimes_le {α ψ : ℝ} {p : ℂ} {u : Circle} (hα : 0 < α)
    (hs : (conj (u : ℂ) * p).im ≠ 0) :
    (wedgeReflectionTimes α ψ p u).encard ≤ ⌈Real.pi / α⌉₊ := by
  obtain ⟨c, hc⟩ := exists_unfoldedAngle_mem_Ioo (ψ := ψ) hs
  have hinj := unfoldedAngle_injective (ψ := ψ) hs
  refine (encard_le_encard_of_injOn (f := fun t ↦ ⌊unfoldedAngle ψ p u t / α⌋) ?_ ?_).trans
    (encard_setOf_mul_mem_Ioo_le hα c)
  · rintro t ⟨k, hk⟩
    simp only [mem_ofPred_eq, hk, mul_div_cancel_right₀ _ hα.ne', Int.floor_intCast]
    exact hk ▸ hc t
  · rintro t₁ ⟨k₁, hk₁⟩ t₂ ⟨k₂, hk₂⟩ h
    simp only [hk₁, hk₂, mul_div_cancel_right₀ _ hα.ne', Int.floor_intCast] at h
    exact hinj (by rw [hk₁, hk₂, h])

/-! #### Checks -/

/-- In a right-angled corner, at most `2` reflections. -/
theorem natCeil_pi_div_pi_div_two : ⌈Real.pi / (Real.pi / 2)⌉₊ = 2 := by
  rw [show Real.pi / (Real.pi / 2) = 2 by field_simp]
  exact Nat.ceil_ofNat 2

/-- In a corner of angle `2π/3`, at most `⌈3/2⌉ = 2` reflections. -/
theorem natCeil_pi_div_two_pi_div_three : ⌈Real.pi / (2 * Real.pi / 3)⌉₊ = 2 := by
  rw [show Real.pi / (2 * Real.pi / 3) = 3 / 2 by field_simp, Nat.ceil_eq_iff (by norm_num)]
  norm_num

/-- In a reflex corner of angle `3π/2`, at most `1` reflection. -/
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

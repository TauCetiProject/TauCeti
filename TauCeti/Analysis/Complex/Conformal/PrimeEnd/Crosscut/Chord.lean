/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.PrimeEnd.Crosscut.Basic
import TauCeti.Analysis.Complex.Inner
import TauCeti.Topology.ConnectedComponents
import Mathlib.Analysis.InnerProductSpace.Continuous

/-!
# Chords of the unit disc

For a point `ζ` of the unit circle and `-1 < t < 1`, the chord of the unit disc perpendicular to
`ζ` at level `t` is the segment between the two points of the circle whose real inner product with
`ζ` is `t`. It is a crosscut of the disc, it is the level set `⟪ζ, z⟫_ℝ = t` of the closed disc,
and the cap `{z | t < ⟪ζ, z⟫_ℝ}` of the disc beyond it is a connected component of the cut disc.
The real diameter is the chord perpendicular to `I` (or to `-I`) at level `0`.

## Main declarations

* `TauCeti.unitDiscChord` -- the chord of the unit disc perpendicular to `ζ` at level `t`.
* `TauCeti.unitDiscChord_eq` -- the chord is the level set `⟪ζ, z⟫_ℝ = t` of the closed disc.
* `TauCeti.unitDiscChord_I_zero`, `TauCeti.unitDiscChord_neg_I_zero` -- the real diameter is the
  chord perpendicular to `I` (or to `-I`) at level `0`.
* `TauCeti.exists_isCrosscut_unitDiscChord` -- the chord is the range of a crosscut of the disc.
* `TauCeti.connectedComponentIn_ball_sdiff_unitDiscChord` -- the cap beyond a chord is a
  connected component of the cut disc.

## References

* Ch. Pommerenke, *Boundary Behaviour of Conformal Maps*, Section 2.4.
-/

public section

noncomputable section

open Complex Metric Set Topology

namespace TauCeti

/-- The chord of the unit disc perpendicular to `ζ` at level `t`: for a unit vector `ζ` and
`-1 < t < 1`, the segment between the two points of the unit circle whose real inner product with
`ζ` is `t`. -/
def unitDiscChord (ζ : ℂ) (t : ℝ) : Set ℂ :=
  segment ℝ (ζ * (t + √(1 - t ^ 2) * I)) (ζ * (t - √(1 - t ^ 2) * I))

/-- The chord perpendicular to `ζ` at level `t` is the segment between its two endpoints. -/
theorem unitDiscChord_def (ζ : ℂ) (t : ℝ) :
    unitDiscChord ζ t = segment ℝ (ζ * (t + √(1 - t ^ 2) * I)) (ζ * (t - √(1 - t ^ 2) * I)) :=
  (rfl)

/-- The chord perpendicular to `I` at level `0` is the real diameter. -/
theorem unitDiscChord_I_zero : unitDiscChord I 0 = range (Path.segment (-1 : ℂ) 1) := by
  rw [Path.range_segment, unitDiscChord_def]
  norm_num

/-- The chord perpendicular to `-I` at level `0` is the real diameter. -/
theorem unitDiscChord_neg_I_zero : unitDiscChord (-I) 0 = range (Path.segment (-1 : ℂ) 1) := by
  rw [Path.range_segment, unitDiscChord_def, segment_symm]
  norm_num

variable {ζ : ℂ} {t : ℝ}

private lemma mul_add_mul_I_mem_sphere (hζ : ‖ζ‖ = 1) (s : ℝ)
    (hs : s ^ 2 = 1 - t ^ 2) : ζ * (t + s * I) ∈ sphere (0 : ℂ) 1 := by
  rw [mem_sphere_zero_iff_norm, norm_mul, hζ, one_mul, norm_add_mul_I, hs]
  simp

private lemma sq_sqrt_one_sub_sq (ht : |t| ≤ 1) : √(1 - t ^ 2) ^ 2 = 1 - t ^ 2 := by
  have : t ^ 2 ≤ 1 := by nlinarith [abs_nonneg t, sq_abs t]
  exact Real.sq_sqrt (by linarith)

/-- The endpoints of a chord lie on the unit circle. -/
private lemma chord_endpoints_mem_sphere (hζ : ‖ζ‖ = 1) (ht : |t| ≤ 1) :
    ζ * (t + √(1 - t ^ 2) * I) ∈ sphere (0 : ℂ) 1 ∧
      ζ * (t - √(1 - t ^ 2) * I) ∈ sphere (0 : ℂ) 1 := by
  refine ⟨mul_add_mul_I_mem_sphere hζ _ (sq_sqrt_one_sub_sq ht), ?_⟩
  rw [show (t : ℂ) - √(1 - t ^ 2) * I = t + ((-√(1 - t ^ 2) : ℝ) : ℂ) * I by push_cast; ring]
  exact mul_add_mul_I_mem_sphere hζ _ (by rw [neg_sq, sq_sqrt_one_sub_sq ht])

private lemma chord_endpoints_ne (hζ : ‖ζ‖ = 1) (ht : |t| < 1) :
    ζ * (t + √(1 - t ^ 2) * I) ≠ ζ * (t - √(1 - t ^ 2) * I) := by
  have hs : 0 < √(1 - t ^ 2) := Real.sqrt_pos.mpr (by nlinarith [abs_nonneg t, sq_abs t])
  have hζ0 : ζ ≠ 0 := by rintro rfl; simp at hζ
  intro h
  have := congrArg Complex.im (mul_left_cancel₀ hζ0 h)
  simp at this
  linarith

/-- Every point of the chord perpendicular to `ζ` at level `t` has real inner product `t`
with `ζ`. -/
theorem inner_eq_of_mem_unitDiscChord (hζ : ‖ζ‖ = 1) {z : ℂ}
    (hz : z ∈ unitDiscChord ζ t) : inner ℝ ζ z = t := by
  refine (convex_hyperplane (innerₗ ℂ ζ).isLinear t).segment_subset ?_ ?_ hz <;>
    exact (inner_mul_left_of_norm_eq_one hζ _).trans (by simp)

/-- For `|t| ≤ 1`, the chord perpendicular to `ζ` at level `t` lies in the closed unit disc. -/
theorem unitDiscChord_subset_closedBall (hζ : ‖ζ‖ = 1) (ht : |t| ≤ 1) :
    unitDiscChord ζ t ⊆ closedBall 0 1 :=
  (convex_closedBall 0 1).segment_subset
    (sphere_subset_closedBall (chord_endpoints_mem_sphere hζ ht).1)
    (sphere_subset_closedBall (chord_endpoints_mem_sphere hζ ht).2)

private lemma mem_unitDiscChord_of_inner_eq (hζ : ‖ζ‖ = 1) (ht : |t| < 1) {z : ℂ}
    (hz : ‖z‖ ≤ 1) (hzt : inner ℝ ζ z = t) : z ∈ unitDiscChord ζ t := by
  set w := (starRingEnd ℂ) ζ * z with hw
  have hzw : z = ζ * w := by rw [hw, ← mul_assoc, mul_conj_eq_one_of_norm_eq_one hζ, one_mul]
  have hre : w.re = t := by rw [← hzt, hzw, inner_mul_left_of_norm_eq_one hζ]
  have hwn : ‖w‖ ≤ 1 := by rwa [hw, norm_mul, Complex.norm_conj, hζ, one_mul]
  have hwsq : w.re ^ 2 + w.im ^ 2 ≤ 1 := by
    have h := Complex.sq_norm w
    rw [Complex.normSq_apply] at h
    nlinarith [norm_nonneg w]
  set s := √(1 - t ^ 2) with hs_def
  have hs : 0 < s := Real.sqrt_pos.mpr (by nlinarith [abs_nonneg t, sq_abs t])
  obtain ⟨him₁, him₂⟩ := abs_le.mp (Real.abs_le_sqrt (by rw [← hre]; linarith) : |w.im| ≤ s)
  have hw' : w = t + w.im * I := by rw [← hre]; exact (re_add_im w).symm
  set v := w.im
  clear_value v s
  refine ⟨(s + v) / (2 * s), (s - v) / (2 * s), div_nonneg (by linarith) (by positivity),
    div_nonneg (by linarith) (by positivity), by field_simp; ring, ?_⟩
  have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  rw [hzw, hw', ← hs_def]
  simp only [Complex.real_smul]
  push_cast
  field_simp
  ring

/-- **The chord is a level set of the closed disc.** For a unit vector `ζ` and `-1 < t < 1`, the
chord perpendicular to `ζ` at level `t` consists of the points of the closed unit disc whose real
inner product with `ζ` is `t`. -/
theorem unitDiscChord_eq (hζ : ‖ζ‖ = 1) (ht : |t| < 1) :
    unitDiscChord ζ t = closedBall 0 1 ∩ {z | inner ℝ ζ z = t} :=
  Subset.antisymm
    (fun _ hz => ⟨unitDiscChord_subset_closedBall hζ ht.le hz, inner_eq_of_mem_unitDiscChord hζ hz⟩)
    fun _ hz => mem_unitDiscChord_of_inner_eq hζ ht (mem_closedBall_zero_iff.mp hz.1) hz.2

/-- A point of the open unit disc at level `t` lies on the chord at level `t`. -/
theorem mem_unitDiscChord_of_mem_ball (hζ : ‖ζ‖ = 1) {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1)
    (hzt : inner ℝ ζ z = t) : z ∈ unitDiscChord ζ t := by
  have hz' : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  have ht : |t| < 1 := by
    rw [← hzt]
    exact (abs_real_inner_le_norm ζ z).trans_lt (by rw [hζ, one_mul]; exact hz')
  exact mem_unitDiscChord_of_inner_eq hζ ht hz'.le hzt

/-- For `-1 < t < 1`, the chord perpendicular to `ζ` at level `t` is the range of a crosscut of
the unit disc. -/
theorem exists_isCrosscut_unitDiscChord (hζ : ‖ζ‖ = 1) (ht : |t| < 1) :
    ∃ (x y : ℂ) (γ : Path x y), γ.IsCrosscut (ball 0 1) ∧ range γ = unitDiscChord ζ t := by
  obtain ⟨hp, hq⟩ := chord_endpoints_mem_sphere hζ ht.le
  exact ⟨_, _, Path.segment _ _, Path.isCrosscut_segment_ball hp hq (chord_endpoints_ne hζ ht),
    Path.range_segment _ _⟩

/-- The cap of the unit disc beyond the chord perpendicular to `ζ` at level `t`. -/
private def cap (ζ : ℂ) (t : ℝ) : Set ℂ :=
  ball 0 1 ∩ {z | t < inner ℝ ζ z}

private lemma isPreconnected_cap (ζ : ℂ) (t : ℝ) : IsPreconnected (cap ζ t) :=
  ((convex_ball 0 1).inter (convex_halfSpace_gt (innerₗ ℂ ζ).isLinear t)).isPreconnected

private lemma cap_subset_sdiff (hζ : ‖ζ‖ = 1) : cap ζ t ⊆ ball 0 1 \ unitDiscChord ζ t :=
  fun _ hz => ⟨hz.1, fun hzc => (inner_eq_of_mem_unitDiscChord hζ hzc).not_gt hz.2⟩

/-- **The cap beyond a chord is a component.** The cap `{z | t < ⟪ζ, z⟫_ℝ}` of the unit disc is
the connected component of each of its points in the disc cut by the chord at level `t`. -/
theorem connectedComponentIn_ball_sdiff_unitDiscChord (hζ : ‖ζ‖ = 1) {z : ℂ}
    (hz : z ∈ ball (0 : ℂ) 1 ∩ {z | t < inner ℝ ζ z}) :
    connectedComponentIn (ball 0 1 \ unitDiscChord ζ t) z =
      ball (0 : ℂ) 1 ∩ {z | t < inner ℝ ζ z} :=
  connectedComponentIn_eq_of_lt (isPreconnected_cap ζ t) (cap_subset_sdiff hζ) hz hz.2
    (continuous_const.inner continuous_id).continuousOn
    (fun _ hq hqt => hq.2 (mem_unitDiscChord_of_mem_ball hζ hq.1 hqt))
    fun _ hq hqt => ⟨hq.1, hqt⟩

end TauCeti

end

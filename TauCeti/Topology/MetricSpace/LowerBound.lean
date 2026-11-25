/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Instances.EReal.Lemmas
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Global lower bounds from local lower semicontinuity

An extended-real function on a pseudometric space is bounded below when it admits
positive-modulus convex interpolation from a finite point of lower semicontinuity. The
interpolating points need not lie on a geodesic or on a single curve.

## Main results

* `TauCeti.iInf_ne_bot_of_lowerSemicontinuousAt`: positive-modulus interpolation from a
  finite point of lower semicontinuity gives a real global lower bound.
-/

public section

open Filter Set Topology

namespace TauCeti

variable {X : Type*} [PseudoMetricSpace X]

-- Complete the square to bound the quadratic penalty minus the linear term.
private theorem quadratic_lower_bound {κ δ R t : ℝ}
    (hκ : 0 < κ) (hδ : 0 < δ) (ht : t ≤ 1 / 2) :
    2 * R / δ - 4 / (κ * δ ^ 2) ≤ κ / 2 * (1 - t) * R ^ 2 := by
  have hquad : κ / 4 * R ^ 2 ≤ κ / 2 * (1 - t) * R ^ 2 := by
    calc κ / 4 * R ^ 2 = 1 / 4 * (κ * R ^ 2) := by ring
      _ ≤ (1 - t) / 2 * (κ * R ^ 2) :=
        mul_le_mul_of_nonneg_right (by linarith [ht]) (by positivity)
      _ = κ / 2 * (1 - t) * R ^ 2 := by ring
  have hsq : 2 * R / δ ≤ κ / 4 * R ^ 2 + 4 / (κ * δ ^ 2) := by
    calc 2 * R / δ = (2 * (κ * δ * R) * 4) / (4 * κ * δ ^ 2) := by
          field_simp
      _ ≤ ((κ * δ * R) ^ 2 + 4 ^ 2) / (4 * κ * δ ^ 2) :=
        div_le_div_of_nonneg_right (two_mul_le_add_sq (κ * δ * R) 4) (by positivity)
      _ = κ / 4 * R ^ 2 + 4 / (κ * δ ^ 2) := by
          field_simp
  linarith

/-- **Global lower bound from local lower semicontinuity and `κ`-convex interpolation**
(Ambrosio–Gigli–Savaré, Lemma 2.4.8). Let `Ψ : X → EReal` be lower semicontinuous and finite at a
point `x₀`, and let `κ > 0`. Suppose that every point `z` with `Ψ z ≠ ⊤` can be interpolated
towards `x₀` at some scale `R : ℝ` so that for every `t ∈ [0, 1]` there is a point `y` at distance
at most `t R` from `x₀` satisfying
`Ψ y ≤ (1 - t) Ψ x₀ + t Ψ z - (κ / 2) t (1 - t) R ^ 2`.
Then `Ψ` is bounded below by a real constant; in particular `⨅ z, Ψ z ≠ ⊥`. -/
theorem iInf_ne_bot_of_lowerSemicontinuousAt {Ψ : X → EReal} {x₀ : X} {κ : ℝ}
    (hΨ : LowerSemicontinuousAt Ψ x₀) (htop : Ψ x₀ ≠ ⊤) (hbot : Ψ x₀ ≠ ⊥) (hκ : 0 < κ)
    (hinterp : ∀ z, Ψ z ≠ ⊤ → ∃ R : ℝ, ∀ t ∈ Icc (0 : ℝ) 1, ∃ y, dist x₀ y ≤ t * R ∧
      Ψ y ≤ ((1 - t : ℝ) : EReal) * Ψ x₀ + (t : EReal) * Ψ z -
        ((κ / 2 * t * (1 - t) * R ^ 2 : ℝ) : EReal)) :
    (⨅ z, Ψ z) ≠ ⊥ := by
  -- Local boundedness below near `x₀` extends to a global lower bound by choosing `t = 1` when
  -- `R < δ` and `t = δ / (2R)` when `R ≥ δ`, then completing the square against `(κ / 4) R²`.
  set a : ℝ := (Ψ x₀).toReal
  have ha : Ψ x₀ = a := (EReal.coe_toReal htop hbot).symm
  have hnhds : ∀ᶠ y in 𝓝 x₀, ((a - 1 : ℝ) : EReal) < Ψ y :=
    hΨ _ (by simp only [gt_iff_lt, ha, EReal.coe_lt_coe_iff]; exact sub_one_lt a)
  obtain ⟨δ, hδ, hball⟩ := Metric.nhds_basis_ball.eventually_iff.1 hnhds
  set L : ℝ := min (a - 1) (a - 4 / (κ * δ ^ 2))
  refine ne_bot_of_le_ne_bot (EReal.coe_ne_bot L) (le_iInf fun z ↦ ?_)
  rcases eq_or_ne (Ψ z) ⊤ with hztop | hztop
  · exact hztop ▸ le_top
  obtain ⟨R, hinterp_z⟩ := hinterp z hztop
  rcases lt_or_ge R δ with hR | hR
  · obtain ⟨y, hy_dist, hy_le⟩ := hinterp_z 1 ⟨zero_le_one, le_rfl⟩
    have hy_ball : y ∈ Metric.ball x₀ δ :=
      Metric.mem_ball'.2 (hy_dist.trans_lt (by simpa only [one_mul] using hR))
    have h1 : Ψ y ≤ Ψ z := by simpa [ha] using hy_le
    exact (EReal.coe_le_coe_iff.2 (min_le_left _ _)).trans ((hball hy_ball).le.trans h1)
  have hRpos : 0 < R := hδ.trans_le hR
  set t : ℝ := δ / (2 * R)
  have htpos : 0 < t := by positivity
  have ht12 : t ≤ 1 / 2 := (div_le_div_iff₀ (by positivity) two_pos).2 (by linarith)
  have htIcc : t ∈ Icc (0 : ℝ) 1 := ⟨htpos.le, ht12.trans (by norm_num)⟩
  obtain ⟨y, hy_dist, hy_le⟩ := hinterp_z t htIcc
  have hy_ball : y ∈ Metric.ball x₀ δ := by
    rw [Metric.mem_ball']
    have htR : t * R = δ / 2 := by dsimp [t]; field_simp
    linarith
  have hlow : ((a - 1 : ℝ) : EReal) < Ψ y := hball hy_ball
  have hzbot : Ψ z ≠ ⊥ := fun hzbot ↦ by
    rw [hzbot, EReal.coe_mul_bot_of_pos htpos, EReal.add_bot, EReal.bot_sub, le_bot_iff] at hy_le
    exact not_lt_bot (hy_le ▸ hlow)
  set b : ℝ := (Ψ z).toReal
  have hb : Ψ z = b := (EReal.coe_toReal hztop hzbot).symm
  rw [ha, hb] at hy_le
  norm_cast at hy_le
  have hmid : a - 1 ≤ (1 - t) * a + t * b - κ / 2 * t * (1 - t) * R ^ 2 := by
    exact_mod_cast hlow.le.trans hy_le
  have hslope : a - 2 * R / δ ≤ b - κ / 2 * (1 - t) * R ^ 2 := by
    refine le_of_mul_le_mul_left ?_ htpos
    have : t * (2 * R / δ) = 1 := by dsimp [t]; field_simp
    linarith
  have hquad := quadratic_lower_bound (R := R) hκ hδ ht12
  rw [hb]
  exact EReal.coe_le_coe_iff.2 ((min_le_right _ _).trans (by linarith))

end TauCeti

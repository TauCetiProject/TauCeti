/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.DysonBrownianMotion.Truncation
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Real.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import TauCeti.Algebra.BigOperators.Finset.Pairs
import TauCeti.Algebra.BigOperators.Intervals

/-!
# Cutoff-uniform nonexplosion of truncated Dyson trajectories

A continuous forcing path can be shifted by a fixed decreasing staircase so that its ordered gaps
are positive on any fixed compact time interval. The squared Euclidean distance from the shifted
forcing then has a cutoff-independent linear upper bound. The estimate also controls the integrated
truncated inverse gaps, even when the truncated trajectory crosses a chamber wall.
Consequently every compact time interval has a common bound for all positive cutoffs.

The quadratic Lyapunov method is motivated by Anderson–Guionnet–Zeitouni, *An Introduction to
Random Matrices* (2010), §4.3.1. The pathwise shift by a staircase used here is a deterministic
argument for arbitrary continuous forcing.
-/

public section

open MeasureTheory Set
open scoped NNReal

namespace TauCeti.Probability

private theorem two_mul_inv_mul_sum_Ioi_one (n : ℕ) :
    2 * (n : ℝ)⁻¹ * (∑ i : Fin n, ∑ _j ∈ Finset.Ioi i, (1 : ℝ)) = (n - 1 : ℕ) := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  rw [← Finset.sum_sum_Iio_eq_sum_sum_Ioi (fun _ _ : Fin n ↦ (1 : ℝ))]
  simp only [Finset.sum_const, nsmul_eq_mul, Fin.card_Iio, mul_one, Fin.sum_univ_eq_sum_range]
  rw [show 2 * (n : ℝ)⁻¹ * (∑ r ∈ Finset.range n, (r : ℝ)) =
    (n : ℝ)⁻¹ * ((∑ r ∈ Finset.range n, (r : ℝ)) * 2) by ring]
  rw [Finset.sum_range_natCast_mul_two, inv_mul_cancel_left₀ (Nat.cast_ne_zero.2 hn.ne'),
    Nat.cast_sub hn, Nat.cast_one]

private theorem sum_sub_mul_truncatedDysonDrift_le {ε : ℝ} (hε : 0 < ε) (n : ℕ)
    (z b : Fin n → ℝ) (c : ℝ) (hb : ∀ i j, i < j → c ≤ b i - b j) :
    2 * (∑ i : Fin n, (z i - b i) * truncatedDysonDrift ε n z i) +
        2 * c * (n : ℝ)⁻¹ * (∑ i : Fin n, ∑ j ∈ Finset.Ioi i,
          (max (z i - z j) ε)⁻¹) ≤ (n - 1 : ℕ) := by
  rw [sum_mul_truncatedDysonDrift_eq_sum_Ioi, ← two_mul_inv_mul_sum_Ioi_one n]
  have hp (i j : Fin n) (hij : i < j) :
      ((z i - b i) - (z j - b j) + c) * (max (z i - z j) ε)⁻¹ ≤ 1 := by
    rw [mul_inv_le_iff₀ (hε.trans_le (le_max_right _ _))]
    linarith [hb i j hij, le_max_left (z i - z j) ε]
  calc
    _ = 2 * (n : ℝ)⁻¹ * (∑ i : Fin n, ∑ j ∈ Finset.Ioi i,
        ((z i - b i) - (z j - b j) + c) * (max (z i - z j) ε)⁻¹) := by
          simp_rw [add_mul, Finset.sum_add_distrib, ← Finset.mul_sum]
          ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j hj ↦ hp i j (Finset.mem_Ioi.1 hj))
      (by positivity)

/-- **Shifted quadratic Lyapunov estimate.** If the shifted forcing `a + w` has all ordered gaps
at least `c` up to time `t`, its squared Euclidean distance from the truncated trajectory, together
with the weighted integrated truncated inverse gaps, grows by at most `(n - 1) t`. The estimate
holds for every positive cutoff, arbitrary initial configurations, and continuous forcing. -/
theorem sum_truncatedDysonPath_sub_sq_add_integral_le {ε : ℝ} (hε : 0 < ε) (n : ℕ)
    (x a : Fin n → ℝ) (w : ℝ≥0 → Fin n → ℝ) (hw : Continuous w) (t : ℝ≥0) (c : ℝ)
    (hgap : ∀ s ≤ t, ∀ i j : Fin n, i < j → c ≤ (a i + w s i) - (a j + w s j)) :
    (∑ i : Fin n, (truncatedDysonPath hε n x w hw t i - w t i - a i) ^ 2) +
        2 * c * (n : ℝ)⁻¹ * (∫ s in (0 : ℝ)..t, ∑ i : Fin n, ∑ j ∈ Finset.Ioi i,
          (max (truncatedDysonPath hε n x w hw s.toNNReal i -
            truncatedDysonPath hε n x w hw s.toNNReal j) ε)⁻¹) ≤
      (∑ i : Fin n, (x i - a i) ^ 2) + (n - 1 : ℕ) * (t : ℝ) := by
  let X := truncatedDysonPath hε n x w hw
  let Z : ℝ → Fin n → ℝ := fun s ↦ X s.toNNReal - w s.toNNReal - a
  let E : ℝ → ℝ := fun s ↦ ∑ i : Fin n, (Z s i) ^ 2
  let D : ℝ → ℝ := fun s ↦ 2 * ∑ i : Fin n,
    Z s i * truncatedDysonDrift ε n (X s.toNNReal) i
  let G : ℝ → ℝ := fun s ↦ ∑ i : Fin n, ∑ j ∈ Finset.Ioi i,
    (max (X s.toNNReal i - X s.toNNReal j) ε)⁻¹
  have hX : Continuous fun s : ℝ ↦ X s.toNNReal :=
    (continuous_truncatedDysonPath hε n x w hw).comp continuous_real_toNNReal
  have hZ : Continuous Z := (hX.sub (hw.comp continuous_real_toNNReal)).sub continuous_const
  have hD : Continuous D := continuous_const.mul (continuous_finsetSum _ fun i _ ↦
    ((continuous_apply i).comp hZ).mul ((continuous_apply i).comp
      ((continuous_truncatedDysonDrift hε n).comp hX)))
  have hG : Continuous G := continuous_finsetSum _ fun i _ ↦
    continuous_finsetSum _ fun j _ ↦
      ((((continuous_apply i).comp hX).sub ((continuous_apply j).comp hX)).max
        continuous_const).inv₀ (fun _ ↦ ne_of_gt (hε.trans_le (le_max_right _ _)))
  have hE (r : ℝ) (hr : 0 < r) : HasDerivAt E (D r) r := by
    have hd := ((hasDerivWithinAt_truncatedDysonPath_sub hε n x w hw r hr.le).hasDerivAt
      (Ici_mem_nhds hr)).sub_const a
    have hc (i : Fin n) := (hasDerivAt_pi.1 hd i).pow 2
    simpa [E, D, Z, X, Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc] using
      HasDerivAt.fun_sum (fun i _ ↦ hc i)
  have hFTC : (∫ s in (0 : ℝ)..t, D s) = E t - E 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le t.coe_nonneg
      (continuous_finsetSum _ fun i _ ↦ ((continuous_apply i).comp hZ).pow 2).continuousOn
      (fun r hr ↦ hE r hr.1) (hD.intervalIntegrable 0 t)
  have hle : (∫ s in (0 : ℝ)..t, D s + 2 * c * (n : ℝ)⁻¹ * G s) ≤
      (n - 1 : ℕ) * (t : ℝ) := by
    calc
      _ ≤ ∫ _s in (0 : ℝ)..t, ((n - 1 : ℕ) : ℝ) :=
        intervalIntegral.integral_mono_on t.coe_nonneg
          ((hD.add (continuous_const.mul hG)).intervalIntegrable 0 t)
          (intervalIntegrable_const) fun s hs ↦ by
            have h := sum_sub_mul_truncatedDysonDrift_le hε n (X s.toNNReal)
              (a + w s.toNNReal) c
              (hgap s.toNNReal (Real.toNNReal_le_iff_le_coe.2 hs.2))
            have hshift : Z s = X s.toNNReal - (a + w s.toNNReal) := by
              dsimp only [Z]
              abel
            simpa only [Pi.add_apply, Pi.mul_apply, D, G, hshift, Pi.sub_apply] using h
      _ = _ := by simp [mul_comm]
  rw [intervalIntegral.integral_add (hD.intervalIntegrable 0 t)
    ((hG.intervalIntegrable 0 t).const_mul _), hFTC, intervalIntegral.integral_const_mul] at hle
  have h0 : E 0 = ∑ i : Fin n, (x i - a i) ^ 2 := by
    simp [E, Z, X]
  rw [h0] at hle
  have ht' : E t + 2 * c * (n : ℝ)⁻¹ * (∫ s in (0 : ℝ)..t, G s) ≤
      (∑ i : Fin n, (x i - a i) ^ 2) + (n - 1 : ℕ) * (t : ℝ) := by linarith
  simpa only [E, Z, X, Real.toNNReal_coe, Pi.sub_apply, G] using ht'

/-- **Cutoff-uniform nonexplosion.** For arbitrary initial configurations and continuous additive
forcing, the truncated trajectories for all positive cutoffs are bounded together on every compact
time interval. The bound depends only on the initial configuration, the forcing, and the horizon. -/
theorem exists_forall_norm_truncatedDysonPath_le (n : ℕ) (x : Fin n → ℝ)
    (w : ℝ≥0 → Fin n → ℝ) (hw : Continuous w) (T : ℝ≥0) :
    ∃ R : ℝ, ∀ (ε : ℝ) (hε : 0 < ε) (t : ℝ≥0), t ≤ T →
      ‖truncatedDysonPath hε n x w hw t‖ ≤ R := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (hw.continuousOn :
    ContinuousOn w (Icc 0 T))
  have hC₀ : 0 ≤ C := (norm_nonneg (w 0)).trans (hC 0 ⟨le_rfl, bot_le⟩)
  let a : Fin n → ℝ := fun i ↦ -(2 * C + 1) * (i : ℝ)
  have hgap (s : ℝ≥0) (hs : s ≤ T) (i j : Fin n) (hij : i < j) :
      0 ≤ (a i + w s i) - (a j + w s j) := by
    have hc (k : Fin n) : |w s k| ≤ C :=
      (norm_le_pi_norm (w s) k).trans (hC s ⟨bot_le, hs⟩)
    have hij' : (i : ℝ) + 1 ≤ (j : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt (Fin.lt_def.1 hij)
    have hmul := mul_le_mul_of_nonneg_left hij' (by positivity : 0 ≤ 2 * C + 1)
    dsimp only [a]
    linarith [(abs_le.1 (hc i)).1, (abs_le.1 (hc j)).2]
  let B : ℝ := (∑ i : Fin n, (x i - a i) ^ 2) + (n - 1 : ℕ) * (T : ℝ)
  refine ⟨Real.sqrt B + C + ‖a‖, fun ε hε t ht ↦ ?_⟩
  let X := truncatedDysonPath hε n x w hw
  have hE : (∑ i : Fin n, (X t i - w t i - a i) ^ 2) ≤ B := by
    have h := sum_truncatedDysonPath_sub_sq_add_integral_le hε n x a w hw t 0
      (fun s hs ↦ hgap s (hs.trans ht))
    simp only [mul_zero, zero_mul, add_zero] at h
    exact h.trans (add_le_add le_rfl
      (mul_le_mul_of_nonneg_left (NNReal.coe_le_coe.2 ht) (Nat.cast_nonneg (n - 1))))
  have hZ : ‖X t - w t - a‖ ≤ Real.sqrt B := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg B)).2 fun i ↦ ?_
    have hi : (X t i - w t i - a i) ^ 2 ≤ B :=
      (Finset.single_le_sum (fun k _ ↦ sq_nonneg (X t k - w t k - a k))
        (Finset.mem_univ i)).trans hE
    exact Real.abs_le_sqrt hi
  calc
    ‖X t‖ = ‖(X t - w t - a) + w t + a‖ := by congr 1; abel
    _ ≤ ‖X t - w t - a‖ + ‖w t‖ + ‖a‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ Real.sqrt B + C + ‖a‖ := add_le_add (add_le_add hZ (hC t ⟨bot_le, ht⟩)) le_rfl

end TauCeti.Probability

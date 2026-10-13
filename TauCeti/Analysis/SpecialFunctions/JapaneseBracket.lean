/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import TauCeti.Analysis.SpecialFunctions.Beta
import TauCeti.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# The integral of the Japanese bracket

Mathlib proves that `x ↦ (1 + ‖x‖ ^ 2) ^ (-r / 2)` is integrable on a finite-dimensional real
inner product space `V` of dimension `d` as soon as `d < r`
(`integrable_rpow_neg_one_add_norm_sq`). This file computes the integral:

`∫ x : V, (1 + ‖x‖ ^ 2) ^ (-r / 2) = π ^ (d / 2) Γ((r - d) / 2) / Γ(r / 2)`.

Integrating in polar coordinates and substituting `u = ‖x‖ ^ 2` turns the integral into Euler's
second beta integral `∫₀^∞ u ^ (a - 1) (1 + u) ^ (-(a + b)) du = Β(a, b)` with `a = d / 2` and
`b = (r - d) / 2` (`TauCeti.integral_rpow_mul_one_add_rpow`). For `r = d + 1` this is the
normalization of the multivariate Cauchy distribution and of the Poisson kernel of a half-space.

## Main declarations

* `TauCeti.integral_rpow_neg_one_add_norm_sq`: the value of the integral.
-/

public section

namespace TauCeti

open MeasureTheory Metric Module ProbabilityTheory Real Set

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- **The integral of the Japanese bracket.** On a real inner product space `V` of dimension
`d < r`, `∫ (1 + ‖x‖ ^ 2) ^ (-r / 2) = π ^ (d / 2) Γ((r - d) / 2) / Γ(r / 2)`. -/
theorem integral_rpow_neg_one_add_norm_sq {r : ℝ} (hr : (finrank ℝ V : ℝ) < r) :
    ∫ x : V, (1 + ‖x‖ ^ 2) ^ (-r / 2) =
      π ^ ((finrank ℝ V : ℝ) / 2) * Gamma ((r - finrank ℝ V) / 2) / Gamma (r / 2) := by
  have hr0 : 0 < r := lt_of_le_of_lt (finrank ℝ V).cast_nonneg hr
  rcases subsingleton_or_nontrivial V with hV | hV
  · -- In dimension zero the integral is the value at the only point, of volume one.
    have hvol : volume.real (univ : Set V) = 1 := by
      have h := (stdOrthonormalBasis ℝ V).volume_parallelepiped
      rw [Subsingleton.eq_univ_of_nonempty
        ⟨0, (mem_parallelepiped_iff _ _).2 ⟨0, ⟨le_rfl, zero_le_one⟩, by simp⟩⟩] at h
      rw [measureReal_def, h, ENNReal.toReal_one]
    have : Unique V := uniqueOfSubsingleton 0
    rw [integral_unique, hvol, finrank_zero_of_subsingleton, Subsingleton.elim (default : V) 0]
    simp [(Gamma_pos_of_pos (half_pos hr0)).ne']
  set d := finrank ℝ V with hd
  have hd0 : 0 < d := finrank_pos
  have hsum : (d : ℝ) / 2 + (r - d) / 2 = r / 2 := by ring
  -- The radial integral is half of Euler's second beta integral, after `u = y ^ 2`.
  have hrad : ∫ y in Ioi (0 : ℝ), y ^ (d - 1) • (1 + y ^ 2) ^ (-r / 2) =
      beta (d / 2) ((r - d) / 2) / 2 := by
    have h := integral_comp_rpow_Ioi (fun u : ℝ ↦
      (1 / 2 : ℝ) * (u ^ ((d : ℝ) / 2 - 1) * (1 + u) ^ (-((d : ℝ) / 2 + (r - d) / 2))))
      (p := 2) two_ne_zero
    rw [integral_const_mul, integral_rpow_mul_one_add_rpow (by positivity) (by linarith)] at h
    rw [show beta (d / 2) ((r - d) / 2) / 2 = 1 / 2 * beta (d / 2) ((r - d) / 2) by ring, ← h]
    refine setIntegral_congr_fun measurableSet_Ioi fun y (hy : 0 < y) ↦ ?_
    have hpow : (y ^ 2) ^ ((d : ℝ) / 2 - 1) * y = y ^ (d - 1) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hy.le, ← Real.rpow_natCast,
        Nat.cast_sub hd0, Nat.cast_one, ← Real.rpow_add_one hy.ne']
      ring_nf
    simp only [smul_eq_mul, hsum, abs_two, neg_div]
    rw [← hpow]
    norm_num
    ring
  have hΓ := Gamma_pos_of_pos (show 0 < (d : ℝ) / 2 by positivity)
  rw [integral_fun_norm_addHaar volume (fun t ↦ (1 + t ^ 2) ^ (-r / 2)), hrad, volume_real_unitBall,
    beta, nsmul_eq_mul, smul_eq_mul, Gamma_add_one (by positivity), hsum, ← hd]
  field_simp

end TauCeti

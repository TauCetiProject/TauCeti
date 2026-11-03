/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.ParallelVolume
public import TauCeti.MeasureTheory.Measure.Lebesgue.BrunnMinkowski.Parallel
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import TauCeti.Analysis.BoundedVariation.Convex
import TauCeti.Analysis.BoundedVariation.Isoperimetric
import TauCeti.Analysis.Convex.Measure

/-!
# Equality in the isoperimetric inequality for convex bodies

Let `K` be a convex body of positive volume `V` in a Euclidean space of dimension `n ≥ 1`, and
write `ω_n = volume (ball 0 1)` and `P(K)` for the perimeter of `K` in the whole space. Like every
null-measurable set of finite positive volume, `K` satisfies the isoperimetric inequality
`P(K)^n ≥ n^n ω_n V^(n-1)`
(`TauCeti.finrank_pow_mul_volume_ball_mul_volume_pow_le_perimeter_pow_of_volume_ne_zero`). For a
convex body, equality holds exactly when `K` is a closed ball of positive radius
(`ConvexBody.perimeter_pow_eq_iff_exists_eq_closedBall`). Balls have equality by
`TauCeti.perimeter_ball_pow`, which fixes the constant.

The perimeter is the first variation of parallel volume: the volume of `K + t • closedBall 0 1`
has right derivative `P(K)` at `t = 0` (`Convex.hasDerivWithinAt_measureReal_add_smul_closedBall`).
Hence its `n`-th root has right derivative `P(K) / (n V^(1 - 1/n))`
(`ConvexBody.hasDerivWithinAt_volume_real_add_smul_closedBall_rpow`). By the Brunn–Minkowski
inequality this derivative equals `ω_n^(1/n)` exactly when `K` is a closed ball
(`ConvexBody.hasDerivWithinAt_volume_real_add_smul_closedBall_rpow_iff_exists_eq_closedBall`),
which is the equality case.

## References

* R. Schneider, *Convex Bodies: The Brunn–Minkowski Theory*, 2nd ed., Cambridge University
  Press, 2014, Section 7.2, for the isoperimetric inequality as a case of Minkowski's first
  inequality.
* R. J. Gardner, *The Brunn–Minkowski inequality*, Bull. Amer. Math. Soc. **39** (2002),
  355–405, Section 5.
-/

public section

open MeasureTheory Metric Module Set TauCeti
open scoped ENNReal Pointwise

namespace ConvexBody

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- **The first variation of the parallel volume root of a convex body.** For a convex body `K`
of positive volume `V` in dimension `n`, the function
`t ↦ volume (K + t • closedBall 0 1) ^ (1 / n)` has right derivative `P(K) / (n V ^ (1 - 1 / n))`
at zero, where `P(K)` is the perimeter of `K`. -/
theorem hasDerivWithinAt_volume_real_add_smul_closedBall_rpow (K : ConvexBody E)
    (hK : volume (K : Set E) ≠ 0) :
    HasDerivWithinAt (fun t : ℝ ↦
      volume.real ((K : Set E) + t • closedBall (0 : E) 1) ^ (finrank ℝ E : ℝ)⁻¹)
      ((perimeter volume ⊤ (K : Set E)).toReal /
        (finrank ℝ E * volume.real (K : Set E) ^ (1 - (finrank ℝ E : ℝ)⁻¹))) (Ioi 0) 0 := by
  have hKi := (K.convex.addHaar_pos_iff_interior_nonempty (μ := volume)).1 (pos_iff_ne_zero.2 hK)
  have hf := (K.convex.hasDerivWithinAt_measureReal_add_smul_closedBall (μ := volume) K.isCompact
    hKi).mono Ioi_subset_Ici_self
  have h0 : volume.real ((K : Set E) + (0 : ℝ) • closedBall (0 : E) 1) =
      volume.real (K : Set E) := by
    rw [zero_smul_set (nonempty_closedBall.2 zero_le_one), add_zero]
  have hV : 0 < volume.real (K : Set E) :=
    ENNReal.toReal_pos hK K.isCompact.measure_lt_top.ne
  convert HasDerivWithinAt.rpow_const hf (p := (finrank ℝ E : ℝ)⁻¹) (Or.inl (h0 ▸ hV.ne'))
    using 1
  rw [h0, div_eq_mul_inv, mul_inv, ← Real.rpow_neg hV.le, neg_sub]
  ring

/-- **Equality in the isoperimetric inequality for convex bodies.** In dimension `n ≥ 1`, a
convex body `K` of positive volume satisfies `P(K)^n = n^n ω_n |K|^(n-1)`, where
`ω_n = volume (ball 0 1)`, exactly when it is a closed ball of positive radius. -/
theorem perimeter_pow_eq_iff_exists_eq_closedBall (K : ConvexBody E)
    (hn : finrank ℝ E ≠ 0) (hK : volume (K : Set E) ≠ 0) :
    perimeter volume ⊤ (K : Set E) ^ finrank ℝ E =
        (finrank ℝ E : ℝ≥0∞) ^ finrank ℝ E * volume (ball (0 : E) 1) *
          volume (K : Set E) ^ (finrank ℝ E - 1) ↔
      ∃ c : E, ∃ r : ℝ, 0 < r ∧ (K : Set E) = closedBall c r := by
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (Nat.pos_of_ne_zero hn)
  have hP : perimeter volume ⊤ (K : Set E) ≠ ⊤ :=
    (K.convex.perimeter_lt_top K.isCompact.isBounded).ne
  have hV : 0 < volume.real (K : Set E) :=
    ENNReal.toReal_pos hK K.isCompact.measure_lt_top.ne
  have hd := K.hasDerivWithinAt_volume_real_add_smul_closedBall_rpow hK
  rw [← K.hasDerivWithinAt_volume_real_add_smul_closedBall_rpow_iff_exists_eq_closedBall hn hK,
    Measure.addHaar_real_closedBall_eq_addHaar_real_ball,
    finrank_pow_mul_volume_ball_mul_volume_pow_eq_ofReal hn K.isCompact.measure_lt_top.ne,
    ← ENNReal.ofReal_toReal hP,
    ← ENNReal.ofReal_pow ENNReal.toReal_nonneg,
    ENNReal.ofReal_eq_ofReal_iff (by positivity) (by positivity),
    pow_left_inj₀ ENNReal.toReal_nonneg (by positivity) hn]
  refine ⟨fun h => hd.congr_deriv ?_, fun h => ?_⟩
  · rw [div_eq_iff (by positivity), h]
    ring
  · have := (uniqueDiffWithinAt_Ioi 0).eq_deriv _ hd h
    rw [div_eq_iff (by positivity)] at this
    rw [this]
    ring

end ConvexBody

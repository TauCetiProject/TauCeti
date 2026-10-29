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
import TauCeti.Analysis.Convex.Measure

/-!
# The isoperimetric inequality for convex bodies

Let `K` be a convex body of positive volume `V` in a Euclidean space of dimension `n ≥ 1`, and
write `ω_n = volume (ball 0 1)` and `P(K)` for the perimeter of `K` in the whole space. Then

`P(K)^n ≥ n^n ω_n V^(n-1)`

(`ConvexBody.finrank_pow_mul_volume_ball_mul_volume_pow_le_perimeter_pow`), with equality exactly
when `K` is a closed ball of positive radius
(`ConvexBody.perimeter_pow_eq_iff_exists_eq_closedBall`). Balls have equality by
`TauCeti.perimeter_ball_pow`, which fixes the constant.

The perimeter is the first variation of parallel volume: the volume of `K + t • closedBall 0 1`
has right derivative `P(K)` at `t = 0` (`Convex.hasDerivWithinAt_measureReal_add_smul_closedBall`).
Hence its `n`-th root has right derivative `P(K) / (n V^(1 - 1/n))`
(`ConvexBody.hasDerivWithinAt_volume_real_add_smul_closedBall_rpow`). By the Brunn–Minkowski
inequality this root is concave and bounded below by `V^(1/n) + t ω_n^(1/n)`, so the derivative is
at least `ω_n^(1/n)` (`ConvexBody.volume_real_rpow_le_of_hasDerivWithinAt`), which is the
inequality. The derivative equals `ω_n^(1/n)` exactly when `K` is a closed ball
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

/-- The `n`-th power of `n w^(1/n) V^(1 - 1/n)` is `n^n w V^(n - 1)`, read in `ℝ≥0∞`. -/
private theorem ofReal_mul_rpow_mul_rpow_pow {n : ℕ} (hn : n ≠ 0) {w V : ℝ} (hw : 0 ≤ w)
    (hV : 0 ≤ V) :
    ENNReal.ofReal ((n * w ^ (n : ℝ)⁻¹ * V ^ (1 - (n : ℝ)⁻¹)) ^ n) =
      (n : ℝ≥0∞) ^ n * ENNReal.ofReal w * ENNReal.ofReal V ^ (n - 1) := by
  have hV' : (V ^ (1 - (n : ℝ)⁻¹)) ^ n = V ^ (n - 1) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hV, ← Real.rpow_natCast,
      Nat.cast_sub (Nat.one_le_iff_ne_zero.2 hn), sub_mul,
      inv_mul_cancel₀ (Nat.cast_ne_zero.2 hn), one_mul, Nat.cast_one]
  rw [mul_pow, mul_pow, Real.rpow_inv_natCast_pow hw hn, hV', ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by positivity),
    ENNReal.ofReal_pow hV, ENNReal.ofReal_natCast]

/-- The isoperimetric inequality for a convex body of positive volume, in real-valued form
`n ω^(1/n) V^(1 - 1/n) ≤ P`. -/
private theorem mul_volume_real_rpow_mul_le_perimeter_toReal (K : ConvexBody E)
    (hn : finrank ℝ E ≠ 0) (hK : volume (K : Set E) ≠ 0) :
    finrank ℝ E * volume.real (ball (0 : E) 1) ^ (finrank ℝ E : ℝ)⁻¹ *
        volume.real (K : Set E) ^ (1 - (finrank ℝ E : ℝ)⁻¹) ≤
      (perimeter volume ⊤ (K : Set E)).toReal := by
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (Nat.pos_of_ne_zero hn)
  let B : ConvexBody E := ⟨closedBall 0 1, convex_closedBall 0 1, isCompact_closedBall 0 1,
    nonempty_closedBall.2 zero_le_one⟩
  have hB : (B : Set E) = closedBall 0 1 := ConvexBody.coe_mk _ _ _ _
  have hV : 0 < volume.real (K : Set E) :=
    ENNReal.toReal_pos hK K.isCompact.measure_lt_top.ne
  have h := K.volume_real_rpow_le_of_hasDerivWithinAt B hn
    (hB ▸ K.hasDerivWithinAt_volume_real_add_smul_closedBall_rpow hK)
  rw [hB, measureReal_def, Measure.addHaar_closedBall_eq_addHaar_ball, ← measureReal_def,
    le_div_iff₀ (by positivity)] at h
  linarith

/-- **The isoperimetric inequality for convex bodies.** In dimension `n ≥ 1`, a convex body `K`
of positive volume satisfies `P(K)^n ≥ n^n ω_n |K|^(n-1)`, where `ω_n = volume (ball 0 1)`. -/
theorem finrank_pow_mul_volume_ball_mul_volume_pow_le_perimeter_pow (K : ConvexBody E)
    (hn : finrank ℝ E ≠ 0) (hK : volume (K : Set E) ≠ 0) :
    (finrank ℝ E : ℝ≥0∞) ^ finrank ℝ E * volume (ball (0 : E) 1) *
        volume (K : Set E) ^ (finrank ℝ E - 1) ≤
      perimeter volume ⊤ (K : Set E) ^ finrank ℝ E := by
  have hP : perimeter volume ⊤ (K : Set E) ≠ ⊤ :=
    (K.convex.perimeter_lt_top K.isCompact.isBounded).ne
  rw [← ofReal_measureReal measure_ball_lt_top.ne,
    ← ofReal_measureReal K.isCompact.measure_lt_top.ne,
    ← ofReal_mul_rpow_mul_rpow_pow hn measureReal_nonneg measureReal_nonneg,
    ← ENNReal.ofReal_toReal hP, ← ENNReal.ofReal_pow ENNReal.toReal_nonneg]
  exact ENNReal.ofReal_le_ofReal
    (pow_le_pow_left₀ (by positivity) (K.mul_volume_real_rpow_mul_le_perimeter_toReal hn hK) _)

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
    measureReal_def, Measure.addHaar_closedBall_eq_addHaar_ball, ← measureReal_def,
    ← ofReal_measureReal measure_ball_lt_top.ne,
    ← ofReal_measureReal K.isCompact.measure_lt_top.ne,
    ← ofReal_mul_rpow_mul_rpow_pow hn measureReal_nonneg measureReal_nonneg,
    ← ENNReal.ofReal_toReal hP, ← ENNReal.ofReal_pow ENNReal.toReal_nonneg,
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

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import TauCeti.Analysis.SpecialFunctions.Pow.Real
import TauCeti.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# The real volume of the unit ball

Mathlib computes the volume of a ball in a finite-dimensional real inner product space as an
extended nonnegative real (`InnerProductSpace.volume_ball`). This file records the real volume of
the unit ball and closed unit ball in the form `π ^ (d / 2) / Γ(d / 2 + 1)`, where `d` is the
dimension, which is the form used in normalizing constants, and compares `vol (closedBall 0 1)`
from below with the inscribed cube `[-1 / √d, 1 / √d] ^ d` (`2 ^ d ≤ (√d) ^ d * vol`). It also
shows that every finite-dimensional real inner product space has a closed ball of volume one about
the origin, that a closed ball of radius `r` in a one-dimensional space has volume `2 * r`, and
that a disc of radius `r` in `ℂ` has real volume `π * r ^ 2`, so that a constant `c` on it has
`L²` norm `‖c‖ r √π`.

## Main results

* `TauCeti.volume_real_unitBall` and `TauCeti.volume_real_closedUnitBall`: real volume
  `π ^ (d / 2) / Γ(d / 2 + 1)` of the open and closed unit balls in dimension `d`.
* `TauCeti.exists_volume_closedBall_eq_one`: existence of an origin-centered closed ball of volume
  `1`.
* `TauCeti.two_pow_le_sqrt_finrank_pow_mul_volume_real_closedUnitBall`,
  `TauCeti.two_pow_div_volume_real_closedUnitBall_le_sqrt_finrank_pow`, and
  `TauCeti.two_pow_div_volume_real_closedUnitBall_le_pow_of_finrank_eq_two_mul`: inscribed-cube
  lower bounds on the closed unit ball volume.
* `TauCeti.volume_real_closedBall_of_finrank_eq_one` and `TauCeti.Complex.volume_real_ball`:
  one-dimensional and complex-plane ball volumes.
-/

public section

namespace TauCeti

open MeasureTheory Metric Module Real Set

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [Nontrivial V]

omit [Nontrivial V] in
/-- The real volume of the unit ball of a real inner product space of dimension `d` is
`π ^ (d / 2) / Γ(d / 2 + 1)`. -/
theorem volume_real_unitBall :
    volume.real (ball (0 : V) 1) =
      π ^ ((finrank ℝ V : ℝ) / 2) / Gamma (finrank ℝ V / 2 + 1) := by
  rcases subsingleton_or_nontrivial V with hV | hV
  · -- In the zero space the unit ball is the whole space.
    simp [measureReal_def, volume_eq_one_of_subsingleton (nonempty_ball.2 one_pos :
      (ball (0 : V) 1).Nonempty), finrank_zero_of_subsingleton]
  rw [measureReal_def, InnerProductSpace.volume_ball, ENNReal.ofReal_one, one_pow, one_mul,
    ENNReal.toReal_ofReal (by positivity), Real.pow_sqrt_eq_rpow pi_pos.le]

omit [Nontrivial V] in
/-- There is a closed ball about the origin of volume one. -/
theorem exists_volume_closedBall_eq_one : ∃ ρ : ℝ, 0 < ρ ∧ volume (closedBall (0 : V) ρ) = 1 := by
  rcases subsingleton_or_nontrivial V with hV | hV
  · -- In the zero space every closed ball is the whole space, the unit parallelepiped.
    refine ⟨1, one_pos, ?_⟩
    exact volume_eq_one_of_subsingleton (nonempty_closedBall.2 zero_le_one)
  -- Otherwise rescale the unit ball by `vol (ball 0 1) ^ (-1 / n)`.
  set n := finrank ℝ V
  set v := volume.real (ball (0 : V) 1)
  have hv : 0 < v :=
    ENNReal.toReal_pos (measure_ball_pos volume 0 one_pos).ne' measure_ball_lt_top.ne
  have hn : n ≠ 0 := finrank_pos.ne'
  refine ⟨v⁻¹ ^ (n⁻¹ : ℝ), by positivity, ?_⟩
  have hpow : (v⁻¹ ^ (n⁻¹ : ℝ)) ^ n = v⁻¹ := rpow_inv_natCast_pow (inv_nonneg.2 hv.le) hn
  have hinv : ENNReal.ofReal v⁻¹ = (volume (ball (0 : V) 1))⁻¹ := by
    rw [ENNReal.ofReal_inv_of_pos hv, ofReal_measureReal measure_ball_lt_top.ne]
  rw [Measure.addHaar_closedBall volume 0 (by positivity), hpow, hinv,
    ENNReal.inv_mul_cancel (measure_ball_pos volume 0 one_pos).ne' measure_ball_lt_top.ne]

omit [Nontrivial V] in
/-- The real volume of the closed unit ball of a real inner product space of dimension `d` is
`π ^ (d / 2) / Γ(d / 2 + 1)`. -/
theorem volume_real_closedUnitBall :
    volume.real (closedBall (0 : V) 1) =
      π ^ ((finrank ℝ V : ℝ) / 2) / Gamma (finrank ℝ V / 2 + 1) := by
  rcases subsingleton_or_nontrivial V with hV | hV
  · simp [measureReal_def, volume_eq_one_of_subsingleton (nonempty_closedBall.2 zero_le_one :
      (closedBall (0 : V) 1).Nonempty), finrank_zero_of_subsingleton]
  rw [measureReal_def, Measure.addHaar_closedBall_eq_addHaar_ball, ← measureReal_def,
    volume_real_unitBall]

omit [Nontrivial V] in
/-- The closed unit ball of a finite-dimensional real inner product space has positive real
volume, including in dimension zero where its volume is one. -/
theorem volume_real_closedUnitBall_pos : 0 < volume.real (closedBall (0 : V) 1) := by
  rw [volume_real_closedUnitBall]
  positivity

omit [Nontrivial V] in
/-- Comparing the closed unit ball of a `d`-dimensional real inner product space with the
inscribed cube `[-1 / √d, 1 / √d] ^ d` gives `2 ^ d ≤ (√d) ^ d * vol (closedBall 0 1)`,
including at `d = 0`. -/
theorem two_pow_le_sqrt_finrank_pow_mul_volume_real_closedUnitBall :
    (2 : ℝ) ^ finrank ℝ V ≤
      (√(finrank ℝ V : ℝ)) ^ finrank ℝ V * volume.real (closedBall (0 : V) 1) := by
  rcases subsingleton_or_nontrivial V with hV | hV
  · simp [volume_real_closedUnitBall, finrank_zero_of_subsingleton]
  set d := finrank ℝ V
  have hd_pos : 0 < (d : ℝ) := Nat.cast_pos.2 finrank_pos
  have hsqrt_pos : 0 < √(d : ℝ) := Real.sqrt_pos.2 hd_pos
  let b := stdOrthonormalBasis ℝ V
  -- Pull back to `EuclideanSpace ℝ (Fin d)` along `b.repr` and inscribe `[-1 / √d, 1 / √d] ^ d`.
  let box : Set (Fin d → ℝ) := univ.pi fun _ ↦ closedBall (0 : ℝ) (1 / √(d : ℝ))
  let cube : Set (EuclideanSpace ℝ (Fin d)) :=
    (MeasurableEquiv.toLp 2 (Fin d → ℝ)).symm ⁻¹' box
  have hsub : cube ⊆ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1 := by
    intro x hx
    rw [mem_closedBall_zero_iff]
    have hxi (i : Fin d) : ‖x i‖ ^ 2 ≤ (1 / √(d : ℝ)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (mem_closedBall_zero_iff.1 (hx i (mem_univ i))) 2
    have hsq : ‖x‖ ^ 2 ≤ 1 := by
      calc ‖x‖ ^ 2 = ∑ i : Fin d, ‖x i‖ ^ 2 := EuclideanSpace.norm_sq_eq x
        _ ≤ ∑ _ : Fin d, (1 / √(d : ℝ)) ^ 2 := Finset.sum_le_sum fun i _ ↦ hxi i
        _ = 1 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, div_pow, one_pow,
            Real.sq_sqrt hd_pos.le, mul_one_div_cancel hd_pos.ne']
    exact (sq_le_one_iff₀ (norm_nonneg x)).1 hsq
  have hvol_cube : volume cube = ENNReal.ofReal ((2 / √(d : ℝ)) ^ d) := by
    rw [(EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin d)).measure_preimage
      (MeasurableSet.univ_pi fun _ ↦ measurableSet_closedBall).nullMeasurableSet]
    simp only [volume_pi_pi, Real.volume_closedBall, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
    rw [mul_one_div, ENNReal.ofReal_pow (by positivity)]
  have hvol_eq : volume (closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) =
      volume (closedBall (0 : V) 1) := by
    rw [← b.measurePreserving_repr_symm.measure_preimage measurableSet_closedBall.nullMeasurableSet,
      LinearIsometryEquiv.preimage_closedBall, map_zero]
  have hle_enn : ENNReal.ofReal ((2 / √(d : ℝ)) ^ d) ≤ volume (closedBall (0 : V) 1) :=
    hvol_cube ▸ (measure_mono hsub).trans_eq hvol_eq
  have hle : (2 / √(d : ℝ)) ^ d ≤ volume.real (closedBall (0 : V) 1) := by
    rw [measureReal_def]
    exact (ENNReal.toReal_ofReal (by positivity)).symm.trans_le
      (ENNReal.toReal_mono measure_closedBall_lt_top.ne hle_enn)
  calc (2 : ℝ) ^ d
      = (√(d : ℝ)) ^ d * (2 / √(d : ℝ)) ^ d := by
        rw [div_pow, mul_div_cancel₀ _ (pow_ne_zero d hsqrt_pos.ne')]
    _ ≤ (√(d : ℝ)) ^ d * volume.real (closedBall (0 : V) 1) :=
        mul_le_mul_of_nonneg_left hle (by positivity)

omit [Nontrivial V] in
/-- For any `d`-dimensional real inner product space `V`,
`2 ^ d / vol (closedBall 0 1) ≤ (√d) ^ d`. -/
theorem two_pow_div_volume_real_closedUnitBall_le_sqrt_finrank_pow :
    (2 : ℝ) ^ finrank ℝ V / volume.real (closedBall (0 : V) 1) ≤
      (√(finrank ℝ V : ℝ)) ^ finrank ℝ V :=
  (div_le_iff₀ volume_real_closedUnitBall_pos).2
    two_pow_le_sqrt_finrank_pow_mul_volume_real_closedUnitBall

omit [Nontrivial V] in
/-- In an even-dimensional real inner product space of dimension `2 * k`,
`2 ^ k / vol (closedBall 0 1) ≤ k ^ k`. -/
theorem two_pow_div_volume_real_closedUnitBall_le_pow_of_finrank_eq_two_mul {k : ℕ}
    (hk : finrank ℝ V = 2 * k) :
    (2 : ℝ) ^ k / volume.real (closedBall (0 : V) 1) ≤ (k : ℝ) ^ k := by
  have h := two_pow_le_sqrt_finrank_pow_mul_volume_real_closedUnitBall (V := V)
  rw [hk] at h
  have hlhs : (2 : ℝ) ^ (2 * k) = (2 : ℝ) ^ k * (2 : ℝ) ^ k := by ring
  have hrhs : (√((2 * k : ℕ) : ℝ)) ^ (2 * k) = (2 : ℝ) ^ k * (k : ℝ) ^ k := by
    rw [pow_mul, Real.sq_sqrt (Nat.cast_nonneg _), Nat.cast_mul, Nat.cast_ofNat, mul_pow]
  rw [hlhs, hrhs, mul_assoc] at h
  exact (div_le_iff₀ volume_real_closedUnitBall_pos).2
    (le_of_mul_le_mul_left h (pow_pos zero_lt_two k))

omit [Nontrivial V] in
/-- In a one-dimensional real inner product space, a closed ball of radius `r ≥ 0` has volume
`2 * r`. -/
theorem volume_real_closedBall_of_finrank_eq_one (h : finrank ℝ V = 1) (x : V) {r : ℝ}
    (hr : 0 ≤ r) : volume.real (closedBall x r) = 2 * r := by
  rw [measureReal_def, InnerProductSpace.volume_closedBall_of_dim_odd (k := 0) h, h]
  simp [ENNReal.toReal_ofReal hr, mul_comm]

end TauCeti

namespace Complex

open MeasureTheory Metric Real

/-- A disc of radius `r ≥ 0` in `ℂ` has real volume `π * r ^ 2`. -/
theorem volume_real_ball (a : ℂ) {r : ℝ} (hr : 0 ≤ r) : volume.real (ball a r) = π * r ^ 2 := by
  simp [Measure.real, Complex.volume_ball, ENNReal.toReal_ofReal hr, mul_comm]

/-- The `L²` norm of a constant `c` on the closed disc of radius `R` in `ℂ` is `‖c‖ R √π`, the
square root of the disc area `π R²` times `‖c‖`. -/
theorem eLpNorm_two_indicator_closedBall_const {E : Type*} [NormedAddCommGroup E] (a : ℂ)
    (c : E) {R : ℝ} (hR : 0 ≤ R) :
    eLpNorm ((closedBall a R).indicator fun _ ↦ c) 2 volume = ‖c‖ₑ * ENNReal.ofReal (R * √π) := by
  rw [eLpNorm_indicator_const measurableSet_closedBall.nullMeasurableSet two_ne_zero
    ENNReal.ofNat_ne_top, Complex.volume_closedBall]
  congr 1
  -- The area `R² π` is the square of `R √π`.
  have harea : ENNReal.ofReal R ^ 2 * NNReal.pi = ENNReal.ofReal (R * √π) ^ 2 := by
    rw [ENNReal.ofReal_mul hR, mul_pow, ← ENNReal.ofReal_pow (Real.sqrt_nonneg π),
      Real.sq_sqrt Real.pi_pos.le, ← ENNReal.ofReal_coe_nnreal, NNReal.coe_real_pi]
  rw [harea, ENNReal.toReal_ofNat, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

end Complex

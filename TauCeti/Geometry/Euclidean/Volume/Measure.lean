/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Euclidean.Volume.Measure
public import Mathlib.MeasureTheory.Measure.Regular
public import TauCeti.MeasureTheory.Measure.Hausdorff
import TauCeti.MeasureTheory.Covering.HausdorffDensity
import TauCeti.MeasureTheory.Measure.Lebesgue.Isodiametric

/-!
# Comparing Euclidean and raw Hausdorff measures

Mathlib's Euclidean Hausdorff measure `μHE[d]` is the raw Hausdorff measure `μH[d]` rescaled by
the constant that makes it agree with Lebesgue measure on `d`-dimensional Euclidean space. This
constant is positive and finite, so the two normalizations have the same null sets and the same
sets of finite measure; statements of either kind may be proved with either normalization.
In dimension zero, Hausdorff measure is counting measure
(`TauCeti.hausdorffMeasure_zero_eq_count`). In dimension one the normalizing constant is `1`,
because `μH[1]` already agrees with Lebesgue measure on `ℝ`. Hence `μHE[1] = μH[1]` on every
extended metric space, so length statements may be proved with either normalization.

In every dimension `k` the normalizing constant is `ω_k / 2 ^ k`, where `ω_k` is the volume of the
unit ball of `EuclideanSpace ℝ (Fin k)`: `μHE[k] = (ω_k / 2 ^ k) • μH[k]` on every extended metric
space (`TauCeti.euclideanHausdorffMeasure_eq_smul_hausdorffMeasure`). On `EuclideanSpace ℝ (Fin k)`
itself, the density comparison of `TauCeti.MeasureTheory.Covering.HausdorffDensity` applied to
volume gives one inequality, and the isodiametric inequality the other
(`EuclideanSpace.volume_eq_smul_hausdorffMeasure`). In this normalization the density comparison
reads `c * μHE[k] A ≤ μ U` whenever `μ (closedBall x r) ≥ c ω_k r ^ k` along arbitrarily small radii
at every `x ∈ A` (`MeasureTheory.Measure.mul_euclideanHausdorffMeasure_le_measure_of_isOpen`), and a
null-measurable set `A` of finite `μHE[k]` measure satisfies
`μHE[k] (A ∩ closedBall x r) / (ω_k r ^ k) → 0` for `μHE[k]`-almost every `x ∉ A`
(`TauCeti.ae_tendsto_euclideanHausdorffMeasure_inter_closedBall_div`).

On a nonempty affine subspace `s` of a Euclidean affine space, volume on the direction of `s`,
transported to `s` by adding a base point, is the Euclidean Hausdorff measure of the dimension
of `s` (`AffineSubspace.volume_preimage_coe_vadd`). These coordinates `v ↦ v +ᵥ q` are Mathlib's
`IsometryEquiv.vaddConst q` followed by the inclusion of `s`
(`AffineSubspace.val_comp_vaddConst`), so they form an isometry onto `s`
(`AffineSubspace.isometry_coe_vadd`, `AffineSubspace.range_coe_vadd`).

## References

* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised edition,
  Theorem 2.10 and Theorem 2.4 (the normalization of Hausdorff measure).
-/

public section

open MeasureTheory Module Set
open scoped ENNReal

namespace MeasureTheory.Measure

section Comparison

variable {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- A set is null for the Euclidean Hausdorff measure `μHE[d]` if and only if it is null for the
raw Hausdorff measure `μH[d]`. -/
@[simp]
theorem euclideanHausdorffMeasure_eq_zero_iff {d : ℕ} {s : Set X} :
    μHE[d] s = 0 ↔ μH[d] s = 0 := by
  rw [euclideanHausdorffMeasure_def, smul_apply, ENNReal.smul_def, smul_eq_mul, mul_eq_zero,
    ENNReal.coe_eq_zero,
    or_iff_right (addHaarScalarFactor_volume_hausdorffMeasure_ne_zero d)]

/-- A set has finite Euclidean Hausdorff measure `μHE[d]` if and only if it has finite raw
Hausdorff measure `μH[d]`. -/
@[simp]
theorem euclideanHausdorffMeasure_lt_top_iff {d : ℕ} {s : Set X} :
    μHE[d] s < ∞ ↔ μH[d] s < ∞ := by
  rw [euclideanHausdorffMeasure_def, smul_apply, ENNReal.smul_def, smul_eq_mul]
  simp [lt_top_iff_ne_top, ENNReal.mul_eq_top, addHaarScalarFactor_volume_hausdorffMeasure_ne_zero]

end Comparison

/-- The one-dimensional Euclidean Hausdorff measure is the raw one-dimensional Hausdorff measure,
on every extended metric space. -/
theorem euclideanHausdorffMeasure_one {X : Type*} [EMetricSpace X] [MeasurableSpace X]
    [BorelSpace X] : (μHE[1] : Measure X) = μH[1] := by
  have hℝ : (μHE[1] : Measure ℝ) = μH[1] := by
    rw [hausdorffMeasure_real, ← InnerProductSpace.euclideanHausdorffMeasure_eq_volume,
      Module.finrank_self]
  have hreal : (μH[((1 : ℕ) : ℝ)] : Measure ℝ) = volume := by
    rw [Nat.cast_one, hausdorffMeasure_real]
  have hc : addHaarScalarFactor (volume : Measure (EuclideanSpace ℝ (Fin 1)))
      μH[((1 : ℕ) : ℝ)] = 1 := by
    have h := congr($hℝ (Icc (0 : ℝ) 1))
    rw [euclideanHausdorffMeasure_def, smul_apply, hreal, hausdorffMeasure_real] at h
    simpa using h
  rw [euclideanHausdorffMeasure_def, hc, one_smul, Nat.cast_one]

end MeasureTheory.Measure

section Normalization

open Filter Metric MeasureTheory Measure
open scoped Topology

namespace EuclideanSpace

/-- The normalizing constant `ω_k / 2 ^ k` is nonzero, where `ω_k` is the volume of the unit ball
of `EuclideanSpace ℝ (Fin k)`. -/
theorem volume_ball_div_two_pow_ne_zero (k : ℕ) :
    volume (ball (0 : EuclideanSpace ℝ (Fin k)) 1) / 2 ^ k ≠ 0 :=
  ENNReal.div_ne_zero.2 ⟨(measure_ball_pos _ _ one_pos).ne', by simp⟩

/-- The normalizing constant `ω_k / 2 ^ k` is finite, where `ω_k` is the volume of the unit ball
of `EuclideanSpace ℝ (Fin k)`. -/
theorem volume_ball_div_two_pow_ne_top (k : ℕ) :
    volume (ball (0 : EuclideanSpace ℝ (Fin k)) 1) / 2 ^ k ≠ ∞ :=
  ENNReal.div_ne_top measure_ball_lt_top.ne (by simp)

/-- The volume of a closed ball of radius `r ≥ 0` in `EuclideanSpace ℝ (Fin k)` is
`(ω_k / 2 ^ k) (2 r) ^ k`, where `ω_k` is the volume of the unit ball. -/
theorem volume_closedBall_eq_div_mul {k : ℕ} (x : EuclideanSpace ℝ (Fin k)) {r : ℝ}
    (hr : 0 ≤ r) :
    volume (closedBall x r) = volume (ball (0 : EuclideanSpace ℝ (Fin k)) 1) / 2 ^ k *
      ENNReal.ofReal (2 * r) ^ (k : ℝ) := by
  rw [Measure.addHaar_closedBall _ _ hr, finrank_euclideanSpace_fin]
  -- `ofReal (2 r) ^ k = 2 ^ k * ofReal r ^ k`; the factor `2 ^ k` cancels the division.
  simp only [ENNReal.rpow_natCast, ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_ofNat,
    ENNReal.ofReal_pow hr, mul_pow]
  rw [← mul_assoc, ENNReal.div_mul_cancel (by simp) (by simp), mul_comm]

/-- On `EuclideanSpace ℝ (Fin k)`, volume is `(ω_k / 2 ^ k) • μH[k]`, where `ω_k` is the volume
of the unit ball: the density comparison gives one inequality and the isodiametric inequality the
other. This is the Euclidean counterpart of Mathlib's `hausdorffMeasure_pi_real`. -/
theorem volume_eq_smul_hausdorffMeasure (k : ℕ) :
    (volume : Measure (EuclideanSpace ℝ (Fin k))) =
      (volume (ball (0 : EuclideanSpace ℝ (Fin k)) 1) / 2 ^ k) • μH[k] := by
  set ω' := volume (ball (0 : EuclideanSpace ℝ (Fin k)) 1) / 2 ^ k
  have hω0 : ω' ≠ 0 := volume_ball_div_two_pow_ne_zero k
  have hωtop : ω' ≠ ∞ := volume_ball_div_two_pow_ne_top k
  refine le_antisymm (Measure.le_iff'.2 fun s => ?_) (Measure.le_iff'.2 fun s => ?_)
  · -- Isodiametric inequality: `volume s ≤ ω' ediam s ^ k`.
    have hle : ω'⁻¹ • (volume : Measure (EuclideanSpace ℝ (Fin k))) ≤ μH[k] :=
      le_hausdorffMeasure _ _ 1 one_pos fun t _ => by
        rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_le_iff hω0 hωtop, ENNReal.rpow_natCast]
        refine (TauCeti.volume_le_ediam_div_two_pow_mul_volume_ball t).trans_eq ?_
        simp only [finrank_euclideanSpace_fin, ω', div_eq_mul_inv, mul_pow, ENNReal.inv_pow]
        ring
    rw [Measure.smul_apply, smul_eq_mul, ← ENNReal.inv_mul_le_iff hω0 hωtop]
    simpa using hle s
  · rw [Measure.smul_apply, smul_eq_mul]
    exact mul_hausdorffMeasure_le_measure volume (Nat.cast_nonneg k) fun x _ =>
      (eventually_mem_nhdsWithin.mono fun r (hr : 0 < r) =>
        (volume_closedBall_eq_div_mul x hr.le).ge).frequently

end EuclideanSpace

namespace TauCeti

variable {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- **Normalization of Euclidean Hausdorff measure.** Mathlib's `k`-dimensional Euclidean
Hausdorff measure is `ω_k / 2 ^ k` times the raw `k`-dimensional Hausdorff measure, where
`ω_k` is the volume of the unit ball of `EuclideanSpace ℝ (Fin k)`. For `k = 1` this is
`MeasureTheory.Measure.euclideanHausdorffMeasure_one`. -/
theorem euclideanHausdorffMeasure_eq_smul_hausdorffMeasure (k : ℕ) :
    (μHE[k] : Measure X) = (volume (ball (0 : EuclideanSpace ℝ (Fin k)) 1) / 2 ^ k) • μH[k] := by
  set ω' := volume (ball (0 : EuclideanSpace ℝ (Fin k)) 1) / 2 ^ k
  set a := addHaarScalarFactor (volume : Measure (EuclideanSpace ℝ (Fin k))) μH[k]
  suffices ha : (a : ℝ≥0∞) = ω' by
    rw [euclideanHausdorffMeasure_def, ← ha, ENNReal.smul_def]
  -- Compare the two expressions for volume on `EuclideanSpace ℝ (Fin k)` at the unit ball.
  have hdef := congr($(EuclideanSpace.euclideanHausdorffMeasure_eq_volume k)
    (ball (0 : EuclideanSpace ℝ (Fin k)) 1))
  have hvol := congr($(EuclideanSpace.volume_eq_smul_hausdorffMeasure k)
    (ball (0 : EuclideanSpace ℝ (Fin k)) 1))
  rw [euclideanHausdorffMeasure_def, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at hdef
  rw [Measure.smul_apply, smul_eq_mul] at hvol
  have hB0 : μH[k] (ball (0 : EuclideanSpace ℝ (Fin k)) 1) ≠ 0 := fun h0 =>
    (measure_ball_pos volume (0 : EuclideanSpace ℝ (Fin k)) one_pos).ne'
      (by rw [hvol, h0, mul_zero])
  have hBtop : μH[k] (ball (0 : EuclideanSpace ℝ (Fin k)) 1) ≠ ∞ := fun htop => by
    exact measure_ball_lt_top.ne (hvol.trans (by
      rw [htop]; exact ENNReal.mul_top (EuclideanSpace.volume_ball_div_two_pow_ne_zero k)))
  exact (ENNReal.mul_left_inj hB0 hBtop).1 (hdef.trans hvol)

end TauCeti

namespace MeasureTheory.Measure

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- **Density comparison for Euclidean Hausdorff measure**, open-set form. If at every point `x`
of `A` there are arbitrarily small radii `r > 0` with `c ω_k r ^ k ≤ μ (closedBall x r)`, where
`ω_k r ^ k` is the volume of a ball of radius `r` in `EuclideanSpace ℝ (Fin k)`, then
`c * μHE[k] A ≤ μ U` for every open set `U` containing `A`. -/
theorem mul_euclideanHausdorffMeasure_le_measure_of_isOpen (μ : Measure X) (k : ℕ) {c : ℝ≥0∞}
    {A U : Set X} (hU : IsOpen U) (hAU : A ⊆ U)
    (h : ∀ x ∈ A, ∃ᶠ r in 𝓝[>] 0,
      c * volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r) ≤ μ (closedBall x r)) :
    c * μHE[k] A ≤ μ U := by
  rw [TauCeti.euclideanHausdorffMeasure_eq_smul_hausdorffMeasure, smul_apply, smul_eq_mul,
    ← mul_assoc]
  refine mul_hausdorffMeasure_le_measure_of_isOpen μ (Nat.cast_nonneg k) hU hAU fun x hx =>
    (h x hx).mp (eventually_mem_nhdsWithin.mono fun r (hr : 0 < r) hle => ?_)
  rwa [EuclideanSpace.volume_closedBall_eq_div_mul 0 hr.le, ← mul_assoc] at hle

/-- **Density comparison for Euclidean Hausdorff measure**, outer regular form. If `μ` is outer
regular and at every point `x` of `A` there are arbitrarily small radii `r > 0` with
`c ω_k r ^ k ≤ μ (closedBall x r)`, then `c * μHE[k] A ≤ μ A`. -/
theorem mul_euclideanHausdorffMeasure_le_measure (μ : Measure X) [μ.OuterRegular] (k : ℕ)
    {c : ℝ≥0∞} {A : Set X}
    (h : ∀ x ∈ A, ∃ᶠ r in 𝓝[>] 0,
      c * volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r) ≤ μ (closedBall x r)) :
    c * μHE[k] A ≤ μ A := by
  refine le_of_forall_gt fun b hb => ?_
  obtain ⟨U, hAU, hU, hUb⟩ := A.exists_isOpen_lt_of_lt b hb
  exact (mul_euclideanHausdorffMeasure_le_measure_of_isOpen μ k hU hAU h).trans_lt hUb

end MeasureTheory.Measure

namespace TauCeti

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- **Zero density outside a set**, Euclidean normalization. A null-measurable set `A` of finite
`k`-dimensional Euclidean Hausdorff measure satisfies
`μHE[k] (A ∩ closedBall x r) / (ω_k r ^ k) → 0` as `r → 0⁺` for `μHE[k]`-almost every `x ∉ A`,
where `ω_k r ^ k` is the volume of a ball of radius `r` in `EuclideanSpace ℝ (Fin k)`. -/
theorem ae_tendsto_euclideanHausdorffMeasure_inter_closedBall_div (k : ℕ) {A : Set X}
    (hA : NullMeasurableSet A μHE[k]) (hAfin : μHE[k] A ≠ ∞) :
    ∀ᵐ x ∂μHE[k], x ∉ A → Tendsto (fun r => μHE[k] (A ∩ closedBall x r) /
      volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0) (𝓝 0) := by
  set ω' := volume (ball (0 : EuclideanSpace ℝ (Fin k)) 1) / 2 ^ k
  have hω0 : ω' ≠ 0 := EuclideanSpace.volume_ball_div_two_pow_ne_zero k
  have hωtop : ω' ≠ ∞ := EuclideanSpace.volume_ball_div_two_pow_ne_top k
  rw [euclideanHausdorffMeasure_eq_smul_hausdorffMeasure] at hA hAfin ⊢
  replace hAfin : μH[k] A ≠ ∞ := fun h => hAfin (by
    rw [Measure.smul_apply, smul_eq_mul, h]; exact ENNReal.mul_top hω0)
  refine ae_smul_measure ?_ _
  filter_upwards [ae_tendsto_hausdorffMeasure_inter_closedBall_div (Nat.cast_nonneg k)
    (hA.mono_ac (absolutelyContinuous_smul hω0)) hAfin] with x hx hxA
  refine (hx hxA).congr' (eventually_mem_nhdsWithin.mono fun r (hr : 0 < r) => ?_)
  dsimp only
  rw [Measure.smul_apply, smul_eq_mul, EuclideanSpace.volume_closedBall_eq_div_mul 0 hr.le,
    ENNReal.mul_div_mul_left _ _ hω0 hωtop]

end TauCeti

end Normalization

namespace AffineSubspace

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- Adding a base point `q` of `s` to the directions of `s` and including the result in `P` is
`IsometryEquiv.vaddConst q` followed by the inclusion of `s`. -/
theorem val_comp_vaddConst (s : AffineSubspace ℝ P) [Nonempty s] (q : s) :
    Subtype.val ∘ IsometryEquiv.vaddConst q = fun v : s.direction ↦ ((v +ᵥ q : s) : P) :=
  funext fun v ↦ by rw [Function.comp_apply, IsometryEquiv.vaddConst_apply]

/-- Adding a base point `q` of `s` to the directions of `s` is an isometry into `P`. -/
theorem isometry_coe_vadd (s : AffineSubspace ℝ P) [Nonempty s] (q : s) :
    Isometry fun v : s.direction ↦ ((v +ᵥ q : s) : P) := by
  rw [← s.val_comp_vaddConst q]
  exact isometry_subtype_coe.comp (IsometryEquiv.vaddConst q).isometry

/-- Adding a base point `q` of `s` to the directions of `s` reaches exactly the points of `s`. -/
theorem range_coe_vadd (s : AffineSubspace ℝ P) [Nonempty s] (q : s) :
    range (fun v : s.direction ↦ ((v +ᵥ q : s) : P)) = s := by
  rw [← s.val_comp_vaddConst q, range_comp, (IsometryEquiv.vaddConst q).range_eq_univ, image_univ,
    Subtype.range_coe]

variable [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V] [MeasurableSpace P]
  [BorelSpace P]

/-- Volume on the direction of an affine subspace `s`, transported to `s` by adding a base point
`q`, is the Euclidean Hausdorff measure of the dimension of `s`: the volume of the set of
directions `v` with `v +ᵥ q ∈ t` is `μHE[finrank ℝ s.direction] (t ∩ s)`. -/
theorem volume_preimage_coe_vadd (s : AffineSubspace ℝ P) [Nonempty s] (q : s) (t : Set P) :
    volume ((fun v : s.direction ↦ ((v +ᵥ q : s) : P)) ⁻¹' t) =
      μHE[finrank ℝ s.direction] (t ∩ s) := by
  rw [← InnerProductSpace.euclideanHausdorffMeasure_eq_volume, ← s.val_comp_vaddConst q,
    preimage_comp, (IsometryEquiv.vaddConst q).isometry.euclideanHausdorffMeasure_preimage,
    (IsometryEquiv.vaddConst q).range_eq_univ, inter_univ, euclideanHausdorffMeasure_preimage_coe]

end AffineSubspace

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Body
public import Mathlib.Analysis.Convex.Deriv
public import TauCeti.Analysis.Convex.Parallel
public import TauCeti.MeasureTheory.Measure.Lebesgue.BrunnMinkowski.Basic
-- Proof-only: the equality cases of Brunn–Minkowski for convex bodies.
import TauCeti.MeasureTheory.Measure.Lebesgue.BrunnMinkowski.Homothety

/-!
# Concavity of parallel volume and its extremal bodies

For convex bodies `K` and `L` in a positive-dimensional Euclidean space of dimension `n`,
the function `t ↦ volume.real (K + t • L) ^ (n : ℝ)⁻¹` is concave on `t ≥ 0`.
Here a convex body is compact and nonempty, but may have empty interior or zero volume.
All volumes in these real-valued statements are finite by compactness.

Brunn–Minkowski also bounds this function below by the affine function with intercept
`volume.real K ^ (n : ℝ)⁻¹` and slope `volume.real L ^ (n : ℝ)⁻¹`.
Consequently, whenever the right derivative at zero exists, it is at least this slope.
Equality holds exactly when the whole volume profile equals that affine function.
For the closed unit ball `L`, this is the concave tangent argument that turns a sharp
first-variation identity into equality in Brunn–Minkowski at every positive radius.
The derivative is an explicit hypothesis; no perimeter or first-variation formula is asserted.

When `K` and `L` both have positive volume, the equality case of Brunn–Minkowski for convex
bodies identifies the extremal profiles: the right derivative at zero equals the volume root
of `L` exactly when `L` is homothetic to `K`. For the closed unit ball `L`, the right derivative
equals `volume (closedBall 0 1) ^ (1 / n)` exactly when `K` is a closed ball of positive radius.
This is the step of the ball-rigidity argument for the sharp isoperimetric inequality that
passes from a sharp first variation of parallel volume to the shape of `K`.

The concavity proof combines `Convex.add_smul_interpolation` with
`TauCeti.mul_volume_real_rpow_add_mul_volume_real_rpow_le`. The derivative comparison uses
Mathlib's `ConcaveOn.slope_le_of_hasDerivWithinAt_Ioi`. The homothety characterization applies
`Convex.volume_real_smul_add_smul_rpow_eq_iff` at a single positive parameter.

## References

* R. J. Gardner, *The Brunn–Minkowski inequality*, Bull. Amer. Math. Soc. **39** (2002),
  355–405, for concavity of volume roots and the first Minkowski inequality.
* R. Schneider, *Convex Bodies: The Brunn–Minkowski Theory*, 2nd ed., Cambridge University
  Press, 2014, Section 7.2, for the equality case of the first Minkowski inequality.
-/

public section

open MeasureTheory Metric Set
open scoped Pointwise

namespace ConvexBody

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The dimension root of the volume of parallel convex bodies is concave for nonnegative
parameters. No positive-volume or interior hypothesis is needed. -/
theorem concaveOn_volume_real_add_smul_rpow (K L : ConvexBody E)
    (hn : Module.finrank ℝ E ≠ 0) :
    ConcaveOn ℝ (Ici 0) (fun t : ℝ ↦
      volume.real ((K : Set E) + t • (L : Set E)) ^ (Module.finrank ℝ E : ℝ)⁻¹) := by
  refine ⟨convex_Ici _, fun s hs t ht p q hp hq hpq ↦ ?_⟩
  have hS := K.isCompact.add (L.isCompact.smul s)
  have hT := K.isCompact.add (L.isCompact.smul t)
  have hU := K.isCompact.add (L.isCompact.smul (p * s + q * t))
  have h := TauCeti.mul_volume_real_rpow_add_mul_volume_real_rpow_le hn
    (K.nonempty.add L.nonempty.smul_set) hS.measurableSet.nullMeasurableSet
    (K.nonempty.add L.nonempty.smul_set) hT.measurableSet.nullMeasurableSet hp hq
    (by rw [K.convex.add_smul_interpolation L.convex hp hq hpq hs ht]
        exact hU.measure_lt_top.ne)
  simpa only [K.convex.add_smul_interpolation L.convex hp hq hpq hs ht,
    smul_eq_mul] using h

/-- The dimension root of parallel volume is bounded below by the affine function whose
intercept and slope are the volume roots of the two convex bodies. -/
theorem volume_real_rpow_add_mul_le_volume_real_add_smul_rpow (K L : ConvexBody E)
    (hn : Module.finrank ℝ E ≠ 0) {t : ℝ} (ht : 0 ≤ t) :
    volume.real (K : Set E) ^ (Module.finrank ℝ E : ℝ)⁻¹ +
      t * volume.real (L : Set E) ^ (Module.finrank ℝ E : ℝ)⁻¹ ≤
        volume.real ((K : Set E) + t • (L : Set E)) ^ (Module.finrank ℝ E : ℝ)⁻¹ := by
  simpa only [one_mul, one_smul] using
    TauCeti.mul_volume_real_rpow_add_mul_volume_real_rpow_le hn
      K.nonempty K.isCompact.measurableSet.nullMeasurableSet
      L.nonempty L.isCompact.measurableSet.nullMeasurableSet zero_le_one ht
      (by simpa only [one_smul] using (K.isCompact.add (L.isCompact.smul t)).measure_lt_top.ne)

/-- The dimension root of parallel volume is bounded above on nonnegative parameters by
its tangent at zero whenever the right derivative exists. -/
theorem volume_real_add_smul_rpow_le_of_hasDerivWithinAt (K L : ConvexBody E)
    (hn : Module.finrank ℝ E ≠ 0) {d : ℝ}
    (hd : HasDerivWithinAt (fun t : ℝ ↦
      volume.real ((K : Set E) + t • (L : Set E)) ^ (Module.finrank ℝ E : ℝ)⁻¹)
      d (Ioi 0) 0) {t : ℝ} (ht : 0 ≤ t) :
    volume.real ((K : Set E) + t • (L : Set E)) ^ (Module.finrank ℝ E : ℝ)⁻¹ ≤
      volume.real (K : Set E) ^ (Module.finrank ℝ E : ℝ)⁻¹ + t * d := by
  obtain rfl | htpos := ht.eq_or_lt
  · simp [zero_smul_set L.nonempty]
  have hconc := K.concaveOn_volume_real_add_smul_rpow L hn
  have htangent := hconc.slope_le_of_hasDerivWithinAt_Ioi (by simp) ht htpos hd
  simp only [slope_def_field, zero_smul_set L.nonempty, add_zero, sub_zero] at htangent
  linarith [(div_le_iff₀ htpos).1 htangent]

/-- If the right derivative of the parallel volume root exists at zero, it is bounded
below by the volume root of the added convex body. -/
theorem volume_real_rpow_le_of_hasDerivWithinAt (K L : ConvexBody E)
    (hn : Module.finrank ℝ E ≠ 0) {d : ℝ}
    (hd : HasDerivWithinAt (fun t : ℝ ↦
      volume.real ((K : Set E) + t • (L : Set E)) ^ (Module.finrank ℝ E : ℝ)⁻¹)
      d (Ioi 0) 0) :
    volume.real (L : Set E) ^ (Module.finrank ℝ E : ℝ)⁻¹ ≤ d := by
  have hlower := K.volume_real_rpow_add_mul_le_volume_real_add_smul_rpow L hn
    (t := 1) zero_le_one
  have hupper := K.volume_real_add_smul_rpow_le_of_hasDerivWithinAt L hn hd
    (t := 1) zero_le_one
  linarith

/-- The right derivative at zero attains its Brunn–Minkowski lower bound exactly when
the dimension root of parallel volume is affine on the entire nonnegative half-line.
This includes zero-volume convex bodies. -/
theorem hasDerivWithinAt_volume_real_add_smul_rpow_iff (K L : ConvexBody E)
    (hn : Module.finrank ℝ E ≠ 0) :
    HasDerivWithinAt (fun t : ℝ ↦
      volume.real ((K : Set E) + t • (L : Set E)) ^ (Module.finrank ℝ E : ℝ)⁻¹)
      (volume.real (L : Set E) ^ (Module.finrank ℝ E : ℝ)⁻¹) (Ioi 0) 0 ↔
    ∀ t : ℝ, 0 ≤ t →
      volume.real ((K : Set E) + t • (L : Set E)) ^ (Module.finrank ℝ E : ℝ)⁻¹ =
        volume.real (K : Set E) ^ (Module.finrank ℝ E : ℝ)⁻¹ +
          t * volume.real (L : Set E) ^ (Module.finrank ℝ E : ℝ)⁻¹ := by
  constructor
  · intro hd t ht
    exact le_antisymm (K.volume_real_add_smul_rpow_le_of_hasDerivWithinAt L hn hd ht)
      (K.volume_real_rpow_add_mul_le_volume_real_add_smul_rpow L hn ht)
  · intro h
    have hd := ((hasDerivAt_id (0 : ℝ)).mul_const
      (volume.real (L : Set E) ^ (Module.finrank ℝ E : ℝ)⁻¹)).const_add
      (volume.real (K : Set E) ^ (Module.finrank ℝ E : ℝ)⁻¹)
    simp only [one_mul] at hd
    exact hd.hasDerivWithinAt.congr (fun t ht ↦ h t ht.le) (h 0 le_rfl)

/-- For convex bodies `K` and `L` of positive volume, the right derivative at zero of the
dimension root of parallel volume attains its Brunn–Minkowski lower bound
`volume L ^ (1 / n)` exactly when `L` is homothetic to `K`. -/
theorem hasDerivWithinAt_volume_real_add_smul_rpow_iff_exists_eq_vadd_smul
    (K L : ConvexBody E) (hn : Module.finrank ℝ E ≠ 0) (hK : volume (K : Set E) ≠ 0)
    (hL : volume (L : Set E) ≠ 0) :
    HasDerivWithinAt (fun t : ℝ ↦
      volume.real ((K : Set E) + t • (L : Set E)) ^ (Module.finrank ℝ E : ℝ)⁻¹)
      (volume.real (L : Set E) ^ (Module.finrank ℝ E : ℝ)⁻¹) (Ioi 0) 0 ↔
    ∃ v : E, ∃ r : ℝ, 0 < r ∧ (L : Set E) = v +ᵥ r • (K : Set E) := by
  rw [K.hasDerivWithinAt_volume_real_add_smul_rpow_iff L hn]
  have heq {t : ℝ} (ht : 0 < t) := K.convex.volume_real_smul_add_smul_rpow_eq_iff hn K.isCompact
    hK L.convex L.isCompact hL one_pos ht
  simp only [one_smul, one_mul] at heq
  refine ⟨fun h ↦ (heq one_pos).1 (h 1 zero_le_one), fun h t ht ↦ ?_⟩
  obtain rfl | htpos := ht.eq_or_lt
  · simp [zero_smul_set L.nonempty]
  · exact (heq htpos).2 h

/-- **Ball rigidity from the sharp first variation of parallel volume.** A convex body `K` of
positive volume has parallel-volume root `t ↦ volume (K + t • closedBall 0 1) ^ (1 / n)` with
right derivative `volume (closedBall 0 1) ^ (1 / n)` at zero exactly when `K` is a closed ball
of positive radius. -/
theorem hasDerivWithinAt_volume_real_add_smul_closedBall_rpow_iff_exists_eq_closedBall
    (K : ConvexBody E) (hn : Module.finrank ℝ E ≠ 0) (hK : volume (K : Set E) ≠ 0) :
    HasDerivWithinAt (fun t : ℝ ↦
      volume.real ((K : Set E) + t • closedBall (0 : E) 1) ^ (Module.finrank ℝ E : ℝ)⁻¹)
      (volume.real (closedBall (0 : E) 1) ^ (Module.finrank ℝ E : ℝ)⁻¹) (Ioi 0) 0 ↔
    ∃ c : E, ∃ r : ℝ, 0 < r ∧ (K : Set E) = closedBall c r := by
  let B : ConvexBody E := ⟨closedBall 0 1, convex_closedBall 0 1, isCompact_closedBall 0 1,
    nonempty_closedBall.2 zero_le_one⟩
  have hB : (B : Set E) = closedBall 0 1 := ConvexBody.coe_mk _ _ _ _
  rw [← hB, K.hasDerivWithinAt_volume_real_add_smul_rpow_iff_exists_eq_vadd_smul B hn hK
    (hB ▸ (measure_closedBall_pos volume 0 one_pos).ne'), hB]
  constructor
  · rintro ⟨v, r, hr, hvr⟩
    have hrK : r • (K : Set E) = -v +ᵥ closedBall (0 : E) 1 := eq_neg_vadd_iff.2 hvr.symm
    refine ⟨r⁻¹ • -v, r⁻¹, inv_pos.2 hr, ?_⟩
    rw [← inv_smul_smul₀ hr.ne' (K : Set E), hrK, Metric.vadd_closedBall, vadd_eq_add, add_zero,
      smul_closedBall _ _ zero_le_one, Real.norm_of_nonneg (inv_nonneg.2 hr.le), mul_one]
  · rintro ⟨c, r, hr, hKc⟩
    refine ⟨-(r⁻¹ • c), r⁻¹, inv_pos.2 hr, ?_⟩
    rw [hKc, smul_closedBall _ _ hr.le, Real.norm_of_nonneg (inv_nonneg.2 hr.le),
      inv_mul_cancel₀ hr.ne', Metric.vadd_closedBall, vadd_eq_add, neg_add_cancel]

end ConvexBody

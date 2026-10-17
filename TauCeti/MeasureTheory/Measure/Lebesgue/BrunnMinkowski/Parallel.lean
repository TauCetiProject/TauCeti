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

/-!
# Concavity of parallel volume

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

The concavity proof combines `Convex.add_smul_interpolation` with
`TauCeti.mul_volume_real_rpow_add_mul_volume_real_rpow_le`. The derivative comparison uses
Mathlib's `ConcaveOn.slope_le_of_hasDerivWithinAt_Ioi`.

## References

* R. J. Gardner, *The Brunn–Minkowski inequality*, Bull. Amer. Math. Soc. **39** (2002),
  355–405, for concavity of volume roots and the first Minkowski inequality.
-/

public section

open MeasureTheory Set
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

end ConvexBody

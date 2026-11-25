/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.Measure.ExtendCoefficients.Clopen
public import TauCeti.NumberTheory.Padics.Measure.Units.Basic

/-!
# Coefficient extension on the p-adic unit group

Extension along a uniformly bounded homomorphism from a topological commutative ring to a complete
ultrametric normed commutative ring commutes with restriction from the p-adic integers to their
unit group and with the ambient unit projector. Together with pushforward along the value map,
this lets one compute coefficient extension on intrinsic unit measures by extending ambient
measures and then restricting to the units.

## References

* J. Rodrigues Jacinto and C. Williams,
  [*An introduction to p-adic L-functions*](https://doi.org/10.2140/ent.2025.4.101),
  §3.5.3, Remarks 3.31 and 3.33.
-/

public section

open scoped AbstractMeasure

namespace AbstractMeasure

variable {p : ℕ} [Fact p.Prime]

/-- Extension along a uniformly bounded homomorphism from a topological commutative ring to a
complete ultrametric normed commutative ring commutes with restriction to the p-adic unit group. -/
@[simp]
theorem extendCoefficients_restrictUnits {O K : Type*} [CommRing O] [TopologicalSpace O]
    [IsTopologicalRing O] [NormedCommRing K] [CompleteSpace K] [IsUltrametricDist K] {B : ℝ}
    (μ : D(ℤ_[p], O)) (j : O →+* K) (hj : ∀ a, ‖j a‖ ≤ B) :
    extendCoefficients j hj (restrictUnits μ) = restrictUnits (extendCoefficients j hj μ) := by
  simp only [restrictUnits_def, coe_arrowCongrLeft, extendCoefficients_map,
    extendCoefficients_restrictClopen]

/-- Extension along a uniformly bounded homomorphism from a topological commutative ring to a
complete ultrametric normed commutative ring commutes with the ambient unit-support projector. -/
@[simp]
theorem extendCoefficients_unitRestriction {O K : Type*} [CommRing O] [TopologicalSpace O]
    [IsTopologicalRing O] [NormedCommRing K] [CompleteSpace K] [IsUltrametricDist K] {B : ℝ}
    (μ : D(ℤ_[p], O)) (j : O →+* K) (hj : ∀ a, ‖j a‖ ≤ B) :
    extendCoefficients j hj (unitRestriction μ) = unitRestriction (extendCoefficients j hj μ) := by
  rw [← map_unitsVal_restrictUnits, extendCoefficients_map, extendCoefficients_restrictUnits,
    map_unitsVal_restrictUnits]

/-- Coefficient extension on the unit group can be computed by pushing the measure to the p-adic
integers, extending its coefficients there, and restricting to the units. -/
theorem extendCoefficients_eq_restrictUnits_map {O K : Type*} [CommRing O] [TopologicalSpace O]
    [IsTopologicalRing O] [NormedCommRing K] [CompleteSpace K] [IsUltrametricDist K] {B : ℝ}
    (μ : D(ℤ_[p]ˣ, O)) (j : O →+* K) (hj : ∀ a, ‖j a‖ ≤ B) :
    extendCoefficients j hj μ =
      restrictUnits (extendCoefficients j hj (map ⟨Units.val, Units.continuous_val⟩ μ)) := by
  rw [← extendCoefficients_restrictUnits, restrictUnits_map_unitsVal]

end AbstractMeasure

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.Measure.ExtendCoefficients.Clopen
public import TauCeti.NumberTheory.Padics.Measure.ExtendCoefficients.IntegralLattice
public import TauCeti.NumberTheory.Padics.Measure.Units.Basic
import TauCeti.NumberTheory.Padics.Measure.Dirac

/-!
# Coefficient extension on the p-adic unit group

Extension of coefficients commutes with restriction from the p-adic integers to their unit group.
Together with pushforward along the value map, this lets one compute coefficient extension on
intrinsic unit measures by extending ambient measures and then restricting to the units.

For the inclusion `ℤ_p → ℚ_p`, the integral unit measures identify with the weakly closed unit
ball, and one power of `p` clears the denominators of any rational unit measure.

## References

* J. Rodrigues Jacinto and C. Williams,
  [*An introduction to p-adic L-functions*](https://doi.org/10.2140/ent.2025.4.101),
  §3.5.3, Remarks 3.31 and 3.33.
-/

public section

open scoped AbstractMeasure

namespace AbstractMeasure

variable {p : ℕ} [Fact p.Prime]

/-- Extending coefficients commutes with restriction to the p-adic unit group. -/
@[simp]
theorem extendCoefficients_restrictUnits {O K : Type*} [NormedCommRing O] [NormedCommRing K]
    [CompleteSpace K] [IsUltrametricDist K] {B : ℝ}
    (j : O →+* K) (hj : ∀ a, ‖j a‖ ≤ B) (μ : D(ℤ_[p], O)) :
    extendCoefficients j hj (restrictUnits μ) = restrictUnits (extendCoefficients j hj μ) := by
  simp only [restrictUnits_def, coe_arrowCongrLeft, extendCoefficients_map,
    extendCoefficients_restrictClopen]

/-- Coefficient extension commutes with the ambient projector onto measures supported on units. -/
@[simp]
theorem extendCoefficients_unitRestriction {O K : Type*} [NormedCommRing O] [NormedCommRing K]
    [CompleteSpace K] [IsUltrametricDist K] {B : ℝ}
    (j : O →+* K) (hj : ∀ a, ‖j a‖ ≤ B) (μ : D(ℤ_[p], O)) :
    extendCoefficients j hj (unitRestriction μ) = unitRestriction (extendCoefficients j hj μ) := by
  rw [← map_unitsVal_restrictUnits, extendCoefficients_map, extendCoefficients_restrictUnits,
    map_unitsVal_restrictUnits]

section Examples

-- The canonical map also extends coefficients into rings whose unit need not have norm one.
example {R : Type*} [NormedCommRing R] [Algebra ℤ_[p] R] [IsBoundedSMul ℤ_[p] R]
    [CompleteSpace R] [IsUltrametricDist R] (μ : D(ℤ_[p]ˣ, ℤ_[p])) :
    let hj : ∀ a : ℤ_[p], ‖algebraMap ℤ_[p] R a‖ ≤ ‖(1 : R)‖ := fun a ↦ by
      rw [Algebra.algebraMap_eq_smul_one]
      exact (norm_smul_le a (1 : R)).trans <|
        mul_le_of_le_one_left (norm_nonneg _) (PadicInt.norm_le_one a)
    extendCoefficients (algebraMap ℤ_[p] R) hj μ =
      restrictUnits (extendCoefficients (algebraMap ℤ_[p] R) hj
        (map ⟨Units.val, Units.continuous_val⟩ μ)) := by
  dsimp only
  rw [← extendCoefficients_restrictUnits, restrictUnits_map_unitsVal]

-- Scaling the unit Dirac measure by the inverse of p puts its norm above one.
example :
    ¬∃ μ : D(ℤ_[p]ˣ, ℤ_[p]),
      extendCoefficients PadicInt.Coe.ringHom PadicInt.norm_coe_ringHom_le_one μ =
        (p : ℚ_[p])⁻¹ • dirac ℚ_[p] (1 : ℤ_[p]ˣ) := by
  rw [← AddMonoidHom.mem_range, mem_range_extendCoefficients_iff _
    PadicInt.isEmbedding_coe_ringHom PadicInt.closedBall_subset_range_coe_ringHom]
  simp only [map_smul, norm_smul, TauCeti.AbstractMeasure.norm_dirac, norm_inv, Padic.norm_p,
    mul_one, inv_inv, not_le]
  exact_mod_cast (Fact.out : p.Prime).one_lt

end Examples

end AbstractMeasure

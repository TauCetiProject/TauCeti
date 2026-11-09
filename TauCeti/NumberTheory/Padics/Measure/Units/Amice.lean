/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.Measure.Topology.Amice
public import TauCeti.NumberTheory.Padics.Measure.Units.Topology

/-!
# Integral unit measures in Amice coordinates

Integral measures on `ℤ_pˣ` identify linearly and topologically with the kernel of series
psi. The forward map includes the measure in `ℤ_p` and takes its Amice transform; the
inverse takes the inverse Amice transform and restricts to the units. The measure topology
is weak, and the series kernel carries the coefficientwise p-adic subspace topology.

This is not an algebra equivalence: convolution on the unit group is multiplicative,
whereas the ambient Amice transform uses additive convolution on `ℤ_p`.

## References

* Rodrigues Jacinto and Williams, *An introduction to p-adic L-functions*,
  Remark 3.31, Corollary 3.32 and Remark 3.33.
-/

public section

open Topology ContinuousMap PowerSeries
open scoped PowerSeries.WithPiTopology

noncomputable section

namespace AbstractMeasure

variable {p : ℕ} [Fact p.Prime]

/-- The unit-measure Amice equivalence is a homeomorphism for the weak measure topology
and the coefficientwise p-adic topology on the series kernel. -/
theorem isHomeomorph_unitsMeasureAmiceEquiv_weak :
    @IsHomeomorph _ _ (WeakTopology (X := ℤ_[p]ˣ) (R := ℤ_[p]) (E := ℤ_[p])) _
      (unitsMeasureAmiceEquiv (p := p)) := by
  let : TopologicalSpace D(ℤ_[p], ℤ_[p]) := WeakTopology
  let : TopologicalSpace D(ℤ_[p]ˣ, ℤ_[p]) := WeakTopology
  have hA := isHomeomorph_amiceTransformEquiv_weak (p := p)
  rw [LinearEquiv.isHomeomorph_iff] at hA ⊢
  constructor
  · apply continuous_induced_rng.mpr
    exact (hA.1.comp (continuous_abstractMeasure_map_weak (R := ℤ_[p]) (E := ℤ_[p])
      (⟨Units.val, Units.continuous_val⟩ : C(ℤ_[p]ˣ, ℤ_[p])))).congr fun ν ↦
        (amiceTransformEquiv_apply _).trans (unitsMeasureAmiceEquiv_apply ν).symm
  · exact (continuous_restrictUnits_weak.comp (hA.2.comp continuous_subtype_val)).congr
      fun F ↦ (unitsMeasureAmiceEquiv_symm_apply F).symm

-- The atom at two has its usual binomial transform, without a derivative or inverse factor.
example : (unitsMeasureAmiceEquiv (dirac ℤ_[3]
    ((PadicInt.isUnit_natCast_of_coprime (p := 3) (n := 2) (by decide)).unit)) : ℤ_[3]⟦X⟧) =
    (1 + X) ^ 2 := by
  simp only [unitsMeasureAmiceEquiv_apply, map_dirac, amiceTransform_dirac,
    coe_mk, IsUnit.unit_spec]
  rw [binomialSeries_nat]

-- The dyadic sign atom has first moment minus one, not one.
example : PowerSeries.coeff 1 (unitsMeasureAmiceEquiv (dirac ℤ_[2] (-1 : ℤ_[2]ˣ)) :
    ℤ_[2]⟦X⟧) = -1 := by
  simp [amiceTransform_dirac, binomialSeries_coeff]

end AbstractMeasure

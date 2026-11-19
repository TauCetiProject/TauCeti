/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.Measure.Topology.TowerCoordinates
public import TauCeti.NumberTheory.Padics.Measure.UnitCoordinates

/-!
# The weak topology in finite unit coordinates

The imported tower-coordinate topology results, specialized to
`TauCeti.FiniteQuotientTower.unitTower`, embed integral measures on the p-adic units as a closed
subspace of their finite unit coordinates and give continuous reconstruction from compatible
families via `AbstractMeasure.towerCoordinatesEquiv`. Reducing each coordinate
modulo every power of the prime gives another closed embedding, into a product of finite
discrete rings. Consequently weak convergence is equivalent to eventual equality of each
joint finite projection.

Compactness is supplied by the existing comparison with the completed group algebra,
`AbstractMeasure.compactSpace_integralMeasures_weak`. No topology instance is installed on
measures: every occurrence below explicitly selects `AbstractMeasure.WeakTopology`.

## References

J. Rodrigues Jacinto and C. Williams, *An introduction to p-adic L-functions*, Definition 3.5,
Remark 3.11, Proposition 3.16 and Remark 3.18.
-/

public noncomputable section

open ContinuousMap Topology Filter
open scoped AbstractMeasure

namespace AbstractMeasure

open TauCeti

variable {p : ℕ} [Fact p.Prime]

/-- Joint finite unit coordinates vary continuously in the weak topology. -/
theorem continuous_jointUnitCoordinates_weak :
    @Continuous _ _ (WeakTopology (X := ℤ_[p]ˣ) (R := ℤ_[p]) (E := ℤ_[p]))
      inferInstance (jointUnitCoordinates (p := p)) := by
  let : TopologicalSpace D(ℤ_[p]ˣ, ℤ_[p]) := WeakTopology
  refine continuous_pi fun r ↦ continuous_pi fun n ↦ continuous_pi fun a ↦ ?_
  exact ((PadicInt.continuous_toZModPow r).comp
    ((continuous_apply a).comp (continuous_finiteProjection
      (PadicInt.unitsToZModPow (p := p) n : C(ℤ_[p]ˣ, (ZMod (p ^ n))ˣ))))).congr
        fun μ ↦ (jointUnitCoordinates_apply μ r n a).symm

/-- Joint finite unit coordinates give a closed embedding into a product of finite discrete
rings. Both coefficient precision and unit-group depth are allowed to vary independently. -/
theorem isClosedEmbedding_jointUnitCoordinates_weak :
    @IsClosedEmbedding _ _ (WeakTopology (X := ℤ_[p]ˣ) (R := ℤ_[p]) (E := ℤ_[p]))
      inferInstance (jointUnitCoordinates (p := p)) := by
  let : TopologicalSpace D(ℤ_[p]ˣ, ℤ_[p]) := WeakTopology
  let : CompactSpace D(ℤ_[p]ˣ, ℤ_[p]) := compactSpace_integralMeasures_weak
  exact continuous_jointUnitCoordinates_weak.isClosedEmbedding jointUnitCoordinates_injective

/-- Weak convergence of integral unit measures is equivalent to eventual equality of every
joint finite projection. This holds for arbitrary filters, not just sequences. -/
theorem tendsto_weak_iff_jointFiniteProjection {ι : Type*} {l : Filter ι}
    {μ : ι → D(ℤ_[p]ˣ, ℤ_[p])} {ν : D(ℤ_[p]ˣ, ℤ_[p])} :
    @Tendsto _ _ μ l (@nhds _ (WeakTopology (X := ℤ_[p]ˣ) (R := ℤ_[p]) (E := ℤ_[p])) ν) ↔
      ∀ r n : ℕ, ∀ᶠ i in l,
        jointFiniteProjection r
          (↑(PadicInt.unitsToZModPow (p := p) n) : C(ℤ_[p]ˣ, (ZMod (p ^ n))ˣ)) (μ i) =
          jointFiniteProjection r
            (↑(PadicInt.unitsToZModPow (p := p) n) : C(ℤ_[p]ˣ, (ZMod (p ^ n))ˣ)) ν := by
  let : TopologicalSpace D(ℤ_[p]ˣ, ℤ_[p]) := WeakTopology
  rw [isClosedEmbedding_jointUnitCoordinates_weak.tendsto_nhds_iff]
  simp only [tendsto_pi_nhds, Function.comp_apply]
  constructor
  · intro h r n
    have ha (a : (ZMod (p ^ n))ˣ) := h r n a
    simp only [tendsto_pure, nhds_discrete,
      jointUnitCoordinates_apply_eq_jointFiniteProjection] at ha
    filter_upwards [eventually_all.mpr ha] with i hi
    exact Finsupp.ext hi
  · intro h r n a
    rw [nhds_discrete, tendsto_pure]
    filter_upwards [h r n] with i hi
    simpa only [jointUnitCoordinates_apply_eq_jointFiniteProjection] using
      congrArg (fun c ↦ c a) hi

end AbstractMeasure

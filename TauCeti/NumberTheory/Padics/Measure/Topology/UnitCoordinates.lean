/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.Measure.TowerCoordinates
public import TauCeti.NumberTheory.Padics.Measure.JointFiniteProjection

/-!
# The weak topology in finite unit coordinates

Integral measures on the p-adic units embed as a closed subspace of the product of their
finite unit coordinates. The existing `AbstractMeasure.towerCoordinatesEquiv` identifies
measures with compatible families, and its inverse is continuous. Reducing each coordinate
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

/-- Taking tower coordinates of unit measures, viewed as coefficient functions with their
product topology, is weakly continuous. -/
theorem continuous_unitCoordinates_weak {R : Type*} [NormedCommRing R] :
    @Continuous _ _ (WeakTopology (X := ℤ_[p]ˣ) (R := R) (E := R)) inferInstance
      (fun μ : D(ℤ_[p]ˣ, R) ↦ fun n a ↦
        (towerCoordinates (FiniteQuotientTower.unitTower p) μ).val n a) := by
  let : TopologicalSpace D(ℤ_[p]ˣ, R) := WeakTopology
  refine continuous_pi fun n ↦ ?_
  simpa only [towerCoordinates_apply, FiniteQuotientTower.unitTower_q] using
    continuous_finiteProjection (R := R)
      (PadicInt.unitsToZModPow (p := p) n : C(ℤ_[p]ˣ, (ZMod (p ^ n))ˣ))

/-- Integral unit coordinates give a closed embedding for the weak topology. In particular,
they induce exactly that topology, not the continuous-dual operator-norm topology. -/
theorem isClosedEmbedding_unitCoordinates_weak :
    @IsClosedEmbedding _ _ (WeakTopology (X := ℤ_[p]ˣ) (R := ℤ_[p]) (E := ℤ_[p]))
      inferInstance (fun μ : D(ℤ_[p]ˣ, ℤ_[p]) ↦ fun n a ↦
        (towerCoordinates (FiniteQuotientTower.unitTower p) μ).val n a) := by
  let : TopologicalSpace D(ℤ_[p]ˣ, ℤ_[p]) := WeakTopology
  let : CompactSpace D(ℤ_[p]ˣ, ℤ_[p]) := compactSpace_integralMeasures_weak
  refine continuous_unitCoordinates_weak.isClosedEmbedding fun μ ν h ↦ ?_
  apply towerCoordinates_injective (FiniteQuotientTower.unitTower p)
  exact Subtype.ext (funext fun n ↦ Finsupp.ext fun a ↦ congrArg (fun c ↦ c n a) h)

/-- A family of coefficient functions comes from an integral unit measure exactly when its
finite-support forms belong to the unit tower's compatible families. -/
theorem mem_range_unitCoordinates_iff
    (c : ∀ n : ℕ, (ZMod (p ^ n))ˣ → ℤ_[p]) :
    c ∈ Set.range (fun μ : D(ℤ_[p]ˣ, ℤ_[p]) ↦ fun n a ↦
      (towerCoordinates (FiniteQuotientTower.unitTower p) μ).val n a) ↔
      (fun n ↦ Finsupp.equivFunOnFinite.symm (c n)) ∈
        (FiniteQuotientTower.unitTower p).compatibleFamilies ℤ_[p] := by
  constructor
  · rintro ⟨μ, rfl⟩
    simpa only [Finsupp.equivFunOnFinite_symm_coe] using
      (towerCoordinates (FiniteQuotientTower.unitTower p) μ).property
  · intro hc
    obtain ⟨μ, hμ⟩ := towerCoordinates_surjective (FiniteQuotientTower.unitTower p)
      ⟨fun n ↦ Finsupp.equivFunOnFinite.symm (c n), hc⟩
    refine ⟨μ, funext fun n ↦ funext fun a ↦ ?_⟩
    simpa only [Finsupp.coe_equivFunOnFinite_symm] using
      congrArg (fun d ↦ d.val n a) hμ

/-- The inverse of the integral unit-tower coordinate equivalence is continuous from the
product topology on compatible coefficients to the weak topology on measures. -/
theorem continuous_unitTowerCoordinatesEquiv_symm_weak :
    @Continuous _ _
      (TopologicalSpace.induced
        (fun c : (FiniteQuotientTower.unitTower p).compatibleFamilies ℤ_[p] ↦
          fun n a ↦ c.val n a) inferInstance)
      (WeakTopology (X := ℤ_[p]ˣ) (R := ℤ_[p]) (E := ℤ_[p]))
      (towerCoordinatesEquiv (FiniteQuotientTower.unitTower p)).symm := by
  let : TopologicalSpace D(ℤ_[p]ˣ, ℤ_[p]) := WeakTopology
  let : TopologicalSpace ((FiniteQuotientTower.unitTower p).compatibleFamilies ℤ_[p]) :=
    TopologicalSpace.induced (fun c ↦ fun n a ↦ c.val n a) inferInstance
  apply isClosedEmbedding_unitCoordinates_weak.isEmbedding.continuous_iff.mpr
  simpa only [Function.comp_def, ← towerCoordinatesEquiv_apply,
    LinearEquiv.apply_symm_apply] using
    (continuous_induced_dom : Continuous
      (fun c : (FiniteQuotientTower.unitTower p).compatibleFamilies ℤ_[p] ↦
        fun n a ↦ c.val n a))

/-- Joint coordinates record finite unit coefficients at independent coefficient precision
`r` and group depth `n`. Each target ring has its discrete topology. -/
def jointUnitCoordinates : D(ℤ_[p]ˣ, ℤ_[p]) →+
    ∀ r n : ℕ, (ZMod (p ^ n))ˣ → ZMod (p ^ r) where
  toFun μ r n a := jointFiniteProjection r (↑(PadicInt.unitsToZModPow (p := p) n)) μ a
  map_zero' := by ext r n a; simp
  map_add' μ ν := by ext r n a; simp

/-- A joint unit coordinate is the coefficient of the corresponding joint finite projection. -/
theorem jointUnitCoordinates_apply_eq_jointFiniteProjection (μ : D(ℤ_[p]ˣ, ℤ_[p]))
    (r n : ℕ) (a : (ZMod (p ^ n))ˣ) :
    jointUnitCoordinates μ r n a =
      jointFiniteProjection r (↑(PadicInt.unitsToZModPow (p := p) n)) μ a := (rfl)

@[simp]
theorem jointUnitCoordinates_apply (μ : D(ℤ_[p]ˣ, ℤ_[p])) (r n : ℕ)
    (a : (ZMod (p ^ n))ˣ) :
    jointUnitCoordinates μ r n a = PadicInt.toZModPow r
      (finiteProjection (↑(PadicInt.unitsToZModPow (p := p) n)) μ a) := by
  simp [jointUnitCoordinates_apply_eq_jointFiniteProjection, finiteProjection_apply]

/-- Joint finite unit coordinates separate integral measures. -/
theorem jointUnitCoordinates_injective :
    Function.Injective (jointUnitCoordinates (p := p)) := by
  intro μ ν h
  apply towerCoordinates_injective (FiniteQuotientTower.unitTower p)
  apply Subtype.ext
  funext n
  apply Finsupp.ext
  intro a
  apply PadicInt.ext_of_toZModPow.mp
  intro r
  simpa only [jointUnitCoordinates_apply, towerCoordinates_apply,
    FiniteQuotientTower.unitTower_q] using congrArg (fun c ↦ c r n a) h

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

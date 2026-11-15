/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Uniform.Sphere.Circle
public import TauCeti.Probability.Distributions.VonMises.Basic
public import TauCeti.Probability.Distributions.VonMisesFisher.Basic

import TauCeti.MeasureTheory.Measure.Tilted

/-!
# Von Mises laws as planar von Mises–Fisher laws

The cosine-sine parametrization carries `vonMisesMeasure m κ` on the additive circle to
`vonMisesFisherMeasure (circleSphereHomeomorph m) κ` on the planar unit sphere. The inverse
homeomorphism recovers the circle law from every planar von Mises–Fisher law. Both identities
include zero concentration and the zero measures at negative concentration, and have
`HasLaw` forms for random variables on either carrier.

The identification uses the Haar-to-sphere transport, the cosine difference formula for
the inner product, and `MeasureTheory.Measure.map_tilted`.

## References

* K. V. Mardia, P. E. Jupp, *Directional Statistics*, Wiley (2000), sections 3.5.4 and 9.3.2.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Metric Real AddCircle
open scoped InnerProductSpace

namespace TauCeti.Probability

local instance factTwoPiPosVonMisesFisherCircle : Fact (0 < 2 * π) := ⟨two_pi_pos⟩

/-- The cosine-sine image of a von Mises circle law is the planar von Mises–Fisher law
with the corresponding mean direction and the same concentration. -/
@[simp]
theorem map_circleSphereHomeomorph_vonMisesMeasure (m : AddCircle (2 * π)) (κ : ℝ) :
    (vonMisesMeasure m κ).map circleSphereHomeomorph =
      vonMisesFisherMeasure (circleSphereHomeomorph m) κ := by
  rcases le_or_gt 0 κ with hκ | hκ
  · let g : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 → ℝ :=
      fun x ↦ ⟪κ • (circleSphereHomeomorph m : EuclideanSpace ℝ (Fin 2)),
        (x : EuclideanSpace ℝ (Fin 2))⟫_ℝ
    have hg : Measurable g := by fun_prop
    have heq : (fun θ ↦ κ * cos_periodic.lift (θ - m)) = g ∘ circleSphereHomeomorph := by
      funext θ
      simp [g, inner_smul_left]
    rw [vonMisesMeasure_eq_tilted hκ, vonMisesFisherMeasure_of_nonneg _ hκ,
      vonMisesFisherNaturalMeasure_def, heq,
      Measure.map_tilted _ circleSphereHomeomorph.measurable hg,
      map_circleSphereHomeomorph_haarAddCircle]
  · rw [vonMisesMeasure_of_neg hκ, vonMisesFisherMeasure_of_neg _ hκ, Measure.map_zero]

/-- Reading a planar von Mises–Fisher direction as a circle angle gives the von Mises law. -/
@[simp]
theorem map_circleSphereHomeomorph_symm_vonMisesFisherMeasure
    (m : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) (κ : ℝ) :
    (vonMisesFisherMeasure m κ).map circleSphereHomeomorph.symm =
      vonMisesMeasure (circleSphereHomeomorph.symm m) κ := by
  have h := map_circleSphereHomeomorph_vonMisesMeasure (circleSphereHomeomorph.symm m) κ
  rw [circleSphereHomeomorph.apply_symm_apply] at h
  exact ((MeasurableEquiv.map_apply_eq_iff_map_symm_apply_eq
    circleSphereHomeomorph.toMeasurableEquiv).1 h).symm

end TauCeti.Probability

namespace ProbabilityTheory

open TauCeti TauCeti.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ}

/-- A von Mises random angle gives a planar von Mises–Fisher random direction. -/
theorem HasLaw.circleSphereHomeomorph_vonMisesMeasure {X : Ω → AddCircle (2 * π)}
    {m : AddCircle (2 * π)} (hX : HasLaw X (vonMisesMeasure m κ) P) :
    HasLaw (fun ω ↦ circleSphereHomeomorph (X ω))
      (vonMisesFisherMeasure (circleSphereHomeomorph m) κ) P := by
  rw [← map_circleSphereHomeomorph_vonMisesMeasure]
  exact (hasLaw_map circleSphereHomeomorph.measurable.aemeasurable).comp hX

/-- A planar von Mises–Fisher random direction gives a von Mises random angle. -/
theorem HasLaw.circleSphereHomeomorph_symm_vonMisesFisherMeasure
    {X : Ω → sphere (0 : EuclideanSpace ℝ (Fin 2)) 1}
    {m : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1}
    (hX : HasLaw X (vonMisesFisherMeasure m κ) P) :
    HasLaw (fun ω ↦ circleSphereHomeomorph.symm (X ω))
      (vonMisesMeasure (circleSphereHomeomorph.symm m) κ) P := by
  rw [← map_circleSphereHomeomorph_symm_vonMisesFisherMeasure]
  exact (hasLaw_map circleSphereHomeomorph.symm.measurable.aemeasurable).comp hX

end ProbabilityTheory

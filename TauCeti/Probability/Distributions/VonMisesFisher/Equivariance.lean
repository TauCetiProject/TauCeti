/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.VonMisesFisher.Basic
import TauCeti.MeasureTheory.Measure.WithDensity

/-!
# Orthogonal equivariance of von Mises–Fisher laws

A linear isometric equivalence transports a von Mises–Fisher law by transporting its natural
parameter, or its unit direction while keeping the concentration fixed. Consequently its
embedded mean transforms as a vector. The corresponding `HasLaw` statements transport
random points between the unit spheres of the two ambient spaces.

The transport argument uses `LinearIsometryEquiv.map_uniformSphereMeasure` and
`MeasureTheory.Measure.map_withDensity_eq_withDensity`.

## References

* K. V. Mardia, P. E. Jupp, *Directional Statistics*, Wiley (2000), §9.3.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal RealInnerProductSpace

namespace LinearIsometryEquiv

open TauCeti.Probability

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]

/-- A linear isometric equivalence transports the natural parameter of a von Mises–Fisher law.
This also includes the empty sphere in dimension zero. -/
theorem map_vonMisesFisherNaturalMeasure (f : E ≃ₗᵢ[ℝ] F) (η : E) :
    (vonMisesFisherNaturalMeasure η).map
      (Subtype.map f fun x hx ↦ by simpa using hx) =
      vonMisesFisherNaturalMeasure (f η) := by
  let g : sphere (0 : E) 1 → sphere (0 : F) 1 :=
    Subtype.map f fun x hx ↦ by simpa using hx
  have hg : Measurable g := f.continuous.measurable.subtype_map _
  have hZ : (∫ y : sphere (0 : F) 1, Real.exp ⟪f η, (y : F)⟫
      ∂uniformSphereMeasure F) =
      ∫ x : sphere (0 : E) 1, Real.exp ⟪η, (x : E)⟫ ∂uniformSphereMeasure E := by
    rw [← f.map_uniformSphereMeasure, integral_map hg.aemeasurable (by fun_prop)]
    simp only [g, Subtype.map_coe, f.inner_map_map]
  rw [vonMisesFisherNaturalMeasure_eq_withDensity,
    vonMisesFisherNaturalMeasure_eq_withDensity]
  refine Measure.map_withDensity_eq_withDensity (jac := fun _ ↦ 1) hg measurable_const
    (by fun_prop) (by simpa using f.map_uniformSphereMeasure) ?_
  filter_upwards with x
  simp only [one_mul, Subtype.map_coe, f.inner_map_map, hZ]

/-- Orthogonal transport changes the unit direction and retains the concentration, including
zero and invalid negative concentrations. -/
theorem map_vonMisesFisherMeasure (f : E ≃ₗᵢ[ℝ] F) (m : sphere (0 : E) 1) (κ : ℝ) :
    (vonMisesFisherMeasure m κ).map (Subtype.map f fun x hx ↦ by simpa using hx) =
      vonMisesFisherMeasure (⟨f m, by simp⟩) κ := by
  by_cases hκ : 0 ≤ κ
  · simp only [vonMisesFisherMeasure_of_nonneg _ hκ, f.map_vonMisesFisherNaturalMeasure,
      map_smul]
  · simp [vonMisesFisherMeasure_of_neg _ (lt_of_not_ge hκ)]

/-- The embedded mean transforms by the same linear isometric equivalence as the natural
parameter. -/
theorem integral_coe_vonMisesFisherNaturalMeasure_comm (f : E ≃ₗᵢ[ℝ] F) (η : E) :
    (∫ y : sphere (0 : F) 1, (y : F) ∂vonMisesFisherNaturalMeasure (f η)) =
      f (∫ x : sphere (0 : E) 1, (x : E) ∂vonMisesFisherNaturalMeasure η) := by
  rw [← f.map_vonMisesFisherNaturalMeasure,
    integral_map (f.continuous.measurable.subtype_map _).aemeasurable (by fun_prop)]
  simp only [Subtype.map_coe]
  exact f.toLinearIsometry.integral_comp_comm _

end LinearIsometryEquiv

namespace ProbabilityTheory

open TauCeti.Probability

variable {E F Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F] [MeasurableSpace Ω] {P : Measure Ω}
  {X : Ω → sphere (0 : E) 1} {η : E} {m : sphere (0 : E) 1} {κ : ℝ}

/-- Applying an orthogonal coordinate change to a von Mises–Fisher random point transports its
natural parameter. -/
theorem HasLaw.linearIsometryEquiv_vonMisesFisherNaturalMeasure
    (hX : HasLaw X (vonMisesFisherNaturalMeasure η) P) (f : E ≃ₗᵢ[ℝ] F) :
    HasLaw (fun ω ↦ Subtype.map f (fun x hx ↦ by simpa using hx) (X ω))
      (vonMisesFisherNaturalMeasure (f η)) P :=
  (HasLaw.mk (f.continuous.measurable.subtype_map _).aemeasurable
    (f.map_vonMisesFisherNaturalMeasure η)).fun_comp hX

/-- Applying an orthogonal coordinate change to a von Mises–Fisher random point transports its
unit direction. -/
theorem HasLaw.linearIsometryEquiv_vonMisesFisherMeasure
    (hX : HasLaw X (vonMisesFisherMeasure m κ) P) (f : E ≃ₗᵢ[ℝ] F) :
    HasLaw (fun ω ↦ Subtype.map f (fun x hx ↦ by simpa using hx) (X ω))
      (vonMisesFisherMeasure (⟨f m, by simp⟩) κ) P :=
  (HasLaw.mk (f.continuous.measurable.subtype_map _).aemeasurable
    (f.map_vonMisesFisherMeasure m κ)).fun_comp hX

end ProbabilityTheory

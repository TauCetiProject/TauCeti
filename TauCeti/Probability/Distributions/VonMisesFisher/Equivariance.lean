/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.VonMisesFisher.Basic
import TauCeti.MeasureTheory.Measure.WithDensity
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

/-!
# Orthogonal equivariance of von Mises–Fisher laws

A linear isometric equivalence transports a von Mises–Fisher law by transporting its natural
parameter, or its unit direction while keeping the concentration fixed. Consequently its
embedded mean transforms as a vector. Reflection in the parameter's span shows that the mean
lies in that span, and every perpendicular linear observable has mean zero. In the
direction/concentration parametrization the vector mean is the mean projection times the unit
direction. These identities reduce vector mean calculations to a single scalar projection.

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
theorem integral_coe_vonMisesFisherNaturalMeasure (f : E ≃ₗᵢ[ℝ] F) (η : E) :
    (∫ y : sphere (0 : F) 1, (y : F) ∂vonMisesFisherNaturalMeasure (f η)) =
      f (∫ x : sphere (0 : E) 1, (x : E) ∂vonMisesFisherNaturalMeasure η) := by
  rw [← f.map_vonMisesFisherNaturalMeasure,
    integral_map (f.continuous.measurable.subtype_map _).aemeasurable (by fun_prop)]
  exact f.toLinearIsometry.integral_comp_comm _

end LinearIsometryEquiv

namespace TauCeti.Probability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The embedded mean lies in the span of the natural parameter. In particular, the mean is
zero at zero natural parameter. -/
theorem integral_coe_vonMisesFisherNaturalMeasure_mem_span (η : E) :
    (∫ x : sphere (0 : E) 1, (x : E) ∂vonMisesFisherNaturalMeasure η) ∈ ℝ ∙ η := by
  have hfix := Submodule.reflection_mem_subspace_eq_self
    (Submodule.mem_span_singleton_self (R := ℝ) η)
  have h := (Submodule.reflection (ℝ ∙ η)).integral_coe_vonMisesFisherNaturalMeasure η
  rw [hfix] at h
  exact (Submodule.reflection_eq_self_iff _).mp h.symm

/-- Every linear observable perpendicular to the natural parameter has mean zero. -/
theorem integral_inner_vonMisesFisherNaturalMeasure_eq_zero (η θ : E)
    (hθ : ⟪θ, η⟫ = 0) :
    ∫ x : sphere (0 : E) 1, ⟪θ, (x : E)⟫ ∂vonMisesFisherNaturalMeasure η = 0 := by
  rw [integral_inner ((memLp_coe_vonMisesFisherNaturalMeasure η 1).integrable le_rfl)]
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp
    (integral_coe_vonMisesFisherNaturalMeasure_mem_span η)
  rw [← hc, inner_smul_right, hθ, mul_zero]

/-- The vector mean is the mean projection onto the unit direction times that direction.
The formula also holds for the zero measure at negative concentration. -/
theorem integral_coe_vonMisesFisherMeasure_eq_integral_inner_smul
    (m : sphere (0 : E) 1) (κ : ℝ) :
    (∫ x : sphere (0 : E) 1, (x : E) ∂vonMisesFisherMeasure m κ) =
      (∫ x : sphere (0 : E) 1, ⟪(m : E), (x : E)⟫ ∂vonMisesFisherMeasure m κ) • (m : E) := by
  by_cases hκ : 0 ≤ κ
  · rw [vonMisesFisherMeasure_of_nonneg m hκ]
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp
      (integral_coe_vonMisesFisherNaturalMeasure_mem_span (κ • (m : E)))
    rw [integral_inner
      ((memLp_coe_vonMisesFisherNaturalMeasure (κ • (m : E)) 1).integrable le_rfl),
      ← hc]
    simp [smul_smul, real_inner_smul_right]
  · simp [vonMisesFisherMeasure_of_neg m (lt_of_not_ge hκ)]

end TauCeti.Probability

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

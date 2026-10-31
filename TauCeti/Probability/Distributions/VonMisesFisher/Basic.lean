/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.Tilted
public import TauCeti.Probability.Distributions.Uniform.Sphere.Basic
public import Mathlib.Probability.Moments.IntegrableExpMul
public import TauCeti.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Von Mises–Fisher laws as tilts of the uniform sphere

The natural parameter `η` weights uniform sphere probability by `exp ⟪η, x⟫`. The sphere is
bounded, so the weight is integrable, its normalizer is positive in positive dimension, and
all real linear observables have every exponential moment. Their moment-generating functions
are ratios of normalizers at `η + t • θ` and `η`.

The direction/concentration form uses a unit direction and a nonnegative concentration;
negative concentration gives zero. Zero natural parameter or concentration gives the uniform
law. The natural-parameter law on the empty sphere in dimension zero is zero.

This construction uses Mathlib's `Measure.tilted` and its density and integration APIs, and
`TauCeti.measurable_tilted` for joint parameter measurability. The explicit two-point laws in
one dimension are developed in `VonMisesFisher.OneDimensional`.

## References

* K. V. Mardia, P. E. Jupp, *Directional Statistics*, Wiley (2000), §9.3.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Metric Real Set
open scoped ENNReal InnerProductSpace

namespace TauCeti.Probability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The von Mises–Fisher law with natural parameter `η`, relative to uniform sphere probability.
In dimension zero the sphere and this measure are empty. -/
def vonMisesFisherNaturalMeasure (η : E) : Measure (sphere (0 : E) 1) :=
  (uniformSphereMeasure E).tilted fun x ↦ ⟪η, (x : E)⟫_ℝ

/-- The natural-parameter law is the exponential tilt of uniform sphere probability. -/
theorem vonMisesFisherNaturalMeasure_def (η : E) :
    vonMisesFisherNaturalMeasure η =
      (uniformSphereMeasure E).tilted fun x ↦ ⟪η, (x : E)⟫_ℝ := (rfl)

/-- The von Mises–Fisher law with unit direction `m` and concentration `κ ≥ 0`.
Negative concentrations give the zero measure. -/
def vonMisesFisherMeasure (m : sphere (0 : E) 1) (κ : ℝ) : Measure (sphere (0 : E) 1) :=
  if 0 ≤ κ then vonMisesFisherNaturalMeasure (κ • (m : E)) else 0

/-- At nonnegative concentration, the natural parameter is the concentration times the direction. -/
@[simp]
theorem vonMisesFisherMeasure_of_nonneg (m : sphere (0 : E) 1) {κ : ℝ} (hκ : 0 ≤ κ) :
    vonMisesFisherMeasure m κ = vonMisesFisherNaturalMeasure (κ • (m : E)) := by
  simp [vonMisesFisherMeasure, hκ]

/-- Negative concentration gives the zero measure. -/
@[simp]
theorem vonMisesFisherMeasure_of_neg (m : sphere (0 : E) 1) {κ : ℝ} (hκ : κ < 0) :
    vonMisesFisherMeasure m κ = 0 := by
  simp [vonMisesFisherMeasure, hκ.not_ge]

instance (η : E) : IsFiniteMeasure (vonMisesFisherNaturalMeasure η) := by
  rw [vonMisesFisherNaturalMeasure_def]
  infer_instance

instance (m : sphere (0 : E) 1) (κ : ℝ) : IsFiniteMeasure (vonMisesFisherMeasure m κ) := by
  unfold vonMisesFisherMeasure
  split_ifs <;> infer_instance

/-- Every natural parameter defines a probability law in positive dimension. -/
instance isProbabilityMeasure_vonMisesFisherNaturalMeasure [Nontrivial E] (η : E) :
    IsProbabilityMeasure (vonMisesFisherNaturalMeasure η) :=
  isProbabilityMeasure_tilted (integrable_exp_inner_uniformSphereMeasure η)

/-- With a unit direction and nonnegative concentration, the law is a probability measure. -/
theorem isProbabilityMeasure_vonMisesFisherMeasure (m : sphere (0 : E) 1) {κ : ℝ}
    (hκ : 0 ≤ κ) : IsProbabilityMeasure (vonMisesFisherMeasure m κ) := by
  have : Nontrivial E := ⟨⟨m, 0, ne_zero_of_mem_sphere one_ne_zero m⟩⟩
  rw [vonMisesFisherMeasure_of_nonneg m hκ]
  infer_instance

/-- The direction/concentration law is a probability measure exactly at nonnegative
concentration. -/
@[simp]
theorem isProbabilityMeasure_vonMisesFisherMeasure_iff (m : sphere (0 : E) 1) (κ : ℝ) :
    IsProbabilityMeasure (vonMisesFisherMeasure m κ) ↔ 0 ≤ κ := by
  refine ⟨fun h ↦ not_lt.1 fun hκ ↦ ?_, isProbabilityMeasure_vonMisesFisherMeasure m⟩
  rw [vonMisesFisherMeasure_of_neg m hκ] at h
  exact not_isProbabilityMeasure_zero h

/-- The natural-parameter law has the normalized exponential density relative to the uniform
sphere law, including the empty-sphere case. -/
theorem vonMisesFisherNaturalMeasure_eq_withDensity (η : E) :
    vonMisesFisherNaturalMeasure η = (uniformSphereMeasure E).withDensity
      (fun x ↦ ENNReal.ofReal (exp ⟪η, (x : E)⟫_ℝ /
        ∫ y : sphere (0 : E) 1, exp ⟪η, (y : E)⟫_ℝ ∂uniformSphereMeasure E)) := (rfl)

/-- The Radon–Nikodym derivative against uniform sphere probability is the normalized
exponential weight. -/
theorem rnDeriv_vonMisesFisherNaturalMeasure (η : E) :
    (vonMisesFisherNaturalMeasure η).rnDeriv (uniformSphereMeasure E) =ᵐ[uniformSphereMeasure E]
      fun x ↦ ENNReal.ofReal (exp ⟪η, (x : E)⟫_ℝ /
        ∫ y : sphere (0 : E) 1, exp ⟪η, (y : E)⟫_ℝ ∂uniformSphereMeasure E) :=
  rnDeriv_tilted_left_self (by fun_prop)

/-- Zero natural parameter gives the uniform sphere law. -/
@[simp]
theorem vonMisesFisherNaturalMeasure_zero :
    vonMisesFisherNaturalMeasure (0 : E) = uniformSphereMeasure E := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · exact Subsingleton.elim _ _
  · simp [vonMisesFisherNaturalMeasure_def]

/-- In dimension zero the natural-parameter law is zero on the empty sphere. -/
@[simp]
theorem vonMisesFisherNaturalMeasure_of_subsingleton [Subsingleton E] (η : E) :
    vonMisesFisherNaturalMeasure η = 0 := Subsingleton.elim _ _

/-- Natural parameters form a Giry-measurable family, including dimension zero. -/
@[fun_prop]
theorem measurable_vonMisesFisherNaturalMeasure :
    Measurable (vonMisesFisherNaturalMeasure (E := E)) :=
  measurable_tilted (Kernel.const E (uniformSphereMeasure E)) (by fun_prop)

/-- The direction/concentration family is jointly measurable, including negative concentrations. -/
@[fun_prop]
theorem measurable_vonMisesFisherMeasure :
    Measurable fun p : sphere (0 : E) 1 × ℝ ↦ vonMisesFisherMeasure p.1 p.2 := by
  unfold vonMisesFisherMeasure
  exact Measurable.ite (measurableSet_le measurable_const measurable_snd)
    (measurable_vonMisesFisherNaturalMeasure.comp (by fun_prop)) measurable_const

/-- Every linear observable of a natural-parameter sphere law has all finite moments. -/
theorem memLp_inner_vonMisesFisherNaturalMeasure (η θ : E) (p : ℝ≥0∞) :
    MemLp (fun x : sphere (0 : E) 1 ↦ ⟪θ, (x : E)⟫_ℝ) p
      (vonMisesFisherNaturalMeasure η) := by
  refine MemLp.of_bound (by fun_prop) ‖θ‖ (Filter.Eventually.of_forall fun x ↦ ?_)
  simpa using norm_inner_le_norm (𝕜 := ℝ) θ (x : E)

/-- The exact exponential-integrability domain of every linear observable is all of `ℝ`. -/
@[simp]
theorem integrableExpSet_inner_vonMisesFisherNaturalMeasure (η θ : E) :
    integrableExpSet (fun x : sphere (0 : E) 1 ↦ ⟪θ, (x : E)⟫_ℝ)
      (vonMisesFisherNaturalMeasure η) = univ := by
  ext t
  simp only [integrableExpSet, mem_ofPred_eq, mem_univ, iff_true]
  rw [vonMisesFisherNaturalMeasure_def,
    integrable_tilted_iff (integrable_exp_inner_uniformSphereMeasure η)]
  simpa only [smul_eq_mul, ← exp_add, inner_add_left, real_inner_smul_left] using
    integrable_exp_inner_uniformSphereMeasure (η + t • θ)

/-- The directional mgf is the ratio of the sphere normalizers at `η + t • θ` and `η`. -/
theorem mgf_inner_vonMisesFisherNaturalMeasure (η θ : E) (t : ℝ) :
    mgf (fun x : sphere (0 : E) 1 ↦ ⟪θ, (x : E)⟫_ℝ) (vonMisesFisherNaturalMeasure η) t =
      (∫ x : sphere (0 : E) 1, exp ⟪η + t • θ, (x : E)⟫_ℝ ∂uniformSphereMeasure E) /
        ∫ x : sphere (0 : E) 1, exp ⟪η, (x : E)⟫_ℝ ∂uniformSphereMeasure E := by
  rw [mgf, vonMisesFisherNaturalMeasure_def, integral_exp_tilted]
  simp [inner_add_left, real_inner_smul_left]

/-- In positive dimension the directional cgf is the difference of the log normalizers. -/
theorem cgf_inner_vonMisesFisherNaturalMeasure [Nontrivial E] (η θ : E) (t : ℝ) :
    cgf (fun x : sphere (0 : E) 1 ↦ ⟪θ, (x : E)⟫_ℝ) (vonMisesFisherNaturalMeasure η) t =
      log (∫ x : sphere (0 : E) 1, exp ⟪η + t • θ, (x : E)⟫_ℝ ∂uniformSphereMeasure E) -
        log (∫ x : sphere (0 : E) 1, exp ⟪η, (x : E)⟫_ℝ ∂uniformSphereMeasure E) := by
  rw [cgf, mgf_inner_vonMisesFisherNaturalMeasure,
    log_div (integral_exp_inner_uniformSphereMeasure_pos _).ne'
      (integral_exp_inner_uniformSphereMeasure_pos _).ne']

end TauCeti.Probability

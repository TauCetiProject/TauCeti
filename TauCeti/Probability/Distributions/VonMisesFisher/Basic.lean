/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.Tilted
public import TauCeti.Probability.Density
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

Both parameterizations expose their normalized density relative to uniform sphere probability.
The density, `HasPDF`, canonical `pdf`, and Radon--Nikodym interfaces use the same totalized
conventions as the laws: in dimension zero, or at negative concentration in the
direction/concentration form, the density and law are zero.

This construction uses Mathlib's `Measure.tilted` and its density and integration APIs, and
`MeasureTheory.Measure.measurable_tilted` for joint parameter measurability. The explicit
two-point laws in one dimension are developed in `VonMisesFisher.OneDimensional`.

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

/-- The real normalized density of the natural-parameter von Mises--Fisher law relative to
uniform sphere probability. In dimension zero both the normalizing integral and this totalized
density are zero. -/
def vonMisesFisherNaturalPDFReal (η : E) (x : sphere (0 : E) 1) : ℝ :=
  exp ⟪η, (x : E)⟫_ℝ /
    ∫ y : sphere (0 : E) 1, exp ⟪η, (y : E)⟫_ℝ ∂uniformSphereMeasure E

/-- The defining formula of the real natural-parameter von Mises--Fisher density. -/
theorem vonMisesFisherNaturalPDFReal_def (η : E) :
    vonMisesFisherNaturalPDFReal η = fun x : sphere (0 : E) 1 ↦ exp ⟪η, (x : E)⟫_ℝ /
      ∫ y : sphere (0 : E) 1, exp ⟪η, (y : E)⟫_ℝ ∂uniformSphereMeasure E := (rfl)

/-- The extended nonnegative density of the natural-parameter von Mises--Fisher law relative to
uniform sphere probability. -/
def vonMisesFisherNaturalPDF (η : E) (x : sphere (0 : E) 1) : ℝ≥0∞ :=
  ENNReal.ofReal (vonMisesFisherNaturalPDFReal η x)

/-- The extended natural-parameter density is the nonnegative extended-real lift of the real
density. -/
theorem vonMisesFisherNaturalPDF_def (η : E) :
    vonMisesFisherNaturalPDF η = fun x ↦ ENNReal.ofReal (vonMisesFisherNaturalPDFReal η x) :=
  (rfl)

/-- The real normalized density of the direction/concentration von Mises--Fisher law. Negative
concentrations use the zero density, matching the totalized zero law. -/
def vonMisesFisherPDFReal (m : sphere (0 : E) 1) (κ : ℝ) (x : sphere (0 : E) 1) : ℝ :=
  if 0 ≤ κ then vonMisesFisherNaturalPDFReal (κ • (m : E)) x else 0

/-- The defining formula of the real direction/concentration von Mises--Fisher density. -/
theorem vonMisesFisherPDFReal_def (m : sphere (0 : E) 1) (κ : ℝ) :
    vonMisesFisherPDFReal m κ = fun x ↦
      if 0 ≤ κ then vonMisesFisherNaturalPDFReal (κ • (m : E)) x else 0 := (rfl)

/-- The extended nonnegative density of the direction/concentration von Mises--Fisher law
relative to uniform sphere probability. -/
def vonMisesFisherPDF (m : sphere (0 : E) 1) (κ : ℝ) (x : sphere (0 : E) 1) : ℝ≥0∞ :=
  ENNReal.ofReal (vonMisesFisherPDFReal m κ x)

/-- The extended direction/concentration density is the nonnegative extended-real lift of the
real density. -/
theorem vonMisesFisherPDF_def (m : sphere (0 : E) 1) (κ : ℝ) :
    vonMisesFisherPDF m κ = fun x ↦ ENNReal.ofReal (vonMisesFisherPDFReal m κ x) := (rfl)

/-- At nonnegative concentration, the real direction/concentration density is the natural-
parameter density. -/
@[simp]
theorem vonMisesFisherPDFReal_of_nonneg (m : sphere (0 : E) 1) {κ : ℝ} (hκ : 0 ≤ κ) :
    vonMisesFisherPDFReal m κ = vonMisesFisherNaturalPDFReal (κ • (m : E)) := by
  funext x
  rw [vonMisesFisherPDFReal, ite_eq_left hκ]

/-- At negative concentration, the real direction/concentration density is zero. -/
@[simp]
theorem vonMisesFisherPDFReal_of_neg (m : sphere (0 : E) 1) {κ : ℝ} (hκ : κ < 0) :
    vonMisesFisherPDFReal m κ = 0 := by
  funext x
  rw [vonMisesFisherPDFReal, ite_eq_right hκ.not_ge]
  simp only [Pi.zero_apply]

/-- At nonnegative concentration, the direction/concentration density is the natural-parameter
density. -/
@[simp]
theorem vonMisesFisherPDF_of_nonneg (m : sphere (0 : E) 1) {κ : ℝ} (hκ : 0 ≤ κ) :
    vonMisesFisherPDF m κ = vonMisesFisherNaturalPDF (κ • (m : E)) := by
  funext x
  rw [vonMisesFisherPDF, vonMisesFisherNaturalPDF, vonMisesFisherPDFReal_of_nonneg m hκ]

/-- At negative concentration, the direction/concentration density is zero. -/
@[simp]
theorem vonMisesFisherPDF_of_neg (m : sphere (0 : E) 1) {κ : ℝ} (hκ : κ < 0) :
    vonMisesFisherPDF m κ = 0 := by
  funext x
  rw [vonMisesFisherPDF, vonMisesFisherPDFReal_of_neg m hκ]
  exact ENNReal.ofReal_zero

/-- The real natural-parameter von Mises--Fisher density is nonnegative, including in dimension
zero. -/
theorem vonMisesFisherNaturalPDFReal_nonneg (η : E) (x : sphere (0 : E) 1) :
    0 ≤ vonMisesFisherNaturalPDFReal η x :=
  div_nonneg (exp_pos _).le (integral_nonneg fun _ ↦ (exp_pos _).le)

/-- The real direction/concentration von Mises--Fisher density is nonnegative for every
concentration. -/
theorem vonMisesFisherPDFReal_nonneg (m : sphere (0 : E) 1) (κ : ℝ) (x : sphere (0 : E) 1) :
    0 ≤ vonMisesFisherPDFReal m κ x := by
  rw [vonMisesFisherPDFReal]
  split_ifs
  exacts [vonMisesFisherNaturalPDFReal_nonneg _ x, le_rfl]

/-- The real value of the extended natural-parameter density is the real density. -/
@[simp]
theorem toReal_vonMisesFisherNaturalPDF (η : E) (x : sphere (0 : E) 1) :
    (vonMisesFisherNaturalPDF η x).toReal = vonMisesFisherNaturalPDFReal η x :=
  ENNReal.toReal_ofReal (vonMisesFisherNaturalPDFReal_nonneg η x)

/-- The real value of the extended direction/concentration density is the real density for
every concentration. -/
@[simp]
theorem toReal_vonMisesFisherPDF (m : sphere (0 : E) 1) (κ : ℝ) (x : sphere (0 : E) 1) :
    (vonMisesFisherPDF m κ x).toReal = vonMisesFisherPDFReal m κ x :=
  ENNReal.toReal_ofReal (vonMisesFisherPDFReal_nonneg m κ x)

/-- The natural-parameter von Mises--Fisher density is measurable. -/
@[fun_prop]
theorem measurable_vonMisesFisherNaturalPDF (η : E) :
    Measurable (vonMisesFisherNaturalPDF η) := by
  unfold vonMisesFisherNaturalPDF vonMisesFisherNaturalPDFReal
  fun_prop

/-- The direction/concentration von Mises--Fisher density is measurable for every concentration,
including the totalized negative branch. -/
@[fun_prop]
theorem measurable_vonMisesFisherPDF (m : sphere (0 : E) 1) (κ : ℝ) :
    Measurable (vonMisesFisherPDF m κ) := by
  by_cases hκ : 0 ≤ κ
  · rw [vonMisesFisherPDF_of_nonneg m hκ]
    exact measurable_vonMisesFisherNaturalPDF (κ • (m : E))
  · rw [vonMisesFisherPDF_of_neg m (lt_of_not_ge hκ)]
    fun_prop

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
      (vonMisesFisherNaturalPDF η) := (rfl)

/-- The direction/concentration law is the uniform sphere law weighted by its named density for
every concentration, including the totalized negative branch. -/
theorem vonMisesFisherMeasure_eq_withDensity (m : sphere (0 : E) 1) (κ : ℝ) :
    vonMisesFisherMeasure m κ =
      (uniformSphereMeasure E).withDensity (vonMisesFisherPDF m κ) := by
  by_cases hκ : 0 ≤ κ
  · rw [vonMisesFisherMeasure_of_nonneg m hκ,
      vonMisesFisherNaturalMeasure_eq_withDensity, vonMisesFisherPDF_of_nonneg m hκ]
  · rw [vonMisesFisherMeasure_of_neg m (lt_of_not_ge hκ),
      vonMisesFisherPDF_of_neg m (lt_of_not_ge hκ)]
    simp

/-- The Radon–Nikodym derivative against uniform sphere probability is the normalized
exponential weight. -/
theorem rnDeriv_vonMisesFisherNaturalMeasure (η : E) :
    (vonMisesFisherNaturalMeasure η).rnDeriv (uniformSphereMeasure E) =ᵐ[uniformSphereMeasure E]
      vonMisesFisherNaturalPDF η :=
  rnDeriv_tilted_left_self (by fun_prop)

/-- The Radon--Nikodym derivative of the direction/concentration law against uniform sphere
probability is its named density. -/
theorem rnDeriv_vonMisesFisherMeasure (m : sphere (0 : E) 1) (κ : ℝ) :
    (vonMisesFisherMeasure m κ).rnDeriv (uniformSphereMeasure E) =ᵐ[uniformSphereMeasure E]
      vonMisesFisherPDF m κ := by
  rw [vonMisesFisherMeasure_eq_withDensity]
  exact Measure.rnDeriv_withDensity _ (measurable_vonMisesFisherPDF m κ)

end TauCeti.Probability

namespace ProbabilityTheory.HasLaw

open TauCeti.Probability

variable {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω] {P : Measure Ω}

/-- A random variable with a natural-parameter von Mises--Fisher law has its named density
relative to uniform sphere probability. -/
theorem hasPDF_vonMisesFisherNaturalMeasure {X : Ω → sphere (0 : E) 1} {η : E}
    (hX : HasLaw X (vonMisesFisherNaturalMeasure η) P) :
    HasPDF X P (uniformSphereMeasure E) := by
  apply hasPDF_of_hasLaw_withDensity (measurable_vonMisesFisherNaturalPDF η).aemeasurable
  rwa [← vonMisesFisherNaturalMeasure_eq_withDensity]

/-- The canonical density of a random variable with a natural-parameter von Mises--Fisher law
agrees almost everywhere with the named density. -/
theorem pdf_eq_vonMisesFisherNaturalPDF {X : Ω → sphere (0 : E) 1} {η : E}
    (hX : HasLaw X (vonMisesFisherNaturalMeasure η) P) :
    pdf X P (uniformSphereMeasure E) =ᵐ[uniformSphereMeasure E]
      vonMisesFisherNaturalPDF η := by
  apply pdf_eq_of_hasLaw_withDensity (measurable_vonMisesFisherNaturalPDF η).aemeasurable
  rwa [← vonMisesFisherNaturalMeasure_eq_withDensity]

/-- A random variable with a direction/concentration von Mises--Fisher law has its named density
relative to uniform sphere probability, including for the totalized negative branch. -/
theorem hasPDF_vonMisesFisherMeasure {X : Ω → sphere (0 : E) 1}
    {m : sphere (0 : E) 1} {κ : ℝ} (hX : HasLaw X (vonMisesFisherMeasure m κ) P) :
    HasPDF X P (uniformSphereMeasure E) := by
  apply hasPDF_of_hasLaw_withDensity (measurable_vonMisesFisherPDF m κ).aemeasurable
  rwa [← vonMisesFisherMeasure_eq_withDensity]

/-- The canonical density of a random variable with a direction/concentration von Mises--Fisher
law agrees almost everywhere with the named density. -/
theorem pdf_eq_vonMisesFisherPDF {X : Ω → sphere (0 : E) 1}
    {m : sphere (0 : E) 1} {κ : ℝ} (hX : HasLaw X (vonMisesFisherMeasure m κ) P) :
    pdf X P (uniformSphereMeasure E) =ᵐ[uniformSphereMeasure E]
      vonMisesFisherPDF m κ := by
  apply pdf_eq_of_hasLaw_withDensity (measurable_vonMisesFisherPDF m κ).aemeasurable
  rwa [← vonMisesFisherMeasure_eq_withDensity]

end ProbabilityTheory.HasLaw

namespace TauCeti.Probability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

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
  Measure.measurable_tilted (uniformSphereMeasure E) (by fun_prop)

/-- The direction/concentration family is jointly measurable, including negative concentrations. -/
@[fun_prop]
theorem measurable_vonMisesFisherMeasure :
    Measurable fun p : sphere (0 : E) 1 × ℝ ↦ vonMisesFisherMeasure p.1 p.2 := by
  unfold vonMisesFisherMeasure
  exact Measurable.ite (measurableSet_le measurable_const measurable_snd)
    (measurable_vonMisesFisherNaturalMeasure.comp (by fun_prop)) measurable_const

/-- The unit-sphere embedding has every finite moment and is essentially bounded under
every natural-parameter von Mises–Fisher law. -/
@[simp]
theorem memLp_coe_vonMisesFisherNaturalMeasure (η : E) (p : ℝ≥0∞) :
    MemLp ((↑) : sphere (0 : E) 1 → E) p (vonMisesFisherNaturalMeasure η) := by
  exact MemLp.of_bound (by fun_prop) 1 (by filter_upwards with x; simp)

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

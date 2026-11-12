/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.VonMisesFisher.Basic
public import TauCeti.Probability.Distributions.Uniform.Sphere.OneDimensional
public import Mathlib.Probability.Moments.Variance

/-!
# Von Mises–Fisher laws in dimension one

Choose a unit vector `e` in a one-dimensional real inner product space and put `a = ⟪η, e⟫`.
The natural-parameter von Mises–Fisher law assigns masses `exp a / (exp a + exp (-a))` and
`exp (-a) / (exp a + exp (-a))` to `e` and `-e`. Its coordinate along `e` has mean `tanh a`,
variance `1 - tanh a ^ 2`, and a two-step quantile. All formulas allow either sign of `a`.

The calculation uses the two-point identity for `uniformSphereMeasure`, together with
Mathlib's exponential-tilting and Bochner integration APIs.

## References

* K. V. Mardia, P. E. Jupp, *Directional Statistics*, Wiley (2000), §9.3.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Metric Real Set Filter Topology
open scoped ENNReal InnerProductSpace

namespace TauCeti.Probability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Each point of a one-dimensional sphere has its normalized exponential mass. -/
theorem vonMisesFisherNaturalMeasure_singleton_of_finrank_eq_one
    (hdim : Module.finrank ℝ E = 1) (η : E) (e : sphere (0 : E) 1) :
    vonMisesFisherNaturalMeasure η {e} =
      ENNReal.ofReal (exp ⟪η, (e : E)⟫_ℝ /
        (exp ⟪η, (e : E)⟫_ℝ + exp (-⟪η, (e : E)⟫_ℝ))) := by
  rw [vonMisesFisherNaturalMeasure_def, tilted_singleton,
    integral_exp_inner_uniformSphereMeasure_of_finrank_eq_one hdim η e,
    uniformSphereMeasure_singleton_of_finrank_eq_one hdim e]
  have hhalf : (1 / 2 : ℝ≥0∞) = ENNReal.ofReal (1 / 2 : ℝ) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_one, ENNReal.ofReal_ofNat]
  rw [hhalf, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [cosh_eq]
  field_simp

/-- The one-dimensional law is the weighted pair of antipodal point masses. -/
theorem vonMisesFisherNaturalMeasure_eq_of_finrank_eq_one
    (hdim : Module.finrank ℝ E = 1) (η : E) (e : sphere (0 : E) 1) :
    vonMisesFisherNaturalMeasure η =
      ENNReal.ofReal (exp ⟪η, (e : E)⟫_ℝ /
        (exp ⟪η, (e : E)⟫_ℝ + exp (-⟪η, (e : E)⟫_ℝ))) • Measure.dirac e +
      ENNReal.ofReal (exp (-⟪η, (e : E)⟫_ℝ) /
        (exp ⟪η, (e : E)⟫_ℝ + exp (-⟪η, (e : E)⟫_ℝ))) • Measure.dirac (-e) := by
  have hpoints : ∀ x : sphere (0 : E) 1, x = e ∨ x = -e := by
    intro x
    exact (eq_or_eq_neg_of_norm_eq_of_finrank_eq_one hdim
      ((norm_eq_of_mem_sphere x).trans (norm_eq_of_mem_sphere e).symm)).imp
        Subtype.ext Subtype.ext
  have h := (Measure.ae_eq_or_eq_iff_eq_dirac_add_dirac
    (μ := vonMisesFisherNaturalMeasure η) (ne_neg_of_mem_unit_sphere ℝ e)).mp
      (Eventually.of_forall hpoints)
  simpa [vonMisesFisherNaturalMeasure_singleton_of_finrank_eq_one hdim, inner_neg_right,
    add_comm] using h

/-- Integration of a function of the coordinate is the weighted sum of its two values. -/
theorem integral_comp_inner_vonMisesFisherNaturalMeasure_of_finrank_eq_one
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (hdim : Module.finrank ℝ E = 1) (η : E) (e : sphere (0 : E) 1) (f : ℝ → F) :
    ∫ x : sphere (0 : E) 1, f ⟪(e : E), (x : E)⟫_ℝ ∂vonMisesFisherNaturalMeasure η =
      (exp ⟪η, (e : E)⟫_ℝ / (exp ⟪η, (e : E)⟫_ℝ + exp (-⟪η, (e : E)⟫_ℝ))) • f 1 +
      (exp (-⟪η, (e : E)⟫_ℝ) / (exp ⟪η, (e : E)⟫_ℝ + exp (-⟪η, (e : E)⟫_ℝ))) • f (-1) := by
  rw [vonMisesFisherNaturalMeasure_eq_of_finrank_eq_one hdim η e,
    integral_add_measure
      ((integrable_dirac (by finiteness)).smul_measure (by finiteness))
      ((integrable_dirac (by finiteness)).smul_measure (by finiteness)), integral_smul_measure,
    integral_smul_measure]
  simp [ENNReal.toReal_ofReal (by positivity :
    0 ≤ exp ⟪η, (e : E)⟫_ℝ / (exp ⟪η, (e : E)⟫_ℝ + exp (-⟪η, (e : E)⟫_ℝ))),
    ENNReal.toReal_ofReal (by positivity :
    0 ≤ exp (-⟪η, (e : E)⟫_ℝ) / (exp ⟪η, (e : E)⟫_ℝ + exp (-⟪η, (e : E)⟫_ℝ)))]

/-- The coordinate mean of a one-dimensional von Mises–Fisher law is the hyperbolic tangent. -/
theorem integral_inner_vonMisesFisherNaturalMeasure_of_finrank_eq_one
    (hdim : Module.finrank ℝ E = 1) (η : E) (e : sphere (0 : E) 1) :
    ∫ x : sphere (0 : E) 1, ⟪(e : E), (x : E)⟫_ℝ ∂vonMisesFisherNaturalMeasure η =
      tanh ⟪η, (e : E)⟫_ℝ := by
  have h := integral_comp_inner_vonMisesFisherNaturalMeasure_of_finrank_eq_one hdim η e id
  simp only [id_eq, smul_eq_mul, mul_one, mul_neg_one] at h
  rw [h, tanh_eq]
  ring

/-- The coordinate variance of a one-dimensional von Mises–Fisher law is `1 - tanh a ^ 2`. -/
theorem variance_inner_vonMisesFisherNaturalMeasure_of_finrank_eq_one
    (hdim : Module.finrank ℝ E = 1) (η : E) (e : sphere (0 : E) 1) :
    variance (fun x : sphere (0 : E) 1 ↦ ⟪(e : E), (x : E)⟫_ℝ)
      (vonMisesFisherNaturalMeasure η) = 1 - tanh ⟪η, (e : E)⟫_ℝ ^ 2 := by
  have : Nontrivial E := ⟨⟨e, 0, ne_zero_of_mem_sphere one_ne_zero e⟩⟩
  rw [variance_eq_sub (memLp_inner_vonMisesFisherNaturalMeasure η (e : E) 2),
    integral_inner_vonMisesFisherNaturalMeasure_of_finrank_eq_one hdim η e]
  simp only [Pi.pow_apply]
  rw [integral_comp_inner_vonMisesFisherNaturalMeasure_of_finrank_eq_one hdim η e (· ^ 2)]
  simp only [one_pow, neg_one_sq, smul_eq_mul, mul_one]
  rw [← add_div, div_self (by positivity)]

/-- The one-dimensional directional mgf is the ratio `cosh (a + t) / cosh a`. -/
theorem mgf_inner_vonMisesFisherNaturalMeasure_of_finrank_eq_one
    (hdim : Module.finrank ℝ E = 1) (η : E) (e : sphere (0 : E) 1) (t : ℝ) :
    mgf (fun x : sphere (0 : E) 1 ↦ ⟪(e : E), (x : E)⟫_ℝ)
      (vonMisesFisherNaturalMeasure η) t = cosh (⟪η, (e : E)⟫_ℝ + t) / cosh ⟪η, (e : E)⟫_ℝ := by
  rw [mgf_inner_vonMisesFisherNaturalMeasure,
    integral_exp_inner_uniformSphereMeasure_of_finrank_eq_one hdim _ e,
    integral_exp_inner_uniformSphereMeasure_of_finrank_eq_one hdim _ e]
  simp [inner_add_left, real_inner_smul_left]

/-- The one-dimensional coordinate cgf is the difference of the log hyperbolic cosines. -/
theorem cgf_inner_vonMisesFisherNaturalMeasure_of_finrank_eq_one
    (hdim : Module.finrank ℝ E = 1) (η : E) (e : sphere (0 : E) 1) (t : ℝ) :
    cgf (fun x : sphere (0 : E) 1 ↦ ⟪(e : E), (x : E)⟫_ℝ)
      (vonMisesFisherNaturalMeasure η) t =
        log (cosh (⟪η, (e : E)⟫_ℝ + t)) - log (cosh ⟪η, (e : E)⟫_ℝ) := by
  rw [cgf, mgf_inner_vonMisesFisherNaturalMeasure_of_finrank_eq_one hdim η e,
    log_div (cosh_pos _).ne' (cosh_pos _).ne']

/-- The coordinate law is the pair of atoms at `1` and `-1` with exponential weights. -/
theorem map_inner_vonMisesFisherNaturalMeasure_of_finrank_eq_one
    (hdim : Module.finrank ℝ E = 1) (η : E) (e : sphere (0 : E) 1) :
    (vonMisesFisherNaturalMeasure η).map (fun x : sphere (0 : E) 1 ↦ ⟪(e : E), (x : E)⟫_ℝ) =
      ENNReal.ofReal (exp ⟪η, (e : E)⟫_ℝ /
        (exp ⟪η, (e : E)⟫_ℝ + exp (-⟪η, (e : E)⟫_ℝ))) • Measure.dirac 1 +
      ENNReal.ofReal (exp (-⟪η, (e : E)⟫_ℝ) /
        (exp ⟪η, (e : E)⟫_ℝ + exp (-⟪η, (e : E)⟫_ℝ))) • Measure.dirac (-1) := by
  have hm : Measurable fun x : sphere (0 : E) 1 ↦ ⟪(e : E), (x : E)⟫_ℝ := by fun_prop
  rw [vonMisesFisherNaturalMeasure_eq_of_finrank_eq_one hdim η e,
    Measure.map_add _ _ hm, Measure.map_smul _ hm.aemeasurable,
    Measure.map_smul _ hm.aemeasurable]
  simp

/-- The coordinate cdf of a one-dimensional von Mises–Fisher law has jumps at `-1` and `1`. -/
theorem cdf_map_inner_vonMisesFisherNaturalMeasure_of_finrank_eq_one
    (hdim : Module.finrank ℝ E = 1) (η : E) (e : sphere (0 : E) 1) (z : ℝ) :
    cdf ((vonMisesFisherNaturalMeasure η).map
      (fun x : sphere (0 : E) 1 ↦ ⟪(e : E), (x : E)⟫_ℝ)) z =
      if z < -1 then 0 else if z < 1 then
        exp (-⟪η, (e : E)⟫_ℝ) / (exp ⟪η, (e : E)⟫_ℝ + exp (-⟪η, (e : E)⟫_ℝ)) else 1 := by
  have : Nontrivial E := ⟨⟨e, 0, ne_zero_of_mem_sphere one_ne_zero e⟩⟩
  rw [cdf_eq_real, ← integral_indicator_one measurableSet_Iic,
    integral_map (by fun_prop)
      ((stronglyMeasurable_one (α := ℝ) (β := ℝ)).indicator
        measurableSet_Iic).aestronglyMeasurable,
    integral_comp_inner_vonMisesFisherNaturalMeasure_of_finrank_eq_one hdim η e]
  simp only [indicator_apply, mem_Iic, Pi.one_apply, smul_eq_mul]
  split_ifs <;> first | grind | field_simp

/-- The interior coordinate quantile is `-1` through the mass of the negative atom and `1`
above it. In particular the cumulative jump itself belongs to the lower branch. -/
theorem quantile_map_inner_vonMisesFisherNaturalMeasure_of_finrank_eq_one
    (hdim : Module.finrank ℝ E = 1) (η : E) (e : sphere (0 : E) 1) {u : ℝ} (hu : u ∈ Ioo 0 1) :
    ((vonMisesFisherNaturalMeasure η).map
      (fun x : sphere (0 : E) 1 ↦ ⟪(e : E), (x : E)⟫_ℝ)).quantile u =
      if u ≤ exp (-⟪η, (e : E)⟫_ℝ) /
        (exp ⟪η, (e : E)⟫_ℝ + exp (-⟪η, (e : E)⟫_ℝ)) then -1 else 1 := by
  have : Nontrivial E := ⟨⟨e, 0, ne_zero_of_mem_sphere one_ne_zero e⟩⟩
  refine eq_of_forall_lt_iff fun z ↦ ?_
  rw [Measure.lt_quantile_iff _ hu.1 hu.2,
    cdf_map_inner_vonMisesFisherNaturalMeasure_of_finrank_eq_one hdim η e]
  split_ifs <;> grind

/-- The lower support endpoint of the one-dimensional coordinate law is `-1`. -/
theorem tendsto_quantile_map_inner_vonMisesFisherNaturalMeasure_nhdsGT_zero
    (hdim : Module.finrank ℝ E = 1) (η : E) (e : sphere (0 : E) 1) :
    Tendsto (fun u ↦ (((vonMisesFisherNaturalMeasure η).map
      (fun x : sphere (0 : E) 1 ↦ ⟪(e : E), (x : E)⟫_ℝ)).quantile u : EReal))
      (𝓝[>] 0) (𝓝 (-1)) := by
  let w := exp (-⟪η, (e : E)⟫_ℝ) / (exp ⟪η, (e : E)⟫_ℝ + exp (-⟪η, (e : E)⟫_ℝ))
  have hw₀ : 0 < w := by positivity
  have hw₁ : w < 1 := (div_lt_one (by positivity)).2 (by linarith [exp_pos ⟪η, (e : E)⟫_ℝ])
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT hw₀] with u hu
  rw [quantile_map_inner_vonMisesFisherNaturalMeasure_of_finrank_eq_one hdim η e
    ⟨hu.1, hu.2.trans hw₁⟩, ite_eq_left hu.2.le]
  norm_num

/-- The upper support endpoint of the one-dimensional coordinate law is `1`. -/
theorem tendsto_quantile_map_inner_vonMisesFisherNaturalMeasure_nhdsLT_one
    (hdim : Module.finrank ℝ E = 1) (η : E) (e : sphere (0 : E) 1) :
    Tendsto (fun u ↦ (((vonMisesFisherNaturalMeasure η).map
      (fun x : sphere (0 : E) 1 ↦ ⟪(e : E), (x : E)⟫_ℝ)).quantile u : EReal))
      (𝓝[<] 1) (𝓝 1) := by
  let w := exp (-⟪η, (e : E)⟫_ℝ) / (exp ⟪η, (e : E)⟫_ℝ + exp (-⟪η, (e : E)⟫_ℝ))
  have hw₀ : 0 < w := by positivity
  have hw₁ : w < 1 := (div_lt_one (by positivity)).2 (by linarith [exp_pos ⟪η, (e : E)⟫_ℝ])
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT hw₁] with u hu
  rw [quantile_map_inner_vonMisesFisherNaturalMeasure_of_finrank_eq_one hdim η e
    ⟨hw₀.trans hu.1, hu.2⟩, ite_eq_right hu.1.not_ge]
  norm_num

end TauCeti.Probability

namespace ProbabilityTheory

open TauCeti.Probability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {Ω : Type*} [MeasurableSpace Ω]
  {P : Measure Ω} {X : Ω → sphere (0 : E) 1} {η : E}

/-- The coordinate of a one-dimensional von Mises–Fisher random point has the two-point law
with the normalized exponential weights. -/
theorem HasLaw.inner_vonMisesFisherNaturalMeasure_of_finrank_eq_one
    (hX : HasLaw X (vonMisesFisherNaturalMeasure η) P) (hdim : Module.finrank ℝ E = 1)
    (e : sphere (0 : E) 1) :
    HasLaw (fun ω ↦ ⟪(e : E), (X ω : E)⟫_ℝ)
      (ENNReal.ofReal (exp ⟪η, (e : E)⟫_ℝ /
        (exp ⟪η, (e : E)⟫_ℝ + exp (-⟪η, (e : E)⟫_ℝ))) • Measure.dirac 1 +
      ENNReal.ofReal (exp (-⟪η, (e : E)⟫_ℝ) /
        (exp ⟪η, (e : E)⟫_ℝ + exp (-⟪η, (e : E)⟫_ℝ))) • Measure.dirac (-1)) P :=
  HasLaw.comp (Y := fun x : sphere (0 : E) 1 ↦ ⟪(e : E), (x : E)⟫_ℝ)
    ⟨(by fun_prop), map_inner_vonMisesFisherNaturalMeasure_of_finrank_eq_one hdim η e⟩ hX

end ProbabilityTheory

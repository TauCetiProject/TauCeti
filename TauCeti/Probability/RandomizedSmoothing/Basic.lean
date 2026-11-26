/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Gaussian.NullSets
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Gaussian smoothing of bounded functions

Gaussian smoothing averages a function at `x + σ • z`, where `z` has standard Gaussian law.
For a measurable function taking values in `[0, 1]`, its smoothing takes values in the same
interval. At nonzero noise scale, attaining either endpoint at even one point forces the
original function to equal that endpoint almost everywhere and the smoothing to equal it
everywhere. Otherwise the smoothing lies strictly between zero and one at every point.

These endpoint characterizations separate the constant cases from the interior case needed
when composing smoothed probabilities with the Gaussian quantile.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace TauCeti.Probability.RandomizedSmoothing

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E]

/-- Gaussian smoothing with noise scale `σ`. For probabilistic applications `σ` is positive. -/
def smooth (σ : ℝ) (f : E → ℝ) (x : E) : ℝ :=
  ∫ z, f (x + σ • z) ∂stdGaussian E

/-- The integral defining Gaussian smoothing. -/
theorem smooth_def (σ : ℝ) (f : E → ℝ) (x : E) :
    smooth σ f x = ∫ z, f (x + σ • z) ∂stdGaussian E := (rfl)

/-- Smoothing preserves constants, including at zero noise scale. -/
@[simp]
theorem smooth_const (σ c : ℝ) (x : E) : smooth σ (fun _ => c) x = c := by
  simp [smooth]

/-- Zero noise leaves the function unchanged. -/
@[simp]
theorem smooth_zero_scale (f : E → ℝ) (x : E) : smooth 0 f x = f x := by
  simp [smooth]

/-- Smoothing commutes with translating the argument of the function. -/
theorem smooth_apply_add (σ : ℝ) (f : E → ℝ) (x y : E) :
    smooth σ f (x + y) = smooth σ (fun z => f (x + z)) y := by
  simp only [smooth, add_assoc]

/-- Smoothing preserves nonnegativity, even without integrability. -/
theorem smooth_nonneg {f : E → ℝ} (h0 : ∀ z, 0 ≤ f z) (σ : ℝ) (x : E) :
    0 ≤ smooth σ f x :=
  integral_nonneg fun z => h0 (x + σ • z)

/-- An upper bound of one is preserved by smoothing. -/
theorem smooth_le_one {f : E → ℝ} (h1 : ∀ z, f z ≤ 1) (σ : ℝ) (x : E) :
    smooth σ f x ≤ 1 := by
  by_cases hi : Integrable (fun z => f (x + σ • z)) (stdGaussian E)
  · simpa [smooth_def] using integral_mono hi (integrable_const (1 : ℝ))
      (fun z => h1 (x + σ • z))
  · simp [smooth_def, integral_undef hi]

/-- Smoothing preserves the closed unit interval. -/
theorem smooth_mem_Icc {f : E → ℝ} (h0 : ∀ z, 0 ≤ f z) (h1 : ∀ z, f z ≤ 1)
    (σ : ℝ) (x : E) : smooth σ f x ∈ Icc 0 1 :=
  ⟨smooth_nonneg h0 σ x, smooth_le_one h1 σ x⟩

variable [BorelSpace E]

/-- A measurable bounded probability function has an integrable smoothing integrand. -/
theorem integrable_smooth_integrand {f : E → ℝ} (hf : Measurable f)
    (h0 : ∀ z, 0 ≤ f z) (h1 : ∀ z, f z ≤ 1) (σ : ℝ) (x : E) :
    Integrable (fun z => f (x + σ • z)) (stdGaussian E) := by
  refine (integrable_const (1 : ℝ)).mono' (hf.comp (by fun_prop)).aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun z => by
    rw [Real.norm_eq_abs, abs_of_nonneg (h0 _)]
    exact h1 _

/-- Smoothing of a measurable real function is measurable. -/
@[fun_prop]
theorem measurable_smooth {f : E → ℝ} (hf : Measurable f) (σ : ℝ) :
    Measurable (smooth σ f) := by
  have h : Measurable (fun p : E × E => f (p.1 + σ • p.2)) := hf.comp (by fun_prop)
  exact h.stronglyMeasurable.integral_prod_right.measurable

/-- Smoothing commutes with taking the complementary probability. -/
@[simp]
theorem smooth_one_sub {f : E → ℝ} (hf : Measurable f)
    (h0 : ∀ z, 0 ≤ f z) (h1 : ∀ z, f z ≤ 1) (σ : ℝ) (x : E) :
    smooth σ (fun z => 1 - f z) x = 1 - smooth σ f x := by
  simp [smooth, integral_sub (integrable_const (1 : ℝ))
    (integrable_smooth_integrand hf h0 h1 σ x)]

/-- At nonzero noise scale, smoothing depends only on the Gaussian almost-everywhere class. -/
theorem smooth_congr_ae {f g : E → ℝ} (hfg : f =ᵐ[stdGaussian E] g)
    {σ : ℝ} (hσ : σ ≠ 0) (x : E) : smooth σ f x = smooth σ g x := by
  exact integral_congr_ae ((quasiMeasurePreserving_add_smul_stdGaussian x hσ).ae_eq_comp hfg)

/-- Smoothing is monotone on measurable probability functions. -/
theorem smooth_mono {f g : E → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hf0 : ∀ z, 0 ≤ f z) (hg1 : ∀ z, g z ≤ 1)
    (hfg : ∀ z, f z ≤ g z) (σ : ℝ) (x : E) : smooth σ f x ≤ smooth σ g x := by
  exact integral_mono (integrable_smooth_integrand hf hf0 (fun z => (hfg z).trans (hg1 z)) σ x)
    (integrable_smooth_integrand hg (fun z => (hf0 z).trans (hfg z)) hg1 σ x) (fun z => hfg _)

/-- Smoothing a nonnegative bounded function vanishes at one point exactly when the original
function vanishes Gaussian almost everywhere. -/
theorem smooth_eq_zero_iff {f : E → ℝ} (hf : Measurable f)
    (h0 : ∀ z, 0 ≤ f z) (h1 : ∀ z, f z ≤ 1) {σ : ℝ} (hσ : σ ≠ 0) (x : E) :
    smooth σ f x = 0 ↔ f =ᵐ[stdGaussian E] 0 := by
  rw [smooth_def, integral_eq_zero_iff_of_nonneg (fun z => h0 _)
    (integrable_smooth_integrand hf h0 h1 σ x)]
  simpa only [Filter.EventuallyEq, Pi.zero_apply] using
    (ae_add_smul_stdGaussian_iff x hσ (p := fun z => f z = 0))

/-- Smoothing a probability function equals one at one point exactly when the original
function equals one Gaussian almost everywhere. -/
theorem smooth_eq_one_iff {f : E → ℝ} (hf : Measurable f)
    (h0 : ∀ z, 0 ≤ f z) (h1 : ∀ z, f z ≤ 1) {σ : ℝ} (hσ : σ ≠ 0) (x : E) :
    smooth σ f x = 1 ↔ f =ᵐ[stdGaussian E] 1 := by
  have h := integral_eq_iff_of_ae_le (integrable_smooth_integrand hf h0 h1 σ x)
    (integrable_const (1 : ℝ)) (Filter.Eventually.of_forall fun z => h1 (x + σ • z))
  have h' : smooth σ f x = 1 ↔ ∀ᵐ z ∂stdGaussian E, f (x + σ • z) = 1 := by
    simpa [smooth_def, Filter.EventuallyEq] using h
  refine h'.trans ?_
  simpa only [Filter.EventuallyEq, Pi.one_apply] using
    (ae_add_smul_stdGaussian_iff x hσ (p := fun z => f z = 1))

/-- The smoothing is in the open unit interval exactly when neither endpoint is the
almost-everywhere value of the original probability function. -/
theorem smooth_mem_Ioo_iff {f : E → ℝ} (hf : Measurable f)
    (h0 : ∀ z, 0 ≤ f z) (h1 : ∀ z, f z ≤ 1) {σ : ℝ} (hσ : σ ≠ 0) (x : E) :
    smooth σ f x ∈ Ioo 0 1 ↔
      ¬ f =ᵐ[stdGaussian E] 0 ∧ ¬ f =ᵐ[stdGaussian E] 1 := by
  have hb := smooth_mem_Icc h0 h1 σ x
  rw [← smooth_eq_zero_iff hf h0 h1 hσ x, ← smooth_eq_one_iff hf h0 h1 hσ x]
  exact ⟨fun h => ⟨ne_of_gt h.1, ne_of_lt h.2⟩,
    fun h => ⟨lt_of_le_of_ne hb.1 (Ne.symm h.1), lt_of_le_of_ne hb.2 h.2⟩⟩

/-- A Gaussian-smoothed probability function is identically zero, identically one, or
strictly between zero and one everywhere. The endpoint cases also characterize the original
function up to Gaussian almost-everywhere equality. -/
theorem smooth_trichotomy {f : E → ℝ} (hf : Measurable f)
    (h0 : ∀ z, 0 ≤ f z) (h1 : ∀ z, f z ≤ 1) {σ : ℝ} (hσ : σ ≠ 0) :
    (f =ᵐ[stdGaussian E] 0 ∧ ∀ x, smooth σ f x = 0) ∨
    (f =ᵐ[stdGaussian E] 1 ∧ ∀ x, smooth σ f x = 1) ∨
    (∀ x, smooth σ f x ∈ Ioo 0 1) := by
  by_cases hz : f =ᵐ[stdGaussian E] 0
  · exact Or.inl ⟨hz, fun x => (smooth_eq_zero_iff hf h0 h1 hσ x).2 hz⟩
  by_cases ho : f =ᵐ[stdGaussian E] 1
  · exact Or.inr (Or.inl ⟨ho, fun x => (smooth_eq_one_iff hf h0 h1 hσ x).2 ho⟩)
  exact Or.inr (Or.inr fun x => (smooth_mem_Ioo_iff hf h0 h1 hσ x).2 ⟨hz, ho⟩)

end TauCeti.Probability.RandomizedSmoothing

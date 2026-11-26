/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.AEMeasurable
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import TauCeti.Analysis.SpecialFunctions.Log.MulLog

/-!
# Entropy of a function with respect to a measure

Defines the functional entropy `Ent_μ(g) = ∫ g log g dμ - (∫ g dμ) log (∫ g dμ)` with respect to a
measure `μ`, using the convention `0 log 0 = 0` of `Real.log`, and records its basic invariance,
homogeneity, nonnegativity, and dominated-convergence properties.

## Main definitions

* `MeasureTheory.Measure.entropy`: the entropy `Ent_μ(g)` of `g : α → ℝ` under `μ`.

## Main results

* `MeasureTheory.Measure.entropy_congr_ae`: almost everywhere equal functions have equal entropy.
* `MeasureTheory.Measure.entropy_const`: under a probability measure, constants have zero entropy.
* `MeasureTheory.Measure.entropy_const_mul`: `Ent_μ(c * g) = c * Ent_μ(g)` for every real `c` when
  `g` and `g log g` are integrable.
* `MeasureTheory.Measure.entropy_map` and `MeasureTheory.MeasurePreserving.entropy_comp`:
  invariance under measurable embeddings and measure-preserving maps.
* `MeasureTheory.Measure.entropy_nonneg`: under a probability measure, a.e. nonnegative integrable
  functions with `g log g` integrable have nonnegative entropy.
* `MeasureTheory.Measure.tendsto_entropy_of_dominated`: dominated convergence for `Ent_μ(F n)` under
  a finite measure.

## References

* S. Boucheron, G. Lugosi and P. Massart, *Concentration Inequalities*, Oxford University Press
  (2013), §4.10.
* D. Bakry, I. Gentil and M. Ledoux, *Analysis and Geometry of Markov Diffusion Operators*,
  Springer (2014), §5.1.
-/

public section

namespace MeasureTheory.Measure

/-- The **entropy** `Ent_μ(g) = ∫ g log g dμ - (∫ g dμ) log (∫ g dμ)` of a function `g`, with the
convention `0 log 0 = 0` of `Real.log`. -/
noncomputable def entropy {α : Type*} {_ : MeasurableSpace α} (μ : Measure α) (g : α → ℝ) : ℝ :=
  ∫ x, g x * Real.log (g x) ∂μ - (∫ x, g x ∂μ) * Real.log (∫ x, g x ∂μ)

/-- The defining equation for measure entropy. -/
theorem entropy_def {α : Type*} {_ : MeasurableSpace α} (μ : Measure α) (g : α → ℝ) :
    entropy μ g =
      ∫ x, g x * Real.log (g x) ∂μ - (∫ x, g x ∂μ) * Real.log (∫ x, g x ∂μ) :=
  (rfl)

@[simp]
theorem entropy_zero {α : Type*} {mα : MeasurableSpace α} (μ : Measure α) :
    entropy μ (fun _ ↦ (0 : ℝ)) = 0 := by
  simp [entropy]

@[simp]
theorem entropy_zero_measure {α : Type*} {mα : MeasurableSpace α} (g : α → ℝ) :
    entropy (0 : Measure α) g = 0 := by
  simp [entropy]

/-- Functions equal almost everywhere have equal entropy. -/
theorem entropy_congr_ae {α : Type*} {mα : MeasurableSpace α} {μ : Measure α} {g₁ g₂ : α → ℝ}
    (h : g₁ =ᵐ[μ] g₂) : entropy μ g₁ = entropy μ g₂ := by
  simp only [entropy, integral_congr_ae h]
  congr 1; exact integral_congr_ae (h.mono fun _ hx ↦ by simp [hx])

/-- Under a probability measure, any constant function has entropy zero. -/
@[simp]
theorem entropy_const {α : Type*} {mα : MeasurableSpace α} (μ : Measure α)
    [IsProbabilityMeasure μ] (c : ℝ) : entropy μ (fun _ ↦ c) = 0 := by simp [entropy]

/-- Entropy is homogeneous of degree one under scalar multiplication whenever `g` and `g log g`
are integrable: `Ent_μ(c * g) = c * Ent_μ(g)` for every `c : ℝ` (including `c ≤ 0`, since
`Real.log` is even). -/
theorem entropy_const_mul {α : Type*} {mα : MeasurableSpace α} {μ : Measure α} (c : ℝ)
    {g : α → ℝ} (hg : Integrable g μ)
    (hglog : Integrable (fun x ↦ g x * Real.log (g x)) μ) :
    entropy μ (fun x ↦ c * g x) = c * entropy μ g := by
  have hmul (t : ℝ) : (c * t) * Real.log (c * t) = c * (t * Real.log t) + (c * Real.log c) * t := by
    by_cases hc : c = 0; · simp [hc]
    by_cases ht : t = 0; · simp [ht]
    rw [Real.log_mul hc ht]; ring
  simp only [entropy_def, hmul, integral_const_mul]
  rw [integral_add (hglog.const_mul c) (hg.const_mul (c * Real.log c)),
    integral_const_mul, integral_const_mul]
  ring

/-- Entropy is preserved by transporting both the measure and function through a measurable
embedding. -/
theorem entropy_map {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
    {μ : Measure α} {φ : α → β} (hφ : MeasurableEmbedding φ) (g : β → ℝ) :
    entropy (μ.map φ) g = entropy μ (g ∘ φ) := by
  simp only [entropy, hφ.integral_map, Function.comp_apply]

/-- Pulling an a.e. strongly measurable function back along a measure-preserving map preserves its
entropy. -/
theorem _root_.MeasureTheory.MeasurePreserving.entropy_comp {α β : Type*}
    {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μ : Measure α} {ν : Measure β}
    {φ : α → β} (hφ : MeasurePreserving φ μ ν) {g : β → ℝ} (hg : AEStronglyMeasurable g ν) :
    entropy μ (g ∘ φ) = entropy ν g := by
  have hg' : AEStronglyMeasurable g (μ.map φ) := hφ.map_eq.symm ▸ hg
  simp only [entropy_def, Function.comp_def]
  rw [← hφ.map_eq, integral_map hφ.measurable.aemeasurable hg',
    integral_map hφ.measurable.aemeasurable (Real.continuous_mul_log.comp_aestronglyMeasurable hg')]

/-- **Nonnegativity of functional entropy.** Under a probability measure, any a.e. nonnegative
integrable function `g` with `g log g` integrable satisfies `0 ≤ Ent_μ(g)`. -/
theorem entropy_nonneg {α : Type*} {mα : MeasurableSpace α} {μ : Measure α}
    [IsProbabilityMeasure μ] {g : α → ℝ} (hg0 : 0 ≤ᵐ[μ] g) (hg : Integrable g μ)
    (hglog : Integrable (fun x ↦ g x * Real.log (g x)) μ) : 0 ≤ entropy μ g := by
  exact sub_nonneg.2 <| Real.convexOn_mul_log.map_integral_le Real.continuous_mul_log.continuousOn
    isClosed_Ici hg0 hg hglog

/-- **Dominated convergence for functional entropy.** Under a finite measure `μ`, if a family of
a.e. strongly measurable functions `F n` converges `μ`-a.e. to `f` along a countably generated
filter `l` and eventually satisfies `0 ≤ F n ≤ bound` `μ`-a.e. for an integrable `bound` with
`bound * log bound` integrable, then `Ent_μ(F n)` tends to `Ent_μ(f)`. -/
theorem tendsto_entropy_of_dominated {α ι : Type*} {mα : MeasurableSpace α} {μ : Measure α}
    [IsFiniteMeasure μ] {l : Filter ι} [l.IsCountablyGenerated] {F : ι → α → ℝ} {f : α → ℝ}
    (bound : α → ℝ) (hF_meas : ∀ᶠ n in l, AEStronglyMeasurable (F n) μ)
    (hF_nonneg : ∀ᶠ n in l, 0 ≤ᵐ[μ] F n) (hF_le : ∀ᶠ n in l, F n ≤ᵐ[μ] bound)
    (hbound : Integrable bound μ)
    (hbound_log : Integrable (fun x ↦ bound x * Real.log (bound x)) μ)
    (hlim : ∀ᵐ x ∂μ, Filter.Tendsto (fun n ↦ F n x) l (nhds (f x))) :
    Filter.Tendsto (fun n ↦ entropy μ (F n)) l (nhds (entropy μ f)) := by
  have hlim_int : Filter.Tendsto (fun n ↦ ∫ x, F n x ∂μ) l (nhds (∫ x, f x ∂μ)) :=
    tendsto_integral_filter_of_dominated_convergence bound hF_meas
      ((hF_nonneg.and hF_le).mono fun _ ⟨h0, hle⟩ ↦
        (h0.and hle).mono fun _ ⟨hx0, hxle⟩ ↦ by rwa [Real.norm_of_nonneg hx0])
      hbound hlim
  have hlim_log :
      Filter.Tendsto (fun n ↦ ∫ x, F n x * Real.log (F n x) ∂μ) l
        (nhds (∫ x, f x * Real.log (f x) ∂μ)) :=
    tendsto_integral_filter_of_dominated_convergence
      (fun x ↦ 1 + ‖bound x * Real.log (bound x)‖)
      (hF_meas.mono fun _ hn ↦ Real.continuous_mul_log.comp_aestronglyMeasurable hn)
      ((hF_nonneg.and hF_le).mono fun _ ⟨h0, hle⟩ ↦
        (h0.and hle).mono fun _ ⟨hx0, hxle⟩ ↦ by
          simpa only [Real.norm_eq_abs] using
            TauCeti.abs_mul_log_le_one_add_abs_mul_log hx0 hxle)
      ((integrable_const 1).add hbound_log.norm)
      (hlim.mono fun _ hx ↦ Real.continuous_mul_log.continuousAt.tendsto.comp hx)
  simp_rw [entropy_def]
  exact hlim_log.sub (Real.continuous_mul_log.continuousAt.tendsto.comp hlim_int)

end MeasureTheory.Measure

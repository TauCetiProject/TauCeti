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

/-!
# Entropy of a function with respect to a measure

Defines the functional entropy `Ent_μ(g) = ∫ g log g dμ - (∫ g dμ) log (∫ g dμ)` with respect to a
measure `μ`, using the convention `0 log 0 = 0` of `Real.log`, and records its basic invariance,
homogeneity, and nonnegativity properties.

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
  have hlog : (fun x ↦ g₁ x * Real.log (g₁ x)) =ᵐ[μ] fun x ↦ g₂ x * Real.log (g₂ x) :=
    h.mono fun _ hx ↦ by dsimp; rw [hx]
  simp only [entropy, integral_congr_ae h, integral_congr_ae hlog]

/-- Under a probability measure, any constant function has entropy zero. -/
@[simp]
theorem entropy_const {α : Type*} {mα : MeasurableSpace α} (μ : Measure α)
    [IsProbabilityMeasure μ] (c : ℝ) :
    entropy μ (fun _ ↦ c) = 0 := by
  simp [entropy]

/-- Entropy is homogeneous of degree one under scalar multiplication whenever `g` and `g log g`
are integrable: `Ent_μ(c * g) = c * Ent_μ(g)` for every `c : ℝ` (including `c ≤ 0`, since
`Real.log` is even). -/
theorem entropy_const_mul {α : Type*} {mα : MeasurableSpace α} {μ : Measure α} (c : ℝ)
    {g : α → ℝ} (hg : Integrable g μ)
    (hglog : Integrable (fun x ↦ g x * Real.log (g x)) μ) :
    entropy μ (fun x ↦ c * g x) = c * entropy μ g := by
  have hmul (t : ℝ) : (c * t) * Real.log (c * t) = c * (t * Real.log t) + (c * Real.log c) * t := by
    by_cases hc : c = 0
    · simp [hc]
    by_cases ht : t = 0
    · simp [ht]
    rw [Real.log_mul hc ht]
    ring
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
  have hglog' : AEStronglyMeasurable (fun y ↦ g y * Real.log (g y)) (μ.map φ) :=
    Real.continuous_mul_log.comp_aestronglyMeasurable hg'
  simp only [entropy_def, Function.comp_def]
  rw [← hφ.map_eq, integral_map hφ.measurable.aemeasurable hg',
    integral_map hφ.measurable.aemeasurable hglog']

/-- **Nonnegativity of functional entropy.** Under a probability measure, any a.e. nonnegative
integrable function `g` with `g log g` integrable satisfies `0 ≤ Ent_μ(g)`. -/
theorem entropy_nonneg {α : Type*} {mα : MeasurableSpace α} {μ : Measure α}
    [IsProbabilityMeasure μ] {g : α → ℝ} (hg0 : 0 ≤ᵐ[μ] g) (hg : Integrable g μ)
    (hglog : Integrable (fun x ↦ g x * Real.log (g x)) μ) :
    0 ≤ entropy μ g := by
  rw [entropy_def, sub_nonneg]
  exact Real.convexOn_mul_log.map_integral_le Real.continuous_mul_log.continuousOn
    isClosed_Ici hg0 hg hglog

end MeasureTheory.Measure

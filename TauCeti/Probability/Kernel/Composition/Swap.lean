/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Kernel.Composition.MeasureCompProd
public import Mathlib.Probability.Kernel.Disintegration.StandardBorel

/-!
# The composition-product of a measure and a kernel, in the reversed coordinate order

Mathlib's `μ ⊗ₘ κ` records the joint law of "draw `q` from `μ`, then `p` from `κ q`" as a measure
on `V × Ω`, the base coordinate first. `μ.swapCompProd κ` is that same joint law written
on `Ω × V`, the kernel coordinate first, which is the order some product semigroups come in.

Everything Mathlib proves about `⊗ₘ` transports across the swap, and this file records the
transported statements that are awkward to reconstruct at each use: the mass of a measurable
rectangle, the integral of a general function, the second marginal of a Markov composition, and
— for a nonempty standard Borel kernel target — the converse, that *every* finite measure on
`Ω × V` is such a composition of its second marginal and its conditional kernel.

## Main declarations

* `MeasureTheory.Measure.swapCompProd`: the measure `(μ ⊗ₘ κ).map Prod.swap` on `Ω × V`, with
  `MeasureTheory.Measure.swapCompProd_prod` and `MeasureTheory.Measure.lintegral_swapCompProd`
  evaluating it.
* `MeasureTheory.Measure.swapCompProd_snd_condKernel`: every finite measure whose first
  coordinate is nonempty standard Borel is the `swapCompProd` of its second marginal and its
  conditional kernel, by disintegration.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

open scoped ENNReal

namespace MeasureTheory.Measure

variable {V Ω : Type*} [MeasurableSpace V] [MeasurableSpace Ω]

/-- The measure on `Ω × V` assembled from a measure `μ` on `V` and a kernel `κ` from `V` to
`Ω`: draw the `V` coordinate from `μ`, then the `Ω` coordinate from `κ`, and swap the pair. -/
def swapCompProd (μ : Measure V) (κ : Kernel V Ω) : Measure (Ω × V) :=
  (μ ⊗ₘ κ).map Prod.swap

/-- The assembled measure is the swap-map of Mathlib's composition-product measure. -/
theorem swapCompProd_def (μ : Measure V) (κ : Kernel V Ω) :
    μ.swapCompProd κ = (μ ⊗ₘ κ).map Prod.swap :=
  (rfl)

instance isFiniteMeasure_swapCompProd (μ : Measure V) [IsFiniteMeasure μ]
    (κ : Kernel V Ω) [IsFiniteKernel κ] : IsFiniteMeasure (μ.swapCompProd κ) := by
  rw [swapCompProd]
  infer_instance

/-- The mass an assembled measure gives to a measurable rectangle: integrate the kernel mass of
the first-coordinate side over the second-coordinate side. -/
theorem swapCompProd_prod (μ : Measure V) [SFinite μ] (κ : Kernel V Ω)
    [IsSFiniteKernel κ] {A : Set Ω} (hA : MeasurableSet A) {B : Set V} (hB : MeasurableSet B) :
    μ.swapCompProd κ (A ×ˢ B) = ∫⁻ q in B, κ q A ∂μ := by
  rw [swapCompProd, map_apply measurable_swap (hA.prod hB),
    Set.preimage_swap_prod, compProd_apply_prod hB hA]

/-- Integrating against an assembled measure means first integrating over the kernel fibre and
then over the base measure. -/
theorem lintegral_swapCompProd (μ : Measure V) [SFinite μ] (κ : Kernel V Ω)
    [IsSFiniteKernel κ] {f : Ω × V → ℝ≥0∞} (hf : AEMeasurable f (μ.swapCompProd κ)) :
    ∫⁻ y, f y ∂(μ.swapCompProd κ) = ∫⁻ q, ∫⁻ p, f (p, q) ∂(κ q) ∂μ := by
  rw [swapCompProd] at hf ⊢
  rw [lintegral_map' hf measurable_swap.aemeasurable, compProd,
    Kernel.lintegral_compProd₀ (f := fun z => f z.swap) _ _ _
      (hf.comp_measurable measurable_swap)]
  simp

/-- The second marginal of an assembled measure is the measure it was assembled from. -/
@[simp]
theorem snd_swapCompProd (μ : Measure V) [SFinite μ] (κ : Kernel V Ω) [IsMarkovKernel κ] :
    (μ.swapCompProd κ).snd = μ := by
  rw [swapCompProd, snd_map_swap, fst_compProd]

/-- **Every finite measure on `Ω × V` is assembled from its second marginal and its conditional
kernel.** The kernel is the conditional distribution of the first coordinate given the second,
which exists because `Ω` is a nonempty standard Borel space; it is a Markov kernel. -/
@[simp]
theorem swapCompProd_snd_condKernel [StandardBorelSpace Ω] [Nonempty Ω]
    (μ : Measure (Ω × V)) [IsFiniteMeasure μ] :
    μ.snd.swapCompProd (μ.map Prod.swap).condKernel = μ := by
  rw [swapCompProd, ← fst_map_swap, disintegrate,
    map_map measurable_swap measurable_swap, Prod.swap_swap_eq, map_id]

end MeasureTheory.Measure

end

end

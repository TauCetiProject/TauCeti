/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.NegativeMultinomial.Basic
public import TauCeti.Probability.Distributions.Poisson.Sum
import Mathlib.Probability.Kernel.Composition.Lemmas

/-!
# Convolution of negative-multinomial laws

At fixed success and category weights, convolution adds the nonnegative shape parameters.
The identity includes shape zero, zero category weights, and empty coordinate types. Invalid
weights give zero on both sides. The corresponding independent-sum theorem retains the native
natural-valued count vectors.

The argument uses the Gamma–Poisson construction of `negativeMultinomialMeasure`: independent
Gamma intensities add their shapes, and convolution of the conditional Poisson product laws
adds their coordinate rates. Mathlib's kernel composition and product identities perform the
mixing without summing the negative-multinomial masses.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Discrete Multivariate Distributions*, Wiley, 1997.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι]

private theorem negativeMultinomialMeasure_conv_of_pos {r s p₀ : ℝ}
    (hr : 0 < r) (hs : 0 < s) (hp₀ : 0 < p₀) {p : ι → ℝ≥0}
    (hp : p₀ + ∑ i, (p i : ℝ) = 1) :
    negativeMultinomialMeasure r p₀ p ∗ negativeMultinomialMeasure s p₀ p =
      negativeMultinomialMeasure (r + s) p₀ p := by
  -- Bundling the measurable Poisson family lets us use the existing kernel product API.
  let K : Kernel ℝ (ι → ℕ) :=
    ⟨fun x => Measure.pi fun i => poissonMeasure (p i * Real.toNNReal x),
      measurable_pi_poissonMeasure_mul_toNNReal p⟩
  have hK (x : ℝ) : K x = Measure.pi fun i =>
      poissonMeasure (p i * Real.toNNReal x) := rfl
  have : IsMarkovKernel K := ⟨fun x => by rw [hK]; infer_instance⟩
  have := isProbabilityMeasure_gammaMeasure hr hp₀
  have := isProbabilityMeasure_gammaMeasure hs hp₀
  have hprod : (K ∘ₘ gammaMeasure r p₀).prod (K ∘ₘ gammaMeasure s p₀) =
      (K ∥ₖ K) ∘ₘ ((gammaMeasure r p₀).prod (gammaMeasure s p₀)) := by
    rw [Measure.prod_comp_right, Measure.prod_comp_left, Measure.comp_assoc,
      Kernel.parallelComp_comp_parallelComp, Kernel.id_comp, Kernel.comp_id]
  have hmix :
      ((K ∘ₘ gammaMeasure r p₀).prod (K ∘ₘ gammaMeasure s p₀)).map
          (fun z => z.1 + z.2) =
        ((gammaMeasure r p₀).prod (gammaMeasure s p₀)).bind (fun z => K (z.1 + z.2)) := by
    rw [hprod, Measure.map_comp _ _ (by fun_prop)]
    apply Measure.bind_congr_right
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae (ae_pos_gammaMeasure r p₀),
      Measure.quasiMeasurePreserving_snd.ae (ae_pos_gammaMeasure s p₀)] with z hz₁ hz₂
    rw [Kernel.map_apply _ (by fun_prop), Kernel.parallelComp_apply, hK, hK, hK,
      ← Measure.conv, pi_poissonMeasure_conv_pi_poissonMeasure]
    congr 1
    funext i
    rw [Real.toNNReal_add hz₁.le hz₂.le, mul_add]
  rw [negativeMultinomialMeasure_of_pos hr hp₀ hp,
    negativeMultinomialMeasure_of_pos hs hp₀ hp,
    negativeMultinomialMeasure_of_pos (add_pos hr hs) hp₀ hp]
  calc
    _ = (K ∘ₘ gammaMeasure r p₀) ∗ (K ∘ₘ gammaMeasure s p₀) := rfl
    _ = ((gammaMeasure r p₀).prod (gammaMeasure s p₀)).bind
        (fun z => K (z.1 + z.2)) := hmix
    _ = ((gammaMeasure r p₀) ∗ (gammaMeasure s p₀)).bind K := by
      rw [Measure.conv, Measure.bind_map (by fun_prop) K.aemeasurable]
    _ = _ := by
      rw [gammaMeasure_conv_gammaMeasure hr hs hp₀]
      exact Measure.bind_congr_right (ae_of_all _ hK)

/-- At fixed weights, convolution adds nonnegative negative-multinomial shapes.
Shape zero is allowed. Invalid weights give zero on both sides. -/
@[simp]
theorem negativeMultinomialMeasure_conv_negativeMultinomialMeasure {r s : ℝ}
    (hr : 0 ≤ r) (hs : 0 ≤ s) (p₀ : ℝ) (p : ι → ℝ≥0) :
    negativeMultinomialMeasure r p₀ p ∗ negativeMultinomialMeasure s p₀ p =
      negativeMultinomialMeasure (r + s) p₀ p := by
  by_cases hp : 0 < p₀ ∧ p₀ + ∑ i, (p i : ℝ) = 1
  · let _ := isProbabilityMeasure_negativeMultinomialMeasure hr hp.1 hp.2
    let _ := isProbabilityMeasure_negativeMultinomialMeasure hs hp.1 hp.2
    rcases hr.eq_or_lt with rfl | hr
    · simp [negativeMultinomialMeasure_zero hp.1 hp.2]
    rcases hs.eq_or_lt with rfl | hs
    · simp [negativeMultinomialMeasure_zero hp.1 hp.2]
    exact negativeMultinomialMeasure_conv_of_pos hr hs hp.1 hp.2
  · have hzero (t : ℝ) : negativeMultinomialMeasure t p₀ p = 0 :=
      negativeMultinomialMeasure_eq_zero_of_invalid (by tauto)
    simp [hzero]

end TauCeti.Probability

namespace ProbabilityTheory.IndepFun

open TauCeti.Probability

/-- The sum of independent negative-multinomial count vectors at fixed weights has the sum
of their nonnegative shapes, including the shape-zero and zero-category-weight boundaries. -/
theorem hasLaw_add_negativeMultinomialMeasure {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {P : Measure Ω} {X Y : Ω → ι → ℕ} {r s p₀ : ℝ} {p : ι → ℝ≥0}
    (hXY : IndepFun X Y P) (hX : HasLaw X (negativeMultinomialMeasure r p₀ p) P)
    (hY : HasLaw Y (negativeMultinomialMeasure s p₀ p) P)
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hp₀ : 0 < p₀)
    (hp : p₀ + ∑ i, (p i : ℝ) = 1) :
    HasLaw (X + Y) (negativeMultinomialMeasure (r + s) p₀ p) P := by
  let _ := isProbabilityMeasure_negativeMultinomialMeasure hr hp₀ hp
  let _ := isProbabilityMeasure_negativeMultinomialMeasure hs hp₀ hp
  simpa only [negativeMultinomialMeasure_conv_negativeMultinomialMeasure hr hs] using
    hXY.hasLaw_add hX hY

end ProbabilityTheory.IndepFun

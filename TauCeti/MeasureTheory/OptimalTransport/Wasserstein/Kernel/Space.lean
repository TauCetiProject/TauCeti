/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Kernel.Moment

/-!
# Markov kernels acting on finite-moment Wasserstein spaces

A Markov kernel with a pointwise Wasserstein-Lipschitz bound induces a Lipschitz map
between finite-moment Wasserstein spaces, for every finite exponent `1 ≤ p < ∞`,
provided one kernel law has finite moment. The underlying law is the usual mixture
`κ ∘ₘ μ`. Deterministic kernels agree with pushforward, and constant kernels give
constant maps. The construction depends only on the kernel, not the proofs or the
chosen Lipschitz bound.

## References

* Y. Ollivier, *Ricci curvature of Markov chains on metric spaces*, J. Funct. Anal.
  256 (2009), 810--864.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace TauCeti.WassersteinSpace

variable {X Y : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  [PseudoMetricSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]
  [TopologicalSpace.SeparableSpace Y] [StandardBorelSpace Y]
  {p : ℝ≥0∞} [Fact (1 ≤ p)] {L : ℝ≥0}

/-- Mixing a finite-moment probability law through a Wasserstein-Lipschitz Markov kernel.
An existential finite-moment anchor suffices; no basepoint is part of the resulting law. -/
def comp (μ : WassersteinSpace p X) (κ : Kernel X Y) [IsMarkovKernel κ] (hp : p ≠ ∞)
    (hκ : ∀ x x', wassersteinEDist p (κ x) (κ x') ≤ L * edist x x')
    (hκ₀ : ∃ x, HasFiniteMoment p (κ x)) : WassersteinSpace p Y :=
  mk (⟨κ ∘ₘ ((μ : ProbabilityMeasure X) : Measure X), inferInstance⟩ : ProbabilityMeasure Y) <| by
    obtain ⟨x, hx⟩ := hκ₀
    exact μ.hasFiniteMoment.comp_kernel Fact.out hp (.of_forall (hκ x)) hx

/-- The probability measure underlying the Wasserstein-space action is the kernel mixture. -/
@[simp]
theorem coe_comp (μ : WassersteinSpace p X) (κ : Kernel X Y) [IsMarkovKernel κ]
    (hp : p ≠ ∞) (hκ : ∀ x x', wassersteinEDist p (κ x) (κ x') ≤ L * edist x x')
    (hκ₀ : ∃ x, HasFiniteMoment p (κ x)) :
    (μ.comp κ hp hκ hκ₀ : ProbabilityMeasure Y) =
      ⟨κ ∘ₘ ((μ : ProbabilityMeasure X) : Measure X), inferInstance⟩ := by
  rw [comp]
  exact coe_mk _ _

/-- The measure underlying the Wasserstein-space action is the ordinary kernel mixture. -/
-- Simplify the outer coercion before `coe_comp` rewrites the inner probability measure.
@[simp↓]
theorem toMeasure_comp (μ : WassersteinSpace p X) (κ : Kernel X Y) [IsMarkovKernel κ]
    (hp : p ≠ ∞) (hκ : ∀ x x', wassersteinEDist p (κ x) (κ x') ≤ L * edist x x')
    (hκ₀ : ∃ x, HasFiniteMoment p (κ x)) :
    ((μ.comp κ hp hκ hκ₀ : ProbabilityMeasure Y) : Measure Y) =
      κ ∘ₘ ((μ : ProbabilityMeasure X) : Measure X) := by
  rw [coe_comp, ProbabilityMeasure.coe_mk]

/-- Kernels agreeing almost everywhere under the input law induce the same action,
independently of their chosen bounds and witness proofs. -/
theorem comp_congr (μ : WassersteinSpace p X) {κ η : Kernel X Y}
    [IsMarkovKernel κ] [IsMarkovKernel η] (hp : p ≠ ∞) {M : ℝ≥0}
    (hκ : ∀ x x', wassersteinEDist p (κ x) (κ x') ≤ L * edist x x')
    (hη : ∀ x x', wassersteinEDist p (η x) (η x') ≤ M * edist x x')
    (hκ₀ : ∃ x, HasFiniteMoment p (κ x)) (hη₀ : ∃ x, HasFiniteMoment p (η x))
    (heq : ∀ᵐ x ∂((μ : ProbabilityMeasure X) : Measure X), κ x = η x) :
    μ.comp κ hp hκ hκ₀ = μ.comp η hp hη hη₀ := by
  apply ext
  apply ProbabilityMeasure.toMeasure_injective
  simp only [toMeasure_comp]
  exact Measure.comp_congr heq

section Lipschitz

variable [StandardBorelSpace X] [SecondCountableTopology X] [BorelSpace X]
  [SecondCountableTopology Y] [BorelSpace Y]

/-- A pointwise `L`-Lipschitz Markov kernel acts `L`-Lipschitzly on finite-moment laws. -/
theorem lipschitzWith_comp {κ : Kernel X Y} [IsMarkovKernel κ] (hp : p ≠ ∞)
    (hκ : ∀ x x', wassersteinEDist p (κ x) (κ x') ≤ L * edist x x')
    (hκ₀ : ∃ x, HasFiniteMoment p (κ x)) :
    LipschitzWith L (fun μ : WassersteinSpace p X ↦ μ.comp κ hp hκ hκ₀) := by
  intro μ ν
  have hμ : HasFiniteMoment p (κ ∘ₘ ((μ : ProbabilityMeasure X) : Measure X)) := by
    simpa only [toMeasure_comp] using (μ.comp κ hp hκ hκ₀).hasFiniteMoment
  have hν : HasFiniteMoment p (κ ∘ₘ ((ν : ProbabilityMeasure X) : Measure X)) := by
    simpa only [toMeasure_comp] using (ν.comp κ hp hκ hκ₀).hasFiniteMoment
  simpa only [edist_def, toMeasure_comp] using
    wassersteinEDist_comp_le_mul Fact.out hp hμ hν hκ

end Lipschitz

/-- A deterministic kernel acts by the existing pushforward map. -/
@[simp]
theorem comp_deterministic (μ : WassersteinSpace p X) {f : X → Y} (hf : Measurable f)
    (hLip : LipschitzWith L f) (hp : p ≠ ∞)
    (hκ : ∀ x x', wassersteinEDist p (Kernel.deterministic f hf x)
      (Kernel.deterministic f hf x') ≤ L * edist x x' := (by
        intro x x'
        simpa only [Kernel.deterministic_apply,
          wassersteinEDist_dirac_dirac (zero_lt_one.trans_le Fact.out).ne'] using hLip x x'))
    (hκ₀ : ∃ x, HasFiniteMoment p (Kernel.deterministic f hf x) := (by
      obtain ⟨x⟩ := (μ : ProbabilityMeasure X).nonempty
      refine ⟨x, ?_⟩
      rw [Kernel.deterministic_apply,
        hasFiniteMoment_iff_wassersteinEDist_dirac_ne_top measurable_edist (f x)]
      simp)) :
    μ.comp (Kernel.deterministic f hf) hp hκ hκ₀ =
      map f (fun _ ↦ measurable_edist_right) hf hLip μ := by
  apply ext
  apply ProbabilityMeasure.toMeasure_injective
  simp only [toMeasure_comp, coe_map, ProbabilityMeasure.toMeasure_map]
  exact Measure.deterministic_comp_eq_map hf

/-- A constant kernel returns its fixed law, independently of the input. -/
@[simp]
theorem comp_const (μ : WassersteinSpace p X) (ν : WassersteinSpace p Y) (hp : p ≠ ∞)
    (hκ : ∀ x x', wassersteinEDist p ((Kernel.const X ((ν : ProbabilityMeasure Y) : Measure Y)) x)
      ((Kernel.const X ((ν : ProbabilityMeasure Y) : Measure Y)) x') ≤ L * edist x x' := (by
        intro x x'
        simp))
    (hκ₀ : ∃ x, HasFiniteMoment p ((Kernel.const X ((ν : ProbabilityMeasure Y) : Measure Y)) x) :=
      (by
        obtain ⟨x⟩ := (μ : ProbabilityMeasure X).nonempty
        exact ⟨x, by simpa only [Kernel.const_apply] using ν.hasFiniteMoment⟩)) :
    μ.comp (Kernel.const X ((ν : ProbabilityMeasure Y) : Measure Y)) hp hκ hκ₀ = ν := by
  apply ext
  apply ProbabilityMeasure.toMeasure_injective
  simp only [toMeasure_comp, Measure.const_comp, measure_univ, one_smul]

end TauCeti.WassersteinSpace

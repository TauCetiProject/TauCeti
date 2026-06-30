module

public import TauCeti.Probability.Process.Tail
public import Mathlib.Probability.Kernel.Condexp

/-!
# The de Finetti directing measure

For a process `X : ℕ → Ω → α` on a standard Borel space, `directingMeasure μ X ω` is the conditional
law of the initial coordinate `X 0` given the process tail σ-algebra `tailProcess X`, realised
through Mathlib's conditional-expectation kernel `condExpKernel`:

```
directingMeasure μ X ω = (condExpKernel μ (tailProcess X) ω).map (X 0).
```

This is the random directing measure of the martingale (and kernel-based Koopman) route to de
Finetti's theorem. This file records its basic theory: it is a probability measure
(`isProbabilityMeasure_directingMeasure`), its set evaluations are measurable
(`measurable_directingMeasure_coe`), and it is the conditional law of `X 0` given the tail
(`directingMeasure_X0_marginal`). Packaging it as a directing measure for `ConditionallyIIDWith`
(the product factorisation across a whole block) is left to a later step.

Adapted from `cameronfreer/exchangeability` (`DeFinetti/ViaMartingale/DirectingMeasure.lean`, pin
`e0532e59ceff23edab44dda9ab0655debbc9cc22`), here over Mathlib's `condExpKernel` and the Tau Ceti
`tailProcess` API.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace TauCeti

namespace Probability

variable {Ω α : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableSpace α]

/-- The **de Finetti directing measure**: the conditional law of the initial coordinate `X 0` given
the process tail σ-algebra `tailProcess X`, as the pushforward of the conditional-expectation kernel
`condExpKernel μ (tailProcess X)` along `X 0`. -/
@[expose]
def directingMeasure (μ : Measure Ω) [IsFiniteMeasure μ] (X : ℕ → Ω → α) (ω : Ω) : Measure α :=
  (condExpKernel μ (tailProcess X) ω).map (X 0)

/-- The directing measure is a probability measure: the conditional-expectation kernel is Markov and
`X 0` is measurable. -/
theorem isProbabilityMeasure_directingMeasure {μ : Measure Ω} [IsFiniteMeasure μ] {X : ℕ → Ω → α}
    (hX0 : Measurable (X 0)) (ω : Ω) : IsProbabilityMeasure (directingMeasure μ X ω) := by
  rw [directingMeasure]
  exact Measure.isProbabilityMeasure_map hX0.aemeasurable

/-- Each set-evaluation `ω ↦ directingMeasure μ X ω B` is measurable: it is `tailProcess`-measurable
(the conditional-expectation kernel's coordinate is), hence ambient-measurable. -/
@[fun_prop]
theorem measurable_directingMeasure_coe {μ : Measure Ω} [IsFiniteMeasure μ] {X : ℕ → Ω → α}
    (hX : ∀ n, Measurable (X n)) {B : Set α} (hB : MeasurableSet B) :
    Measurable fun ω => directingMeasure μ X ω B := by
  simp_rw [directingMeasure, Measure.map_apply (hX 0) hB]
  exact ((condExpKernel μ (tailProcess X)).measurable_coe ((hX 0) hB)).mono
    (tailProcess_le_ambient 0 fun k _ => hX k) le_rfl

/-- The directing measure is the **conditional law of the initial coordinate** `X 0` given the tail
σ-algebra: for measurable `B`, the real evaluation `ω ↦ directingMeasure μ X ω B` is a version of
the conditional expectation of `𝟙_B ∘ X 0` given `tailProcess X`. -/
theorem directingMeasure_X0_marginal {μ : Measure Ω} [IsFiniteMeasure μ] {X : ℕ → Ω → α}
    (hX : ∀ n, Measurable (X n)) {B : Set α} (hB : MeasurableSet B) :
    (fun ω => (directingMeasure μ X ω B).toReal)
      =ᵐ[μ] μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ X 0 | tailProcess X] := by
  have hcomp : (Set.indicator B (fun _ => (1 : ℝ)) ∘ X 0)
      = ((X 0) ⁻¹' B).indicator (fun _ => (1 : ℝ)) := by
    funext y
    by_cases h : X 0 y ∈ B <;> simp [Set.mem_preimage, h]
  have hint : Integrable (Set.indicator B (fun _ => (1 : ℝ)) ∘ X 0) μ := by
    rw [hcomp]; exact (integrable_const (1 : ℝ)).indicator ((hX 0) hB)
  have hpt : (fun ω => (directingMeasure μ X ω B).toReal)
      = fun ω => ∫ y, (Set.indicator B (fun _ => (1 : ℝ)) ∘ X 0) y
          ∂(condExpKernel μ (tailProcess X) ω) := by
    funext ω
    rw [hcomp, directingMeasure, Measure.map_apply (hX 0) hB,
      integral_indicator_const (1 : ℝ) ((hX 0) hB), smul_eq_mul, mul_one, measureReal_def]
  rw [hpt]
  exact (condExp_ae_eq_integral_condExpKernel
    (tailProcess_le_ambient 0 fun k _ => hX k) hint).symm

end Probability

end TauCeti

module

public import TauCeti.Probability.Process.Tail
public import Mathlib.Probability.Kernel.CondDistrib
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# The de Finetti directing measure

For a process `X : ℕ → Ω → α` valued in a standard Borel space `α`, `directingMeasure μ X ω` is the
conditional law of the initial coordinate `X 0` given the process tail σ-algebra `tailProcess X`,
realised as Mathlib's regular conditional distribution `condDistrib` of `X 0`, conditioning on
`tailProcess X` via the identity map:

```
directingMeasure μ X ω = condDistrib (X 0) (id) μ ω    (conditioning on tailProcess X).
```

Because it lives over the **value** space `α`, it needs only `[StandardBorelSpace α]` (and
`[Nonempty α]`); the sample space `Ω` is an arbitrary measurable space.

This is the random directing measure of the martingale (and kernel-based Koopman) route to de
Finetti's theorem. This file records its basic theory: it is a probability measure
(`isProbabilityMeasure_directingMeasure`), its set evaluations are `tailProcess X`-measurable
(`measurable_tailProcess_directingMeasure_coe`, with the ambient corollary
`measurable_directingMeasure_coe`), and it is the conditional law of `X 0` given the tail
(`directingMeasure_ae_eq_condExp`). It is also bundled as the `ProbabilityMeasure`-valued
`directingProbabilityMeasure`, with measurability `measurable_directingProbabilityMeasure` — the
form `ConditionallyIIDWith` consumes as its directing measure `ν`. The full block-product
factorisation (conditional independence across a whole block) is left to a later step.

Adapted from `cameronfreer/exchangeability` (`DeFinetti/ViaMartingale/DirectingMeasure.lean`, pin
`e0532e59ceff23edab44dda9ab0655debbc9cc22`); that version conditions over `Ω` (needing
`[StandardBorelSpace Ω]`), here strengthened to the value-space formulation over Mathlib's
`condDistrib` and the Tau Ceti `tailProcess` API.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace TauCeti

namespace Probability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]

/-- The **de Finetti directing measure**: the conditional law of the initial coordinate `X 0` given
the process tail σ-algebra `tailProcess X`, as the regular conditional distribution of `X 0` given
that σ-algebra (Mathlib's `condDistrib`, conditioning on `tailProcess X` via the identity map). It
lives over the value space `α`, so it needs `α` standard Borel, not `Ω`. -/
-- `directingMeasure` is intentionally opaque (no `@[expose]`): downstream code uses the
-- characteristic lemmas below (probability measure, `tailProcess`-measurability,
-- `directingMeasure_ae_eq_condExp`) rather than the definition body. A public `rfl`-unfold lemma is
-- incompatible with hiding the body (an exported unfold would require `@[expose]`), so the
-- characteristic API takes its place.
def directingMeasure (μ : Measure Ω) [IsFiniteMeasure μ] (X : ℕ → Ω → α) (ω : Ω) : Measure α :=
  @condDistrib Ω Ω α _ _ _ _ (tailProcess X) (X 0) id μ _ ω

/-- The directing measure is a probability measure: the regular conditional distribution is a Markov
kernel. -/
instance isProbabilityMeasure_directingMeasure {μ : Measure Ω} [IsFiniteMeasure μ] {X : ℕ → Ω → α}
    {ω : Ω} : IsProbabilityMeasure (directingMeasure μ X ω) := by
  rw [directingMeasure]
  infer_instance

/-- The characteristic measurability of the directing measure: each set-evaluation
`ω ↦ directingMeasure μ X ω B` is **`tailProcess X`-measurable** (it is a coordinate of the
conditional-distribution kernel conditioning on `tailProcess X`). -/
theorem measurable_tailProcess_directingMeasure_coe {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → α} {B : Set α} (hB : MeasurableSet B) :
    Measurable[tailProcess X] fun ω => directingMeasure μ X ω B := by
  have h := measurable_condDistrib (μ := μ) (Y := X 0) (X := (id : Ω → Ω))
    (mβ := tailProcess X) hB
  rwa [MeasurableSpace.comap_id] at h

/-- Ambient-measurability of the set-evaluation, a corollary of the `tailProcess`-measurable form
via `hTail : tailProcess X ≤ ‹MeasurableSpace Ω›`. -/
@[fun_prop]
theorem measurable_directingMeasure_coe {μ : Measure Ω} [IsFiniteMeasure μ] {X : ℕ → Ω → α}
    (hTail : tailProcess X ≤ (inferInstance : MeasurableSpace Ω)) {B : Set α}
    (hB : MeasurableSet B) : Measurable fun ω => directingMeasure μ X ω B :=
  (measurable_tailProcess_directingMeasure_coe hB).mono hTail le_rfl

/-- The directing measure is the **conditional law of the initial coordinate** `X 0` given the tail
σ-algebra: for measurable `B`, the real evaluation `ω ↦ directingMeasure μ X ω B` is a version of
the conditional expectation of `𝟙_B ∘ X 0` given `tailProcess X`. -/
theorem directingMeasure_ae_eq_condExp {μ : Measure Ω} [IsFiniteMeasure μ] {X : ℕ → Ω → α}
    (hTail : tailProcess X ≤ (inferInstance : MeasurableSpace Ω)) (hX0 : Measurable (X 0))
    {B : Set α} (hB : MeasurableSet B) :
    (fun ω => (directingMeasure μ X ω).real B)
      =ᵐ[μ] μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ X 0 | tailProcess X] := by
  have hid : @Measurable Ω Ω _ (tailProcess X) id := measurable_id'' hTail
  have hcomp : ((X 0) ⁻¹' B).indicator (fun _ => (1 : ℝ))
      = Set.indicator B (fun _ => (1 : ℝ)) ∘ X 0 := by
    funext y
    by_cases h : X 0 y ∈ B <;> simp [Set.mem_preimage, h]
  have h := condDistrib_ae_eq_condExp (μ := μ) (Y := X 0) (X := (id : Ω → Ω)) hid hX0 hB
  rw [MeasurableSpace.comap_id, hcomp] at h
  exact h

/-- The directing measure bundled as a `ProbabilityMeasure`-valued map — the form that
`ConditionallyIIDWith` consumes as its directing measure `ν`. -/
@[expose]
def directingProbabilityMeasure (μ : Measure Ω) [IsFiniteMeasure μ] (X : ℕ → Ω → α) (ω : Ω) :
    ProbabilityMeasure α :=
  ⟨directingMeasure μ X ω, inferInstance⟩

@[simp]
theorem directingProbabilityMeasure_toMeasure {μ : Measure Ω} [IsFiniteMeasure μ] {X : ℕ → Ω → α}
    (ω : Ω) : (directingProbabilityMeasure μ X ω : Measure α) = directingMeasure μ X ω :=
  rfl

/-- The bundled directing measure is measurable into `ProbabilityMeasure α` — the measurability of
the directing measure that `ConditionallyIIDWith` requires. -/
theorem measurable_directingProbabilityMeasure {μ : Measure Ω} [IsFiniteMeasure μ] {X : ℕ → Ω → α}
    (hTail : tailProcess X ≤ (inferInstance : MeasurableSpace Ω)) :
    Measurable (directingProbabilityMeasure μ X) := by
  refine Measurable.subtype_mk ?_
  exact Measure.measurable_of_measurable_coe _ fun B hB =>
    measurable_directingMeasure_coe hTail hB

end Probability

end TauCeti

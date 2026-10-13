/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Kernel.ProbabilityMeasure
public import TauCeti.Probability.Process.Tail.Basic
public import Mathlib.Probability.Kernel.CondDistrib

/-!
# Tail-conditioned laws of a process

For a process `X : ℕ → Ω → α` valued in a standard Borel space `α`, `directingMeasure μ X ω` is the
conditional law of the initial coordinate `X 0` given the process tail σ-algebra `tailProcess X`,
realised as Mathlib's regular conditional distribution `condDistrib` of `X 0`, conditioning on
`tailProcess X` via the identity map:

```
directingMeasure μ X ω = condDistrib (X 0) (id) μ ω    (conditioning on tailProcess X).
```

Because it lives over the **value** space `α`, it needs only `[StandardBorelSpace α]` (and
`[Nonempty α]`); the sample space `Ω` is an arbitrary measurable space.

No symmetry assumption is needed to construct this conditional law. It becomes a directing
measure when a separate theorem establishes that the coordinates are conditionally i.i.d. with
this law. The construction alone does not assert that it is the conditional law of any coordinate
other than `X 0`.

Conditioning on a different σ-algebra gives a different construction: see
`TauCeti.Probability.Process.PathLaw.InvariantConditionalLaw` for the shift-invariant one.
Agreement of these conditional laws under suitable hypotheses is a separate theorem.

This file records the basic theory: it is a probability measure
(`isProbabilityMeasure_directingMeasure`), its set evaluations are `tailProcess X`-measurable
(`measurable_tailProcess_directingMeasure_coe`, with the ambient corollary
`measurable_directingMeasure_coe`), and it is the conditional law of `X 0` given the tail
(`directingMeasure_ae_eq_condExp`). It is also bundled as the `ProbabilityMeasure`-valued
`directingProbabilityMeasure`, measurable at the `tailProcess X` level
(`measurable_tailProcess_directingProbabilityMeasure`, with the ambient corollary
`measurable_directingProbabilityMeasure`). Integration of finite products of its evaluations
lives in `TauCeti.Probability.Process.Tail.ConditionalLaw.Integral`.

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

/-- The conditional law of the initial coordinate `X 0` given
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

/-- The tail-conditioned law bundled as a `ProbabilityMeasure`-valued map. -/
def directingProbabilityMeasure (μ : Measure Ω) [IsFiniteMeasure μ] (X : ℕ → Ω → α) (ω : Ω) :
    ProbabilityMeasure α :=
  Kernel.probabilityMeasure (mβ := tailProcess X)
    (@condDistrib Ω Ω α _ _ _ _ (tailProcess X) (X 0) id μ _) ω

/-- The underlying measure of the bundled directing measure is `directingMeasure μ X ω`. -/
@[simp]
theorem directingProbabilityMeasure_toMeasure {μ : Measure Ω} [IsFiniteMeasure μ] {X : ℕ → Ω → α}
    (ω : Ω) : (directingProbabilityMeasure μ X ω : Measure α) = directingMeasure μ X ω := by
  simp only [directingProbabilityMeasure, Kernel.probabilityMeasure_toMeasure, directingMeasure]

/-- The bundled directing measure is **`tailProcess X`-measurable** into `ProbabilityMeasure α`. -/
theorem measurable_tailProcess_directingProbabilityMeasure {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → α} : Measurable[tailProcess X] (directingProbabilityMeasure μ X) :=
  Kernel.measurable_probabilityMeasure (mβ := tailProcess X)
    (@condDistrib Ω Ω α _ _ _ _ (tailProcess X) (X 0) id μ _)

/-- The bundled tail-conditioned law is ambient-measurable whenever the process tail is contained
in the ambient measurable space. -/
@[fun_prop]
theorem measurable_directingProbabilityMeasure {μ : Measure Ω} [IsFiniteMeasure μ] {X : ℕ → Ω → α}
    (hTail : tailProcess X ≤ (inferInstance : MeasurableSpace Ω)) :
    Measurable (directingProbabilityMeasure μ X) :=
  measurable_tailProcess_directingProbabilityMeasure.mono hTail le_rfl

end Probability

end TauCeti

module

public import TauCeti.Probability.Exchangeability.Basic
public import Mathlib.MeasureTheory.Measure.FiniteMeasurePi
public import Mathlib.MeasureTheory.Measure.GiryMonad

/-!
# Conditionally i.i.d. sequences

The directing-measure API for de Finetti's theorem. A process is *conditionally i.i.d.* when
there is a measurable random probability measure `ν : Ω → ProbabilityMeasure α` such that
every finite block of **distinct** coordinates has, as its law, the `ν`-mixture of the
corresponding product measure. `ConditionallyIIDWith μ X ν` names the directing measure;
`ConditionallyIID` is the existential wrapper.

This file adds the Layer 0 directing-measure definitions and their destructors only. The
bridge `ConditionallyIID → Exchangeable` (permutation invariance of the finite product
measures) is a later milestone.

These declarations follow the roadmap signatures in
`TauCetiRoadmap/Exchangeability/README.md` and
`TauCetiRoadmap/Exchangeability/Targets.lean`, Layer 0, refining the existential
`ConditionallyIID` of the roadmap into a named-directing-measure relation
(`ConditionallyIIDWith`) plus its existential wrapper. They are adapted from the
`cameronfreer/exchangeability` Layer 0 sources pinned at
`e0532e59ceff23edab44dda9ab0655debbc9cc22`, with Tau Ceti API names and hypotheses.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace Probability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- Conditional i.i.d.-ness with a specified directing probability measure `ν`: the random
measure `ν` is measurable, and along every finite selection `k` of **distinct** coordinates
the block law is the `ν`-mixture of the product measure
`ProbabilityMeasure.pi (fun _ => ν ω)`. Distinctness (`Function.Injective k`) is what product
laws need, in contrast with the order condition `StrictMono` of `Contractable`. -/
def ConditionallyIIDWith (μ : Measure Ω) (X : ℕ → Ω → α) (ν : Ω → ProbabilityMeasure α) :
    Prop :=
  Measurable ν ∧
    ∀ (m : ℕ) (k : Fin m → ℕ), Function.Injective k →
      blockLaw μ X k = μ.bind fun ω => (ProbabilityMeasure.pi fun _ : Fin m => ν ω).toMeasure

/-- Constructor: a measurable directing measure together with the finite-block mixture identity. -/
theorem ConditionallyIIDWith.intro {μ : Measure Ω} {X : ℕ → Ω → α} {ν : Ω → ProbabilityMeasure α}
    (hν : Measurable ν)
    (h : ∀ (m : ℕ) (k : Fin m → ℕ), Function.Injective k →
      blockLaw μ X k = μ.bind fun ω => (ProbabilityMeasure.pi fun _ : Fin m => ν ω).toMeasure) :
    ConditionallyIIDWith μ X ν :=
  ⟨hν, h⟩

/-- Characteristic restatement of `ConditionallyIIDWith`. -/
theorem conditionallyIIDWith_iff {μ : Measure Ω} {X : ℕ → Ω → α} {ν : Ω → ProbabilityMeasure α} :
    ConditionallyIIDWith μ X ν ↔
      Measurable ν ∧
        ∀ (m : ℕ) (k : Fin m → ℕ), Function.Injective k →
          blockLaw μ X k = μ.bind fun ω => (ProbabilityMeasure.pi fun _ : Fin m => ν ω).toMeasure :=
  Iff.rfl

/-- Conditional i.i.d.-ness: existence of a directing probability measure. -/
def ConditionallyIID (μ : Measure Ω) (X : ℕ → Ω → α) : Prop :=
  ∃ ν : Ω → ProbabilityMeasure α, ConditionallyIIDWith μ X ν

/-- Constructor from a directing measure together with its witness. -/
theorem ConditionallyIID.of_directing {μ : Measure Ω} {X : ℕ → Ω → α}
    {ν : Ω → ProbabilityMeasure α} (h : ConditionallyIIDWith μ X ν) : ConditionallyIID μ X :=
  ⟨ν, h⟩

/-- Characteristic restatement of `ConditionallyIID`. -/
theorem conditionallyIID_iff {μ : Measure Ω} {X : ℕ → Ω → α} :
    ConditionallyIID μ X ↔ ∃ ν : Ω → ProbabilityMeasure α, ConditionallyIIDWith μ X ν :=
  Iff.rfl

/-- The directing measure of a `ConditionallyIIDWith` witness is measurable. -/
@[grind →]
theorem ConditionallyIIDWith.measurable_directing {μ : Measure Ω} {X : ℕ → Ω → α}
    {ν : Ω → ProbabilityMeasure α} (h : ConditionallyIIDWith μ X ν) : Measurable ν :=
  h.1

/-- The defining finite-block mixture identity of a `ConditionallyIIDWith` witness. -/
@[grind =>]
theorem ConditionallyIIDWith.map {μ : Measure Ω} {X : ℕ → Ω → α}
    {ν : Ω → ProbabilityMeasure α} (h : ConditionallyIIDWith μ X ν)
    {m : ℕ} (k : Fin m → ℕ) (hk : Function.Injective k) :
    blockLaw μ X k = μ.bind fun ω => (ProbabilityMeasure.pi fun _ : Fin m => ν ω).toMeasure :=
  h.2 m k hk

/-- A `ConditionallyIID` process has a directing probability measure. -/
theorem ConditionallyIID.exists_directing {μ : Measure Ω} {X : ℕ → Ω → α}
    (h : ConditionallyIID μ X) :
    ∃ ν : Ω → ProbabilityMeasure α, ConditionallyIIDWith μ X ν :=
  h

end Probability

end TauCeti

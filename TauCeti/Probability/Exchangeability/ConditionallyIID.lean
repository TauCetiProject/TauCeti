module

public import TauCeti.Probability.Exchangeability.Basic
public import Mathlib.MeasureTheory.Measure.FiniteMeasurePi

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
@[expose]
def ConditionallyIIDWith (μ : Measure Ω) (X : ℕ → Ω → α) (ν : Ω → ProbabilityMeasure α) :
    Prop :=
  Measurable ν ∧
    ∀ (m : ℕ) (k : Fin m → ℕ), Function.Injective k →
      blockLaw μ X k = μ.bind fun ω => (ProbabilityMeasure.pi fun _ : Fin m => ν ω).toMeasure

/-- Conditional i.i.d.-ness: existence of a directing probability measure. -/
@[expose]
def ConditionallyIID (μ : Measure Ω) (X : ℕ → Ω → α) : Prop :=
  ∃ ν : Ω → ProbabilityMeasure α, ConditionallyIIDWith μ X ν

/-- The directing measure of a `ConditionallyIIDWith` witness is measurable. -/
theorem ConditionallyIIDWith.measurable_directing {μ : Measure Ω} {X : ℕ → Ω → α}
    {ν : Ω → ProbabilityMeasure α} (h : ConditionallyIIDWith μ X ν) : Measurable ν :=
  h.1

/-- The defining finite-block mixture identity of a `ConditionallyIIDWith` witness. Named
`finite_map_eq` rather than `map_eq` to avoid colliding with `Measure.map` lemmas. -/
theorem ConditionallyIIDWith.finite_map_eq {μ : Measure Ω} {X : ℕ → Ω → α}
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

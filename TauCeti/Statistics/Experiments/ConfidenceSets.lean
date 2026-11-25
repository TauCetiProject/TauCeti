/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Statistics.Experiments.Tests

/-!
# Confidence sets and their duality with tests

A confidence set for a family of laws `P : Θ → Measure X` assigns to each observation `x` a set
`C x` of parameters. It has coverage `1 - α` when for every `θ` the event `{x | θ ∈ C x}` is
measurable and has `P θ`-probability at least `1 - α`.

Confidence sets and tests are dual. Given for each `θ` a nonrandomized test of the point null
hypothesis `{θ}`, with rejection region `reject θ`, the set of parameters that are not rejected
at `x` is a confidence set; it has coverage `1 - α` exactly when every test has level `α`.
Conversely a confidence set `C` gives the tests rejecting `θ` on `{x | θ ∉ C x}`.

## Main definitions

* `TauCeti.HasConfidenceCoverage P C α`: `C` has coverage `1 - α`.
  It is used through `TauCeti.hasConfidenceCoverage_iff`, the constructor
  `TauCeti.HasConfidenceCoverage.mk` and the accessors `TauCeti.HasConfidenceCoverage.measurableSet`
  and `TauCeti.HasConfidenceCoverage.le_measureReal`.
* `TauCeti.confidenceSetOfTests reject`: the confidence set `x ↦ {θ | x ∉ reject θ}`.

## Main results

* `TauCeti.hasConfidenceCoverage_iff_forall_hasTestLevel`: `C` has coverage `1 - α` iff for
  every `θ` the indicator of `{x | θ ∉ C x}` is a test of level `α` for `{θ}`.
* `TauCeti.HasConfidenceCoverage.hasTestLevel`: a confidence set of coverage `1 - α` gives
  level-`α` tests.
* `TauCeti.hasConfidenceCoverage_confidenceSetOfTests`: inverting level-`α` tests gives a
  confidence set of coverage `1 - α`.
* `TauCeti.HasConfidenceCoverage.mono`, `TauCeti.hasConfidenceCoverage_empty_iff`,
  `TauCeti.hasConfidenceCoverage_univ_iff`: coverage `1 - α` implies coverage `1 - β` for
  `α ≤ β`; the empty confidence set has coverage `1 - α` iff `1 ≤ α`, and the trivial one iff
  `0 ≤ α`.

## References

* M. J. Schervish, *Theory of Statistics*, Springer (1995), Definition 5.47 and
  Proposition 5.48.

The definitions and the test-to-confidence-set direction are adapted from the lean-CKSD project
(<https://github.com/bjbraams/lean-CKSD>), file `CKSD/Inference/Model.lean`.
-/

public section

noncomputable section

open MeasureTheory Set

namespace TauCeti

variable {Θ X : Type*} [MeasurableSpace X] {P : Θ → Measure X}

/-- The confidence set `C` has **coverage** `1 - α`: for every `θ` the event `{x | θ ∈ C x}` is
measurable and has `P θ`-probability at least `1 - α`. -/
def HasConfidenceCoverage (P : Θ → Measure X) (C : X → Set Θ) (α : ℝ) : Prop :=
  ∀ θ, MeasurableSet {x | θ ∈ C x} ∧ 1 - α ≤ (P θ).real {x | θ ∈ C x}

section API

variable {C : X → Set Θ} {α β : ℝ}

/-- The defining property of `HasConfidenceCoverage`. -/
theorem hasConfidenceCoverage_iff :
    HasConfidenceCoverage P C α ↔
      ∀ θ, MeasurableSet {x | θ ∈ C x} ∧ 1 - α ≤ (P θ).real {x | θ ∈ C x} := Iff.rfl

namespace HasConfidenceCoverage

/-- Coverage `1 - α` from measurability and the probability bound at every `θ`. -/
theorem mk (hm : ∀ θ, MeasurableSet {x | θ ∈ C x})
    (hle : ∀ θ, 1 - α ≤ (P θ).real {x | θ ∈ C x}) : HasConfidenceCoverage P C α :=
  hasConfidenceCoverage_iff.2 fun θ ↦ ⟨hm θ, hle θ⟩

/-- For a confidence set with coverage, the event that it covers `θ` is measurable. -/
theorem measurableSet (h : HasConfidenceCoverage P C α) (θ : Θ) :
    MeasurableSet {x | θ ∈ C x} :=
  (hasConfidenceCoverage_iff.1 h θ).1

/-- A confidence set of coverage `1 - α` covers `θ` with `P θ`-probability at least `1 - α`. -/
theorem le_measureReal (h : HasConfidenceCoverage P C α) (θ : Θ) :
    1 - α ≤ (P θ).real {x | θ ∈ C x} :=
  (hasConfidenceCoverage_iff.1 h θ).2

/-- Coverage `1 - α` implies coverage `1 - β` for every `β ≥ α`. -/
theorem mono (h : HasConfidenceCoverage P C α) (hαβ : α ≤ β) : HasConfidenceCoverage P C β :=
  .mk h.measurableSet fun θ ↦ (sub_le_sub_left hαβ 1).trans (h.le_measureReal θ)

end HasConfidenceCoverage

/-- The empty confidence set has coverage `1 - α` iff `1 ≤ α`, for a nonempty parameter type. -/
@[simp]
theorem hasConfidenceCoverage_empty_iff [Nonempty Θ] :
    HasConfidenceCoverage P (fun _ ↦ ∅) α ↔ 1 ≤ α := by
  simp [hasConfidenceCoverage_iff]

/-- The confidence set of all parameters has coverage `1 - α` iff `0 ≤ α`, for a nonempty
parameter type and probability laws. -/
@[simp]
theorem hasConfidenceCoverage_univ_iff [Nonempty Θ] [∀ θ, IsProbabilityMeasure (P θ)] :
    HasConfidenceCoverage P (fun _ ↦ univ) α ↔ 0 ≤ α := by
  simp [hasConfidenceCoverage_iff]

end API

/-- The confidence set obtained by **inverting tests** with rejection regions `reject θ`: at `x`
it contains the parameters `θ` whose test does not reject. -/
def confidenceSetOfTests (reject : Θ → Set X) (x : X) : Set Θ :=
  {θ | x ∉ reject θ}

omit [MeasurableSpace X] in
/-- A parameter lies in the inverted confidence set at `x` iff its test does not reject at `x`. -/
@[simp]
theorem mem_confidenceSetOfTests {reject : Θ → Set X} {x : X} {θ : Θ} :
    θ ∈ confidenceSetOfTests reject x ↔ x ∉ reject θ := Iff.rfl

/-- **Duality of confidence sets and tests**: `C` has coverage `1 - α` iff for every `θ` the
nonrandomized test rejecting on `{x | θ ∉ C x}` has level `α` for the null hypothesis `{θ}`. -/
theorem hasConfidenceCoverage_iff_forall_hasTestLevel [∀ θ, IsProbabilityMeasure (P θ)]
    {C : X → Set Θ} {α : ℝ} :
    HasConfidenceCoverage P C α ↔
      ∀ θ, HasTestLevel P {θ} α ({x | θ ∉ C x}.indicator 1) := by
  refine forall_congr' fun θ ↦ ?_
  have hcompl : {x | θ ∉ C x} = {x | θ ∈ C x}ᶜ := rfl
  rw [hasTestLevel_iff, hcompl, isStatisticalTest_indicator_one_iff, MeasurableSet.compl_iff,
    forall_mem_singleton]
  refine and_congr_right fun hm ↦ ?_
  rw [testPower_indicator_one hm.compl, measureReal_compl hm, probReal_univ, sub_le_comm]

/-- A confidence set `C` of coverage `1 - α` gives, at every `θ` whose law `P θ` is a probability
measure, the nonrandomized test of level `α` for the null hypothesis `{θ}` that rejects on
`{x | θ ∉ C x}`. Only the law at `θ` needs to be normalized. -/
theorem HasConfidenceCoverage.hasTestLevel {C : X → Set Θ} {α : ℝ}
    (h : HasConfidenceCoverage P C α) (θ : Θ) [IsProbabilityMeasure (P θ)] :
    HasTestLevel P {θ} α ({x | θ ∉ C x}.indicator 1) := by
  have hcompl : {x | θ ∉ C x} = {x | θ ∈ C x}ᶜ := rfl
  have hm := (h.measurableSet θ).compl
  rw [hcompl]
  refine .mk (isStatisticalTest_indicator_one_iff.2 hm) fun θ' hθ' ↦ ?_
  rw [mem_singleton_iff.1 hθ', testPower_indicator_one hm, measureReal_compl (h.measurableSet θ),
    probReal_univ]
  linarith [h.le_measureReal θ]

/-- **Inverting level-`α` tests**: if for every `θ` the nonrandomized test with rejection region
`reject θ` has level `α` for the null hypothesis `{θ}`, then the parameters not rejected at `x`
form a confidence set of coverage `1 - α`. -/
theorem hasConfidenceCoverage_confidenceSetOfTests [∀ θ, IsProbabilityMeasure (P θ)]
    {reject : Θ → Set X} {α : ℝ} (h : ∀ θ, HasTestLevel P {θ} α ((reject θ).indicator 1)) :
    HasConfidenceCoverage P (confidenceSetOfTests reject) α :=
  hasConfidenceCoverage_iff_forall_hasTestLevel.2 fun θ ↦ by
    simpa only [mem_confidenceSetOfTests, not_not, ofPred_mem_eq] using h θ

end TauCeti

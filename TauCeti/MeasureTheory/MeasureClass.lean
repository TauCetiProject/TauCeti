/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-!
# Measure classes

Two measures are **equivalent**, or in the same *measure class*, when each is absolutely
continuous with respect to the other:

```text
MeasureEquiv μ ν  ↔  μ ≪ ν ∧ ν ≪ μ.
```

This is the datum that spectral multiplicity theory carries: by
`ForTauCeti/MeasureTheory/RadonNikodymL2.lean`, the `L²` space of a measure *together with its
multiplication operators* depends only on the measure class, so a multiplication model records a
class and not a measure.

Mathlib has no name for this relation -- a search for `MutuallyAbsolutelyContinuous`,
`MeasureClass` and `Measure.Equivalent` turns up only `OuterMeasureClass`, which is unrelated --
so it is introduced here.

## Main results

* `TauCeti.MeasureEquiv`: the relation.
* `TauCeti.measureEquiv_equivalence` and `TauCeti.measureClassSetoid`: it is an equivalence
  relation, packaged so that the quotient can be formed without touching a call site.
* `TauCeti.MeasureEquiv.restrict`: it is preserved by restriction.
* `TauCeti.measureEquiv_restrict_congr`: restricting to almost-equal sets gives equal measures.
* `TauCeti.measureEquiv_withDensity_restrict`: **a density and the restriction to its support are
  equivalent** -- the lemma that converts a dominated family of measures into a family of
  restrictions of one measure.

## Design notes

`Equivalence` is proved here even though the immediate consumers only need the conjunction.  It
costs three lines, and it is what lets the canonical (quotient-valued) form of the multiplicity
datum be built later as a strict extension rather than a rewrite: the existential form of the
multiplicity invariant needs only the conjunction, but the canonical form needs the quotient.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Extraction class: **authored in place** for the Tau Ceti staging layer.
* Spectra influence: **none** -- this module imports only Mathlib.
-/

public section

open MeasureTheory

open scoped ENNReal

namespace TauCeti

variable {α : Type*} [MeasurableSpace α] {μ ν ρ : Measure α}

/-- **Two measures are equivalent** when each is absolutely continuous with respect to the
other, i.e. they have the same null sets.

This is the standard "same measure class" relation.  It is stated as a plain conjunction rather
than as a structure so that the two halves are available as `.1` and `.2` with no projection
lemmas.  Exposed so that consumers can take `.1` and `.2` and build the conjunction directly:
`measureEquiv_sliceSum` and the frontier's `SameSpectralMultiplicity` both do. -/
@[expose]
def MeasureEquiv (μ ν : Measure α) : Prop :=
  μ ≪ ν ∧ ν ≪ μ

/-- Measure equivalence is reflexive. -/
@[refl]
theorem MeasureEquiv.refl (μ : Measure α) : MeasureEquiv μ μ :=
  ⟨Measure.AbsolutelyContinuous.rfl, Measure.AbsolutelyContinuous.rfl⟩

/-- Measure equivalence is reflexive, with the measure implicit. -/
theorem MeasureEquiv.rfl : MeasureEquiv μ μ :=
  MeasureEquiv.refl μ

/-- Measure equivalence is symmetric. -/
@[symm]
theorem MeasureEquiv.symm (h : MeasureEquiv μ ν) : MeasureEquiv ν μ :=
  ⟨h.2, h.1⟩

/-- Measure equivalence is transitive. -/
theorem MeasureEquiv.trans (h : MeasureEquiv μ ν) (h' : MeasureEquiv ν ρ) : MeasureEquiv μ ρ :=
  ⟨h.1.trans h'.1, h'.2.trans h.2⟩

/-- Measure equivalence is an equivalence relation.  Proved at the point of definition so the
quotient by it -- the *measure class* proper -- can be formed later without disturbing any
consumer of the relation itself. -/
theorem measureEquiv_equivalence : Equivalence (@MeasureEquiv α _) where
  refl := MeasureEquiv.refl
  symm := MeasureEquiv.symm
  trans := MeasureEquiv.trans

/-- The setoid of measures under equivalence.  Its quotient is the type of **measure classes**. -/
def measureClassSetoid (α : Type*) [MeasurableSpace α] : Setoid (Measure α) where
  r := MeasureEquiv
  iseqv := measureEquiv_equivalence

/-- Two equivalent measures have the same null sets -- which is the relation unfolded, stated in
the form a call site usually wants. -/
theorem MeasureEquiv.measure_eq_zero_iff (h : MeasureEquiv μ ν) (s : Set α) :
    μ s = 0 ↔ ν s = 0 :=
  ⟨fun hs => h.2 hs, fun hs => h.1 hs⟩

/-- Equivalent measures have the same almost-everywhere filter. -/
theorem MeasureEquiv.ae_eq (h : MeasureEquiv μ ν) : (ae μ : Filter α) = ae ν :=
  le_antisymm h.1.ae_le h.2.ae_le

/-- Measure equivalence is preserved by restriction to a common set. -/
theorem MeasureEquiv.restrict (h : MeasureEquiv μ ν) (s : Set α) :
    MeasureEquiv (μ.restrict s) (ν.restrict s) :=
  ⟨h.1.restrict s, h.2.restrict s⟩

/-- Restricting one measure to two almost-equal sets gives literally the same measure, hence
equivalent ones.

This is what lets the multiplicity level sets of two operators be compared "up to a null set":
the models built from them are then built from *equal* measures. -/
theorem measureEquiv_restrict_congr {s t : Set α} (h : s =ᵐ[μ] t) :
    MeasureEquiv (μ.restrict s) (μ.restrict t) := by
  rw [Measure.restrict_congr_set h]

/-- **A density and the restriction to its support carry the same measure class.**

For measurable `f : α → ℝ≥0∞`, the measure `f · μ` and the restriction of `μ` to
`{x | f x ≠ 0}` have exactly the same null sets: a set is `f · μ`-null iff `f` vanishes
`μ`-almost everywhere on it, iff its intersection with the support of `f` is `μ`-null.

This is the step that turns a *dominated countable family* of measures into a family of
restrictions of a single measure: if every `μₙ` is absolutely continuous with respect to `ρ`
then `μₙ = ρ.withDensity (dμₙ/dρ)` is equivalent to `ρ.restrict {dμₙ/dρ ≠ 0}`, so all the
measures in the family become restrictions of the one measure `ρ` to Borel sets. -/
theorem measureEquiv_withDensity_restrict (μ : Measure α) {f : α → ℝ≥0∞} (hf : Measurable f) :
    MeasureEquiv (μ.withDensity f) (μ.restrict {x | f x ≠ 0}) := by
  have hmeas : MeasurableSet {x | f x ≠ 0} := (hf (measurableSet_singleton (0 : ℝ≥0∞))).compl
  have key : ∀ s : Set α, MeasurableSet s →
      (μ.withDensity f s = 0 ↔ μ.restrict {x | f x ≠ 0} s = 0) := by
    intro s hs
    have hrestrict : μ.restrict {x | f x ≠ 0} s = μ.restrict s {x | f x ≠ 0} := by
      rw [Measure.restrict_apply hs, Measure.restrict_apply hmeas, Set.inter_comm]
    rw [withDensity_apply _ hs, lintegral_eq_zero_iff hf, hrestrict]
    constructor
    · intro hzero
      rw [Filter.EventuallyEq, ae_iff] at hzero
      exact measure_mono_null (fun x hx => by simpa using hx) hzero
    · intro hzero
      rw [Filter.EventuallyEq, ae_iff]
      exact measure_mono_null (fun x hx => by simpa using hx) hzero
  exact ⟨Measure.AbsolutelyContinuous.mk fun s hs hs0 => (key s hs).mpr hs0,
    Measure.AbsolutelyContinuous.mk fun s hs hs0 => (key s hs).mp hs0⟩

/-- **Every measure absolutely continuous with respect to `ρ` is a restriction of `ρ`, up to
class.**  The set is the support of the Radon--Nikodym derivative.

This is `measureEquiv_withDensity_restrict` composed with `Measure.withDensity_rnDeriv_eq`, and
it is the form the multiplicity construction consumes. -/
theorem exists_measurableSet_measureEquiv_restrict (μ ρ : Measure α)
    [μ.HaveLebesgueDecomposition ρ] (h : μ ≪ ρ) :
    ∃ s : Set α, MeasurableSet s ∧ MeasureEquiv μ (ρ.restrict s) := by
  refine ⟨{x | μ.rnDeriv ρ x ≠ 0},
    (Measure.measurable_rnDeriv μ ρ (measurableSet_singleton 0)).compl, ?_⟩
  have := measureEquiv_withDensity_restrict ρ (Measure.measurable_rnDeriv μ ρ)
  rwa [Measure.withDensity_rnDeriv_eq μ ρ h] at this

end TauCeti

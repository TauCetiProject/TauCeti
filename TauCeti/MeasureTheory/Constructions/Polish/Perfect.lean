/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.SetTheory.Cardinal.Continuum

/-!
# The perfect set theorem and the cardinality of Borel sets

Mathlib proves the perfect set theorem for closed sets: an uncountable closed subset of a Polish
space contains the range of a continuous injection of Cantor space
(`IsClosed.exists_nat_bool_injection_of_not_countable`). This file extends it to Borel sets. A
Borel set is clopen for a finer Polish topology (`MeasurableSet.isClopenable`); the closed-set
theorem applies there, and a map continuous for the finer topology is continuous for the
original one.

For cardinality, Mathlib's Borel isomorphism theorem says that an uncountable standard Borel
space is Borel isomorphic to Cantor space (`PolishSpace.measurableEquivNatBoolOfNotCountable`), and
a measurable subset of a standard Borel space is standard Borel (`MeasurableSet.standardBorel`).
Hence an uncountable measurable subset of a standard Borel space, such as an uncountable Borel
subset of a Polish space, has exactly `𝔠` points: Borel sets satisfy the continuum hypothesis.

## Main results

* `MeasurableSet.exists_nat_bool_injection_of_not_countable`: an uncountable Borel subset of a
  Polish space contains the range of a continuous injection of Cantor space.
* `MeasurableSet.mk_eq_continuum_of_not_countable`: an uncountable measurable subset of a standard
  Borel space has exactly `𝔠` points.

## References

* A. S. Kechris, *Classical Descriptive Set Theory*, Graduate Texts in Mathematics 156,
  Springer, 1995, Theorem 13.6 (the perfect set theorem for Borel sets, proved through
  Theorem 13.1 on finer Polish topologies).
-/

public section

open Set Function Cardinal

universe u

variable {X : Type u}

/-- **The perfect set theorem for Borel sets** (Alexandrov–Hausdorff). An uncountable Borel
subset of a Polish space contains the range of a continuous injection of Cantor space. -/
theorem MeasurableSet.exists_nat_bool_injection_of_not_countable [TopologicalSpace X]
    [PolishSpace X] [MeasurableSpace X] [BorelSpace X] {s : Set X} (hs : MeasurableSet s)
    (hunc : ¬s.Countable) :
    ∃ f : (ℕ → Bool) → X, range f ⊆ s ∧ Continuous f ∧ Injective f := by
  obtain ⟨t, hle, ht, hclosed, -⟩ := hs.isClopenable
  obtain ⟨f, hfs, hf, hinj⟩ :=
    @IsClosed.exists_nat_bool_injection_of_not_countable X t ht s hclosed hunc
  exact ⟨f, hfs, continuous_le_rng hle hf, hinj⟩

/-- **Borel sets satisfy the continuum hypothesis.** An uncountable measurable subset of a
standard Borel space, such as an uncountable Borel subset of a Polish space, has exactly continuum
many points. -/
theorem MeasurableSet.mk_eq_continuum_of_not_countable [MeasurableSpace X] [StandardBorelSpace X]
    {s : Set X} (hs : MeasurableSet s) (hunc : ¬s.Countable) : #s = 𝔠 := by
  have := hs.standardBorel
  simpa using lift_mk_eq'.2
    ⟨(PolishSpace.measurableEquivNatBoolOfNotCountable (countable_coe_iff.not.2 hunc)).toEquiv⟩

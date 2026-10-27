/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import TauCeti.MeasureTheory.MeasurableSpace.Card

/-!
# The perfect set theorem for Borel sets, and cardinality bounds

Mathlib proves the perfect set theorem for closed sets: an uncountable closed subset of a Polish
space contains the range of a continuous injection of Cantor space
(`IsClosed.exists_nat_bool_injection_of_not_countable`). This file extends it to Borel sets. A
Borel set is clopen for a finer Polish topology (`MeasurableSet.isClopenable`); the closed-set
theorem applies there, and a map continuous for the finer topology is continuous for the
original one.

In the other direction, a countably separated measurable space, and in particular a standard
Borel space, has at most continuum many points (`TauCeti.mk_le_continuum_of_countablySeparated`).
Combined, an uncountable Borel subset of a Polish space has exactly `𝔠` points: Borel sets
satisfy the continuum hypothesis.

## Main results

* `MeasurableSet.exists_nat_bool_injection_of_not_countable`: an uncountable Borel subset of a
  Polish space contains the range of a continuous injection of Cantor space.
* `MeasurableSet.mk_eq_continuum_of_not_countable`: an uncountable Borel subset of a Polish space
  has exactly `𝔠` points.

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

/-- **Borel sets satisfy the continuum hypothesis.** An uncountable Borel subset of a Polish space
has exactly continuum many points. -/
theorem MeasurableSet.mk_eq_continuum_of_not_countable [TopologicalSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X] {s : Set X} (hs : MeasurableSet s) (hunc : ¬s.Countable) :
    #s = 𝔠 := by
  refine le_antisymm (TauCeti.mk_le_continuum_of_countablySeparated s) ?_
  obtain ⟨f, hfs, -, hf⟩ := hs.exists_nat_bool_injection_of_not_countable hunc
  have hinj : Injective fun x => (⟨f x, hfs (mem_range_self x)⟩ : s) := fun x y hxy =>
    hf (congrArg Subtype.val hxy)
  simpa using lift_mk_le_lift_mk_of_injective hinj

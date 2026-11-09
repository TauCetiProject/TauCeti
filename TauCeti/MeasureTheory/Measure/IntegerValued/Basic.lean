/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Count
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.Restrict
public import TauCeti.MeasureTheory.Measure.Sub

/-!
# Integer-valued measures

`Measure.IsIntegerValued` says that every measurable set of finite mass has natural-number
mass. Equivalently, measurable sets have mass in `ℕ ∪ {∞}`: this is the extended
integer-valued condition of Kallenberg. It implies neither s-finiteness nor a representation
as a countable sum of Dirac measures. In general it is weaker than the counting measures of
Last–Penrose, Definition 2.1, which are countable sums of finite integer-valued measures.
Neither local finiteness nor simplicity is part of this predicate.

Integer-valued measures are closed under mapping, restriction and
superposition. In particular, `IsIntegerValued.sum` applies to sums of Dirac occurrences,
without requiring distinct locations or nonexplosion. Repeated locations retain their
multiplicity. With measurable singletons, removing one Dirac occurrence also preserves
integrality. Local finiteness can subsequently be checked separately on compact sets.

The characterization `isIntegerValued_smul_dirac_iff` distinguishes an occurrence with natural
multiplicity from an atom of fractional mass, and also records the allowed infinite-mass case.

## References

* Olav Kallenberg, *Random Measures, Theory and Applications*, Springer, 2017
  (extended integer-valued measures).
* Günter Last and Mathew Penrose, *Lectures on the Poisson Process*, Cambridge University
  Press, 2018, Chapter 2 (the stronger counting-measure notion motivating point processes).
-/

public section

open scoped ENNReal

namespace MeasureTheory.Measure

variable {X Y ι : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {μ ν : Measure X}

/-- A measure is integer-valued if every measurable set of finite mass has natural-number mass.
Sets of infinite mass are allowed, and multiplicities need not be at most one. -/
def IsIntegerValued (μ : Measure X) : Prop :=
  ∀ ⦃A : Set X⦄, MeasurableSet A → μ A < ∞ → ∃ n : ℕ, μ A = n

/-- The defining finite-mass characterization of an integer-valued measure. -/
theorem isIntegerValued_def : μ.IsIntegerValued ↔
    ∀ ⦃A : Set X⦄, MeasurableSet A → μ A < ∞ → ∃ n : ℕ, μ A = n := (Iff.rfl)

/-- Every finite measurable mass of an integer-valued measure is a natural number. -/
theorem IsIntegerValued.exists_eq_natCast (hμ : μ.IsIntegerValued) {A : Set X}
    (hA : MeasurableSet A) (hfin : μ A < ∞) : ∃ n : ℕ, μ A = n :=
  isIntegerValued_def.1 hμ hA hfin

/-- An integer-valued measure takes only natural-number or infinite values on measurable sets. -/
theorem isIntegerValued_iff : μ.IsIntegerValued ↔
    ∀ A : Set X, MeasurableSet A → (∃ n : ℕ, μ A = n) ∨ μ A = ∞ := by
  constructor
  · intro h A hA
    by_cases hfin : μ A = ∞
    · exact Or.inr hfin
    · exact Or.inl (h hA (lt_top_iff_ne_top.2 hfin))
  · intro h A hA hfin
    exact (h A hA).resolve_right hfin.ne

/-- A nonzero measurable mass of an integer-valued measure is at least one. -/
theorem IsIntegerValued.one_le_apply (hμ : μ.IsIntegerValued) {A : Set X}
    (hA : MeasurableSet A) (hne : μ A ≠ 0) : 1 ≤ μ A := by
  rcases isIntegerValued_iff.1 hμ A hA with ⟨n, hn⟩ | hn
  · rw [hn] at hne ⊢
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (by simpa using hne)
  · simp [hn]

/-- The zero measure is integer-valued. -/
@[simp] theorem isIntegerValued_zero : (0 : Measure X).IsIntegerValued := by
  intro A _ _
  exact ⟨0, by simp⟩

/-- A single occurrence is integer-valued, without a measurable-singleton assumption. -/
@[simp] theorem isIntegerValued_dirac (x : X) : (dirac x).IsIntegerValued := by
  classical
  intro A hA _
  by_cases hx : x ∈ A
  · exact ⟨1, by simp [dirac_apply' _ hA, hx]⟩
  · exact ⟨0, by simp [dirac_apply' _ hA, hx]⟩

/-- Superposition of two integer-valued measures retains integer multiplicities. -/
theorem IsIntegerValued.add (hμ : μ.IsIntegerValued) (hν : ν.IsIntegerValued) :
    (μ + ν).IsIntegerValued := by
  intro A hA hfin
  rw [add_apply] at hfin ⊢
  obtain ⟨m, hm⟩ := hμ hA ((le_add_right le_rfl).trans_lt hfin)
  obtain ⟨n, hn⟩ := hν hA ((le_add_left le_rfl).trans_lt hfin)
  exact ⟨m + n, by simp [hm, hn]⟩

/-- Arbitrary superpositions of integer-valued measures are integer-valued. On any measurable
set of finite total mass only finitely many summands have nonzero mass. -/
theorem IsIntegerValued.sum {μ : ι → Measure X} (hμ : ∀ i, (μ i).IsIntegerValued) :
    (Measure.sum μ).IsIntegerValued := by
  classical
  intro A hA hfin
  rw [Measure.sum_apply _ hA] at hfin ⊢
  have hi (i : ι) : μ i A < ∞ := (le_tsum (fun j => μ j A) i).trans_lt hfin
  choose n hn using fun i => hμ i hA (hi i)
  have hs : {i | μ i A ≠ 0}.Finite :=
    (ENNReal.finite_const_le_of_tsum_ne_top hfin.ne one_ne_zero).subset
      fun i hi => (hμ i).one_le_apply hA hi
  refine ⟨∑ i ∈ hs.toFinset, n i, ?_⟩
  rw [tsum_eq_sum (s := hs.toFinset) (fun i hi => by simpa using hi)]
  simp [hn]

/-- Counting measure is integer-valued even on a space without measurable singletons. -/
@[simp] theorem isIntegerValued_count : (count : Measure X).IsIntegerValued :=
  IsIntegerValued.sum fun x => isIntegerValued_dirac x

/-- Restricting to any set preserves integrality. -/
theorem IsIntegerValued.restrict (hμ : μ.IsIntegerValued) {A : Set X} :
    (μ.restrict A).IsIntegerValued := by
  intro B hB hfin
  rw [restrict_apply hB, ← measure_toMeasurable (B ∩ A)] at hfin ⊢
  exact hμ (measurableSet_toMeasurable μ (B ∩ A)) hfin

/-- Mapping preserves integrality; neither injectivity nor a local-finiteness hypothesis is
needed. Different occurrences may be mapped to the same location. For a non-a.e.-measurable
map, Mathlib's pushforward is zero or a Dirac measure, so integrality still holds. -/
theorem IsIntegerValued.map (hμ : μ.IsIntegerValued) {f : X → Y} :
    (μ.map f).IsIntegerValued := by
  by_cases hf : AEMeasurable f μ
  · intro A hA hfin
    rw [map_apply_of_aemeasurable hf hA, ← measure_toMeasurable (f ⁻¹' A)] at hfin ⊢
    exact hμ (measurableSet_toMeasurable μ (f ⁻¹' A)) hfin
  · obtain rfl | hne := eq_or_ne μ 0
    · simp
    · rw [map_of_not_aemeasurable_of_ne_zero hf hne]
      exact isIntegerValued_dirac _

/-- An atom is integer-valued exactly when its mass is a natural number or infinity. Thus
fractional atoms are excluded, while infinite atoms require a separate finiteness condition. -/
@[simp] theorem isIntegerValued_smul_dirac_iff (c : ℝ≥0∞) (x : X) :
    (c • dirac x).IsIntegerValued ↔ (∃ n : ℕ, c = n) ∨ c = ∞ := by
  classical
  constructor
  · intro h
    simpa using isIntegerValued_iff.1 h Set.univ MeasurableSet.univ
  · intro hc
    rw [isIntegerValued_iff]
    intro A hA
    by_cases hx : x ∈ A
    · simpa [smul_apply, dirac_apply' _ hA, hx] using hc
    · exact Or.inl ⟨0, by simp [smul_apply, dirac_apply' _ hA, hx]⟩

/-- Removing one occurrence preserves integer multiplicities, including absent and infinite
atoms. No local-finiteness or sigma-finiteness assumption is needed. -/
theorem IsIntegerValued.sub_dirac [MeasurableSingletonClass X] (hμ : μ.IsIntegerValued)
    (x : X) : (μ - dirac x).IsIntegerValued := by
  rw [sub_dirac_eq_restrict_add_smul]
  refine hμ.restrict.add ((isIntegerValued_smul_dirac_iff _ _).2 ?_)
  rcases isIntegerValued_iff.1 hμ {x} (measurableSet_singleton x) with ⟨n, hn⟩ | hn
  · left
    cases n with
    | zero => exact ⟨0, by simp [hn]⟩
    | succ n => exact ⟨n, by simp [hn, Nat.cast_add]⟩
  · right
    simp [hn]

end MeasureTheory.Measure

namespace Finset

open MeasureTheory

/-- Finite superpositions of integer-valued measures are integer-valued. -/
theorem isIntegerValued_sum {ι X : Type*} [MeasurableSpace X]
    (s : Finset ι) {μ : ι → Measure X} (hμ : ∀ i ∈ s, (μ i).IsIntegerValued) :
    (∑ i ∈ s, μ i).IsIntegerValued := by
  rw [← Measure.sum_coe_finset]
  exact Measure.IsIntegerValued.sum fun i => hμ i i.2

end Finset

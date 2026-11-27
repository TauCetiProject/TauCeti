/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.MeasureTheory.Measure.MeasuredSets
import Mathlib.MeasureTheory.Measure.Trim
import TauCeti.MeasureTheory.SetAlgebra

/-!
# Approximation through an increasing sequence of σ-algebras

Let `m 0 ≤ m 1 ≤ ⋯` be sub-σ-algebras of a space with a finite measure `μ`. A set measurable for
`⨆ n, m n` is approximated in measure by sets measurable for some `m n`. Consequently, when the
`m n` generate the σ-algebra modulo `μ`-null sets, every measurable label `η` into a finite type
agrees, outside a set of small measure, with a label whose fibers are measurable for some `m n`.

## Main results

* `TauCeti.exists_measurableSet_measure_symmDiff_lt_of_monotone`: a set measurable for the
  supremum of an increasing sequence of sub-σ-algebras is approximated in measure by sets
  measurable for its members.
* `TauCeti.exists_measure_ne_le_of_monotone`: a measurable finite label is approximated in
  measure by labels whose fibers are measurable for a member of an increasing sequence of
  sub-σ-algebras generating modulo null sets.
-/

public section

open MeasureTheory Filter
open scoped ENNReal symmDiff

namespace TauCeti

variable {X κ : Type*} {mX : MeasurableSpace X} {μ : Measure X}

/-- A set measurable for the supremum of an increasing sequence of sub-σ-algebras is approximated,
for a finite measure, by sets measurable for a member of the sequence: the symmetric difference has
measure less than any given `ε > 0`. -/
theorem exists_measurableSet_measure_symmDiff_lt_of_monotone [IsFiniteMeasure μ]
    {m : ℕ → MeasurableSpace X} (hm : Monotone m) (hle : ∀ n, m n ≤ mX) {s : Set X}
    (hs : MeasurableSet[⨆ n, m n] s) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ n t, MeasurableSet[m n] t ∧ μ (t ∆ s) < ε := by
  have hle' : (⨆ n, m n) ≤ mX := iSup_le hle
  obtain ⟨t, htC, ht⟩ := exists_measure_symmDiff_lt_of_generateFrom_isSetRing
    (mα := ⨆ n, m n) (μ := μ.trim hle') (isSetAlgebra_iUnion_measurableSet hm.directed_le).isSetRing
    ⟨{Set.univ}, Set.countable_singleton _,
      Set.singleton_subset_iff.2 (Set.mem_iUnion.2 ⟨0, @MeasurableSet.univ X (m 0)⟩), by simp⟩
    (MeasurableSpace.generateFrom_iUnion_measurableSet m).symm hs hε
  obtain ⟨n, hn⟩ := Set.mem_iUnion.1 htC
  have htm : MeasurableSet[⨆ n, m n] t := (le_iSup m n) _ hn
  refine ⟨n, t, hn, ?_⟩
  rwa [trim_measurableSet_eq hle' (htm.symmDiff hs)] at ht

/-- **Approximation of finite labels.** Let `m 0 ≤ m 1 ≤ ⋯` be sub-σ-algebras that generate the
σ-algebra of `X` modulo `μ`-null sets, for a finite measure `μ`. Every measurable label `η` into a
finite type is approximated by labels whose fibers are measurable for some `m n`: for `ε > 0` there
are `n` and `b` with `μ {η ≠ b} ≤ card κ * ε`. -/
theorem exists_measure_ne_le_of_monotone [IsFiniteMeasure μ] {m : ℕ → MeasurableSpace X}
    (hm : Monotone m) (hle : ∀ n, m n ≤ mX)
    (hgen : ∀ s : Set X, MeasurableSet s → ∃ t : Set X, MeasurableSet[⨆ n, m n] t ∧ s =ᵐ[μ] t)
    [Fintype κ] [MeasurableSpace κ] [MeasurableSingletonClass κ] {η : X → κ}
    (hη : Measurable η) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ (n : ℕ) (b : X → κ), (∀ i, MeasurableSet[m n] (b ⁻¹' {i})) ∧
      μ {x | η x ≠ b x} ≤ Fintype.card κ * ε := by
  classical
  rcases isEmpty_or_nonempty κ with hκ | ⟨⟨κ₀⟩⟩
  · exact ⟨0, η, fun i ↦ isEmptyElim i, by simp⟩
  -- Approximate each fiber of `η` by a set measurable for some `m n`.
  have happrox (i : κ) : ∃ n t, MeasurableSet[m n] t ∧ μ (t ∆ (η ⁻¹' {i})) < ε := by
    obtain ⟨t, ht, hst⟩ := hgen _ (hη (measurableSet_singleton i))
    obtain ⟨n, t', ht', hlt⟩ :=
      exists_measurableSet_measure_symmDiff_lt_of_monotone (μ := μ) hm hle ht hε
    exact ⟨n, t', ht', by rwa [measure_congr (ae_eq_set_symmDiff (EventuallyEqSet.refl _ _) hst)]⟩
  choose ni t ht hlt using happrox
  set n := Finset.univ.sup ni
  have htn (i : κ) : MeasurableSet[m n] (t i) := hm (Finset.le_sup (Finset.mem_univ i)) _ (ht i)
  -- The label `b` picks a fiber containing `x`; it is read off which of the sets `t i` contain `x`.
  set g : (κ → Prop) → κ := fun w ↦ if h : ∃ i, w i then h.choose else κ₀
  set v : X → (κ → Prop) := fun x i ↦ x ∈ t i
  have hv : Measurable[m n] v := @Measurable.of_eval X κ (fun _ ↦ Prop) (m n) _ v fun i ↦
    (@measurableSet_setOfPred X (m n) (· ∈ t i)).1 (htn i)
  refine ⟨n, g ∘ v, fun i ↦ hv (Set.toFinite (g ⁻¹' {i})).measurableSet, ?_⟩
  have hsub : {x | η x ≠ g (v x)} ⊆ ⋃ i, t i ∆ (η ⁻¹' {i}) := by
    intro x hx
    simp only [Set.mem_ofPred_eq, g, v] at hx
    split_ifs at hx with h
    · refine Set.mem_iUnion.2 ⟨h.choose, Or.inl ⟨h.choose_spec, ?_⟩⟩
      simpa [eq_comm] using hx
    · exact Set.mem_iUnion.2 ⟨η x, Or.inr ⟨rfl, fun hmem ↦ h ⟨η x, hmem⟩⟩⟩
  calc μ {x | η x ≠ g (v x)}
      ≤ ∑ i, μ (t i ∆ (η ⁻¹' {i})) := (measure_mono hsub).trans (measure_iUnion_fintype_le μ _)
    _ ≤ ∑ _i : κ, ε := Finset.sum_le_sum fun i _ ↦ (hlt i).le
    _ = Fintype.card κ * ε := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end TauCeti

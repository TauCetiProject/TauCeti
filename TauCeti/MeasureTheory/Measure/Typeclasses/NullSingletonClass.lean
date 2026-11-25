/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass

/-!
# Operations preserving measures with null singletons

This file records closure of `MeasureTheory.NullSingletonClass` under the zero measure, finite
addition, and scalar multiplication, characterizes when sums and scaled measures have null
singletons, shows that Dirac measures never have null singletons, and proves that a nonzero measure
vanishing outside a countable set gives positive mass to one of its points. It also proves that
removing countably many inputs changes the image of an arbitrary map only on a null set. Dually, a
map injective on a set meets a countable set at a null set of points of that set.

On a metric space any bounded set of diameter zero is a subsingleton and therefore has zero
restricted measure (`MeasureTheory.Measure.restrict_eq_zero_of_diam_eq_zero`).
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α]

/-- The zero measure assigns zero mass to every singleton. -/
instance instNullSingletonClassZero : NullSingletonClass (0 : Measure α) :=
  ⟨fun _ ↦ by simp⟩

/-- The sum of two measures with null singletons has null singletons. -/
instance instNullSingletonClassAdd {μ ν : Measure α} [NullSingletonClass μ]
    [NullSingletonClass ν] : NullSingletonClass (μ + ν) :=
  ⟨fun x ↦ by simp⟩

/-- A sum of two measures has null singletons if and only if both summands do. -/
theorem nullSingletonClass_add_iff {μ ν : Measure α} :
    NullSingletonClass (μ + ν) ↔ NullSingletonClass μ ∧ NullSingletonClass ν :=
  ⟨fun h ↦ ⟨⟨fun x ↦ (add_eq_zero.mp (by simpa using h.measure_singleton x)).1⟩,
    ⟨fun x ↦ (add_eq_zero.mp (by simpa using h.measure_singleton x)).2⟩⟩,
    fun ⟨_, _⟩ ↦ inferInstance⟩

/-- Scaling a measure with null singletons by any scalar acting through `ℝ≥0∞` preserves null
singletons, including at infinity. -/
instance instNullSingletonClassSMul {R : Type*} [SMul R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞]
    {μ : Measure α} [NullSingletonClass μ] {c : R} : NullSingletonClass (c • μ) :=
  ⟨fun x ↦ by
    rw [smul_apply, NullSingletonClass.measure_singleton,
      ← smul_one_smul ℝ≥0∞ c (0 : ℝ≥0∞), smul_zero]⟩

/-- Scaling a measure by an extended nonnegative real yields a measure with null singletons if and
only if the scalar vanishes or the original measure has null singletons. -/
theorem nullSingletonClass_smul_iff {c : ℝ≥0∞} {μ : Measure α} :
    NullSingletonClass (c • μ) ↔ c = 0 ∨ NullSingletonClass μ := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp only [zero_smul, true_or, iff_true]
    infer_instance
  · simp only [hc, false_or]
    exact ⟨fun h ↦ ⟨fun x ↦
      (mul_eq_zero.mp (by simpa using h.measure_singleton x)).resolve_left hc⟩,
      fun _ ↦ inferInstance⟩

/-- A Dirac measure never has null singletons, without any singleton-measurability assumption. -/
@[simp]
theorem not_nullSingletonClass_dirac (a : α) :
    ¬ NullSingletonClass (Measure.dirac a) := fun h ↦
  one_ne_zero ((Measure.dirac_apply_of_mem (mem_singleton a)).symm.trans (h.measure_singleton a))

/-- A scaled Dirac measure has null singletons if and only if the scalar weight vanishes. -/
@[simp]
theorem nullSingletonClass_smul_dirac_iff {c : ℝ≥0∞} {a : α} :
    NullSingletonClass (c • Measure.dirac a) ↔ c = 0 := by
  simp [nullSingletonClass_smul_iff]

end MeasureTheory

/-- A nonzero measure whose mass outside a countable set `s` vanishes gives nonzero mass to some
singleton in `s`. No singleton-measurability assumption is needed. -/
theorem Set.Countable.exists_mem_measure_singleton_ne_zero {α : Type*} {_ : MeasurableSpace α}
    {s : Set α} (hs : s.Countable) {μ : Measure α} (hμ : μ ≠ 0) (hsc : μ sᶜ = 0) :
    ∃ x ∈ s, μ {x} ≠ 0 := by
  by_contra! h0
  have hs0 : μ s = 0 := by
    rw [← biUnion_of_singleton s]
    exact (measure_biUnion_null_iff hs).mpr h0
  have huniv : μ univ = 0 := le_bot_iff.mp <|
    calc μ univ = μ (s ∪ sᶜ) := by rw [union_compl_self]
      _ ≤ μ s + μ sᶜ := measure_union_le s sᶜ
      _ = 0 := by rw [hs0, hsc, add_zero]
  exact hμ (Measure.measure_univ_eq_zero.mp huniv)

/-- Removing countably many inputs preserves an arbitrary image almost everywhere for a
measure with null singletons. -/
theorem Set.Countable.image_sdiff_ae_eq {α β : Type*} [MeasurableSpace β]
    {Z : Set α} (hZ : Z.Countable) (f : α → β) (s : Set α)
    (μ : Measure β) [NullSingletonClass μ] : f '' (s \ Z) =ᵐ[μ] f '' s := by
  refine (ae_eq_set.mpr ?_).symm
  constructor
  · apply measure_mono_null ?_ ((hZ.image f).measure_zero μ)
    rintro y ⟨⟨x, hx, rfl⟩, hn⟩
    exact ⟨x, by by_contra hne; exact hn ⟨x, ⟨hx, hne⟩, rfl⟩, rfl⟩
  · rw [sdiff_eq_empty.mpr (image_mono sdiff_subset), measure_empty]

/-- For a measure with null singletons on a metric space, a bounded set of diameter zero has zero
restricted measure. -/
theorem MeasureTheory.Measure.restrict_eq_zero_of_diam_eq_zero {α : Type*} [MetricSpace α]
    [MeasurableSpace α] {μ : Measure α} [NullSingletonClass μ] {s : Set α}
    (hs : Bornology.IsBounded s) (hd : Metric.diam s = 0) : μ.restrict s = 0 :=
  Measure.restrict_eq_zero.2 <|
    (Set.not_nontrivial_iff.1 fun hn => (Metric.diam_pos hn hs).ne' hd).measure_zero μ

/-- A map injective on `A` meets a countable set `S` at a null set of points of `A`, for a
measure with null singletons: those points form a countable set, at most one per point of `S`. -/
theorem Set.InjOn.measure_setOf_mem_eq_zero {α β : Type*} [MeasurableSpace α] {f : α → β}
    {A : Set α} (hf : InjOn f A) {S : Set β} (hS : S.Countable) {μ : Measure α}
    [NullSingletonClass μ] : μ {x ∈ A | f x ∈ S} = 0 :=
  (MapsTo.countable_of_injOn (s := {x ∈ A | f x ∈ S}) (fun _ hx => hx.2)
    (hf.mono (sep_subset A _)) hS).measure_zero μ

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Ergodic.ReturnTime

/-!
# Induced maps

For a map `T : X → X` and a set `A ⊆ X`, the first-return (induced) map
`TauCeti.inducedMap T A x = T^[positiveReturnTime T A x] x` sends a point to its first return to
`A`; where the return time is infinite it fixes the point (`ℕ∞.toNat ⊤ = 0`).

For a measure-preserving map of a finite measure space and a measurable set `A`, the induced map
preserves the restriction `μ.restrict A` (`TauCeti.measurePreserving_inducedMap`), and so the
normalized restriction `(μ A)⁻¹ • μ.restrict A`
(`TauCeti.measurePreserving_inducedMap_smul`). No invertibility is needed: the return time is
finite almost everywhere on `A` by Poincaré recurrence
(`TauCeti.ae_positiveReturnTime_ne_top`). For measurable `B ⊆ A`, splitting
`μ B = μ (T⁻¹ B)` according to whether `x ∈ A` gives

`μ B = ∑_{1 ≤ k ≤ n} μ (A ∩ {τ = k} ∩ T^[k]⁻¹ B) + μ D_n`,

where `D_n` is the set of points avoiding `A` before time `n` and lying in `B` at time `n`, that
is, first entering `A` at time `n`, inside `B`. These sets are disjoint, so `μ D_n → 0`.

## Main definitions

* `TauCeti.inducedMap T A`: the first-return map of `T` to `A`.

## Main results

* `TauCeti.inducedMap_mem`: points with finite return time return to `A`.
* `TauCeti.measurable_inducedMap`.
* `TauCeti.measure_inter_inducedMap_preimage`: `μ (A ∩ inducedMap T A ⁻¹' B) = μ B` for
  measurable `B ⊆ A`.
* `TauCeti.measurePreserving_inducedMap`, `TauCeti.measurePreserving_inducedMap_smul`.

## References

* O. Sarig, *Lecture Notes on Ergodic Theory* (author notes dated 3 April 2023), Theorem 1.7,
  p. 28.
-/

public section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace TauCeti

variable {X : Type*}

/-- The first-return (induced) map of `T` to `A`: `x ↦ T^[positiveReturnTime T A x] x`, and `x`
itself where the return time is infinite. -/
noncomputable def inducedMap (T : X → X) (A : Set X) (x : X) : X :=
  T^[(positiveReturnTime T A x).toNat] x

theorem inducedMap_def (T : X → X) (A : Set X) (x : X) :
    inducedMap T A x = T^[(positiveReturnTime T A x).toNat] x :=
  (rfl)

/-- Where the return time is a natural number `n`, the induced map is `T^[n]`. -/
theorem inducedMap_eq_iterate_of_positiveReturnTime_eq {T : X → X} {A : Set X} {x : X} {n : ℕ}
    (h : positiveReturnTime T A x = n) : inducedMap T A x = T^[n] x := by
  rw [inducedMap_def, h, ENat.toNat_natCast]

/-- Where the return time is infinite, the induced map fixes the point. -/
@[simp]
theorem inducedMap_of_eq_top {T : X → X} {A : Set X} {x : X}
    (h : positiveReturnTime T A x = ⊤) : inducedMap T A x = x := by
  simp [inducedMap_def, h]

/-- A point with finite return time is sent into `A`. -/
theorem inducedMap_mem {T : X → X} {A : Set X} {x : X} (h : positiveReturnTime T A x ≠ ⊤) :
    inducedMap T A x ∈ A :=
  iterate_toNat_positiveReturnTime_mem h

/-- **Check.** The induced map of the identity is the identity. -/
@[simp]
theorem inducedMap_id (A : Set X) : inducedMap id A = id :=
  funext fun x ↦ by simp [inducedMap_def]

variable [MeasurableSpace X]

/-- The induced map of a measurable map to a measurable set is measurable. -/
theorem measurable_inducedMap {T : X → X} (hT : Measurable T) {A : Set X} (hA : MeasurableSet A) :
    Measurable (inducedMap T A) := by
  intro S hS
  have hτ : Measurable fun x ↦ (positiveReturnTime T A x).toNat :=
    measurable_from_top.comp (measurable_positiveReturnTime hT hA)
  have : inducedMap T A ⁻¹' S =
      ⋃ n : ℕ, (fun x ↦ (positiveReturnTime T A x).toNat) ⁻¹' {n} ∩ T^[n] ⁻¹' S := by
    ext x
    simp [inducedMap_def]
  rw [this]
  exact .iUnion fun n ↦ (hτ (measurableSet_singleton n)).inter (hT.iterate n hS)

variable {μ : Measure X}

section Core

variable {T : X → X} {A B : Set X}

/-- The points avoiding `A` before time `n` and lying in `B` at time `n`: `T^[i] x ∉ A` for
`i < n` and `T^[n] x ∈ B`. When `B ⊆ A`, these are the points first entering `A` at time `n`,
inside `B`. -/
def firstEntrySet (T : X → X) (A B : Set X) (n : ℕ) : Set X :=
  {x | (∀ i < n, T^[i] x ∉ A) ∧ T^[n] x ∈ B}

/-- The points of `A` returning first at time `n + 1`, into `B`. -/
def returnSet (T : X → X) (A B : Set X) (n : ℕ) : Set X :=
  A ∩ {x | positiveReturnTime T A x = (n + 1 : ℕ)} ∩ T^[n + 1] ⁻¹' B

omit [MeasurableSpace X] in
theorem firstEntrySet_def (T : X → X) (A B : Set X) (n : ℕ) :
    firstEntrySet T A B n = {x | (∀ i < n, T^[i] x ∉ A) ∧ T^[n] x ∈ B} :=
  (rfl)

omit [MeasurableSpace X] in
theorem returnSet_def (T : X → X) (A B : Set X) (n : ℕ) :
    returnSet T A B n =
      A ∩ {x | positiveReturnTime T A x = (n + 1 : ℕ)} ∩ T^[n + 1] ⁻¹' B :=
  (rfl)

omit [MeasurableSpace X] in
@[simp]
theorem mem_firstEntrySet_iff {n : ℕ} {x : X} :
    x ∈ firstEntrySet T A B n ↔ (∀ i < n, T^[i] x ∉ A) ∧ T^[n] x ∈ B :=
  Iff.rfl

omit [MeasurableSpace X] in
@[simp]
theorem mem_returnSet_iff {n : ℕ} {x : X} :
    x ∈ returnSet T A B n ↔
      (x ∈ A ∧ positiveReturnTime T A x = (n + 1 : ℕ)) ∧ T^[n + 1] x ∈ B :=
  Iff.rfl

theorem measurableSet_firstEntrySet (hT : Measurable T) (hA : MeasurableSet A)
    (hB : MeasurableSet B) (n : ℕ) : MeasurableSet (firstEntrySet T A B n) := by
  have : firstEntrySet T A B n = (⋂ i ∈ Finset.range n, T^[i] ⁻¹' Aᶜ) ∩ T^[n] ⁻¹' B := by
    ext x
    simp
  rw [this]
  exact (Finset.measurableSet_biInter _ fun i _ ↦ hT.iterate i hA.compl).inter (hT.iterate n hB)

theorem measurableSet_returnSet (hT : Measurable T) (hA : MeasurableSet A)
    (hB : MeasurableSet B) (n : ℕ) : MeasurableSet (returnSet T A B n) :=
  (hA.inter (measurable_positiveReturnTime hT hA (measurableSet_singleton _))).inter
    (hT.iterate _ hB)

omit [MeasurableSpace X] in
/-- Splitting `T⁻¹ (firstEntrySet n)` according to `A`: the part in `A` is `returnSet n`. -/
theorem preimage_firstEntrySet_inter (hBA : B ⊆ A) (n : ℕ) :
    T ⁻¹' firstEntrySet T A B n ∩ A = returnSet T A B n := by
  ext x
  simp only [mem_inter_iff, mem_preimage, mem_firstEntrySet_iff, mem_returnSet_iff,
    ← Function.iterate_succ_apply]
  rw [positiveReturnTime_eq_coe_iff (Nat.succ_pos n)]
  constructor
  · rintro ⟨⟨h, hB⟩, hx⟩
    refine ⟨⟨hx, hBA hB, fun i hi hin ↦ ?_⟩, hB⟩
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hi.ne'
    exact h j (by omega)
  · rintro ⟨⟨hx, -, h⟩, hB⟩
    exact ⟨⟨fun i hi ↦ h (i + 1) (by omega) (by omega), hB⟩, hx⟩

omit [MeasurableSpace X] in
/-- Splitting `T⁻¹ (firstEntrySet n)` according to `A`: the part outside `A` is
`firstEntrySet (n + 1)`. -/
theorem preimage_firstEntrySet_diff (n : ℕ) :
    T ⁻¹' firstEntrySet T A B n \ A = firstEntrySet T A B (n + 1) := by
  ext x
  simp only [Set.mem_sdiff, mem_preimage, mem_firstEntrySet_iff]
  constructor
  · rintro ⟨⟨h, hB⟩, hx⟩
    refine ⟨fun i hi ↦ ?_, hB⟩
    rcases i with _ | i
    · exact hx
    · exact h i (by omega)
  · rintro ⟨h, hB⟩
    exact ⟨⟨fun i hi ↦ h (i + 1) (by omega), hB⟩, h 0 (by omega)⟩

omit [MeasurableSpace X] in
/-- The first-entry sets into `B ⊆ A` at different times are disjoint. -/
theorem pairwise_disjoint_firstEntrySet (hBA : B ⊆ A) :
    Pairwise (Function.onFun Disjoint (firstEntrySet T A B)) := by
  intro m n hmn
  refine Set.disjoint_left.2 fun x hm hn ↦ ?_
  rcases hmn.lt_or_gt with h | h
  · exact hn.1 m h (hBA hm.2)
  · exact hm.1 n h (hBA hn.2)

omit [MeasurableSpace X] in
/-- The return sets at different times are disjoint. -/
theorem pairwise_disjoint_returnSet : Pairwise (Function.onFun Disjoint (returnSet T A B)) := by
  intro m n hmn
  refine Set.disjoint_left.2 fun x hm hn ↦ hmn ?_
  rw [mem_returnSet_iff] at hm hn
  have := ENat.natCast_inj.1 (hm.1.2.symm.trans hn.1.2)
  omega

/-- `μ B = ∑_{k < n} μ (returnSet k) + μ (firstEntrySet n)`. -/
theorem measure_eq_sum_returnSet_add (hT : MeasurePreserving T μ μ) (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hBA : B ⊆ A) (n : ℕ) :
    μ B = ∑ k ∈ Finset.range n, μ (returnSet T A B k) + μ (firstEntrySet T A B n) := by
  induction n with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, zero_add]
    congr 1
    ext x
    simp
  | succ n ih =>
    rw [ih, Finset.sum_range_succ, add_assoc, ← hT.measure_preimage
      (measurableSet_firstEntrySet hT.measurable hA hB n).nullMeasurableSet,
      ← measure_inter_add_sdiff _ hA, preimage_firstEntrySet_inter hBA,
      preimage_firstEntrySet_diff]

/-- `μ B` is the sum of the measures of the return sets. -/
theorem measure_eq_tsum_returnSet [IsFiniteMeasure μ] (hT : MeasurePreserving T μ μ)
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hBA : B ⊆ A) :
    μ B = ∑' k, μ (returnSet T A B k) := by
  have hE : Tendsto (fun n ↦ μ (firstEntrySet T A B n)) atTop (𝓝 0) := by
    refine ENNReal.tendsto_atTop_zero_of_tsum_ne_top ?_
    rw [← measure_iUnion (pairwise_disjoint_firstEntrySet hBA)
      (measurableSet_firstEntrySet hT.measurable hA hB)]
    exact measure_ne_top _ _
  have h := (ENNReal.tendsto_nat_tsum fun k ↦ μ (returnSet T A B k)).add hE
  rw [add_zero] at h
  exact tendsto_nhds_unique (tendsto_const_nhds.congr
    (measure_eq_sum_returnSet_add hT hA hB hBA)) h

/-- For measurable `B ⊆ A`, `μ (A ∩ inducedMap T A ⁻¹' B) = μ B`. -/
theorem measure_inter_inducedMap_preimage [IsFiniteMeasure μ] (hT : MeasurePreserving T μ μ)
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hBA : B ⊆ A) :
    μ (A ∩ inducedMap T A ⁻¹' B) = μ B := by
  rw [measure_eq_tsum_returnSet hT hA hB hBA, ← measure_iUnion pairwise_disjoint_returnSet
    (measurableSet_returnSet hT.measurable hA hB)]
  refine measure_congr (eventuallyEqSet_iff.2 ?_)
  filter_upwards [ae_positiveReturnTime_ne_top hT.conservative hA.nullMeasurableSet] with x hx
  simp only [mem_iUnion, mem_returnSet_iff, mem_inter_iff, mem_preimage]
  constructor
  · rintro ⟨hxA, hxB⟩
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 (hx hxA)
    have hm0 : m ≠ 0 := by
      rintro rfl
      exact positiveReturnTime_ne_zero T A x (by simpa using hm.symm)
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hm0
    refine ⟨k, ⟨hxA, hm.symm⟩, ?_⟩
    rwa [inducedMap_eq_iterate_of_positiveReturnTime_eq hm.symm] at hxB
  · rintro ⟨k, ⟨hxA, hk⟩, hxB⟩
    exact ⟨hxA, by rwa [inducedMap_eq_iterate_of_positiveReturnTime_eq hk]⟩

end Core

/-- **The induced map preserves the restricted measure.** For a measure-preserving map of a
finite measure space and a measurable set `A`, the induced map preserves `μ.restrict A`. -/
theorem measurePreserving_inducedMap [IsFiniteMeasure μ] {T : X → X}
    (hT : MeasurePreserving T μ μ) {A : Set X} (hA : MeasurableSet A) :
    MeasurePreserving (inducedMap T A) (μ.restrict A) (μ.restrict A) where
  measurable := measurable_inducedMap hT.measurable hA
  map_eq := by
    ext S hS
    rw [Measure.map_apply (measurable_inducedMap hT.measurable hA) hS,
      Measure.restrict_apply (measurable_inducedMap hT.measurable hA hS),
      Measure.restrict_apply hS, ← measure_inter_inducedMap_preimage hT hA (hS.inter hA)
        inter_subset_right]
    refine measure_congr (eventuallyEqSet_iff.2 ?_)
    filter_upwards [ae_positiveReturnTime_ne_top hT.conservative hA.nullMeasurableSet] with x hx
    simp only [mem_inter_iff, mem_preimage]
    exact ⟨fun h ↦ ⟨h.2, h.1, inducedMap_mem (hx h.2)⟩, fun h ↦ ⟨h.2.1, h.1⟩⟩

/-- The induced map preserves the normalized restriction `(μ A)⁻¹ • μ.restrict A`. -/
theorem measurePreserving_inducedMap_smul [IsFiniteMeasure μ] {T : X → X}
    (hT : MeasurePreserving T μ μ) {A : Set X} (hA : MeasurableSet A) :
    MeasurePreserving (inducedMap T A) ((μ A)⁻¹ • μ.restrict A) ((μ A)⁻¹ • μ.restrict A) :=
  (measurePreserving_inducedMap hT hA).smul_measure _

end TauCeti

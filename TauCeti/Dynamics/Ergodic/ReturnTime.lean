/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.Ergodic.Ergodic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Instances
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Return times and Kac's lemma

For a map `T : X → X` and a set `A ⊆ X`, the positive return time
`TauCeti.positiveReturnTime T A x : ℕ∞` is the least `n ≥ 1` with `T^[n] x ∈ A`, and `∞` if there
is none. It is measurable for measurable `T` and `A`.

**Kac's lemma** (`TauCeti.kac_return_time_integral`): for an ergodic measurable equivalence `T` of
a probability space and a measurable set `A` of positive measure, the return time is finite
almost everywhere on `A`, it is integrable on `A`, and `∫ x in A, positiveReturnTime T A x dμ = 1`.
Thus the mean return time for the conditional probability on `A` is `1 / μ A`.

The proof computes the extended integral. Layer by layer,
`∫⁻ x in A, positiveReturnTime T A x ∂μ = ∑ k, μ (A ∩ {k < positiveReturnTime T A})`, and `T^[k]`
carries `A ∩ {k < positiveReturnTime T A}` onto the set `C k` of points whose last visit to `A`
in backward time happened exactly `k` steps ago. These sets are disjoint, and their union, the set
of points whose backward orbit meets `A`, is invariant up to inclusion and contains `A`, so it is
conull by ergodicity. Finiteness of the integral then gives finiteness of the return time almost
everywhere on `A`.

## Main results

* `TauCeti.lt_positiveReturnTime_iff`: `k < positiveReturnTime T A x` iff `T^[i] x ∉ A` for
  `1 ≤ i ≤ k`.
* `TauCeti.measurable_positiveReturnTime`.
* `TauCeti.lintegral_positiveReturnTime_eq_tsum`: the layer-cake formula for the return time.
* `TauCeti.lt_positiveReturnTime_inter_eq_preimage`: the sets of points of `A` with return time
  greater than `k` are carried by `T^[k]` onto the sets of last backward visits.
* `TauCeti.lintegral_positiveReturnTime`: `∫⁻ x in A, positiveReturnTime T A x ∂μ = 1`.
* `TauCeti.kac_return_time_integral`: Kac's lemma.

## References

* M. Hochman, *Notes on ergodic theory*, 5 July 2017, §3.3, Theorem 3.3.1 and proof, printed
  pp. 18–19.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace TauCeti

variable {X : Type*}

open Classical in
/-- The positive return time of `x` to `A` under `T`: the least `n ≥ 1` with `T^[n] x ∈ A`, and
`∞` if there is no such `n`. -/
noncomputable def positiveReturnTime (T : X → X) (A : Set X) (x : X) : ℕ∞ :=
  if h : ∃ n, 0 < n ∧ T^[n] x ∈ A then (Nat.find h : ℕ∞) else ⊤

/-- The return time exceeds `k` exactly when the orbit avoids `A` at the times `1, …, k`. -/
theorem lt_positiveReturnTime_iff {T : X → X} {A : Set X} {x : X} {k : ℕ} :
    (k : ℕ∞) < positiveReturnTime T A x ↔ ∀ i, 0 < i → i ≤ k → T^[i] x ∉ A := by
  classical
  unfold positiveReturnTime
  split_ifs with h
  · rw [Nat.cast_lt, Nat.lt_find_iff]
    exact ⟨fun H i hi hik hA ↦ H i hik ⟨hi, hA⟩, fun H i hik hi ↦ H i hi.1 hik hi.2⟩
  · push Not at h
    simpa using fun i hi _ ↦ h i hi

/-- The return time is at most `n ≥ 1` when the orbit visits `A` at time `n`. -/
theorem positiveReturnTime_le {T : X → X} {A : Set X} {x : X} {n : ℕ} (hn : 0 < n)
    (hx : T^[n] x ∈ A) : positiveReturnTime T A x ≤ n :=
  not_lt.1 fun h ↦ lt_positiveReturnTime_iff.1 h n hn le_rfl hx

/-- The return time is `n ≥ 1` exactly when the orbit visits `A` at time `n` and not before. -/
theorem positiveReturnTime_eq_coe_iff {T : X → X} {A : Set X} {x : X} {n : ℕ} (hn : 0 < n) :
    positiveReturnTime T A x = n ↔ T^[n] x ∈ A ∧ ∀ i, 0 < i → i < n → T^[i] x ∉ A := by
  classical
  unfold positiveReturnTime
  split_ifs with h
  · rw [Nat.cast_inj, Nat.find_eq_iff]
    exact ⟨fun ⟨⟨_, hA⟩, H⟩ ↦ ⟨hA, fun i hi hin hiA ↦ H i hin ⟨hi, hiA⟩⟩,
      fun ⟨hA, H⟩ ↦ ⟨⟨hn, hA⟩, fun i hin ⟨hi, hiA⟩ ↦ H i hi hin hiA⟩⟩
  · simp only [ENat.top_ne_natCast, false_iff, not_and]
    exact fun hA _ ↦ h ⟨n, hn, hA⟩

/-- The return time is `∞` exactly when the orbit never returns to `A`. -/
theorem positiveReturnTime_eq_top_iff {T : X → X} {A : Set X} {x : X} :
    positiveReturnTime T A x = ⊤ ↔ ∀ n, 0 < n → T^[n] x ∉ A := by
  refine ⟨fun h n hn hx ↦ ?_, fun h ↦ ?_⟩
  · exact absurd (h ▸ positiveReturnTime_le hn hx) (by simp)
  · classical
    unfold positiveReturnTime
    split_ifs with h'
    · obtain ⟨n, hn, hx⟩ := h'
      exact absurd hx (h n hn)
    · rfl

variable [MeasurableSpace X]

/-- For measurable `T` and `A`, the set where the return time exceeds `k` is measurable. -/
theorem measurableSet_lt_positiveReturnTime {T : X → X} (hT : Measurable T) {A : Set X}
    (hA : MeasurableSet A) (k : ℕ) :
    MeasurableSet {x | (k : ℕ∞) < positiveReturnTime T A x} := by
  have : {x | (k : ℕ∞) < positiveReturnTime T A x} = ⋂ i ∈ Finset.Icc 1 k, T^[i] ⁻¹' Aᶜ := by
    ext x
    simp only [mem_ofPred_eq, lt_positiveReturnTime_iff, Finset.mem_Icc, mem_iInter, mem_preimage,
      mem_compl_iff]
    exact ⟨fun h i hi ↦ h i hi.1 hi.2, fun h i hi hik ↦ h i ⟨hi, hik⟩⟩
  rw [this]
  exact Finset.measurableSet_biInter _ fun i _ ↦ (hT.iterate i) hA.compl

/-- The positive return time to a measurable set under a measurable map is measurable. -/
theorem measurable_positiveReturnTime {T : X → X} (hT : Measurable T) {A : Set X}
    (hA : MeasurableSet A) : Measurable (positiveReturnTime T A) := by
  have hlt := measurableSet_lt_positiveReturnTime hT hA
  refine measurable_to_countable' fun v ↦ ?_
  induction v using ENat.recTopCoe with
  | top =>
    have : positiveReturnTime T A ⁻¹' {⊤} = ⋂ k : ℕ, {x | (k : ℕ∞) < positiveReturnTime T A x} := by
      ext x
      simp only [mem_preimage, mem_singleton_iff, mem_iInter, mem_ofPred_eq]
      refine ⟨fun h k ↦ h ▸ ENat.natCast_lt_top k, fun h ↦ ?_⟩
      induction h' : positiveReturnTime T A x using ENat.recTopCoe with
      | top => rfl
      | coe n => exact absurd (h n) (by simp [h'])
    rw [this]
    exact MeasurableSet.iInter hlt
  | coe n =>
    have : positiveReturnTime T A ⁻¹' {(n : ℕ∞)} =
        {x | (n : ℕ∞) < positiveReturnTime T A x}ᶜ ∩
          ⋂ k ∈ Finset.range n, {x | (k : ℕ∞) < positiveReturnTime T A x} := by
      ext x
      simp only [mem_preimage, mem_singleton_iff, mem_inter_iff, mem_compl_iff, mem_ofPred_eq,
        mem_iInter, Finset.mem_range]
      refine ⟨fun h ↦ ⟨by simp [h], fun k hk ↦ by simpa [h] using hk⟩, fun ⟨h₁, h₂⟩ ↦ ?_⟩
      refine le_antisymm (not_lt.1 h₁) ?_
      rcases n with _ | m
      · exact zero_le
      · exact (Order.add_one_le_of_lt (h₂ m (Nat.lt_succ_self m))).trans_eq' (by push_cast; rfl)
    rw [this]
    exact (hlt n).compl.inter (Finset.measurableSet_biInter _ fun k _ ↦ hlt k)

/-- An element of `ℕ∞` is the sum over `k : ℕ` of the indicators of `k < v`. -/
private theorem toENNReal_eq_tsum_ite (v : ℕ∞) :
    (v : ℝ≥0∞) = ∑' k : ℕ, if (k : ℕ∞) < v then 1 else 0 := by
  induction v using ENat.recTopCoe with
  | top => simp
  | coe n =>
    rw [tsum_eq_sum (s := Finset.range n) fun k hk ↦ by simp_all]
    rw [Finset.sum_congr rfl (g := fun _ ↦ (1 : ℝ≥0∞)) fun k hk ↦ by
      simp only [Finset.mem_range] at hk; simp [hk]]
    simp

variable {μ : Measure X}

/-- **Layer-cake formula.** For measurable `T` and `A`, the extended integral of the return time
over `A` is `∑ k, μ ({k < positiveReturnTime T A} ∩ A)`. -/
theorem lintegral_positiveReturnTime_eq_tsum {T : X → X} (hT : Measurable T) {A : Set X}
    (hA : MeasurableSet A) :
    ∫⁻ x in A, (positiveReturnTime T A x : ℝ≥0∞) ∂μ =
      ∑' k : ℕ, μ ({x | (k : ℕ∞) < positiveReturnTime T A x} ∩ A) := by
  have hS := measurableSet_lt_positiveReturnTime hT hA
  simp_rw [toENNReal_eq_tsum_ite]
  rw [lintegral_tsum fun k ↦
    (Measurable.ite (hS k) measurable_const measurable_const).aemeasurable]
  refine tsum_congr fun k ↦ ?_
  rw [← Measure.restrict_apply (hS k), ← lintegral_indicator_one (hS k)]
  refine lintegral_congr fun x ↦ ?_
  simp [Set.indicator_apply]

/-- For a measurable equivalence `T`, `T^[k]` maps the points of `A` whose return time exceeds `k`
onto the points whose backward orbit visits `A` for the last time `k` steps ago: the first set is
the preimage of the second. -/
theorem lt_positiveReturnTime_inter_eq_preimage (T : X ≃ᵐ X) (A : Set X) (k : ℕ) :
    {x | (k : ℕ∞) < positiveReturnTime T A x} ∩ A =
      T^[k] ⁻¹' {y | T.symm^[k] y ∈ A ∧ ∀ j < k, T.symm^[j] y ∉ A} := by
  have hsymm (j : ℕ) (hjk : j ≤ k) (x : X) : T.symm^[j] (T^[k] x) = T^[k - j] x := by
    conv_lhs => rw [← Nat.add_sub_cancel' hjk, Function.iterate_add_apply]
    exact (Function.LeftInverse.iterate T.symm_apply_apply j) _
  ext x
  simp only [mem_inter_iff, mem_ofPred_eq, mem_preimage, lt_positiveReturnTime_iff,
    hsymm k le_rfl, Nat.sub_self, Function.iterate_zero_apply]
  refine ⟨fun ⟨h, hx⟩ ↦ ⟨hx, fun j hj ↦ ?_⟩, fun ⟨hx, h⟩ ↦ ⟨fun i hi hik ↦ ?_, hx⟩⟩
  · rw [hsymm j hj.le]
    exact h _ (Nat.sub_pos_of_lt hj) (Nat.sub_le k j)
  · have := h (k - i) (Nat.sub_lt (hi.trans_le hik) hi)
    rwa [hsymm _ (Nat.sub_le k i), Nat.sub_sub_self hik] at this

/-- The extended integral of the return time over `A` for an ergodic measurable equivalence of a
probability space, `A` measurable of positive measure, is `1`. -/
theorem lintegral_positiveReturnTime [IsProbabilityMeasure μ] {T : X ≃ᵐ X} (hT : Ergodic T μ)
    {A : Set X} (hA : MeasurableSet A) (hμA : μ A ≠ 0) :
    ∫⁻ x in A, (positiveReturnTime T A x : ℝ≥0∞) ∂μ = 1 := by
  -- Points whose last visit to `A` in backward time was exactly `k` steps ago.
  set C : ℕ → Set X := fun k ↦ {y | T.symm^[k] y ∈ A ∧ ∀ j < k, T.symm^[j] y ∉ A}
  have hC (k : ℕ) : MeasurableSet (C k) := by
    have : C k = T.symm^[k] ⁻¹' A ∩ ⋂ j ∈ Finset.range k, T.symm^[j] ⁻¹' Aᶜ := by
      ext y
      simp [C]
    rw [this]
    exact (T.symm.measurable.iterate k hA).inter
      (Finset.measurableSet_biInter _ fun j _ ↦ T.symm.measurable.iterate j hA.compl)
  have hmeas (k : ℕ) : μ ({x | (k : ℕ∞) < positiveReturnTime T A x} ∩ A) = μ (C k) := by
    rw [lt_positiveReturnTime_inter_eq_preimage]
    exact (hT.toMeasurePreserving.iterate k).measure_preimage (hC k).nullMeasurableSet
  have hdisj : Pairwise (Function.onFun Disjoint C) := by
    intro k k' hkk'
    rcases lt_or_gt_of_ne hkk' with h | h
    · exact Set.disjoint_left.2 fun y hy hy' ↦ hy'.2 k h hy.1
    · exact Set.disjoint_left.2 fun y hy hy' ↦ hy.2 k' h hy'.1
  -- The union of the `C k` is the set of points whose backward orbit meets `A`.
  set B : Set X := {y | ∃ j, T.symm^[j] y ∈ A}
  have hunion : (⋃ k, C k) = B := by
    classical
    ext y
    refine ⟨fun hy ↦ ?_, fun ⟨j, hj⟩ ↦ ?_⟩
    · obtain ⟨k, hk⟩ := mem_iUnion.1 hy
      exact ⟨k, hk.1⟩
    · have h : ∃ j, T.symm^[j] y ∈ A := ⟨j, hj⟩
      exact mem_iUnion.2 ⟨Nat.find h, Nat.find_spec h, fun j hj ↦ Nat.find_min h hj⟩
  have hB : MeasurableSet B := hunion ▸ MeasurableSet.iUnion hC
  have hBsub : B ⊆ T ⁻¹' B := fun y ⟨j, hj⟩ ↦
    ⟨j + 1, by rwa [Function.iterate_succ_apply, T.symm_apply_apply]⟩
  have hB1 : μ B = 1 := by
    rcases hT.ae_empty_or_univ_of_ae_le_preimage hB.nullMeasurableSet
      (LE.le.eventuallySubset hBsub) with h | h
    · have h0 : μ B = 0 := by rw [measure_congr h, measure_empty]
      exact absurd (measure_mono_null (fun x hx ↦ (⟨0, hx⟩ : x ∈ B)) h0) hμA
    · rw [measure_congr h, measure_univ]
  rw [lintegral_positiveReturnTime_eq_tsum T.measurable hA, tsum_congr hmeas,
    ← measure_iUnion hdisj hC, hunion, hB1]

/-- **Kac's lemma.** Let `T` be an ergodic measurable equivalence of a probability space and `A` a
measurable set of positive measure. Then the positive return time to `A` is finite almost
everywhere on `A`, its value is integrable on `A`, and its integral over `A` is `1`. -/
theorem kac_return_time_integral [IsProbabilityMeasure μ] {T : X ≃ᵐ X} (hT : Ergodic T μ)
    {A : Set X} (hA : MeasurableSet A) (hμA : 0 < μ A) :
    (∀ᵐ x ∂μ.restrict A, positiveReturnTime T A x ≠ ⊤) ∧
      Integrable (fun x ↦ ((positiveReturnTime T A x).toNat : ℝ)) (μ.restrict A) ∧
        ∫ x in A, ((positiveReturnTime T A x).toNat : ℝ) ∂μ = 1 := by
  have hint := lintegral_positiveReturnTime hT hA hμA.ne'
  have hm : Measurable fun x ↦ (positiveReturnTime T A x : ℝ≥0∞) :=
    (measurable_of_countable _).comp (measurable_positiveReturnTime T.measurable hA)
  have hfin : ∀ᵐ x ∂μ.restrict A, (positiveReturnTime T A x : ℝ≥0∞) < ∞ :=
    ae_lt_top hm (by simp [hint])
  have htoReal (v : ℕ∞) : ((v : ℝ≥0∞)).toReal = (v.toNat : ℝ) := by
    induction v using ENat.recTopCoe <;> simp
  simp_rw [← htoReal]
  refine ⟨hfin.mono fun x hx ↦ by simpa using hx.ne, integrable_toReal_of_lintegral_ne_top
    hm.aemeasurable (by simp [hint]), ?_⟩
  rw [integral_toReal hm.aemeasurable hfin, hint, ENNReal.toReal_one]

end TauCeti

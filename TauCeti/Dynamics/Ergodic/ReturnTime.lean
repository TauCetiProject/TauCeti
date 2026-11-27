/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.Ergodic.Ergodic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Instances
public import Mathlib.Probability.Process.HittingTime
import TauCeti.Data.ENat.ENNReal

/-!
# Return times and Kac's lemma

For a map `T : X → X` and a set `A ⊆ X`, the positive return time
`TauCeti.positiveReturnTime T A x : ℕ∞` is the least `n ≥ 1` with `T^[n] x ∈ A`, and `∞` if there
is none. It is Mathlib's hitting time `MeasureTheory.hittingAfter` of the orbit process
`n ↦ T^[n]` after time `1`, and it is measurable for measurable `T` and `A`.

**Kac's lemma** (`TauCeti.kac_return_time_integral`): for an ergodic measurable equivalence `T` of
a probability space and a measurable set `A` of positive measure, the return time is finite
almost everywhere on `A`, it is integrable on `A`, and `∫ x in A, positiveReturnTime T A x dμ = 1`.
Thus the mean return time for the conditional probability on `A` is `1 / μ A`.

For a measure-preserving equivalence alone, `TauCeti.lintegral_positiveReturnTime_eq_measure`
computes the extended integral of the return time over `A` as the measure of the set of points
whose backward orbit meets `A`; ergodicity makes this set conull.

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
* `TauCeti.lintegral_positiveReturnTime_eq_measure`: for a measure-preserving equivalence,
  `∫⁻ x in A, positiveReturnTime T A x ∂μ = μ {y | ∃ j, T.symm^[j] y ∈ A}`.
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

/-- The positive return time of `x` to `A` under `T`: the least `n ≥ 1` with `T^[n] x ∈ A`, and
`∞` if there is no such `n`. This is Mathlib's hitting time of the orbit process after time `1`
(`positiveReturnTime_eq_hittingAfter`). The type `ℕ∞` is by definition `WithTop ℕ`, the value
type of `hittingAfter`, and its order, `1`, `⊤` and casts from `ℕ` are definitionally those of
`WithTop ℕ`; the lemmas below use this to state the `hittingAfter` API in `ℕ∞`. -/
noncomputable def positiveReturnTime (T : X → X) (A : Set X) : X → ℕ∞ :=
  hittingAfter (fun n x ↦ T^[n] x) A 1

/-- The positive return time is Mathlib's hitting time of the orbit process after time `1`. -/
theorem positiveReturnTime_eq_hittingAfter (T : X → X) (A : Set X) :
    positiveReturnTime T A = hittingAfter (fun n x ↦ T^[n] x) A 1 :=
  (rfl)

/-- The return time is at most `k` exactly when the orbit visits `A` at some time in `[1, k]`. -/
theorem positiveReturnTime_le_iff {T : X → X} {A : Set X} {x : X} {k : ℕ} :
    positiveReturnTime T A x ≤ k ↔ ∃ i ∈ Icc 1 k, T^[i] x ∈ A := by
  rw [positiveReturnTime_eq_hittingAfter]
  exact hittingAfter_le_iff

/-- The return time is `≥ 1`: time `0` does not count as a return. -/
theorem one_le_positiveReturnTime (T : X → X) (A : Set X) (x : X) :
    1 ≤ positiveReturnTime T A x := by
  rw [positiveReturnTime_eq_hittingAfter]
  exact le_hittingAfter x

/-- The return time is never `0`. -/
@[simp]
theorem positiveReturnTime_ne_zero (T : X → X) (A : Set X) (x : X) :
    positiveReturnTime T A x ≠ 0 :=
  (zero_lt_one.trans_le (one_le_positiveReturnTime T A x)).ne'

/-- The return time exceeds `k` exactly when the orbit avoids `A` at the times `1, …, k`. -/
theorem lt_positiveReturnTime_iff {T : X → X} {A : Set X} {x : X} {k : ℕ} :
    (k : ℕ∞) < positiveReturnTime T A x ↔ ∀ i, 0 < i → i ≤ k → T^[i] x ∉ A := by
  rw [← not_le, positiveReturnTime_le_iff]
  simp [Nat.one_le_iff_ne_zero, Nat.pos_iff_ne_zero]

/-- The return time is at most `n ≥ 1` when the orbit visits `A` at time `n`. -/
theorem positiveReturnTime_le {T : X → X} {A : Set X} {x : X} {n : ℕ} (hn : 0 < n)
    (hx : T^[n] x ∈ A) : positiveReturnTime T A x ≤ n := by
  rw [positiveReturnTime_eq_hittingAfter]
  exact hittingAfter_le_of_mem (by omega) hx

/-- The return time is `n ≥ 1` exactly when the orbit visits `A` at time `n` and not before. -/
theorem positiveReturnTime_eq_coe_iff {T : X → X} {A : Set X} {x : X} {n : ℕ} (hn : 0 < n) :
    positiveReturnTime T A x = n ↔ T^[n] x ∈ A ∧ ∀ i, 0 < i → i < n → T^[i] x ∉ A := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hn.ne'
  rw [le_antisymm_iff, positiveReturnTime_le_iff, Nat.cast_succ,
    ENat.add_one_le_iff (ENat.natCast_ne_top m), lt_positiveReturnTime_iff]
  constructor
  · rintro ⟨⟨j, ⟨hj1, hjm⟩, hj⟩, h⟩
    obtain rfl | hjm := hjm.eq_or_lt
    · exact ⟨hj, fun i hi him ↦ h i hi (by omega)⟩
    · exact absurd hj (h j (by omega) (by omega))
  · rintro ⟨hA, h⟩
    exact ⟨⟨m + 1, ⟨by omega, le_rfl⟩, hA⟩, fun i hi him ↦ h i hi (by omega)⟩

/-- The return time is `∞` exactly when the orbit never returns to `A`. -/
theorem positiveReturnTime_eq_top_iff {T : X → X} {A : Set X} {x : X} :
    positiveReturnTime T A x = ⊤ ↔ ∀ n, 0 < n → T^[n] x ∉ A := by
  rw [positiveReturnTime_eq_hittingAfter]
  exact hittingAfter_eq_top_iff.trans <| forall_congr' fun n ↦ by
    rw [Nat.one_le_iff_ne_zero, Nat.pos_iff_ne_zero]

/-- The return time is finite exactly when the orbit returns to `A`. -/
theorem positiveReturnTime_ne_top_iff {T : X → X} {A : Set X} {x : X} :
    positiveReturnTime T A x ≠ ⊤ ↔ ∃ n, 0 < n ∧ T^[n] x ∈ A := by
  simp [positiveReturnTime_eq_top_iff]

/-- At a finite return time, the orbit is in `A`. -/
theorem iterate_toNat_positiveReturnTime_mem {T : X → X} {A : Set X} {x : X}
    (h : positiveReturnTime T A x ≠ ⊤) : T^[(positiveReturnTime T A x).toNat] x ∈ A := by
  have hmem := hittingAfter_mem_set_of_ne_top (u := fun n x ↦ T^[n] x) (s := A) (n := 1) h
  rw [← positiveReturnTime_eq_hittingAfter] at hmem
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 h
  simpa [← hn] using hmem

/-- For maps `f` and `g` with `g ∘ f = id`, `f^[k]` maps the points of `A` whose return time under
`f` exceeds `k` onto the points whose backward orbit under `g` visits `A` for the last time `k`
steps ago: the first set is the preimage of the second. -/
theorem lt_positiveReturnTime_inter_eq_preimage {f g : X → X} (hgf : Function.LeftInverse g f)
    (A : Set X) (k : ℕ) :
    {x | (k : ℕ∞) < positiveReturnTime f A x} ∩ A =
      f^[k] ⁻¹' {y | g^[k] y ∈ A ∧ ∀ j < k, g^[j] y ∉ A} := by
  have hsymm (j : ℕ) (hjk : j ≤ k) (x : X) : g^[j] (f^[k] x) = f^[k - j] x := by
    conv_lhs => rw [← Nat.add_sub_cancel' hjk, Function.iterate_add_apply]
    exact (hgf.iterate j) _
  ext x
  simp only [mem_inter_iff, mem_ofPred_eq, mem_preimage, lt_positiveReturnTime_iff,
    hsymm k le_rfl, Nat.sub_self, Function.iterate_zero_apply]
  refine ⟨fun ⟨h, hx⟩ ↦ ⟨hx, fun j hj ↦ ?_⟩, fun ⟨hx, h⟩ ↦ ⟨fun i hi hik ↦ ?_, hx⟩⟩
  · rw [hsymm j hj.le]
    exact h _ (Nat.sub_pos_of_lt hj) (Nat.sub_le k j)
  · have := h (k - i) (Nat.sub_lt (hi.trans_le hik) hi)
    rwa [hsymm _ (Nat.sub_le k i), Nat.sub_sub_self hik] at this

variable [MeasurableSpace X]

/-- The positive return time to a measurable set under a measurable map is measurable. It is a
stopping time for the constant filtration. -/
theorem measurable_positiveReturnTime {T : X → X} (hT : Measurable T) {A : Set X}
    (hA : MeasurableSet A) : Measurable (positiveReturnTime T A) := by
  rw [positiveReturnTime_eq_hittingAfter]
  -- `ℕ∞` carries the discrete measurable structure, `WithTop ℕ` the Borel one: every subset
  -- of the countable type `WithTop ℕ` is Borel.
  exact fun s _ ↦ (Adapted.isStoppingTime_hittingAfter (f := Filtration.const ℕ _ le_rfl)
    (u := fun n x ↦ T^[n] x) (fun i ↦ hT.iterate i) hA (n := 1)).measurable'
    (@Set.Countable.measurableSet (WithTop ℕ) _ _ s s.to_countable)

/-- For measurable `T` and `A`, the set where the return time exceeds `k` is measurable. -/
theorem measurableSet_lt_positiveReturnTime {T : X → X} (hT : Measurable T) {A : Set X}
    (hA : MeasurableSet A) (k : ℕ) :
    MeasurableSet {x | (k : ℕ∞) < positiveReturnTime T A x} :=
  measurable_positiveReturnTime hT hA (.of_discrete (s := Ioi (k : ℕ∞)))

variable {μ : Measure X}

/-- **Layer-cake formula.** For measurable `T` and `A`, the extended integral of the return time
over `A` is `∑ k, μ ({k < positiveReturnTime T A} ∩ A)`. -/
theorem lintegral_positiveReturnTime_eq_tsum {T : X → X} (hT : Measurable T) {A : Set X}
    (hA : MeasurableSet A) :
    ∫⁻ x in A, (positiveReturnTime T A x : ℝ≥0∞) ∂μ =
      ∑' k : ℕ, μ ({x | (k : ℕ∞) < positiveReturnTime T A x} ∩ A) := by
  have hS := measurableSet_lt_positiveReturnTime hT hA
  simp_rw [ENat.toENNReal_eq_tsum_ite]
  rw [lintegral_tsum fun k ↦
    (Measurable.ite (hS k) measurable_const measurable_const).aemeasurable]
  refine tsum_congr fun k ↦ ?_
  rw [← Measure.restrict_apply (hS k), ← lintegral_indicator_one (hS k)]
  refine lintegral_congr fun x ↦ ?_
  simp [Set.indicator_apply]

/-- **Kac's identity** for a measure-preserving measurable equivalence `T`: the extended integral
of the return time over a measurable set `A` is the measure of the set of points whose backward
orbit meets `A`. -/
theorem lintegral_positiveReturnTime_eq_measure {T : X ≃ᵐ X} (hT : MeasurePreserving T μ μ)
    {A : Set X} (hA : MeasurableSet A) :
    ∫⁻ x in A, (positiveReturnTime T A x : ℝ≥0∞) ∂μ = μ {y | ∃ j, T.symm^[j] y ∈ A} := by
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
    rw [lt_positiveReturnTime_inter_eq_preimage T.symm_apply_apply]
    exact (hT.iterate k).measure_preimage (hC k).nullMeasurableSet
  have hdisj : Pairwise (Function.onFun Disjoint C) := by
    intro k k' hkk'
    rcases lt_or_gt_of_ne hkk' with h | h
    · exact Set.disjoint_left.2 fun y hy hy' ↦ hy'.2 k h hy.1
    · exact Set.disjoint_left.2 fun y hy hy' ↦ hy.2 k' h hy'.1
  -- The union of the `C k` is the set of points whose backward orbit meets `A`.
  have hunion : (⋃ k, C k) = {y | ∃ j, T.symm^[j] y ∈ A} := by
    classical
    ext y
    refine ⟨fun hy ↦ ?_, fun ⟨j, hj⟩ ↦ ?_⟩
    · obtain ⟨k, hk⟩ := mem_iUnion.1 hy
      exact ⟨k, hk.1⟩
    · have h : ∃ j, T.symm^[j] y ∈ A := ⟨j, hj⟩
      exact mem_iUnion.2 ⟨Nat.find h, Nat.find_spec h, fun j hj ↦ Nat.find_min h hj⟩
  rw [lintegral_positiveReturnTime_eq_tsum T.measurable hA, tsum_congr hmeas,
    ← measure_iUnion hdisj hC, hunion]

/-- The extended integral of the return time over `A` for an ergodic measurable equivalence of a
probability space, `A` measurable of positive measure, is `1`. -/
theorem lintegral_positiveReturnTime [IsProbabilityMeasure μ] {T : X ≃ᵐ X} (hT : Ergodic T μ)
    {A : Set X} (hA : MeasurableSet A) (hμA : μ A ≠ 0) :
    ∫⁻ x in A, (positiveReturnTime T A x : ℝ≥0∞) ∂μ = 1 := by
  rw [lintegral_positiveReturnTime_eq_measure hT.toMeasurePreserving hA]
  -- The set `B` of points whose backward orbit meets `A` contains `A` and its image under `T⁻¹`.
  set B : Set X := {y | ∃ j, T.symm^[j] y ∈ A}
  have hB : MeasurableSet B := by
    rw [show B = ⋃ j, T.symm^[j] ⁻¹' A by ext; simp [B]]
    exact MeasurableSet.iUnion fun j ↦ T.symm.measurable.iterate j hA
  have hBsub : B ⊆ T ⁻¹' B := fun y ⟨j, hj⟩ ↦
    ⟨j + 1, by rwa [Function.iterate_succ_apply, T.symm_apply_apply]⟩
  rcases hT.ae_empty_or_univ_of_ae_le_preimage hB.nullMeasurableSet
    (LE.le.eventuallySubset hBsub) with h | h
  · have h0 : μ B = 0 := by rw [measure_congr h, measure_empty]
    exact absurd (measure_mono_null (fun x hx ↦ (⟨0, hx⟩ : x ∈ B)) h0) hμA
  · rw [measure_congr h, measure_univ]

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
  simp_rw [← ENat.toReal_toENNReal]
  refine ⟨hfin.mono fun x hx ↦ by simpa using hx.ne, integrable_toReal_of_lintegral_ne_top
    hm.aemeasurable (by simp [hint]), ?_⟩
  rw [integral_toReal hm.aemeasurable hfin, hint, ENNReal.toReal_one]

end TauCeti

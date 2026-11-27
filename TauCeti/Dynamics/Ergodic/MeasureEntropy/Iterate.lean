/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Ergodic.MeasureEntropy.Congr
public import Mathlib.MeasureTheory.MeasurableSpace.Embedding

/-!
# Measure entropy of iterates and of inverses

For a measure-preserving map `T` of a probability space and `k : ℕ`, the Kolmogorov–Sinai entropy
of the iterate is `h_μ(T^[k]) = k * h_μ(T)`, and for an invertible measure-preserving map
`h_μ(T.symm) = h_μ(T)`.

For the iterate, the length-`m` itinerary under `T^[k]` of the length-`k` itinerary
`join_k a` of a label `a` under `T` is a relabeling of the length-`m * k` itinerary of `a`
(`TauCeti.iteratedPartitionLabel_iterate_iteratedPartitionLabel`), so
`h_μ(T^[k], join_k a) = k * h_μ(T, a)`; and `a` is a coarsening of `join_k a`. For the inverse,
the length-`n` itinerary under `T.symm`, composed with `T^[n - 1]`, is the length-`n` itinerary
under `T` read backwards, so every label has the same entropy rate under `T` and `T.symm`.

## Main results

* `TauCeti.countablePartitionEntropy_iteratedPartitionLabel_iterate`:
  `H(join^{T^[k]}_m (join^T_k a)) = H(join^T_{m * k} a)`, for every measure.
* `TauCeti.partitionEntropyRate_iterate_iteratedPartitionLabel`:
  `h_μ(T^[k], join_k a) = k * h_μ(T, a)` for measure-preserving `T` under a probability (or zero)
  measure.
* `TauCeti.partitionEntropyRate_iteratedPartitionLabel`: `h_μ(T, join_N a) = h_μ(T, a)` for
  `0 < N`, for measure-preserving `T` under a probability (or zero) measure.
* `TauCeti.measureEntropy_iterate`: `h_μ(T^[k]) = k * h_μ(T)`.
* `TauCeti.partitionEntropyRate_symm`, `TauCeti.measureEntropy_symm`: for a measure-preserving
  measurable equivalence `e`, `h_μ(e.symm, a) = h_μ(e, a)` and `h_μ(e.symm) = h_μ(e)`.

## References

* O. Sarig, *Lecture Notes on Ergodic Theory*, 2023, Problems 4.4–4.5, p. 130.
-/

public section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace TauCeti

variable {X ι : Type*} {mX : MeasurableSpace X} {μ : Measure X}

/-- The length-`m` itinerary under `T^[k]` of the length-`k` itinerary of `a` under `T` is the
length-`m * k` itinerary of `a` under `T`, cut into `m` blocks of length `k`. -/
theorem iteratedPartitionLabel_iterate_iteratedPartitionLabel (T : X → X) (a : X → ι)
    (k m : ℕ) :
    iteratedPartitionLabel T^[k] (iteratedPartitionLabel T a k) m =
      (fun w j i ↦ w (finProdFinEquiv (j, i))) ∘ iteratedPartitionLabel T a (m * k) := by
  funext x j i
  simp only [iteratedPartitionLabel_apply, Function.comp_apply, finProdFinEquiv_apply_val,
    ← Function.iterate_mul, ← Function.iterate_add_apply]

/-- The length-`m` itinerary under `T^[k]` of the length-`k` itinerary of `a` under `T` has the
entropy of the length-`m * k` itinerary of `a` under `T`, for every measure. -/
theorem countablePartitionEntropy_iteratedPartitionLabel_iterate (T : X → X) (a : X → ι)
    (k m : ℕ) :
    countablePartitionEntropy μ (iteratedPartitionLabel T^[k] (iteratedPartitionLabel T a k) m) =
      countablePartitionEntropy μ (iteratedPartitionLabel T a (m * k)) := by
  rw [iteratedPartitionLabel_iterate_iteratedPartitionLabel]
  exact countablePartitionEntropy_comp_of_injective _
    ((Equiv.curry _ _ _).injective.comp finProdFinEquiv.surjective.injective_comp_right)

variable [MeasurableSpace ι] [MeasurableSingletonClass ι] [Countable ι] {T : X → X}

/-- **Rate of a block label.** For a measure-preserving map under a probability (or zero)
measure and a measurable countable label `a`, the length-`k` itinerary of `a` has rate
`k * h_μ(T, a)` under `T^[k]`. -/
theorem partitionEntropyRate_iterate_iteratedPartitionLabel [IsZeroOrProbabilityMeasure μ]
    (hT : MeasurePreserving T μ μ) {a : X → ι} (ha : Measurable a) (k : ℕ) :
    partitionEntropyRate μ T^[k] (iteratedPartitionLabel T a k) =
      k * partitionEntropyRate μ T a := by
  rcases eq_or_ne k 0 with rfl | hk
  · rw [Nat.cast_zero, zero_mul, iteratedPartitionLabel_zero]
    exact nonpos_iff_eq_zero.mp
      ((partitionEntropyRate_le _ _ _).trans_eq (countablePartitionEntropy_const _))
  set H : ℕ → ℝ≥0∞ := fun n ↦ countablePartitionEntropy μ (iteratedPartitionLabel T a n)
  have hrate : partitionEntropyRate μ T^[k] (iteratedPartitionLabel T a k) =
      ⨅ m : ℕ, k * (H ((m + 1) * k) / (((m + 1) * k : ℕ) : ℝ≥0∞)) := by
    rw [partitionEntropyRate_def]
    refine iInf_congr fun m ↦ ?_
    rw [countablePartitionEntropy_iteratedPartitionLabel_iterate, Nat.cast_mul, ← mul_div_assoc,
      mul_comm (k : ℝ≥0∞), ENNReal.mul_div_mul_right _ _ (by simp [hk])
        (ENNReal.natCast_ne_top k), Nat.cast_succ]
  rw [hrate]
  refine le_antisymm ?_ (le_iInf fun m ↦ ?_)
  · have hlim := (tendsto_partitionEntropyRate hT ha).comp
      (tendsto_atTop_mono (fun m ↦ (Nat.le_succ m).trans (Nat.le_mul_of_pos_right _
        (Nat.pos_of_ne_zero hk))) tendsto_id)
    exact ge_of_tendsto' (ENNReal.Tendsto.const_mul hlim (Or.inr (ENNReal.natCast_ne_top k)))
      fun m ↦ iInf_le _ m
  · gcongr
    exact partitionEntropyRate_le_div (Nat.mul_pos m.succ_pos (Nat.pos_of_ne_zero hk)) μ T a

/-- For a measure-preserving map of a probability space (or the zero measure) and a measurable
countable label `a`, the entropy rate of a finite itinerary of `a` is at most that of `a`:
`h(T, join_N a) ≤ h(T, a)`. -/
theorem partitionEntropyRate_iteratedPartitionLabel_le [IsZeroOrProbabilityMeasure μ]
    (hT : MeasurePreserving T μ μ) {a : X → ι} (ha : Measurable a) (N : ℕ) :
    partitionEntropyRate μ T (iteratedPartitionLabel T a N) ≤ partitionEntropyRate μ T a := by
  rcases eq_or_ne (countablePartitionEntropy μ a) ∞ with htop | hfin
  · -- Every itinerary of `a` has infinite entropy, so the rate of `a` is `∞`.
    refine le_of_le_of_eq le_top ?_
    rw [partitionEntropyRate_def, eq_comm, iInf_eq_top]
    intro n
    have := countablePartitionEntropy_le_iteratedPartitionLabel (μ := μ) T a n.succ_pos
    rw [htop, top_le_iff] at this
    exact ENNReal.div_eq_top.2 (Or.inr ⟨this, by simp⟩)
  set C := countablePartitionEntropy μ (iteratedPartitionLabel T a N)
  have hC : C ≠ ∞ := ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.natCast_ne_top N) hfin)
    (countablePartitionEntropy_iteratedPartitionLabel_le_mul hT ha N)
  have hlim : Tendsto (fun n : ℕ ↦
      countablePartitionEntropy μ (iteratedPartitionLabel T a n) / n + C / n) atTop
        (𝓝 (partitionEntropyRate μ T a + 0)) := by
    refine (tendsto_partitionEntropyRate hT ha).add ?_
    simp only [div_eq_mul_inv]
    simpa using ENNReal.Tendsto.const_mul ENNReal.tendsto_inv_nat_nhds_zero (Or.inr hC)
  rw [add_zero] at hlim
  refine ge_of_tendsto hlim ((eventually_ge_atTop 1).mono fun n hn ↦ ?_)
  refine (partitionEntropyRate_le_div hn μ T _).trans ?_
  rw [← ENNReal.add_div]
  refine ENNReal.div_le_div_right ?_ _
  rw [iteratedPartitionLabel_iteratedPartitionLabel]
  exact (countablePartitionEntropy_comp_le _ _).trans
    (countablePartitionEntropy_iteratedPartitionLabel_add_le hT ha n N)

/-- **Rate of an itinerary.** For a measure-preserving map of a probability space (or the zero
measure) and a measurable countable label `a`, a finite itinerary of positive length has the
entropy rate of `a`: `h(T, join_N a) = h(T, a)` for `0 < N`. -/
theorem partitionEntropyRate_iteratedPartitionLabel [IsZeroOrProbabilityMeasure μ]
    (hT : MeasurePreserving T μ μ) {a : X → ι} (ha : Measurable a) {N : ℕ} (hN : 0 < N) :
    partitionEntropyRate μ T (iteratedPartitionLabel T a N) = partitionEntropyRate μ T a := by
  refine le_antisymm (partitionEntropyRate_iteratedPartitionLabel_le hT ha N) ?_
  have ha' : a = (fun w : Fin N → ι ↦ w ⟨0, hN⟩) ∘ iteratedPartitionLabel T a N := by
    funext x
    simp [iteratedPartitionLabel_apply]
  conv_lhs => rw [ha']
  exact partitionEntropyRate_comp_le T _ _

/-- **Entropy of an iterate.** For a measure-preserving map of a probability space (or the zero
measure), `h_μ(T^[k]) = k * h_μ(T)`. -/
theorem measureEntropy_iterate [IsZeroOrProbabilityMeasure μ] (hT : MeasurePreserving T μ μ)
    (k : ℕ) : measureEntropy μ T^[k] = k * measureEntropy μ T := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp [measureEntropy_id]
  have hk0 : (k : ℝ≥0∞) ≠ 0 := by simpa using hk
  have hktop : (k : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top k
  refine le_antisymm (measureEntropy_le_iff.mpr fun a ha hfin ↦ ?_) ?_
  · -- `a` is a coarsening of its length-`k` itinerary.
    have hcoarse : a = (fun w ↦ w ⟨0, Nat.pos_of_ne_zero hk⟩) ∘ iteratedPartitionLabel T a k :=
      funext fun x ↦ by simp
    calc partitionEntropyRate μ T^[k] a
        ≤ partitionEntropyRate μ T^[k] (iteratedPartitionLabel T a k) := by
          conv_lhs => rw [hcoarse]
          exact partitionEntropyRate_comp_le _ _ _
      _ = k * partitionEntropyRate μ T a :=
          partitionEntropyRate_iterate_iteratedPartitionLabel hT ha k
      _ ≤ k * measureEntropy μ T := by
          gcongr
          exact partitionEntropyRate_le_measureEntropy ha hfin
  · rw [mul_comm, ← ENNReal.le_div_iff_mul_le (Or.inl hk0) (Or.inl hktop)]
    refine measureEntropy_le_iff.mpr fun a ha hfin ↦ ?_
    rw [ENNReal.le_div_iff_mul_le (Or.inl hk0) (Or.inl hktop), mul_comm,
      ← partitionEntropyRate_iterate_iteratedPartitionLabel hT ha k]
    exact partitionEntropyRate_le_measureEntropy_of_countable _
      (measurable_iteratedPartitionLabel hT.measurable ha k)
      (countablePartitionEntropy_iteratedPartitionLabel_ne_top hT ha hfin k)

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] [Countable ι] in
/-- Following the itinerary under `e.symm` from `e^[n] x` reads the itinerary under `e` from `x`
backwards. -/
theorem iteratedPartitionLabel_symm_comp_iterate (e : X ≃ X) (a : X → ι) (n : ℕ) :
    iteratedPartitionLabel e.symm a (n + 1) ∘ e^[n] =
      (fun w ↦ w ∘ Fin.rev) ∘ iteratedPartitionLabel e a (n + 1) := by
  funext x j
  have hj : (j : ℕ) ≤ n := Nat.lt_succ_iff.mp j.isLt
  simp only [Function.comp_apply, iteratedPartitionLabel_apply, Fin.val_rev]
  congr 1
  have key : ∀ (i d : ℕ) (y : X), e.symm^[i] (e^[i + d] y) = e^[d] y := fun i d y ↦ by
    rw [Function.iterate_add_apply, Function.LeftInverse.iterate e.symm_apply_apply i]
  have := key j (n - j) x
  rw [Nat.add_sub_cancel' hj] at this
  rw [this]
  congr 1
  omega

omit [Countable ι] in
/-- **Inverse.** For a measure-preserving measurable equivalence `e`, every measurable label has
the same entropy rate under `e.symm` as under `e`. -/
theorem partitionEntropyRate_symm (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ) {a : X → ι}
    (ha : Measurable a) : partitionEntropyRate μ e.symm a = partitionEntropyRate μ e a := by
  simp only [partitionEntropyRate_def]
  refine iInf_congr fun n ↦ ?_
  congr 1
  have h := iteratedPartitionLabel_symm_comp_iterate e.toEquiv a n
  rw [← countablePartitionEntropy_comp_of_measurePreserving (he.iterate n)
      (measurable_iteratedPartitionLabel e.symm.measurable ha _)]
  rw [e.coe_toEquiv_symm, e.coe_toEquiv] at h
  rw [h, countablePartitionEntropy_comp_of_injective _ Fin.rev_surjective.injective_comp_right]

/-- **Entropy of the inverse.** A measure-preserving measurable equivalence has the same
Kolmogorov–Sinai entropy as its inverse: `h_μ(e.symm) = h_μ(e)`. -/
theorem measureEntropy_symm (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ) :
    measureEntropy μ e.symm = measureEntropy μ e := by
  simp only [measureEntropy_def]
  exact iSup_congr fun a ↦ iSup_congr fun ha ↦ by rw [partitionEntropyRate_symm e he ha]

end TauCeti

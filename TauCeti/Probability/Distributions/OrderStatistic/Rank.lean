/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.UniformOn
public import TauCeti.Data.Fin.Tuple.OrderStatistic
public import TauCeti.MeasureTheory.MeasurableSpace.StrictMono
public import TauCeti.MeasureTheory.MeasurableSpace.TupleSort
import TauCeti.Probability.Independence.InfinitePi

/-!
# The ranks of an atomless sample

For an iid sample of size `n` from an atomless law, the sorting permutation `Tuple.sort` (the
ranks of the sample) is uniformly distributed on the `n!` permutations and independent of the
vector of order statistics. Equivalently, the event that the sorting permutation is `σ` and the
order statistics lie in a set `B` has probability `(n!)⁻¹` times that of the second event. No
measurability of `B` is needed.

Ties are null, so the sample is almost surely injective, and then `Tuple.sort x = σ` exactly
when `x ∘ σ` is strictly increasing. Coordinate permutations preserve the product law and the
order statistics, so every permutation carries the same part of the law of the order
statistics, and the `n!` fibres of `Tuple.sort` partition the sample space.

## Main results

* `TauCeti.Probability.setOf_sort_eq_ae_eq_setOf_strictMono_comp` — almost surely, the sorting
  permutation is `σ` exactly when the sample composed with `σ` is strictly increasing;
* `TauCeti.Probability.measure_setOf_sort_eq_inter_preimage_orderStatistics` and its real form
  `TauCeti.Probability.measureReal_setOf_sort_eq_inter_preimage_orderStatistics`;
* `TauCeti.Probability.map_sort_eq_and_indepFun_orderStatistics` — the ranks are uniform and
  independent of the order statistics.

## References

* D. R. Cox and D. V. Hinkley, *Theoretical Statistics*, Chapman and Hall, 1974, Example 2.11,
  p. 20.

The proofs are adapted from the lean-CKSD project (<https://github.com/bjbraams/lean-CKSD>),
file `CKSD/Inference/Families.lean`.
-/

public section

open MeasureTheory ProbabilityTheory Set Function
open scoped ENNReal

namespace TauCeti.Probability

variable {α : Type*} [LinearOrder α] [TopologicalSpace α] [OrderClosedTopology α]
  [SecondCountableTopology α] [MeasurableSpace α] [OpensMeasurableSpace α]
  {n : ℕ} {μ : Measure α} [IsProbabilityMeasure μ] [NullSingletonClass μ]

/-- For an iid sample from an atomless law, almost surely the sorting permutation is `σ` exactly
when the sample composed with `σ` is strictly increasing: almost every sample has distinct
entries. -/
theorem setOf_sort_eq_ae_eq_setOf_strictMono_comp (σ : Equiv.Perm (Fin n)) :
    {x : Fin n → α | Tuple.sort x = σ} =ᵐ[Measure.pi fun _ : Fin n => μ]
      {x | StrictMono (x ∘ σ)} := by
  have hne : ∀ᵐ x ∂(Measure.pi fun _ : Fin n => μ), Injective x := by
    have h : ∀ᵐ x ∂(Measure.pi fun _ : Fin n => μ), ∀ i j : Fin n, i ≠ j → x i ≠ x j := by
      refine ae_all_iff.mpr fun i => ae_all_iff.mpr fun j => ?_
      by_cases hij : i = j
      · exact Filter.Eventually.of_forall fun _ h => (h hij).elim
      · simpa only [Measure.infinitePi_eq_pi] using
          (ae_eval_ne_eval_infinitePi (fun _ : Fin n => μ) hij).mono fun _ hx _ => hx
    filter_upwards [h] with x hx
    exact injective_iff_pairwise_ne.mpr hx
  filter_upwards [hne] with x hx
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← h]
    exact (Tuple.monotone_sort x).strictMono_of_injective (hx.comp (Tuple.sort x).injective)
  · have heq := Tuple.unique_monotone (Tuple.monotone_sort x) h.monotone
    exact DFunLike.ext _ _ fun i => hx (congrFun heq i)

/-- Every sorting permutation carries the same part of the law of the order statistics: the
part on which the sample itself is strictly increasing. -/
private theorem measure_setOf_sort_eq_inter_eq (σ : Equiv.Perm (Fin n))
    (B : Set (Fin n → α)) :
    (Measure.pi fun _ : Fin n => μ)
        ({x | Tuple.sort x = σ} ∩ (fun x i => orderStatistic i x) ⁻¹' B) =
      (Measure.pi fun _ : Fin n => μ)
        ({x | StrictMono x} ∩ (fun x i => orderStatistic i x) ⁻¹' B) := by
  have hperm := measurePreserving_piCongrLeft (fun _ : Fin n => μ) σ.symm
  have he (x : Fin n → α) : MeasurableEquiv.piCongrLeft (fun _ => α) σ.symm x = x ∘ σ := by
    funext i
    simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
  rw [measure_congr
      ((setOf_sort_eq_ae_eq_setOf_strictMono_comp σ).inter Filter.EventuallyEqSet.rfl),
    ← hperm.measure_preimage_equiv
      ({x | StrictMono x} ∩ (fun x i => orderStatistic i x) ⁻¹' B)]
  congr 1
  ext x
  simp [he, orderStatistic_comp_perm]

/-- **The ranks and the order statistics.** For an iid sample from an atomless law, the event
that the sorting permutation is `σ` and the order statistics lie in `B` has probability `(n!)⁻¹`
times the probability that the order statistics lie in `B`. -/
theorem measure_setOf_sort_eq_inter_preimage_orderStatistics (σ : Equiv.Perm (Fin n))
    (B : Set (Fin n → α)) :
    (Measure.pi fun _ : Fin n => μ)
        ({x | Tuple.sort x = σ} ∩ (fun x i => orderStatistic i x) ⁻¹' B) =
      (n.factorial : ℝ≥0∞)⁻¹ *
        (Measure.pi fun _ : Fin n => μ) ((fun x i => orderStatistic i x) ⁻¹' B) := by
  set ρ := Measure.pi fun _ : Fin n => μ
  have hC (τ : Equiv.Perm (Fin n)) : MeasurableSet {x : Fin n → α | Tuple.sort x = τ} :=
    measurableSet_setOf_sort_eq τ
  have hdisj : Pairwise (Disjoint on fun τ : Equiv.Perm (Fin n) =>
      {x : Fin n → α | Tuple.sort x = τ}) := pairwise_disjoint_fiber Tuple.sort
  -- the fibres of the sorting permutation partition the sample space
  have hpart : ρ = ∑ τ : Equiv.Perm (Fin n), ρ.restrict {x | Tuple.sort x = τ} := by
    rw [← Measure.sum_fintype, ← Measure.restrict_iUnion hdisj hC,
      iUnion_eq_univ_iff.2 fun x => ⟨Tuple.sort x, rfl⟩, Measure.restrict_univ]
  have hsum : ρ ((fun x i => orderStatistic i x) ⁻¹' B) =
      n.factorial * ρ ({x | StrictMono x} ∩ (fun x i => orderStatistic i x) ⁻¹' B) := by
    have hτ (τ : Equiv.Perm (Fin n)) :
        ρ.restrict {x | Tuple.sort x = τ} ((fun x i => orderStatistic i x) ⁻¹' B) =
          ρ ({x | StrictMono x} ∩ (fun x i => orderStatistic i x) ⁻¹' B) := by
      rw [Measure.restrict_apply' (hC τ), inter_comm, measure_setOf_sort_eq_inter_eq]
    conv_lhs => rw [hpart, sum_apply]
    simp only [hτ, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
      nsmul_eq_mul]
  rw [hsum, ← mul_assoc, ENNReal.inv_mul_cancel (by exact_mod_cast n.factorial_ne_zero)
    (ENNReal.natCast_ne_top _), one_mul, measure_setOf_sort_eq_inter_eq]

/-- **The ranks and the order statistics**, for real-valued probabilities: the event that the
sorting permutation is `σ` and the order statistics lie in `B` has probability `(n!)⁻¹` times
the probability that the order statistics lie in `B`. -/
theorem measureReal_setOf_sort_eq_inter_preimage_orderStatistics (σ : Equiv.Perm (Fin n))
    (B : Set (Fin n → α)) :
    (Measure.pi fun _ : Fin n => μ).real
        ({x | Tuple.sort x = σ} ∩ (fun x i => orderStatistic i x) ⁻¹' B) =
      (n.factorial : ℝ)⁻¹ *
        (Measure.pi fun _ : Fin n => μ).real ((fun x i => orderStatistic i x) ⁻¹' B) := by
  rw [measureReal_def, measure_setOf_sort_eq_inter_preimage_orderStatistics, ENNReal.toReal_mul,
    ENNReal.toReal_inv, ENNReal.toReal_natCast, measureReal_def]

/-- The event that the sorting permutation lies in `s` and the order statistics lie in a
measurable set `B` has probability `|s| / n!` times the probability of the second event. -/
private theorem measure_preimage_sort_inter_preimage_orderStatistics
    [MeasurableSpace (Equiv.Perm (Fin n))] [MeasurableSingletonClass (Equiv.Perm (Fin n))]
    (s : Set (Equiv.Perm (Fin n))) {B : Set (Fin n → α)} (hB : MeasurableSet B) :
    (Measure.pi fun _ : Fin n => μ)
        (Tuple.sort ⁻¹' s ∩ (fun x i => orderStatistic i x) ⁻¹' B) =
      Measure.count s * ((n.factorial : ℝ≥0∞)⁻¹ *
        (Measure.pi fun _ : Fin n => μ) ((fun x i => orderStatistic i x) ⁻¹' B)) := by
  classical
  have : MeasurableInf₂ α := ⟨measurable_fst.min measurable_snd⟩
  have : MeasurableSup₂ α := ⟨measurable_fst.max measurable_snd⟩
  have hpre : Tuple.sort ⁻¹' s ∩ (fun x : Fin n → α => fun i => orderStatistic i x) ⁻¹' B =
      ⋃ τ ∈ s.toFinset, {x | Tuple.sort x = τ} ∩ (fun x i => orderStatistic i x) ⁻¹' B := by
    ext x
    simp
  have hS : Measurable fun x : Fin n → α => fun i => orderStatistic i x := by fun_prop
  have hdisj : Pairwise (Disjoint on fun τ : Equiv.Perm (Fin n) =>
      {x : Fin n → α | Tuple.sort x = τ}) := pairwise_disjoint_fiber Tuple.sort
  rw [hpre, measure_biUnion_finset (fun τ _ τ' _ h =>
      (hdisj h).mono inter_subset_left inter_subset_left)
      fun τ _ => (measurableSet_setOf_sort_eq τ).inter (hS hB)]
  simp_rw [measure_setOf_sort_eq_inter_preimage_orderStatistics]
  rw [Finset.sum_const, nsmul_eq_mul, Measure.count_apply_finite s s.toFinite,
    Set.Finite.toFinset_eq_toFinset]

/-- **The law of the ranks.** For an iid sample from an atomless law, the sorting permutation
is uniformly distributed on the `n!` permutations and independent of the vector of order
statistics. -/
theorem map_sort_eq_and_indepFun_orderStatistics [MeasurableSpace (Equiv.Perm (Fin n))]
    [MeasurableSingletonClass (Equiv.Perm (Fin n))] :
    (Measure.pi fun _ : Fin n => μ).map Tuple.sort = uniformOn univ ∧
      IndepFun Tuple.sort (fun x i => orderStatistic i x) (Measure.pi fun _ : Fin n => μ) := by
  have hsort : ∀ s, (Measure.pi fun _ : Fin n => μ) (Tuple.sort ⁻¹' s) =
      Measure.count s * (n.factorial : ℝ≥0∞)⁻¹ := fun s => by
    simpa using measure_preimage_sort_inter_preimage_orderStatistics (μ := μ) s MeasurableSet.univ
  refine ⟨Measure.ext fun s hs => ?_, ?_⟩
  · rw [Measure.map_apply measurable_sort hs, hsort, uniformOn_univ, Fintype.card_perm,
      Fintype.card_fin, ENNReal.div_eq_inv_mul, mul_comm]
  · refine indepFun_iff_measure_inter_preimage_eq_mul.2 fun s B _ hB => ?_
    rw [measure_preimage_sort_inter_preimage_orderStatistics s hB, hsort, mul_assoc]

end TauCeti.Probability

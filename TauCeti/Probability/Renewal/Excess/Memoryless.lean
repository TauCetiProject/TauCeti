/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Renewal.Excess.Basic
public import TauCeti.Probability.Renewal.Exponential

/-!
# Memorylessness at a deterministic time in an exponential renewal process

For independent exponential increments, the residual waiting time at any deterministic time
has the original exponential law. More precisely, on each event that the count equals `n`,
its law factors from every measurable event of the first `n` increments. These are the
completed increments, not the increment straddling the observation time. The factorization
retains the information about completed arrivals needed to restart a renewal process.

The assertions hold on arbitrary probability realizations. Nonexplosion is deduced from
the increment laws, so the exceptional convention in the natural-valued count does not
affect any of the identities. Time zero and an empty completed prefix are included.

## References

* William Feller, *An Introduction to Probability Theory and Its Applications*, vol. II,
  second edition, Wiley, 1971, Chapter I, §4 and Chapter XI, §1.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped ENNReal NNReal

namespace TauCeti.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {T : ℕ → Ω → ℝ≥0} {r : ℝ≥0}

private lemma measure_prefix_count_excess_integral
    (hT : ∀ n, Measurable (T n)) (hindep : iIndepFun T P)
    (hlaw : ∀ n, HasLaw (fun ω ↦ (T n ω : ℝ)) (expMeasure r) P)
    (n : ℕ) {A : Set (Fin n → ℝ≥0)} (hA : MeasurableSet A) (t x : ℝ≥0) :
    P {ω | (fun i : Fin n ↦ T i ω) ∈ A ∧ renewalCountNat T t ω = n ∧
      x < renewalExcess T t ω} =
      ∫⁻ z in A ∩ {z | ∑ i, z i ≤ t},
        ENNReal.ofReal (Real.exp (-((r : ℝ) * ((t : ℝ) - (∑ i, z i : ℝ≥0) + x))))
        ∂P.map (fun ω (i : Fin n) ↦ T i ω) := by
  have := hindep.isProbabilityMeasure
  have hr : 0 < (r : ℝ) := by exact_mod_cast pos_of_hasLaw_expMeasure (hlaw 0)
  have := isProbabilityMeasure_expMeasure hr
  -- The next increment is independent of the entire completed prefix, not just its sum.
  have hp : Measurable (fun ω (i : Fin n) ↦ T i ω) := by fun_prop
  have hi : IndepFun (fun ω (i : Fin n) ↦ T i ω) (fun ω ↦ (T n ω : ℝ)) P := by
    have h := hindep.indepFun_set (Iio n) {n}
      (by simp only [disjoint_left, mem_Iio, mem_singleton_iff]; omega) hT
    exact h.comp
      (by fun_prop : Measurable (fun (z : Iio n → ℝ≥0) (i : Fin n) ↦ z ⟨i, i.isLt⟩))
      (by fun_prop : Measurable (fun (z : ({n} : Set ℕ) → ℝ≥0) ↦ (z ⟨n, by simp⟩ : ℝ)))
  have hsum (ω : Ω) : ∑ i : Fin n, T i ω = arrival T n ω := by
    exact (Fin.sum_univ_eq_sum_range (fun i ↦ T i ω) n).trans (arrival_def T n ω).symm
  let B : Set ((Fin n → ℝ≥0) × ℝ) :=
    {p | p.1 ∈ A ∧ ∑ i, p.1 i ≤ t ∧ (t + x : ℝ≥0) < (∑ i, p.1 i : ℝ≥0) + p.2}
  have hB : MeasurableSet B :=
    (hA.preimage measurable_fst).inter
      ((measurableSet_le
        (by fun_prop : Measurable (fun p : (Fin n → ℝ≥0) × ℝ ↦ ∑ i, p.1 i))
        measurable_const).inter
        (measurableSet_lt measurable_const
          (by fun_prop : Measurable (fun p : (Fin n → ℝ≥0) × ℝ ↦
            ((∑ i, p.1 i : ℝ≥0) : ℝ) + p.2))))
  -- Nonexplosion turns the count slice into a condition on this prefix and the next gap.
  have hevent : {ω | (fun i : Fin n ↦ T i ω) ∈ A ∧ renewalCountNat T t ω = n ∧
      x < renewalExcess T t ω} =ᵐ[P]
      (fun ω ↦ ((fun i : Fin n ↦ T i ω), (T n ω : ℝ))) ⁻¹' B := by
    filter_upwards [ae_tendsto_arrival_atTop_of_expMeasure hindep hlaw] with ω hω
    simp only [mem_ofPred_eq, mem_preimage, B, hsum,
      renewalCountNat_eq_and_lt_renewalExcess_iff hω, arrival_succ]
    norm_cast
  -- Integrate the exponential tail over the prefix.
  -- Outside the allowed prefixes the fiber is empty.
  rw [measure_congr hevent, ← Measure.map_apply (hp.prodMk (hT n).coe_nnreal_real) hB,
    hi.map_prod_eq_prod_map_map hp.aemeasurable ((hT n).coe_nnreal_real.aemeasurable),
    (hlaw n).map_eq, Measure.prod_apply hB, ← lintegral_indicator
      (hA.inter (measurableSet_le (by fun_prop) measurable_const))]
  apply lintegral_congr
  intro z
  by_cases hz : z ∈ A ∧ ∑ i, z i ≤ t
  · rw [indicator_of_mem hz]
    have hfiber : Prod.mk z ⁻¹' B = Ioi ((t : ℝ) - (∑ i, z i : ℝ≥0) + x) := by
      ext u
      simp only [mem_preimage, B, mem_ofPred_eq, hz.1, hz.2, true_and, mem_Ioi,
        NNReal.coe_add]
      constructor <;> intro h <;> linarith
    have hnonneg : 0 ≤ (t : ℝ) - (∑ i, z i : ℝ≥0) + x := by
      have hs : ((∑ i, z i : ℝ≥0) : ℝ) ≤ t := by exact_mod_cast hz.2
      positivity
    rw [hfiber, measure_Ioi_expMeasure hr, ite_eq_left hnonneg]
  · rw [indicator_of_notMem hz]
    have hfiber : Prod.mk z ⁻¹' B = ∅ := by
      ext u
      simp only [mem_preimage, B, mem_ofPred_eq, mem_empty_iff_false, iff_false]
      exact fun h ↦ hz ⟨h.1, h.2.1⟩
    rw [hfiber, measure_empty]

/-- The residual exponential tail factors from every completed-prefix event on each count
slice. In particular, observing the completed increments does not change the waiting-time law. -/
theorem measure_prefix_count_lt_renewalExcess_of_expMeasure
    (hT : ∀ n, Measurable (T n)) (hindep : iIndepFun T P)
    (hlaw : ∀ n, HasLaw (fun ω ↦ (T n ω : ℝ)) (expMeasure r) P)
    (n : ℕ) {A : Set (Fin n → ℝ≥0)} (hA : MeasurableSet A) (t x : ℝ≥0) :
    P {ω | (fun i : Fin n ↦ T i ω) ∈ A ∧ renewalCountNat T t ω = n ∧
      x < renewalExcess T t ω} =
      ENNReal.ofReal (Real.exp (-(r * x : ℝ))) *
        P {ω | (fun i : Fin n ↦ T i ω) ∈ A ∧ renewalCountNat T t ω = n} := by
  have hzero : {ω | (fun i : Fin n ↦ T i ω) ∈ A ∧ renewalCountNat T t ω = n ∧
      0 < renewalExcess T t ω} =ᵐ[P]
      {ω | (fun i : Fin n ↦ T i ω) ∈ A ∧ renewalCountNat T t ω = n} := by
    filter_upwards [ae_tendsto_arrival_atTop_of_expMeasure hindep hlaw] with ω hω
    simp [renewalExcess_pos hω t]
  rw [← measure_congr hzero, measure_prefix_count_excess_integral hT hindep hlaw n hA t x,
    measure_prefix_count_excess_integral hT hindep hlaw n hA t 0,
    ← lintegral_const_mul'' _ (by fun_prop)]
  apply lintegral_congr
  intro z
  simp only [NNReal.coe_zero, add_zero, mul_add, neg_add, Real.exp_add]
  rw [ENNReal.ofReal_mul (Real.exp_nonneg _), mul_comm]

/-- On a count slice and any measurable completed-prefix event, the residual waiting-time
measure is the original exponential law multiplied by the probability of that event.
This includes null events, without requiring a choice of conditional law there. -/
theorem map_renewalExcess_restrict_prefix_count_of_expMeasure
    (hT : ∀ n, Measurable (T n)) (hindep : iIndepFun T P)
    (hlaw : ∀ n, HasLaw (fun ω ↦ (T n ω : ℝ)) (expMeasure r) P)
    (n : ℕ) {A : Set (Fin n → ℝ≥0)} (hA : MeasurableSet A) (t : ℝ≥0) :
    (P.restrict {ω | (fun i : Fin n ↦ T i ω) ∈ A ∧ renewalCountNat T t ω = n}).map
      (fun ω ↦ (renewalExcess T t ω : ℝ)) =
      P {ω | (fun i : Fin n ↦ T i ω) ∈ A ∧ renewalCountNat T t ω = n} • expMeasure r := by
  have := hindep.isProbabilityMeasure
  have hr : 0 < (r : ℝ) := by exact_mod_cast pos_of_hasLaw_expMeasure (hlaw 0)
  have := isProbabilityMeasure_expMeasure hr
  let H := {ω | (fun i : Fin n ↦ T i ω) ∈ A ∧ renewalCountNat T t ω = n}
  have hE : Measurable (fun ω ↦ (renewalExcess T t ω : ℝ)) :=
    (measurable_renewalExcess hT t).coe_nnreal_real
  have htail (x : ℝ) :
      ((P.restrict H).map (fun ω ↦ (renewalExcess T t ω : ℝ))) (Ioi x) =
        (P H • expMeasure r) (Ioi x) := by
    rw [Measure.map_apply hE measurableSet_Ioi, Measure.restrict_apply
      (hE measurableSet_Ioi), smul_apply, smul_eq_mul, measure_Ioi_expMeasure hr]
    by_cases hx : 0 ≤ x
    · lift x to ℝ≥0 using hx with y hy
      rw [ite_eq_left y.coe_nonneg]
      simpa [H, preimage, ← ofPred_and, and_comm, and_left_comm, and_assoc, mul_comm] using
        measure_prefix_count_lt_renewalExcess_of_expMeasure hT hindep hlaw n hA t y
    · rw [ite_eq_right hx]
      have hset : (fun ω ↦ (renewalExcess T t ω : ℝ)) ⁻¹' Ioi x ∩ H = H := by
        apply inter_eq_right.2
        intro ω _
        exact (lt_of_not_ge hx).trans_le (renewalExcess T t ω).coe_nonneg
      simp [hset]
  have hmass : ((P.restrict H).map (fun ω ↦ (renewalExcess T t ω : ℝ))) univ =
      (P H • expMeasure r) univ := by simp [Measure.map_apply hE]
  apply Measure.ext_of_Iic
  intro x
  rw [← compl_Ioi, measure_compl measurableSet_Ioi (by finiteness),
    measure_compl measurableSet_Ioi (by simp; finiteness), hmass, htail]

/-- At every deterministic time, the residual waiting time in an exponential renewal process
has the same exponential law as a fresh increment. -/
theorem hasLaw_renewalExcess_expMeasure
    (hT : ∀ n, Measurable (T n)) (hindep : iIndepFun T P)
    (hlaw : ∀ n, HasLaw (fun ω ↦ (T n ω : ℝ)) (expMeasure r) P) (t : ℝ≥0) :
    HasLaw (fun ω ↦ (renewalExcess T t ω : ℝ)) (expMeasure r) P := by
  have := hindep.isProbabilityMeasure
  have hN := measurable_renewalCountNat hT t
  have hE := (measurable_renewalExcess hT t).coe_nnreal_real
  refine ⟨hE.aemeasurable, ?_⟩
  ext B hB
  rw [Measure.map_apply hE hB]
  have hunion : (fun ω ↦ (renewalExcess T t ω : ℝ)) ⁻¹' B =
      ⋃ n, {ω | renewalCountNat T t ω = n} ∩
        (fun ω ↦ (renewalExcess T t ω : ℝ)) ⁻¹' B := by
    ext ω
    simp
  have hdisj : Pairwise (Disjoint on fun n ↦ {ω | renewalCountNat T t ω = n} ∩
      (fun ω ↦ (renewalExcess T t ω : ℝ)) ⁻¹' B) := by
    intro m n hmn
    exact disjoint_left.2 fun ω hm hn ↦ hmn (hm.1.symm.trans hn.1)
  rw [hunion, measure_iUnion hdisj
      (fun n ↦ (hN (measurableSet_singleton n)).inter (hE hB))]
  have hslice (n : ℕ) : P ({ω | renewalCountNat T t ω = n} ∩
      (fun ω ↦ (renewalExcess T t ω : ℝ)) ⁻¹' B) =
      P {ω | renewalCountNat T t ω = n} * expMeasure r B := by
    have h := congrArg (fun μ : Measure ℝ ↦ μ B)
      (map_renewalExcess_restrict_prefix_count_of_expMeasure hT hindep hlaw n
        MeasurableSet.univ t)
    simpa [Measure.map_apply hE hB, Measure.restrict_apply (hE hB), inter_comm] using h
  simp_rw [hslice]
  have htotal : (∑' n, P {ω | renewalCountNat T t ω = n}) = 1 := by
    rw [← (Equiv.Set.univ ℕ).tsum_eq]
    exact (tsum_measure_preimage_singleton (μ := P) (f := renewalCountNat T t)
      (s := univ) countable_univ (fun n _ ↦ hN (measurableSet_singleton n))).trans
        (by simp)
  rw [ENNReal.tsum_mul_right, htotal, one_mul]

end TauCeti.Probability

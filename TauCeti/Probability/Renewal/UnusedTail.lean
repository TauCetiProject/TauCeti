/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Renewal.Excess.Basic
public import TauCeti.Probability.Independence.DisjointBlocks

/-!
# Unused increments at a renewal observation time

At time `t`, increment `T (renewalCountNat T t)` straddles the observation time.
The increments strictly after it still have their original independent product law.
This remains true after restricting to any event determined by the count and all
increments through the straddling increment. In particular the unused tail is
independent of the count and the excess. This separates the untouched increments
from the residual part of the straddling increment in renewal restart arguments.

Zero increments are allowed. Count slices use the closed arrival endpoint, and
null slices are handled by unnormalized restricted measures.

## References

* W. Feller, *An Introduction to Probability Theory and Its Applications*,
  vol. II, second edition (1971), Chapters I and XI.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal

namespace TauCeti.Probability

variable {Ω : Type*} {T : ℕ → Ω → ℝ≥0}

/-- The infinite sequence of unused increments strictly after the increment straddling `t`.
Its zeroth coordinate is the increment following the straddling one. -/
def renewalUnusedTail (T : ℕ → Ω → ℝ≥0) (t : ℝ≥0) (ω : Ω) (k : ℕ) : ℝ≥0 :=
  T (renewalCountNat T t ω + 1 + k) ω

@[simp]
lemma renewalUnusedTail_apply (t : ℝ≥0) (ω : Ω) (k : ℕ) :
    renewalUnusedTail T t ω k = T (renewalCountNat T t ω + 1 + k) ω := (rfl)

variable [MeasurableSpace Ω] {P : Measure Ω}

/-- The unused increment sequence at a fixed observation time is measurable. -/
@[fun_prop]
lemma measurable_renewalUnusedTail (hT : ∀ n, Measurable (T n)) (t : ℝ≥0) :
    Measurable (renewalUnusedTail T t) :=
  Measurable.of_eval fun k ↦ (Measurable.of_eval hT).eval_index
    (((measurable_renewalCountNat hT t).add_const 1).add_const k)

private theorem measure_eq_sum_restrict_renewalCountNat (hT : ∀ n, Measurable (T n))
    (t : ℝ≥0) :
    P = Measure.sum (fun n : ℕ ↦ P.restrict {ω | renewalCountNat T t ω = n}) := by
  have hu : (⋃ n : ℕ, {ω | renewalCountNat T t ω = n}) = univ := by ext ω; simp
  calc
    P = P.restrict univ := Measure.restrict_univ.symm
    _ = _ := by
      rw [← hu]
      apply Measure.restrict_iUnion
      · intro i j hij
        exact disjoint_left.2 fun ω hi hj ↦ hij (hi.symm.trans hj)
      · exact fun n ↦ (measurable_renewalCountNat hT t) (measurableSet_singleton n)

/-- On a count slice, the entire tail after the straddling increment has its original
product law even after restriction by any event in the increment prefix through that
increment. The identity also applies to null prefix events. -/
theorem map_renewalUnusedTail_restrict_renewalCountNat (hT : ∀ n, Measurable (T n))
    (hindep : iIndepFun T P) (hid : ∀ n, IdentDistrib (T n) (T 0) P P)
    (hzero : P {ω | T 0 ω = 0} < 1) (t : ℝ≥0) (n : ℕ) {A : Set Ω}
    (hA : MeasurableSet[blockSigma T (Iio (n + 1))] A) :
    (P.restrict (A ∩ {ω | renewalCountNat T t ω = n})).map
        (renewalUnusedTail T t) =
      P (A ∩ {ω | renewalCountNat T t ω = n}) •
        Measure.infinitePi (fun _ : ℕ ↦ P.map (T 0)) := by
  have := hindep.isProbabilityMeasure
  let E := A ∩ {ω | arrival T n ω ≤ t ∧ t < arrival T (n + 1) ω}
  have harr {j : ℕ} (hj : j ≤ n + 1) :
      Measurable[blockSigma T (Iio (n + 1))] (arrival T j) :=
    measurable_arrival_of_lt fun i hi ↦ measurable_blockSigma_of_mem (hi.trans_le hj)
  have hE : MeasurableSet[blockSigma T (Iio (n + 1))] E :=
    hA.inter ((measurableSet_le (harr (by omega)) measurable_const).inter
      (measurableSet_lt measurable_const (harr le_rfl)))
  have heq : A ∩ {ω | renewalCountNat T t ω = n} =ᵐ[P] E := by
    filter_upwards [ae_tendsto_arrival_atTop hindep hid hzero] with ω hω
    simp only [E, mem_inter_iff, mem_ofPred_eq, renewalCountNat_eq_iff hω]
  have htail : Measurable[blockSigma T (Ici (n + 1))]
      (fun ω k ↦ T (n + 1 + k) ω) := by
    let : MeasurableSpace Ω := blockSigma T (Ici (n + 1))
    exact Measurable.of_eval fun k ↦
      measurable_blockSigma_of_mem (Z := T) (S := Ici (n + 1))
        (i := n + 1 + k) (Nat.le_add_right _ _)
  have hI := indep_blockSigma_of_disjoint hindep hT (Iio_disjoint_Ici (a := n + 1) le_rfl)
  have hlaw : P.map (fun ω k ↦ T (n + 1 + k) ω) =
      Measure.infinitePi (fun _ : ℕ ↦ P.map (T 0)) := by
    rw [(hindep.precomp (add_right_injective (n + 1))).map_fun_eq_infinitePi_map
      (fun k ↦ hT (n + 1 + k))]
    congr 1
    funext k
    exact (hid (n + 1 + k)).map_eq
  have hmap : (P.restrict (A ∩ {ω | renewalCountNat T t ω = n})).map
      (renewalUnusedTail T t) =
      (P.restrict E).map (fun ω k ↦ T (n + 1 + k) ω) := by
    rw [← Measure.restrict_congr_set heq]
    apply Measure.map_congr
    filter_upwards [ae_restrict_mem ((blockSigma_le _ (fun i _ ↦ hT i)) _ hA |>.inter
      ((measurable_renewalCountNat hT t) (measurableSet_singleton n)))] with ω hω
    simp only [mem_inter_iff, mem_ofPred_eq] at hω
    funext k
    simp only [renewalUnusedTail_apply, hω.2]
  rw [hmap, measure_congr heq]
  ext B hB
  rw [Measure.map_apply (by fun_prop) hB,
    Measure.restrict_apply ((Measurable.of_eval fun k ↦ hT (n + 1 + k)) hB),
    smul_apply, smul_eq_mul, ← hlaw, Measure.map_apply (by fun_prop) hB,
    inter_comm]
  exact (Indep_iff _ _ P).1 hI _ _ hE (htail hB)

/-- The unused infinite increment sequence at a deterministic observation time has the
original i.i.d. product law. Neither strict positivity nor a finite mean is required. -/
theorem hasLaw_renewalUnusedTail (hT : ∀ n, Measurable (T n))
    (hindep : iIndepFun T P) (hid : ∀ n, IdentDistrib (T n) (T 0) P P)
    (hzero : P {ω | T 0 ω = 0} < 1) (t : ℝ≥0) :
    HasLaw (renewalUnusedTail T t)
      (Measure.infinitePi (fun _ : ℕ ↦ P.map (T 0))) P := by
  have := hindep.isProbabilityMeasure
  have hU := measurable_renewalUnusedTail hT t
  refine ⟨hU.aemeasurable, ?_⟩
  have hpartition := measure_eq_sum_restrict_renewalCountNat (P := P) hT t
  calc
    P.map (renewalUnusedTail T t) =
        Measure.sum (fun n : ℕ ↦ P {ω | renewalCountNat T t ω = n} •
          Measure.infinitePi (fun _ : ℕ ↦ P.map (T 0))) := by
      conv_lhs => rw [hpartition]
      rw [Measure.map_sum hU.aemeasurable]
      congr 1
      funext n
      simpa using map_renewalUnusedTail_restrict_renewalCountNat hT hindep hid hzero t n
        (A := univ) MeasurableSet.univ
    _ = Measure.infinitePi (fun _ : ℕ ↦ P.map (T 0)) := by
      have hmass := congrArg (fun μ : Measure Ω ↦ μ univ) hpartition
      have hsum : (∑' n : ℕ, P {ω | renewalCountNat T t ω = n}) = 1 := by
        simpa [Measure.sum_apply, Measure.restrict_apply_univ] using hmass.symm
      ext B hB
      simp only [Measure.sum_apply _ hB, smul_apply, smul_eq_mul,
        ENNReal.tsum_mul_right, hsum, one_mul]

private theorem measure_renewalUnusedTail_inter_slice (hT : ∀ n, Measurable (T n))
    (hindep : iIndepFun T P) (hid : ∀ n, IdentDistrib (T n) (T 0) P P)
    (hzero : P {ω | T 0 ω = 0} < 1) (t : ℝ≥0) (n : ℕ)
    {B : Set (ℕ → ℝ≥0)} {C : Set (ℕ × ℝ≥0)} (hB : MeasurableSet B)
    (hC : MeasurableSet C) :
    P (((renewalUnusedTail T t) ⁻¹' B ∩
        (fun ω ↦ (renewalCountNat T t ω, renewalExcess T t ω)) ⁻¹' C) ∩
        {ω | renewalCountNat T t ω = n}) =
      P ((fun ω ↦ (renewalCountNat T t ω, renewalExcess T t ω)) ⁻¹' C ∩
        {ω | renewalCountNat T t ω = n}) *
        Measure.infinitePi (fun _ : ℕ ↦ P.map (T 0)) B := by
  let A := (fun ω ↦ (n, arrival T (n + 1) ω - t)) ⁻¹' C
  have hA : MeasurableSet[blockSigma T (Iio (n + 1))] A := by
    have harr : Measurable[blockSigma T (Iio (n + 1))] (arrival T (n + 1)) :=
      measurable_arrival_of_lt fun i hi ↦ measurable_blockSigma_of_mem hi
    exact (measurable_const.prodMk (harr.sub_const t)) hC
  have heq : (fun ω ↦ (renewalCountNat T t ω, renewalExcess T t ω)) ⁻¹' C ∩
      {ω | renewalCountNat T t ω = n} = A ∩ {ω | renewalCountNat T t ω = n} := by
    ext ω
    by_cases hn : renewalCountNat T t ω = n <;> simp [A, renewalExcess_def, hn]
  have h := congrArg (fun μ : Measure (ℕ → ℝ≥0) ↦ μ B)
    (map_renewalUnusedTail_restrict_renewalCountNat hT hindep hid hzero t n hA)
  have hU := measurable_renewalUnusedTail hT t
  rw [Measure.map_apply hU hB, Measure.restrict_apply (hU hB),
    smul_apply, smul_eq_mul] at h
  simpa only [inter_assoc, heq] using h

/-- The increments strictly after the straddling increment are independent of both the
observed count and the excess. This statement does not assert memorylessness of the excess. -/
theorem indepFun_renewalUnusedTail_renewalCountNat_renewalExcess (hT : ∀ n, Measurable (T n))
    (hindep : iIndepFun T P) (hid : ∀ n, IdentDistrib (T n) (T 0) P P)
    (hzero : P {ω | T 0 ω = 0} < 1) (t : ℝ≥0) :
    IndepFun (renewalUnusedTail T t)
      (fun ω ↦ (renewalCountNat T t ω, renewalExcess T t ω)) P := by
  have := hindep.isProbabilityMeasure
  let U := renewalUnusedTail T t
  let Y := fun ω ↦ (renewalCountNat T t ω, renewalExcess T t ω)
  have hY : Measurable Y :=
    (measurable_renewalCountNat hT t).prodMk (measurable_renewalExcess hT t)
  have hsplit (D : Set Ω) (hD : MeasurableSet D) :
      P D = ∑' n : ℕ, P (D ∩ {ω | renewalCountNat T t ω = n}) := by
    have h := congrArg (fun μ : Measure Ω ↦ μ D)
      (measure_eq_sum_restrict_renewalCountNat (P := P) hT t)
    simpa only [Measure.sum_apply _ hD, Measure.restrict_apply hD] using h
  have hUlaw := hasLaw_renewalUnusedTail hT hindep hid hzero t
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  intro B C hB hC
  have hUB : MeasurableSet (U ⁻¹' B) := measurable_renewalUnusedTail hT t hB
  rw [hsplit _ (hUB.inter (hY hC))]
  simp_rw [U, Y, measure_renewalUnusedTail_inter_slice hT hindep hid hzero t _ hB hC]
  rw [ENNReal.tsum_mul_right, ← hsplit _ (hY hC), mul_comm]
  congr 1
  exact (hUlaw.measure_eq hB).symm

end TauCeti.Probability

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Binomial.Basic
import TauCeti.Probability.Distributions.Bernoulli.Basic
import TauCeti.MeasureTheory.Measure.Measurability

/-!
# The Poisson-binomial distribution

The Poisson-binomial distribution is the law of a finite sum of independent Bernoulli variables
whose success probabilities need not agree.  This file defines the law by its subset weights and
proves the mass formula, normalization, probability-generating function, independent-sum
characterization, and the recursion obtained by adjoining one Bernoulli trial.

These results provide the count law used for order statistics of independent, non-identically
distributed real random variables.

## Main results

* `poissonBinomialMeasure` is the native law on `ℕ`;
* `poissonBinomialMeasure_singleton` gives its singleton masses as a sum over subsets;
* `integral_poissonBinomialMeasure` writes integration as a finite sum over success sets;
* `poissonBinomialMeasure_singleton_ne_zero_iff` identifies the exact interval of possible counts;
* `pgf_poissonBinomialMeasure` gives its probability-generating function;
* `iIndepFun.hasLaw_sum_poissonBinomialMeasure` identifies independent Bernoulli sums;
* `map_sum_pi_bernoulliMeasure` gives the corresponding product-measure pushforward;
* `map_sum_natCast_pi_bernoulliMeasure` gives its real-cast form;
* `poissonBinomialMeasure_eq_conv_bernoulliMeasure` gives the adjoining-one-trial recursion;
* `poissonBinomialMeasure_const` recovers the binomial distribution.

## References

* Y. H. Wang, “On the number of successes in independent trials”, *Statistica Sinica* 3 (1993),
  295–312.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

open scoped ENNReal NNReal ProbabilityTheory unitInterval

namespace TauCeti

namespace Probability

variable {ι Ω : Type*} [Fintype ι]

open Classical in
/-- The probability of the success set `s` for independent Bernoulli trials with success
probabilities `p`. -/
def poissonBinomialWeight (p : ι → unitInterval) (s : Finset ι) : ℝ≥0 :=
  (∏ i ∈ s, unitInterval.toNNReal (p i)) *
    ∏ i ∈ sᶜ, unitInterval.toNNReal (σ (p i))

/-- The product formula for the probability of a given success set. -/
theorem poissonBinomialWeight_def [DecidableEq ι] (p : ι → unitInterval) (s : Finset ι) :
    poissonBinomialWeight p s =
      (∏ i ∈ s, unitInterval.toNNReal (p i)) *
        ∏ i ∈ sᶜ, unitInterval.toNNReal (σ (p i)) := by
  unfold poissonBinomialWeight
  congr 1
  apply Finset.prod_congr
  · ext i
    simp
  · intros
    rfl

/-- A success set has nonzero weight exactly when it contains every certain success and
contains no trial whose success probability is zero. -/
@[simp]
theorem poissonBinomialWeight_ne_zero_iff (p : ι → unitInterval) (s : Finset ι) :
    poissonBinomialWeight p s ≠ 0 ↔
      (∀ i ∈ s, p i ≠ 0) ∧ (∀ i ∉ s, p i ≠ 1) := by
  classical
  have hzero (q : unitInterval) : unitInterval.toNNReal q = 0 ↔ q = 0 := by
    rw [← NNReal.coe_eq_zero, unitInterval.coe_toNNReal]
    exact Set.Icc.coe_eq_zero
  simp [poissonBinomialWeight_def, Finset.prod_ne_zero_iff, hzero,
    unitInterval.symm_eq_zero]

/-- The Poisson-binomial law with success probabilities `p` is the weighted sum of point masses
at the cardinalities of all possible success sets. -/
def poissonBinomialMeasure (p : ι → unitInterval) : Measure ℕ :=
  ∑ s : Finset ι, poissonBinomialWeight p s • Measure.dirac s.card

/-- The Poisson-binomial weights sum to one. -/
@[simp]
theorem sum_poissonBinomialWeight (p : ι → unitInterval) :
    ∑ s : Finset ι, poissonBinomialWeight p s = 1 := by
  classical
  calc
    ∑ s : Finset ι, poissonBinomialWeight p s =
        ∏ i, (unitInterval.toNNReal (p i) + unitInterval.toNNReal (σ (p i))) := by
      rw [Fintype.prod_add]
      simp only [poissonBinomialWeight_def]
    _ = 1 := by simp

open Classical in
/-- The value of a Poisson-binomial law on a measurable set is the sum of the weights of the
success sets whose cardinalities belong to it. -/
theorem poissonBinomialMeasure_apply (p : ι → unitInterval) (S : Set ℕ) :
    poissonBinomialMeasure p S =
      ∑ s : Finset ι with s.card ∈ S, (poissonBinomialWeight p s : ℝ≥0∞) := by
  classical
  rw [poissonBinomialMeasure, Measure.finsetSum_apply]
  simp only [Measure.smul_apply, Measure.dirac_apply' _ MeasurableSet.of_discrete,
    ENNReal.smul_def, smul_eq_mul,
    Set.indicator, Pi.one_apply]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro s hs
  by_cases hcard : s.card ∈ S <;> simp [hcard]

/-- The Poisson-binomial law is a probability measure. -/
instance isProbabilityMeasure_poissonBinomialMeasure (p : ι → unitInterval) :
    IsProbabilityMeasure (poissonBinomialMeasure p) where
  measure_univ := by
    classical
    rw [poissonBinomialMeasure_apply p Set.univ]
    simp only [Set.mem_univ, Finset.filter_true]
    norm_cast
    exact sum_poissonBinomialWeight p

/-- Every function is integrable against a Poisson-binomial law because the law has finite
support. -/
theorem integrable_poissonBinomialMeasure {E : Type*} [SeminormedAddGroup E]
    (f : ℕ → E) (p : ι → unitInterval) : Integrable f (poissonBinomialMeasure p) := by
  rw [poissonBinomialMeasure]
  exact integrable_finsetSum_measure.mpr fun s _ ↦
    (integrable_dirac (by simp)).smul_measure_nnreal

/-- Integration against a Poisson-binomial law is a finite weighted sum over success sets. -/
theorem integral_poissonBinomialMeasure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (f : ℕ → E) (p : ι → unitInterval) :
    ∫ k, f k ∂poissonBinomialMeasure p =
      ∑ s : Finset ι, (poissonBinomialWeight p s : ℝ) • f s.card := by
  rw [poissonBinomialMeasure, integral_finsetSum_measure]
  · simp [NNReal.smul_def]
  · exact fun s _ ↦ (integrable_dirac (by simp)).smul_measure_nnreal

/-- The mass at `k` is the sum of the success-set weights over subsets of cardinality `k`. -/
@[simp]
theorem poissonBinomialMeasure_singleton (p : ι → unitInterval) (k : ℕ) :
    poissonBinomialMeasure p {k} =
      ∑ s ∈ Finset.univ.powersetCard k, (poissonBinomialWeight p s : ℝ≥0∞) := by
  classical
  rw [poissonBinomialMeasure_apply p {k}, Finset.powersetCard_eq_filter,
    Finset.powerset_univ]
  simp only [Set.mem_singleton_iff]

/-- The real singleton mass of a Poisson-binomial law. -/
@[simp]
theorem poissonBinomialMeasure_real_singleton (p : ι → unitInterval) (k : ℕ) :
    (poissonBinomialMeasure p).real {k} =
      ∑ s ∈ Finset.univ.powersetCard k, (poissonBinomialWeight p s : ℝ) := by
  rw [measureReal_def, poissonBinomialMeasure_singleton]
  rw [ENNReal.toReal_sum]
  · simp only [ENNReal.coe_toReal]
  · intro s hs
    simp

open Classical in
/-- The possible counts run from the number of certain successes to the number of trials with
nonzero success probability, including both endpoints and every count between them. -/
theorem poissonBinomialMeasure_singleton_ne_zero_iff (p : ι → unitInterval) (k : ℕ) :
    poissonBinomialMeasure p {k} ≠ 0 ↔
      (Finset.univ.filter fun i ↦ p i = 1).card ≤ k ∧
        k ≤ (Finset.univ.filter fun i ↦ p i ≠ 0).card := by
  classical
  rw [poissonBinomialMeasure_singleton, ← pos_iff_ne_zero, Finset.sum_pos_iff]
  constructor
  · rintro ⟨s, hs, hweight⟩
    have hcard : s.card = k := (Finset.mem_powersetCard.mp hs).2
    have hw := (poissonBinomialWeight_ne_zero_iff p s).mp (by simpa using hweight.ne')
    constructor
    · rw [← hcard]
      apply Finset.card_le_card
      intro i hi
      by_contra hnot
      exact hw.2 i hnot (by simpa using hi)
    · rw [← hcard]
      exact Finset.card_le_card fun i hi ↦ by simp [hw.1 i hi]
  · rintro ⟨hlower, hupper⟩
    have hsub : (Finset.univ.filter fun i ↦ p i = 1) ⊆
        Finset.univ.filter fun i ↦ p i ≠ 0 := by
      intro i hi
      simp_all
    obtain ⟨s, hlow, hupp, hcard⟩ :=
      Finset.exists_subsuperset_card_eq hsub hlower hupper
    refine ⟨s, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ s, hcard⟩, ?_⟩
    have hw : poissonBinomialWeight p s ≠ 0 :=
      (poissonBinomialWeight_ne_zero_iff p s).mpr ⟨?_, ?_⟩
    · simpa only [pos_iff_ne_zero, ENNReal.coe_ne_zero] using hw
    · intro i hi
      simpa using hupp hi
    · intro i hi hone
      exact hi (hlow (by simp [hone]))

/-- A Poisson-binomial law has no mass above the number of trials. -/
theorem poissonBinomialMeasure_singleton_eq_zero (p : ι → unitInterval) {k : ℕ}
    (hk : Fintype.card ι < k) : poissonBinomialMeasure p {k} = 0 := by
  rw [poissonBinomialMeasure_singleton]
  simp [Finset.powersetCard_eq_empty.mpr hk]

/-- A Poisson-binomial count is at most the number of trials almost surely. -/
@[simp]
theorem poissonBinomialMeasure_Iic_card (p : ι → unitInterval) :
    poissonBinomialMeasure p (Set.Iic (Fintype.card ι)) = 1 := by
  classical
  rw [poissonBinomialMeasure_apply p (Set.Iic (Fintype.card ι))]
  simp only [Set.mem_Iic]
  rw [Finset.filter_eq_self.2]
  · norm_cast
    exact sum_poissonBinomialWeight p
  · intro s hs
    exact s.card_le_univ

/-- The probability-generating function of a Poisson-binomial law is the product of the
Bernoulli probability-generating functions. -/
@[simp]
theorem pgf_poissonBinomialMeasure (p : ι → unitInterval) (z : ℝ) :
    pgf id (poissonBinomialMeasure p) z =
      ∏ i, (1 - (p i : ℝ) + (p i : ℝ) * z) := by
  classical
  rw [pgf_def, poissonBinomialMeasure]
  rw [integral_finsetSum_measure]
  · simp only [integral_smul_nnreal_measure, integral_dirac, id_eq, NNReal.smul_def,
      poissonBinomialWeight_def, NNReal.coe_mul, NNReal.coe_prod, unitInterval.coe_toNNReal,
      smul_eq_mul]
    calc
      ∑ s : Finset ι,
          ((∏ i ∈ s, (p i : ℝ)) * ∏ i ∈ sᶜ, (σ (p i) : ℝ)) * z ^ s.card =
          ∑ s : Finset ι,
            (∏ i ∈ s, (p i : ℝ) * z) * ∏ i ∈ sᶜ, (σ (p i) : ℝ) := by
        apply Fintype.sum_congr
        intro s
        rw [Finset.prod_mul_distrib]
        simp only [Finset.prod_const]
        ring
      _ = ∏ i, ((p i : ℝ) * z + (σ (p i) : ℝ)) := by
        rw [← Fintype.prod_add]
      _ = ∏ i, (1 - (p i : ℝ) + (p i : ℝ) * z) := by
        apply Fintype.prod_congr
        intro i
        simp only [unitInterval.coe_symm_eq]
        ring
  · intro s hs
    exact (integrable_dirac (by simp)).smul_measure_nnreal

end Probability

end TauCeti

namespace ProbabilityTheory

open TauCeti.Probability

/-- A finite sum of independent Bernoulli variables has the Poisson-binomial law with the
corresponding success probabilities. -/
theorem iIndepFun.hasLaw_sum_poissonBinomialMeasure
    {ι Ω : Type*} [Fintype ι]
    [MeasurableSpace Ω] {P : Measure Ω} {X : ι → Ω → ℕ} {p : ι → unitInterval}
    (hindep : iIndepFun X P) (hX : ∀ i, HasLaw (X i) Ber((1 : ℕ), 0, p i) P) :
    HasLaw (fun ω ↦ ∑ i, X i ω) (poissonBinomialMeasure p) P := by
  let _ : IsProbabilityMeasure P := hindep.isProbabilityMeasure
  refine ⟨Finset.aemeasurable_fun_sum Finset.univ fun i _ ↦ (hX i).aemeasurable, ?_⟩
  apply measure_eq_of_pgf_eqOn
  intro z hz
  rw [pgf_map (Finset.aemeasurable_fun_sum Finset.univ fun i _ ↦ (hX i).aemeasurable)]
  have hsumfun : (fun a => ∑ i, X i a) = ∑ i, X i := by
    funext a
    simp
  rw [hsumfun]
  rw [iIndepFun.pgf_sum_of_abs_le_one hindep Finset.univ
    (fun i _ ↦ (hX i).aemeasurable) (abs_le.mpr ⟨hz.1.le, hz.2.le⟩)]
  simp only [pgf_poissonBinomialMeasure]
  apply Finset.prod_congr rfl
  intro i _
  rw [HasLaw.pgf_eq (hX i)]
  exact pgf_bernoulliMeasure (p i) z

end ProbabilityTheory

namespace TauCeti

namespace Probability

variable {ι Ω : Type*} [Fintype ι]

/-- Pushing the product of Bernoulli laws forward by coordinate sum gives the
Poisson-binomial law. -/
theorem map_sum_pi_bernoulliMeasure (p : ι → unitInterval) :
    (Measure.pi fun i : ι ↦ Ber((1 : ℕ), 0, p i)).map (fun x ↦ ∑ i, x i) =
      poissonBinomialMeasure p := by
  have hindep : iIndepFun (fun (i : ι) (x : ι → ℕ) ↦ x i)
      (Measure.pi fun i : ι ↦ Ber((1 : ℕ), 0, p i)) :=
    iIndepFun_pi (X := fun _ ↦ (id : ℕ → ℕ)) fun _ ↦ aemeasurable_id
  exact (hindep.hasLaw_sum_poissonBinomialMeasure fun i ↦
    (measurePreserving_eval (fun i : ι ↦ Ber((1 : ℕ), 0, p i)) i).hasLaw).map_eq

/-- Pushing the product of native Bernoulli laws forward by the sum of the real-cast coordinates
gives the real cast of the Poisson-binomial law. -/
theorem map_sum_natCast_pi_bernoulliMeasure (p : ι → unitInterval) :
    (Measure.pi fun i : ι ↦ Ber((1 : ℕ), 0, p i)).map
        (fun x : ι → ℕ ↦ ∑ i, (x i : ℝ)) =
      (poissonBinomialMeasure p).map (Nat.cast : ℕ → ℝ) := by
  rw [← map_sum_pi_bernoulliMeasure p, Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext x
  simp

/-- The Poisson-binomial law of an empty family is the point mass at zero. -/
@[simp]
theorem poissonBinomialMeasure_of_isEmpty [IsEmpty ι] (p : ι → unitInterval) :
    poissonBinomialMeasure p = Measure.dirac 0 := by
  apply measure_eq_of_pgf_eqOn
  intro z hz
  rw [pgf_poissonBinomialMeasure]
  simp [pgf_def]

/-- Equal success probabilities recover the ordinary binomial distribution. -/
@[simp]
theorem poissonBinomialMeasure_const (p : unitInterval) :
    poissonBinomialMeasure (fun _ : ι ↦ p) = binomial (Fintype.card ι) p := by
  apply measure_eq_of_pgf_eqOn
  intro z hz
  simp [pgf_poissonBinomialMeasure, pgf_binomial]

/-- Adjoining one trial convolves the previous Poisson-binomial law with its Bernoulli law. -/
theorem poissonBinomialMeasure_eq_conv_bernoulliMeasure [DecidableEq ι]
    (j : ι) (p : ι → unitInterval) :
    poissonBinomialMeasure p =
      poissonBinomialMeasure (fun i : {i // i ≠ j} ↦ p i) ∗ Ber((1 : ℕ), 0, p j) := by
  classical
  apply measure_eq_of_pgf_eqOn
  intro z hz
  rw [Measure.pgf_conv_of_abs_le_one _ _ (abs_le.mpr ⟨hz.1.le, hz.2.le⟩)]
  rw [pgf_poissonBinomialMeasure, pgf_poissonBinomialMeasure,
    pgf_bernoulliMeasure]
  let f : ι → ℝ := fun i => 1 - (p i : ℝ) + (p i : ℝ) * z
  have hsubtype : (∏ i : {i // i ≠ j}, f i) = ∏ i ∈ Finset.univ.erase j, f i := by
    exact (Finset.prod_subtype (Finset.univ.erase j) (by simp) f).symm
  calc
    ∏ i, f i = (∏ i ∈ Finset.univ.erase j, f i) * f j := by
      rw [Finset.prod_erase_mul _ _ (Finset.mem_univ j)]
    _ = (∏ i : {i // i ≠ j}, f i) * f j := by rw [hsubtype]

/-- The finite weighted sum defining a Poisson-binomial law, written as a countable measure sum. -/
theorem poissonBinomialMeasure_eq_sum (p : ι → unitInterval) :
    poissonBinomialMeasure p = Measure.sum fun s : Finset ι =>
      (poissonBinomialWeight p s : ℝ≥0∞) • Measure.dirac s.card := by
  simp [poissonBinomialMeasure, Measure.sum_fintype]

/-- The success-set weight is measurable in the vector of success probabilities. -/
@[fun_prop]
theorem measurable_poissonBinomialWeight (s : Finset ι) :
    Measurable fun p : ι → unitInterval ↦ poissonBinomialWeight p s := by
  classical
  apply Continuous.measurable
  simp only [poissonBinomialWeight_def]
  fun_prop

/-- The Poisson-binomial family is measurable in its finite vector of success probabilities. -/
@[fun_prop]
theorem measurable_poissonBinomialMeasure :
    Measurable fun p : ι → unitInterval ↦ poissonBinomialMeasure p := by
  classical
  simp_rw [poissonBinomialMeasure_eq_sum]
  apply TauCeti.MeasureTheory.measurable_sum_smul_dirac
  intro s
  exact measurable_coe_nnreal_ennreal.comp (measurable_poissonBinomialWeight s)

end Probability

end TauCeti

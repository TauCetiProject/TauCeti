/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Data.Fin.Tuple.OrderStatistic
public import TauCeti.Data.Fin.Tuple.Rank
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.UniformOn
import TauCeti.Data.Fin.Tuple.Sort
import TauCeti.MeasureTheory.MeasurableSpace.Sort
import TauCeti.MeasureTheory.Measure.Prod
import TauCeti.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import TauCeti.Probability.Independence.InfinitePi
import TauCeti.Probability.Distributions.OrderStatistic.Joint

/-!
# Ranks of an atomless i.i.d. sample

The sorting permutation and the sorted tuple have a product joint law. Each permutation
labels a chamber that contributes the same measure to the sorted tuple. The resulting uniform
permutation lists the original indices in increasing order of their observations. Its inverse
assigns the rank to each original index.

For the rank vector `TauCeti.rank` this is the law of the ranks: the ranks are uniform on the
permutations and independent of the sorted sample. For a symmetric atomless law on `ℝ`, the signs
of the observations are moreover independent fair coin flips, independent of the absolute ranks
`TauCeti.absRank`, because flipping the signs of some coordinates preserves the law of the
sample and its absolute ranks.

## Main results

* `TauCeti.map_prod_sort_orderStatistics_pi` — the sorting permutation and the sorted sample are
  independent, with the uniform law on the permutations;
* `TauCeti.measure_rank_eq_perm` — the law of the ranks: the ranks are `σ + 1` and the sorted
  sample lies in `A` with probability `(n!)⁻¹` times the probability of the latter;
* `TauCeti.measure_absRank_eq_perm` — the absolute ranks of an atomless sample on `ℝ` are
  uniform on the permutations;
* `TauCeti.measure_signs_absRank_eq` — for a symmetric atomless law on `ℝ`, every sign vector
  and every absolute-rank permutation together have probability `(2ⁿ n!)⁻¹`.

## References

* D. R. Cox and D. V. Hinkley, *Theoretical Statistics*, Chapman and Hall, 1974, Example 2.11.
* A. W. van der Vaart, *Asymptotic Statistics*, Cambridge University Press, 1998, Lemmas 13.1
  and 13.17.
-/

public section

open MeasureTheory ProbabilityTheory Set Function
open scoped ENNReal

namespace TauCeti

variable {α : Type*} [LinearOrder α] [TopologicalSpace α] [OrderClosedTopology α]
  [SecondCountableTopology α] [MeasurableSpace α] [BorelSpace α]
  {n : ℕ} {P : Measure α} [IsProbabilityMeasure P] [NullSingletonClass P]

/-- Restricting the sample to one sorting permutation gives exactly `1 / n!` of the
sorted law. The scaling applies on every measurable set of sorted tuples. -/
theorem map_orderStatistics_pi_restrict_sort_eq (σ : Equiv.Perm (Fin n)) :
    ((Measure.pi fun _ : Fin n ↦ P).restrict {x | Tuple.sort x = σ}).map
        (fun x i ↦ orderStatistic i x) =
      (n.factorial : ℝ≥0∞)⁻¹ •
        (Measure.pi fun _ : Fin n ↦ P).map (fun x i ↦ orderStatistic i x) := by
  have hinj : ∀ᵐ x ∂(Measure.pi fun _ : Fin n ↦ P), Injective x := by
    simpa only [Measure.infinitePi_eq_pi] using
      (Probability.ae_injective_infinitePi (fun _ : Fin n ↦ P))
  have hsets : {x : Fin n → α | Tuple.sort x = σ} =ᵐ[Measure.pi fun _ : Fin n ↦ P]
      {x | StrictMono (x ∘ σ)} := by
    filter_upwards [hinj] with x hx
    exact (Tuple.strictMono_comp_perm_iff_sort_eq hx σ).symm
  rw [Measure.restrict_congr_set hsets, Probability.map_orderStatistics_pi_restrict_strictMono_comp,
    Probability.map_orderStatistics_pi, ← Nat.cast_smul_eq_nsmul ℝ≥0∞, smul_smul,
    ENNReal.inv_mul_cancel (by positivity) (ENNReal.natCast_ne_top _), one_smul]

/-- The probability of a specified sorting permutation and a measurable constraint on
the sorted sample is `1 / n!` times the probability of the constraint alone. -/
theorem measureReal_sort_eq_inter_preimage_orderStatistics (σ : Equiv.Perm (Fin n))
    {B : Set (Fin n → α)} (hB : MeasurableSet B) :
    (Measure.pi fun _ : Fin n ↦ P).real
      ({x | Tuple.sort x = σ} ∩ (fun x i ↦ orderStatistic i x) ⁻¹' B) =
    ((n.factorial : ℝ)⁻¹) *
      (Measure.pi fun _ : Fin n ↦ P).real ((fun x i ↦ orderStatistic i x) ⁻¹' B) := by
  have hS := Measurable.of_eval (fun i : Fin n ↦ measurable_orderStatistic (α := α) i)
  have h := congrArg (fun μ : Measure (Fin n → α) ↦ μ.real B)
    (map_orderStatistics_pi_restrict_sort_eq (P := P) σ)
  simpa [map_measureReal_apply hS hB, measureReal_restrict_apply (hS hB), inter_comm] using h

variable (P) in
/-- **The law of the ranks.** Under an atomless law the rank vector of an i.i.d. sample is
uniform on the permutations and independent of the sorted sample `x ∘ Tuple.sort x`: for every
permutation `σ` and every measurable set `A` of sorted tuples, the event that the ranks are
`σ + 1` and the sorted sample lies in `A` has probability `(n!)⁻¹` times the probability that the
sorted sample lies in `A`. With `A = univ` the rank vector takes each permutation with
probability `(n!)⁻¹`. -/
theorem measure_rank_eq_perm (σ : Equiv.Perm (Fin n)) {A : Set (Fin n → α)}
    (hA : MeasurableSet A) :
    (Measure.pi fun _ : Fin n ↦ P)
        {x | (∀ i, rank x i = (σ i : ℕ) + 1) ∧ (fun i ↦ x (Tuple.sort x i)) ∈ A} =
      ((n.factorial : ℝ≥0∞))⁻¹ *
        (Measure.pi fun _ : Fin n ↦ P) {x | (fun i ↦ x (Tuple.sort x i)) ∈ A} := by
  have hS := Measurable.of_eval (fun i : Fin n ↦ measurable_orderStatistic (α := α) i)
  have hinj : ∀ᵐ x ∂(Measure.pi fun _ : Fin n ↦ P), Injective x := by
    simpa only [Measure.infinitePi_eq_pi] using
      (Probability.ae_injective_infinitePi (fun _ : Fin n ↦ P))
  have hsets : {x : Fin n → α | (∀ i, rank x i = (σ i : ℕ) + 1) ∧
        (fun i ↦ x (Tuple.sort x i)) ∈ A} =ᵐ[Measure.pi fun _ : Fin n ↦ P]
      (fun x i ↦ orderStatistic i x) ⁻¹' A ∩ {x | Tuple.sort x = σ.symm} := by
    filter_upwards [hinj] with x hx
    simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage, orderStatistic_def,
      forall_rank_eq_iff_sort_eq_symm hx, and_comm]
  have h := congrArg (fun μ : Measure (Fin n → α) ↦ μ A)
    (map_orderStatistics_pi_restrict_sort_eq (P := P) σ.symm)
  simp only [Measure.map_apply hS hA, Measure.restrict_apply (hS hA), smul_apply,
    smul_eq_mul] at h
  rw [measure_congr hsets, h]
  simp only [preimage, orderStatistic_def]

/-- Under an atomless law on `ℝ` the vector of absolute ranks of an i.i.d. sample takes each
permutation, shifted by one, with probability `(n!)⁻¹`. -/
theorem measure_absRank_eq_perm (P : Measure ℝ) [IsProbabilityMeasure P] [NullSingletonClass P]
    (σ : Equiv.Perm (Fin n)) :
    (Measure.pi fun _ : Fin n ↦ P) {x | ∀ i, absRank x i = (σ i : ℕ) + 1} =
      ((n.factorial : ℝ≥0∞))⁻¹ := by
  have habs : Measurable fun t : ℝ ↦ |t| := continuous_abs.measurable
  -- The law of `|X|` is atomless: the fibre of `t` under `|·|` is contained in `{t, -t}`.
  have : NullSingletonClass (P.map fun t ↦ |t|) :=
    Measure.nullSingletonClass_map_of_countable_preimage habs.aemeasurable fun t ↦
      ((toFinite {t, -t}).subset fun s hs ↦ by
        rw [mem_preimage, mem_singleton_iff] at hs
        rw [mem_insert_iff, mem_singleton_iff, ← hs]
        rcases abs_choice s with h | h <;> simp [h]).countable
  have : IsProbabilityMeasure (P.map fun t ↦ |t|) :=
    (Measure.isProbabilityMeasure_map_iff habs.aemeasurable).2 inferInstance
  have hmp := measurePreserving_pi (fun _ : Fin n ↦ P) (fun _ ↦ P.map fun t ↦ |t|)
    fun _ ↦ habs.measurePreserving P
  have h := measure_rank_eq_perm (P.map fun t ↦ |t|) σ MeasurableSet.univ
  simp only [mem_univ, and_true, ofPred_true, measure_univ, mul_one] at h
  have hmeas : MeasurableSet {y : Fin n → ℝ | ∀ i, rank y i = (σ i : ℕ) + 1} :=
    measurableSet_setOfPred.2 (Measurable.forall fun i ↦ (measurable_rank i).eq measurable_const)
  rw [← h, ← hmp.measure_preimage hmeas.nullMeasurableSet]
  simp only [preimage, absRank_eq_rank, mem_ofPred_eq]

/-- The event that an i.i.d. sample on `ℝ` has signs `b` and absolute ranks `σ + 1` is
measurable. -/
private theorem measurableSet_signs_absRank (b : Fin n → Bool) (σ : Equiv.Perm (Fin n)) :
    MeasurableSet
      {x : Fin n → ℝ | (∀ i, decide (0 < x i) = b i) ∧ ∀ i, absRank x i = (σ i : ℕ) + 1} := by
  refine measurableSet_setOfPred.2 (Measurable.and (Measurable.forall fun i ↦ ?_)
    (Measurable.forall fun i ↦ ?_))
  · have hlt : MeasurableSet {x : Fin n → ℝ | 0 < x i} :=
      measurableSet_lt measurable_const (measurable_pi_apply i)
    exact (measurable_to_bool (by simpa only [preimage, mem_singleton_iff, decide_eq_true_eq] using
      hlt)).eq measurable_const
  · exact (measurable_absRank i).eq measurable_const

/-- The event that the signs of an i.i.d. sample from a symmetric atomless law on `ℝ` are `b`
and its absolute ranks are `σ + 1` has a probability that does not depend on `b`. -/
private theorem measure_signs_absRank_eq_measure_signs_absRank (P : Measure ℝ)
    [IsProbabilityMeasure P] [NullSingletonClass P] (hsymm : P.map Neg.neg = P)
    (σ : Equiv.Perm (Fin n)) (b b' : Fin n → Bool) :
    (Measure.pi fun _ : Fin n ↦ P)
        {x | (∀ i, decide (0 < x i) = b' i) ∧ ∀ i, absRank x i = (σ i : ℕ) + 1} =
      (Measure.pi fun _ : Fin n ↦ P)
        {x | (∀ i, decide (0 < x i) = b i) ∧ ∀ i, absRank x i = (σ i : ℕ) + 1} := by
  -- Flipping the sign of the coordinates where `b` and `b'` differ preserves the law of the
  -- sample and the absolute ranks, and off the null set where a coordinate vanishes it turns
  -- the signs `b` into the signs `b'`.
  let g : Fin n → ℝ → ℝ := fun i ↦ if b i = b' i then id else Neg.neg
  have hf : MeasurePreserving (fun x i ↦ g i (x i)) (Measure.pi fun _ ↦ P)
      (Measure.pi fun _ ↦ P) :=
    measurePreserving_pi _ _ fun i ↦ by
      simp only [g]
      split_ifs
      exacts [MeasurePreserving.id P, ⟨measurable_neg, hsymm⟩]
  rw [← hf.measure_preimage (measurableSet_signs_absRank b σ).nullMeasurableSet]
  refine measure_congr ?_
  filter_upwards [ae_all_iff.2 fun i ↦ Measure.ae_eval_ne (fun _ ↦ P) i 0] with x hx
  have habs : absRank (fun i ↦ g i (x i)) = absRank x := absRank_congr fun j ↦ by
    simp only [g]
    split_ifs <;> simp
  simp only [mem_preimage, mem_ofPred_eq, habs]
  refine and_congr_left' (forall_congr' fun i ↦ ?_)
  simp only [g]
  rcases (hx i).lt_or_gt with h | h <;> by_cases hb : b i = b' i <;>
    simp [hb, h, h.not_gt, Bool.eq_not_iff, ne_comm]

/-- **Signed ranks.** Under a symmetric atomless law on `ℝ` the signs `1_{0 < x i}` of an
i.i.d. sample are independent fair Bernoulli variables, independent of the vector of absolute
ranks, which takes each permutation, shifted by one, with probability `(n!)⁻¹`: every sign
vector `b` and permutation `σ` together have probability `(2ⁿ n!)⁻¹`. -/
theorem measure_signs_absRank_eq (P : Measure ℝ) [IsProbabilityMeasure P]
    [NullSingletonClass P] (hsymm : P.map Neg.neg = P) (b : Fin n → Bool)
    (σ : Equiv.Perm (Fin n)) :
    (Measure.pi fun _ : Fin n ↦ P)
        {x | (∀ i, decide (0 < x i) = b i) ∧ ∀ i, absRank x i = (σ i : ℕ) + 1} =
      ((2 ^ n * n.factorial : ℕ) : ℝ≥0∞)⁻¹ := by
  let E : (Fin n → Bool) → Set (Fin n → ℝ) := fun b ↦
    {x | (∀ i, decide (0 < x i) = b i) ∧ ∀ i, absRank x i = (σ i : ℕ) + 1}
  -- The absolute-rank event is the disjoint union of the events `E b` over the sign vectors.
  have hunion : {x : Fin n → ℝ | ∀ i, absRank x i = (σ i : ℕ) + 1} = ⋃ b, E b := by
    ext x
    simp only [E, mem_iUnion, mem_ofPred_eq]
    exact ⟨fun h ↦ ⟨fun i ↦ decide (0 < x i), fun _ ↦ rfl, h⟩, fun ⟨_, _, h⟩ ↦ h⟩
  have hdisj : Pairwise (Disjoint on E) := fun b b' hbb' ↦ disjoint_left.2 fun x hb hb' ↦
    hbb' (funext fun i ↦ (hb.1 i).symm.trans (hb'.1 i))
  have h := measure_iUnion hdisj (fun b ↦ measurableSet_signs_absRank b σ)
    (μ := Measure.pi fun _ : Fin n ↦ P)
  -- Each of the `2 ^ n` sign events has the same probability, and they add up to `(n!)⁻¹`.
  rw [← hunion, measure_absRank_eq_perm, tsum_fintype,
    Finset.sum_congr rfl fun b' _ ↦ measure_signs_absRank_eq_measure_signs_absRank P hsymm σ b b'
    ] at h
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat] at h
  rw [Nat.cast_mul, ENNReal.mul_inv (by simp) (by simp), h, Nat.cast_pow, Nat.cast_ofNat,
    ENNReal.inv_mul_cancel_left (by simp) (by simp)]

variable [MeasurableSpace (Equiv.Perm (Fin n))] [MeasurableSingletonClass (Equiv.Perm (Fin n))]

/-- The joint law of the sorting permutation and the vector of ordered observations is
the product of the uniform permutation law and the law of the ordered observations. -/
theorem map_prod_sort_orderStatistics_pi :
    (Measure.pi fun _ : Fin n ↦ P).map (fun x ↦ (Tuple.sort x, fun i ↦ orderStatistic i x)) =
      (uniformOn univ).prod
        ((Measure.pi fun _ : Fin n ↦ P).map (fun x i ↦ orderStatistic i x)) := by
  let ρ := Measure.pi fun _ : Fin n ↦ P
  let S : (Fin n → α) → Fin n → α := fun x i ↦ orderStatistic i x
  let J := ρ.map (fun x ↦ (Tuple.sort x, S x))
  let Q : Measure (Equiv.Perm (Fin n) × (Fin n → α)) := (uniformOn univ).prod (ρ.map S)
  have hS : Measurable S := Measurable.of_eval measurable_orderStatistic
  have hJ : Measurable (fun x ↦ (Tuple.sort x, S x)) := Tuple.measurable_sort.prodMk hS
  refine Measure.ext_prod fun {A B} hA hB ↦ ?_
  -- For a fixed B, the two measures on permutations agree at every singleton.
  have hsections : ((J.restrict (univ ×ˢ B)).map Prod.fst) =
      ((Q.restrict (univ ×ˢ B)).map Prod.fst) := by
    refine Measure.ext_of_singleton fun σ ↦ ?_
    simp only [Measure.map_fst_restrict_prod_apply _ _ _ (measurableSet_singleton σ), inter_univ]
    have hσ : (uniformOn univ : Measure (Equiv.Perm (Fin n))) {σ} =
        (n.factorial : ℝ≥0∞)⁻¹ := by
      simp [uniformOn_univ, Fintype.card_perm]
    have h : ((ρ.restrict {x | Tuple.sort x = σ}).map S) B =
        ((n.factorial : ℝ≥0∞)⁻¹ • ρ.map S) B :=
      congrArg (fun μ : Measure (Fin n → α) ↦ μ B)
        (map_orderStatistics_pi_restrict_sort_eq (P := P) σ)
    rw [Measure.map_apply hS hB, Measure.restrict_apply (hS hB), smul_apply, smul_eq_mul] at h
    simpa only [J, Q, Measure.map_apply hJ ((measurableSet_singleton σ).prod hB),
      mk_preimage_prod, preimage_singleton, Measure.prod_prod, hσ, inter_comm] using h
  simpa only [Measure.map_fst_restrict_prod_apply _ _ _ hA, inter_univ] using
    congrArg (fun μ : Measure (Equiv.Perm (Fin n)) ↦ μ A) hsections

/-- The sorting permutation of an atomless i.i.d. sample is uniformly distributed. -/
theorem map_sort_pi_eq_uniformOn :
    (Measure.pi fun _ : Fin n ↦ P).map Tuple.sort =
      (uniformOn univ : Measure (Equiv.Perm (Fin n))) := by
  have hS := Measurable.of_eval (fun i : Fin n ↦ measurable_orderStatistic (α := α) i)
  have h := congrArg (Measure.map Prod.fst) (map_prod_sort_orderStatistics_pi (P := P) (n := n))
  have : IsProbabilityMeasure ((Measure.pi fun _ : Fin n ↦ P).map
      (fun x i ↦ orderStatistic i x)) :=
    (Measure.isProbabilityMeasure_map_iff hS.aemeasurable).2 inferInstance
  simpa [Measure.map_map measurable_fst (Tuple.measurable_sort.prodMk hS), Function.comp_def]
    using h

/-- The sorting permutation is independent of the ordered observations in an atomless
i.i.d. sample. -/
theorem indepFun_sort_orderStatistics_pi :
    IndepFun Tuple.sort (fun x i ↦ orderStatistic i x) (Measure.pi fun _ : Fin n ↦ P) := by
  have hS := Measurable.of_eval (fun i : Fin n ↦ measurable_orderStatistic (α := α) i)
  rw [indepFun_iff_map_prod_eq_prod_map_map Tuple.measurable_sort.aemeasurable hS.aemeasurable,
    map_sort_pi_eq_uniformOn]
  exact map_prod_sort_orderStatistics_pi

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Data.Fin.Tuple.OrderStatistic
public import TauCeti.MeasureTheory.MeasurableSpace.StrictMono
public import TauCeti.Probability.Distributions.Uniform.Basic
import TauCeti.Probability.Independence.InfinitePi

/-!
# Joint laws of order statistics

Sorting an iid sample from an atomless law restricts its product law to the strictly
increasing chamber and multiplies it by the factorial of the sample size. For unit
uniform samples this gives density `n!` on the ordered open unit cube, relative to
product Lebesgue measure. The joint density, unlike the individual beta marginals,
retains the dependence needed to compute the law of the spacings.

The chamber decomposition uses Mathlib's `Tuple.sort` and measure-preserving
coordinate permutations. Ties form a null set by
`TauCeti.Probability.ae_eval_ne_eval_infinitePi`.

## References

* H. A. David and H. N. Nagaraja, *Order Statistics*, 3rd ed., Wiley, 2003, §2.1.
-/

public section

open MeasureTheory ProbabilityTheory Set Function
open scoped ENNReal

namespace TauCeti.Probability

section Atomless

variable {α : Type*} [LinearOrder α] [TopologicalSpace α] [OrderClosedTopology α]
  [SecondCountableTopology α] [MeasurableSpace α] [BorelSpace α]
  {n : ℕ} {μ : Measure α} [IsProbabilityMeasure μ] [NullSingletonClass μ]

/-- Sorting an atomless iid sample multiplies the product law restricted to the strictly
increasing chamber by `n!`. This includes the empty sample. -/
theorem map_orderStatistics_pi :
    (Measure.pi fun _ : Fin n => μ).map (fun x i => orderStatistic i x) =
      n.factorial • (Measure.pi fun _ : Fin n => μ).restrict {x | StrictMono x} := by
  classical
  let ρ := Measure.pi fun _ : Fin n => μ
  let S : (Fin n → α) → (Fin n → α) := fun x i => orderStatistic i x
  let C : Equiv.Perm (Fin n) → Set (Fin n → α) := fun σ => {x | StrictMono (x ∘ σ)}
  have hS : Measurable S := by fun_prop
  have hmono : MeasurableSet {x : Fin n → α | StrictMono x} := measurableSet_setOf_strictMono
  have hC (σ) : MeasurableSet (C σ) :=
    hmono.preimage (Measurable.of_eval fun i => measurable_pi_apply (σ i))
  -- The chambers are disjoint, and sorting covers every tuple with distinct entries.
  have hdis : Pairwise (Disjoint on C) := by
    intro σ τ hστ
    refine disjoint_left.mpr fun x hxσ hxτ => hστ ?_
    have heq := Tuple.unique_monotone hxσ.monotone hxτ.monotone
    have hinj : Injective x := hxσ.injective.of_comp_right σ.surjective
    exact DFunLike.ext _ _ fun i => hinj (congrFun heq i)
  have hcover : ∀ᵐ x ∂ρ, x ∈ ⋃ σ, C σ := by
    have hne : ∀ᵐ x ∂ρ, ∀ i j : Fin n, i ≠ j → x i ≠ x j := by
      refine ae_all_iff.mpr fun i => ae_all_iff.mpr fun j => ?_
      by_cases hij : i = j
      · exact Filter.Eventually.of_forall fun _ h => (h hij).elim
      · simpa only [Measure.infinitePi_eq_pi] using
          (ae_eval_ne_eval_infinitePi (fun _ : Fin n => μ) hij).mono fun _ hx _ => hx
    filter_upwards [hne] with x hx
    refine mem_iUnion.mpr ⟨Tuple.sort x, ?_⟩
    exact (Tuple.monotone_sort x).strictMono_of_injective
      ((injective_iff_pairwise_ne.mpr hx).comp (Tuple.sort x).injective)
  have hpart : ρ = Measure.sum fun σ => ρ.restrict (C σ) := by
    rw [← Measure.restrict_iUnion hdis hC, Measure.restrict_eq_self_of_ae_mem hcover]
  have hmap (σ : Equiv.Perm (Fin n)) :
      (ρ.restrict (C σ)).map S = ρ.restrict {x | StrictMono x} := by
    have hperm : MeasurePreserving (fun x : Fin n → α => x ∘ σ) ρ ρ := by
      convert measurePreserving_piCongrLeft (fun _ : Fin n => μ) σ.symm using 1
      funext x i
      simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
    conv_rhs => rw [← hperm.map_eq, Measure.restrict_map hperm.measurable hmono]
    apply Measure.map_congr
    filter_upwards [ae_restrict_mem (hC σ)] with x hx
    funext i
    simp only [S, orderStatistic_def]
    exact congrFun (Tuple.unique_monotone (Tuple.monotone_sort x) hx.monotone) i
  -- Every chamber has the same sorted image, so summing contributes the factorial.
  calc
    ρ.map S = (Measure.sum fun σ => ρ.restrict (C σ)).map S := congrArg (Measure.map S) hpart
    _ = Measure.sum fun _ : Equiv.Perm (Fin n) => ρ.restrict {x | StrictMono x} := by
      rw [Measure.map_sum hS.aemeasurable]
      simp_rw [hmap]
    _ = n.factorial • ρ.restrict {x | StrictMono x} := by
      rw [Measure.sum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_perm,
        Fintype.card_fin]

end Atomless

/-- The joint density of the increasingly sorted unit-uniform sample is `n!` on the
strictly increasing open unit cube and zero elsewhere, relative to product volume.
The formula also holds for the empty tuple. -/
theorem map_orderStatistics_pi_uniformMeasure (n : ℕ) :
    (Measure.pi fun _ : Fin n => uniformMeasure 0 1).map (fun x i => orderStatistic i x) =
      volume.withDensity
        ({y : Fin n → ℝ | StrictMono y ∧ ∀ i, y i ∈ Ioo (0 : ℝ) 1}.indicator
          fun _ => (n.factorial : ℝ≥0∞)) := by
  classical
  let _ := isProbabilityMeasure_uniformMeasure (a := 0) (b := 1) zero_lt_one
  let _ : NullSingletonClass (uniformMeasure 0 1) := by
    rw [uniformMeasure_eq_withDensity]
    infer_instance
  have hunit : uniformMeasure 0 1 = volume.restrict (Ioo (0 : ℝ) 1) := by
    rw [uniformMeasure_eq_smul]
    norm_num
    exact restrict_Ioo_eq_restrict_Ioc.symm
  have hprod : (Measure.pi fun _ : Fin n => uniformMeasure 0 1) =
      volume.restrict (univ.pi fun _ : Fin n => Ioo (0 : ℝ) 1) := by
    simp_rw [hunit]
    exact (Measure.restrict_pi_pi _ _).symm
  rw [map_orderStatistics_pi, hprod,
    withDensity_indicator (measurableSet_strictMono_mem_Ioo n 0 1), withDensity_const]
  have hsets : {y : Fin n → ℝ | StrictMono y} ∩
      (univ.pi fun _ : Fin n => Ioo (0 : ℝ) 1) =
        {y | StrictMono y ∧ ∀ i, y i ∈ Ioo (0 : ℝ) 1} := by
    ext y
    simp
  rw [Measure.restrict_restrict' (MeasurableSet.univ_pi fun _ => measurableSet_Ioo),
    hsets, Nat.cast_smul_eq_nsmul]

/-- The sorted tuple of independent unit-uniform variables has the ordered-cube joint
density. No independence is asserted for the sorted coordinates. -/
theorem hasLaw_orderStatistics_iid_uniformMeasure {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {n : ℕ} {X : Fin n → Ω → ℝ} (hindep : iIndepFun X P)
    (hlaw : ∀ i, HasLaw (X i) (uniformMeasure 0 1) P) :
    HasLaw (fun ω i => orderStatistic i (fun j => X j ω))
      (volume.withDensity
        ({y : Fin n → ℝ | StrictMono y ∧ ∀ i, y i ∈ Ioo (0 : ℝ) 1}.indicator
          fun _ => (n.factorial : ℝ≥0∞))) P := by
  rw [← map_orderStatistics_pi_uniformMeasure]
  have hs : Measurable (fun x : Fin n → ℝ => fun i => orderStatistic i x) := by fun_prop
  exact (hasLaw_map hs.aemeasurable).comp
    (hindep.hasLaw_pi hlaw)

end TauCeti.Probability

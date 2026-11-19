/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Data.Fin.Tuple.OrderStatistic
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.UniformOn
import TauCeti.Data.Fin.Tuple.Sort
import TauCeti.MeasureTheory.MeasurableSpace.Sort
import TauCeti.MeasureTheory.Measure.Prod
import TauCeti.Probability.Independence.InfinitePi
import TauCeti.Probability.Distributions.OrderStatistic.Joint

/-!
# Ranks of an atomless i.i.d. sample

The sorting permutation and the sorted tuple have a product joint law. Each permutation
labels a chamber that contributes the same measure to the sorted tuple. The resulting uniform
permutation lists the original indices in increasing order of their observations. Its inverse
assigns the rank to each original index.

## References

* D. R. Cox and D. V. Hinkley, *Theoretical Statistics*, Chapman and Hall, 1974, Example 2.11.
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

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Data.Fin.Tuple.OrderStatistic
public import TauCeti.MeasureTheory.MeasurableSpace.StrictMono
public import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Data.Fintype.Perm

/-!
# Joint laws of order statistics

Sorting an iid sample from an atomless σ-finite law restricts its product law to the strictly
increasing chamber and multiplies it by the factorial of the sample size. No normalization is
needed, so the formula also holds for Lebesgue measure. The densities of the order statistics,
including the unit-uniform case, are in
`TauCeti/Probability/Distributions/OrderStatistic/Density.lean`.

The chamber decomposition uses Mathlib's `Tuple.sort` and measure-preserving
coordinate permutations. Ties form a null set by `TauCeti.Probability.ae_eval_ne_eval_pi`: under
a finite product of σ-finite measures, two coordinates almost surely differ when the law of one
of them has no atoms; in particular almost every sample is injective
(`TauCeti.Probability.ae_injective_pi`).

## Main results

* `TauCeti.Probability.ae_eval_ne_eval_pi`, `TauCeti.Probability.ae_injective_pi` — ties are null;
* `TauCeti.Probability.map_orderStatistics_pi` — the joint law of the order statistics.

## References

* H. A. David and H. N. Nagaraja, *Order Statistics*, 3rd ed., Wiley, 2003, §2.1.
-/

public section

open MeasureTheory Set Function
open scoped ENNReal

namespace TauCeti.Probability

/-- **Two coordinates of a finite product are almost surely distinct when one law is atomless.**
Under a product of σ-finite measures on a space with a measurable diagonal, two distinct
coordinates `i` and `j` of a sample almost surely take different values as soon as the measure at
`j` has no atoms. -/
theorem ae_eval_ne_eval_pi {n : ℕ} {β : Type*} [MeasurableSpace β] [MeasurableEq β]
    (μ : Fin n → Measure β) [∀ i, SigmaFinite (μ i)] {i j : Fin n} [NullSingletonClass (μ j)]
    (hij : i ≠ j) : ∀ᵐ x ∂Measure.pi μ, x i ≠ x j := by
  cases n with
  | zero => exact i.elim0
  | succ n =>
    obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hij
    have hdiag : MeasurableSet {p : β × (Fin n → β) | p.2 k = p.1} :=
      measurableSet_eq_fun ((measurable_pi_apply k).comp measurable_snd) measurable_fst
    -- Splitting off the coordinate `j`, the tie set is a graph over the other coordinates.
    have hset : {x : Fin (n + 1) → β | ¬x (j.succAbove k) ≠ x j} =
        MeasurableEquiv.piFinSuccAbove (fun _ => β) j ⁻¹' {p | p.2 k = p.1} := by
      ext x
      simp [MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv, Fin.removeNth]
    rw [ae_iff, hset, (measurePreserving_piFinSuccAbove μ j).measure_preimage
      hdiag.nullMeasurableSet, Measure.prod_apply_symm hdiag]
    simp

/-- Under a finite product of copies of an atomless σ-finite measure on a space with a
measurable diagonal, almost every sample has distinct entries. -/
theorem ae_injective_pi {n : ℕ} {β : Type*} [MeasurableSpace β] [MeasurableEq β]
    (μ : Measure β) [SigmaFinite μ] [NullSingletonClass μ] :
    ∀ᵐ x ∂(Measure.pi fun _ : Fin n => μ), Injective x := by
  have h : ∀ᵐ x ∂(Measure.pi fun _ : Fin n => μ), ∀ i j : Fin n, i ≠ j → x i ≠ x j := by
    refine ae_all_iff.mpr fun i => ae_all_iff.mpr fun j => ?_
    by_cases hij : i = j
    · exact Filter.Eventually.of_forall fun _ h => (h hij).elim
    · exact (ae_eval_ne_eval_pi (fun _ : Fin n => μ) hij).mono fun _ hx _ => hx
  filter_upwards [h] with x hx
  exact injective_iff_pairwise_ne.mpr hx

section Atomless

variable {α : Type*} [LinearOrder α] [TopologicalSpace α] [OrderClosedTopology α]
  [SecondCountableTopology α] [MeasurableSpace α] [BorelSpace α]
  {n : ℕ} {μ : Measure α} [SigmaFinite μ] [NullSingletonClass μ]

/-- Sorting an iid sample from an atomless σ-finite measure multiplies the product measure
restricted to the strictly increasing chamber by `n!`. This includes the empty sample. -/
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
    filter_upwards [ae_injective_pi μ] with x hx
    refine mem_iUnion.mpr ⟨Tuple.sort x, ?_⟩
    exact (Tuple.monotone_sort x).strictMono_of_injective (hx.comp (Tuple.sort x).injective)
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

end TauCeti.Probability

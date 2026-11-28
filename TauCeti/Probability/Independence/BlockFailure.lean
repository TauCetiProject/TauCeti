/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.MeasureTheory.Constructions.Pi
import TauCeti.MeasureTheory.Constructions.Pi
import TauCeti.Probability.Independence.DisjointBlocks

/-!
# Failure probabilities for disjoint blocks of a product sample

To bound joint failure with a prescribed coordinate, omit the one block that can see that
coordinate. The failure probabilities of the remaining blocks multiply, even if the coordinate
being prescribed has zero probability of taking the prescribed value.
-/

public section

open MeasureTheory ProbabilityTheory Set

namespace TauCeti.Probability

/-- In a product sample, prescribing a coordinate outside a family of disjoint blocks and
prescribing an event in each block has probability equal to the product of the individual
probabilities. The block events need not be identical. -/
theorem measureReal_inter_iInter_preimage_blocks {α ι κ β : Type*} [Fintype α] [Fintype ι]
    [MeasurableSpace β] (μ : α → Measure β) [∀ i, IsProbabilityMeasure (μ i)]
    (e : ι × κ ↪ α) {a : α} (ha : a ∉ range e) {B : Set β} (hB : MeasurableSet B)
    (A : ι → Set (κ → β)) (hA : ∀ i, MeasurableSet (A i)) :
    (Measure.pi μ).real ((fun x ↦ x a) ⁻¹' B ∩
        ⋂ i, (fun x j ↦ x (e (i, j))) ⁻¹' A i) =
      (Measure.pi μ).real ((fun x ↦ x a) ⁻¹' B) *
        ∏ i, (Measure.pi μ).real ((fun x j ↦ x (e (i, j))) ⁻¹' A i) := by
  classical
  rcases isEmpty_or_nonempty ι with h | h
  · simp
  let : Finite κ := Finite.of_injective (fun j ↦ e (Classical.arbitrary ι, j))
    (fun _ _ hij ↦ congrArg Prod.snd (e.injective hij))
  let := Fintype.ofFinite κ
  let F (x : α → β) (i : ι) (j : κ) := x (e (i, j))
  let ν (i : ι) := Measure.pi fun j ↦ μ (e (i, j))
  have hF : MeasurePreserving F (Measure.pi μ) (Measure.pi ν) :=
    (measurePreserving_curry fun i j ↦ μ (e (i, j))).comp
      (measurePreserving_pi_comp_embedding μ e)
  have hind : IndepFun (fun x : α → β ↦ x a) F (Measure.pi μ) := by
    refine indepFun_of_measurable_blockSigma (Z := fun i (x : α → β) ↦ x i)
      ((iIndepFun_pi (μ := μ) (X := fun _ ↦ id) fun _ ↦ aemeasurable_id).precomp
        Subtype.val_injective) (fun i _ ↦ measurable_pi_apply i)
      (disjoint_singleton_left.mpr ha) ?_ ?_
    · exact measurable_blockSigma_of_mem (Z := fun i (x : α → β) ↦ x i) (mem_singleton a)
    · let m := blockSigma (fun i (x : α → β) ↦ x i) (range e)
      exact @Measurable.of_eval _ _ _ m _ _ fun i ↦ @Measurable.of_eval _ _ _ m _ _ fun j ↦
        measurable_blockSigma_of_mem (Z := fun i (x : α → β) ↦ x i) (mem_range_self (i, j))
  have hpre : F ⁻¹' (univ.pi A) = ⋂ i, (fun x j ↦ x (e (i, j))) ⁻¹' A i := by
    ext x
    simp [F]
  have hpi : (Measure.pi μ) (F ⁻¹' univ.pi A) = ∏ i, ν i (A i) := by
    rw [hF.measure_preimage (MeasurableSet.univ_pi hA).nullMeasurableSet, Measure.pi_pi]
  rw [← hpre, measureReal_def,
    hind.measure_inter_preimage_eq_mul B (univ.pi A) hB (MeasurableSet.univ_pi hA),
    hpi, ENNReal.toReal_mul, ENNReal.toReal_prod]
  congr 1
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  exact (((measurePreserving_eval ν i).comp hF).measureReal_preimage (hA i).nullMeasurableSet).symm

/-- If each of a finite family of disjoint blocks succeeds with probability at least `q`, the
joint probability that all blocks fail and a distinguished coordinate lies in `B` is at most
`P(B) * (1 - q) ^ (number of blocks - 1)`. The coordinate can be outside all the blocks; no
positivity assumption on `P(B)` is required. -/
theorem measureReal_inter_iInter_compl_preimage_blocks_le {α ι κ β : Type*} [Fintype α]
    [Fintype ι] [MeasurableSpace β] (μ : α → Measure β)
    [∀ i, IsProbabilityMeasure (μ i)] (e : ι × κ ↪ α) (a : α) {B : Set β} (hB : MeasurableSet B)
    (A : ι → Set (κ → β)) (hA : ∀ i, MeasurableSet (A i)) (q : unitInterval)
    (hprob : ∀ i, (q : ℝ) ≤ (Measure.pi μ).real ((fun x j ↦ x (e (i, j))) ⁻¹' A i)) :
    (Measure.pi μ).real ((fun x ↦ x a) ⁻¹' B ∩
        ⋂ i, (fun x j ↦ x (e (i, j))) ⁻¹' (A i)ᶜ) ≤
      (Measure.pi μ).real ((fun x ↦ x a) ⁻¹' B) * (1 - (q : ℝ)) ^ (Fintype.card ι - 1) := by
  classical
  let U : Finset ι := Finset.univ.filter fun i ↦ ∃ j, e (i, j) = a
  let T : Finset ι := Finset.univ.filter fun i ↦ ¬ ∃ j, e (i, j) = a
  have hU : U.card ≤ 1 := by
    refine Finset.card_le_one.mpr fun i hi k hk ↦ ?_
    obtain ⟨j, hj⟩ := (Finset.mem_filter.mp hi).2
    obtain ⟨l, hl⟩ := (Finset.mem_filter.mp hk).2
    exact congrArg Prod.fst (e.injective (hj.trans hl.symm))
  have hT : Fintype.card ι - 1 ≤ Fintype.card T := by
    rw [Fintype.card_coe]
    have hcard := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset ι))
      (fun i ↦ ∃ j, e (i, j) = a)
    have hsum : U.card + T.card = Fintype.card ι := hcard.trans Finset.card_univ
    omega
  let eT : T × κ ↪ α := (Function.Embedding.prodMap ⟨Subtype.val, Subtype.val_injective⟩
    (Function.Embedding.refl κ)).trans e
  have haT : a ∉ range eT := by
    rintro ⟨⟨i, j⟩, hij⟩
    exact (Finset.mem_filter.mp i.property).2 ⟨j, hij⟩
  -- Discarding any block that reads `a` enlarges the joint failure event.
  have hsub : (⋂ i, (fun x : α → β => fun j ↦ x (e (i, j))) ⁻¹' (A i)ᶜ) ⊆
      ⋂ i : T, (fun x j ↦ x (eT (i, j))) ⁻¹' (A i.val)ᶜ :=
    subset_iInter fun i ↦ iInter_subset _ i.val
  refine (measureReal_mono (Set.inter_subset_inter_right _ hsub)).trans ?_
  rw [measureReal_inter_iInter_preimage_blocks μ eT haT hB (fun i ↦ (A i.val)ᶜ)
    (fun i ↦ (hA i.val).compl)]
  refine mul_le_mul_of_nonneg_left ?_ measureReal_nonneg
  calc
    _ ≤ ∏ _i : T, (1 - (q : ℝ)) := by
      refine Finset.prod_le_prod₀ (fun _ _ ↦ measureReal_nonneg) fun i _ ↦ ?_
      rw [Set.preimage_compl, probReal_compl_eq_one_sub ((hA i.val).preimage (by fun_prop))]
      exact sub_le_sub_left (hprob i.val) 1
    _ = (1 - (q : ℝ)) ^ Fintype.card T := by simp
    _ ≤ _ := pow_le_pow_of_le_one (sub_nonneg.mpr (unitInterval.le_one q))
      (sub_le_self 1 (unitInterval.nonneg q)) hT

end TauCeti.Probability

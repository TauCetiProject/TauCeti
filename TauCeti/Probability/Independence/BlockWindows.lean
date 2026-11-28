/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Independence.DisjointBlocks
public import Mathlib.MeasureTheory.Measure.Real

/-!
# Failure probabilities in windows of independent blocks

If each block has a success event, measurable in that block, a window of `m + 1` disjoint
blocks offers at least `m` independent chances even after excluding the block that reads a
specified conditioning coordinate. Here a window is just a finite set of block indices.
-/

public section

open MeasureTheory Set
open scoped Finset

namespace TauCeti.Probability

variable {Ω ι κ : Type*} [MeasurableSpace Ω] {β : ι → Type*} [∀ i, MeasurableSpace (β i)]
  {μ : Measure Ω} {X : ∀ i, Ω → β i}

/-- Events read from pairwise disjoint blocks of an independent family factor over any finite
collection of the blocks. -/
theorem _root_.ProbabilityTheory.iIndepFun.measure_biInter_eq_prod_of_blockSigma
    (hX : ProbabilityTheory.iIndepFun X μ) (hmX : ∀ i, Measurable (X i))
    {B : κ → Set ι} {E : κ → Set Ω} {s : Finset κ}
    (hB : (↑s : Set κ).PairwiseDisjoint B)
    (hE : ∀ j ∈ s, MeasurableSet[blockSigma X (B j)] (E j)) :
    μ (⋂ j ∈ s, E j) = ∏ j ∈ s, μ (E j) := by
  classical
  have := hX.isProbabilityMeasure
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hj ih =>
    let U := ⋃ k ∈ s, B k
    have hdis : Disjoint (B j) U := by
      refine Set.disjoint_iUnion_right.mpr fun k ↦ Set.disjoint_iUnion_right.mpr fun hk ↦ ?_
      exact hB (Finset.mem_insert_self j s) (Finset.mem_insert_of_mem hk) (by aesop)
    have hmeas : MeasurableSet[blockSigma X U] (⋂ k ∈ s, E k) :=
      s.measurableSet_biInter fun k hk ↦
        blockSigma_mono (subset_iUnion₂ k hk) _ (hE k (Finset.mem_insert_of_mem hk))
    have hind := (indep_blockSigma_of_disjoint hX hmX hdis).indepSet_of_measurableSet
      (hE j (Finset.mem_insert_self j s)) hmeas
    rw [Finset.set_biInter_insert, hind.measure_inter_eq_mul, Finset.prod_insert hj,
      ih (hB.subset (Finset.subset_insert j s)) (fun k hk ↦ hE k (Finset.mem_insert_of_mem hk))]

/-- The probability that `A` occurs and no block in the window `s` succeeds is at most
`P(A) * (1 - q)^m`. Each block has success probability at least `q`, and `A` depends on only
one coordinate, which can affect at most one block in the window. -/
theorem measureReal_inter_biInter_compl_le_of_blockSigma
    (hX : ProbabilityTheory.iIndepFun X μ) (hmX : ∀ i, Measurable (X i))
    {B : κ → Set ι} {E : κ → Set Ω} {s : Finset κ}
    (hB : (↑s : Set κ).PairwiseDisjoint B)
    (hE : ∀ j ∈ s, MeasurableSet[blockSigma X (B j)] (E j))
    {i : ι} {A : Set Ω} (hA : MeasurableSet[blockSigma X {i}] A)
    {q : unitInterval} (hq : ∀ j ∈ s, (q : ℝ) ≤ μ.real (E j))
    {m : ℕ} (hm : m < #s) :
    μ.real (A ∩ ⋂ j ∈ s, (E j)ᶜ) ≤ μ.real A * (1 - q : ℝ) ^ m := by
  classical
  have := hX.isProbabilityMeasure
  let t := s.filter fun j ↦ i ∉ B j
  let U := ⋃ j ∈ t, B j
  have hsub : t ⊆ s := Finset.filter_subset _ _
  have hcard : m ≤ #t := by
    have hbad : #(s.filter fun j ↦ i ∈ B j) ≤ 1 := by
      refine Finset.card_le_one_iff.mpr fun {j k} hj hk ↦ ?_
      obtain ⟨hjs, hji⟩ := Finset.mem_filter.mp hj
      obtain ⟨hks, hki⟩ := Finset.mem_filter.mp hk
      by_contra hne
      exact Set.disjoint_left.mp (hB hjs hks hne) hji hki
    have htotal : #(s.filter fun j ↦ i ∈ B j) + #t = #s :=
      Finset.card_filter_add_card_filter_not _
    omega
  have hdis : Disjoint {i} U := by
    simp [U, t, Set.disjoint_singleton_left]
  have htE (j : κ) (hj : j ∈ t) : MeasurableSet[blockSigma X (B j)] (E j)ᶜ :=
    (hE j (hsub hj)).compl
  have hmeas : MeasurableSet[blockSigma X U] (⋂ j ∈ t, (E j)ᶜ) :=
    t.measurableSet_biInter fun j hj ↦ blockSigma_mono (subset_iUnion₂ j hj) _ (htE j hj)
  have hind := (indep_blockSigma_of_disjoint hX hmX hdis).indepSet_of_measurableSet hA hmeas
  calc
    _ ≤ μ.real (A ∩ ⋂ j ∈ t, (E j)ᶜ) :=
      measureReal_mono (Set.inter_subset_inter_right _ (Set.biInter_subset_biInter_left hsub))
    _ = μ.real A * ∏ j ∈ t, μ.real (E j)ᶜ := by
      simp only [measureReal_def, hind.measure_inter_eq_mul, ENNReal.toReal_mul,
        hX.measure_biInter_eq_prod_of_blockSigma hmX (hB.subset hsub) htE, ENNReal.toReal_prod]
    _ ≤ μ.real A * (1 - q : ℝ) ^ #t := by
      refine mul_le_mul_of_nonneg_left ?_ measureReal_nonneg
      rw [← Finset.prod_const]
      refine Finset.prod_le_prod₀ (fun _ _ ↦ measureReal_nonneg) fun j hj ↦ ?_
      rw [measureReal_compl (blockSigma_le _ (fun k _ ↦ hmX k) _ (hE j (hsub hj))),
        probReal_univ]
      exact sub_le_sub_left (hq j (hsub hj)) _
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (pow_le_pow_of_le_one (sub_nonneg.mpr q.property.2) (sub_le_self _ q.property.1) hcard)
      measureReal_nonneg

end TauCeti.Probability

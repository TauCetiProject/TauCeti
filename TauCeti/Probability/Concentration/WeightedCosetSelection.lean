/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Concentration.SubsetSelection
public import TauCeti.Probability.Concentration.WeightedEventCount
public import TauCeti.Probability.Distributions.Bernoulli.Basic

/-!
# Prescribed selection profiles with weighted bad events

Sample a subset by independent Bernoulli trials with probabilities constant on the fibres
of a finite map. With probability at least one half the subset has both the prescribed
relative fibre counts (up to an explicit error) and few bad events in a weighted count.
The bad events can depend on the entire sample, not just on membership of the element at
which they are tested. For a quotient map by a subgroup the fibres are its cosets.
-/

public section

open Finset MeasureTheory ProbabilityTheory Set

namespace TauCeti

open Classical in
/-- Bernoulli selection with probabilities `δ * ω (f a)` over fibres of size `m`, where
`ω q ∈ [ω₀, 1]` with `ω₀ > 0`. Put `D = δ * |α|` and let `E = δ * m * ∑ ω` be the expected
size, and assume `16 * |Q|² / ω₀² ≤ D`. On an event of probability at least `1/2`, the
selected subset `S` satisfies `E / 2 ≤ |S| ≤ 3 * E / 2`, and each fibre count differs from
`(ω q / ∑ ω) * |S|` by at most `4 * (1 + ω₀) / (ω₀² * √D)` times `|S|`; if moreover
`36 * |Q|² / ω₀² ≤ D`, then `2 * E / 3 ≤ |S|`. On the same event, the weighted bad count is
at most `4 * p * E` times the total weight, and hence at most `8 * p * |S|` times the total
weight. A bad event `B i a` can be arbitrary provided its intersection with the event that
`a` is selected has probability at most `p` times the probability that `a` is selected. -/
theorem half_le_measureReal_bernoulli_card_fiber_and_weightedEventCount
    {α Q ι : Type*} [Fintype α] [Fintype Q] (f : α → Q) {m : ℕ}
    (hf : ∀ q, (univ.filter fun a ↦ f a = q).card = m)
    (δ : unitInterval) (ω : Q → unitInterval) {ω₀ : ℝ} (hω₀ : 0 < ω₀)
    (hω : ∀ q, ω₀ ≤ (ω q : ℝ))
    (hsize : 16 * (Fintype.card Q : ℝ) ^ 2 / ω₀ ^ 2 ≤ (δ : ℝ) * Fintype.card α)
    (t : Finset ι) {w : ι → ℝ} (hw : ∀ i ∈ t, 0 ≤ w i)
    (B : ι → α → Set (α → Bool)) (p : NNReal)
    (hbad : ∀ i ∈ t, ∀ a, (Measure.pi fun a' ↦ bernoulliMeasure true false (δ * ω (f a'))).real
      ({x | x a = true} ∩ B i a) ≤ (p : ℝ) * ((δ : ℝ) * (ω (f a) : ℝ))) :
    let μ := Measure.pi fun a ↦ bernoulliMeasure true false (δ * ω (f a))
    let D := (δ : ℝ) * Fintype.card α
    let E := (δ : ℝ) * m * ∑ q, (ω q : ℝ)
    (1 / 2 : ℝ) ≤ μ.real {x |
      let S := univ.filter fun a ↦ x a = true
      E / 2 ≤ (S.card : ℝ) ∧ (S.card : ℝ) ≤ 3 * E / 2 ∧
      (36 * (Fintype.card Q : ℝ) ^ 2 / ω₀ ^ 2 ≤ D → 2 * E / 3 ≤ (S.card : ℝ)) ∧
      (∀ q : Q, |((S.filter fun a ↦ f a = q).card : ℝ) -
        ((ω q : ℝ) / ∑ j, (ω j : ℝ)) * S.card| ≤
          (4 * (1 + ω₀) / ω₀ ^ 2 / Real.sqrt D) * S.card) ∧
      S.weightedEventCount t w B x ≤ 4 * (p : ℝ) * E * ∑ i ∈ t, w i ∧
      4 * (p : ℝ) * E * ∑ i ∈ t, w i ≤ 8 * (p : ℝ) * S.card * ∑ i ∈ t, w i} := by
  dsimp only
  let ν (a : α) := bernoulliMeasure true false (δ * ω (f a))
  let μ := Measure.pi ν
  let S (x : α → Bool) := univ.filter fun a ↦ x a = true
  let E := (δ : ℝ) * m * ∑ q, (ω q : ℝ)
  have hset (a : α) : {x | a ∈ S x} = {x | x a = true} := by
    ext x
    simp [S]
  have hmem (a : α) : {x | a ∈ S x} = (fun x : α → Bool ↦ x a) ⁻¹' ({true} : Set Bool) := by
    ext x
    simp [S]
  have hm (a : α) : MeasurableSet {x | a ∈ S x} := by
    rw [hmem]
    exact (measurableSet_singleton _).preimage (measurable_pi_apply a)
  have hi : iIndepFun (fun a ↦ {x | a ∈ S x}.indicator (1 : (α → Bool) → ℝ)) μ := by
    simpa only [hset] using
      Probability.iIndepFun_pi_bernoulliMeasure_indicator_eval fun a ↦ δ * ω (f a)
  have hp (a : α) : μ.real {x | a ∈ S x} = (δ : ℝ) * (ω (f a) : ℝ) := by
    rw [hset, Probability.measureReal_pi_bernoulliMeasure_eval_eq_true (fun a ↦ δ * ω (f a)) a]
    simp
  have hmean : (∑ a, μ.real {x | a ∈ S x}) = E := by
    simp only [hp, ← mul_sum, E, mul_assoc]
    congr 1
    rw [← sum_fiberwise univ f (fun a ↦ (ω (f a) : ℝ)), mul_sum]
    refine sum_congr rfl fun q _ ↦ ?_
    rw [sum_eq_card_nsmul (b := (ω q : ℝ)) (fun a ha ↦ by rw [(mem_filter.mp ha).2]), hf,
      nsmul_eq_mul]
  -- Intersect the event controlling fibre counts with the one controlling the weighted cost.
  have hgood := three_div_four_le_measureReal_card_fiber_bounds S f hf
    (fun q ↦ (ω q : ℝ)) hω₀ (fun q ↦ ⟨hω q, (ω q).property.2⟩) hsize hm
    (fun _ _ hab ↦ hi.indepFun hab) hp
  have hbudget := half_le_measureReal_inter_weighted_bad_count_le (p := p) (s := univ)
    (S := fun a ↦ {x | a ∈ S x}) (B := B) hw
    (fun i hi a _ ↦ by
      rw [hp, hmem]
      simpa only [Set.preimage, mem_singleton_iff] using hbad i hi a)
    hgood (fun x hx ↦ by
      have hlo : E / 2 ≤ (S x).card := hx.1
      rw [hmean]
      simpa [S] using (by linarith only [hlo] : E ≤ 2 * (S x).card))
  refine hbudget.trans (measureReal_mono fun x hx ↦ ?_)
  have hcount : univ.weightedEventCount t w (fun i a ↦ {y | a ∈ S y} ∩ B i a) x =
      (S x).weightedEventCount t w B x := by
    simp [weightedEventCount_def, S, filter_filter]
  obtain ⟨⟨hlo, hup, hstrong, hdisc⟩, hbad₁, hbad₂⟩ := hx
  rw [hcount, hmean] at hbad₁
  rw [hmean] at hbad₂
  exact ⟨hlo, hup, hstrong, hdisc, hbad₁, by simpa [S] using hbad₂⟩

end TauCeti

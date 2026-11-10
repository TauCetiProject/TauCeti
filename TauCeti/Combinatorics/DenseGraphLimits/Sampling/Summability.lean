/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.Sampling.Concentration

/-!
# Summable tails for sampled homomorphism densities

For a fixed finite graph and a positive tolerance, the probabilities that its homomorphism
density in a graphon sample deviates from the graphon density have finite total mass. This is the
summability input needed to apply the first Borel--Cantelli lemma to the restrictions of a single
infinite graphon sample.

The proof uses the exponential concentration estimate for all sufficiently large sample sizes.
The empty pattern is handled separately: both densities are identically one, so every deviation
event is empty.

## Main result

* `SimpleGraph.tsum_sampleGraph_homDensityFin_tail_ne_top` — the deviation probabilities at
  sample sizes `n + 1` have finite sum.

## References

* L. Lovász, *Large Networks and Graph Limits*, AMS Colloquium Publications 60 (2012), §10.1.
* C. Freer, `cameronfreer/graphon` at commit
  `6eccca5bbe5c9df46d7129bf59575b8b9b1d6699`, Apache-2.0, `Graphon/SampleExposure.lean`.
  The split between the empty-pattern case and the eventually exponential tail follows that file.
-/

public section

noncomputable section

open MeasureTheory Filter

open scoped ENNReal

namespace SimpleGraph

open TauCeti.DenseGraphLimits

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- For the empty pattern both densities are identically one, so every deviation event is empty
and the total mass is zero. -/
private lemma tsum_sampleGraph_homDensityFin_tail_ne_top_of_isEmpty {V : Type*} [Fintype V]
    [IsEmpty V] (F : SimpleGraph V) [DecidableRel F.Adj] (W : Graphon Ω μ) {ε : ℝ} (hε : 0 < ε) :
    (∑' n : ℕ, (sampleGraph W (n + 1))
      {G | ε ≤ |homDensityFin F G - homDensity F W|}) ≠ ⊤ := by
  have hfin (n : ℕ) (G : SimpleGraph (Fin (n + 1))) : homDensityFin F G = 1 := by
    simp [homDensityFin_def]
  have hedge : F.edgeFinset = ∅ := by
    ext e
    exact isEmptyElim e
  have hgraphon : homDensity F W = 1 := by
    rw [homDensity_def, hedge]
    simp
  have hevent (n : ℕ) :
      {G : SimpleGraph (Fin (n + 1)) | ε ≤ |homDensityFin F G - homDensity F W|} = ∅ := by
    ext G
    simp only [hfin, hgraphon, sub_self, abs_zero, Set.mem_ofPred_eq, Set.mem_empty_iff_false,
      iff_false]
    exact not_le.mpr hε
  simp_rw [hevent, measure_empty]
  simp

/-- For a nonempty pattern, the exponential concentration bound eventually dominates the
deviation probabilities, and its geometric series is summable. -/
private lemma tsum_sampleGraph_homDensityFin_tail_ne_top_of_card_pos {V : Type*} [Fintype V]
    (hq : 0 < Fintype.card V) (F : SimpleGraph V) [DecidableRel F.Adj] (W : Graphon Ω μ) {ε : ℝ}
    (hε : 0 < ε) :
    (∑' n : ℕ, (sampleGraph W (n + 1))
      {G | ε ≤ |homDensityFin F G - homDensity F W|}) ≠ ⊤ := by
  let q := Fintype.card V
  let c : ℝ := -(ε ^ 2) / (2 * (q : ℝ) ^ 2)
  have hc : c < 0 := by
    dsimp [c]
    have hqR : (0 : ℝ) < q := by exact_mod_cast hq
    exact div_neg_of_neg_of_pos (neg_neg_of_pos (sq_pos_of_pos hε))
      (mul_pos zero_lt_two (sq_pos_of_pos hqR))
  have hgeometric : Summable (fun n : ℕ => 2 * Real.exp ((n : ℝ) * c)) :=
    (Real.summable_exp_nat_mul_iff.mpr hc).mul_left 2
  let a : ℕ → ℝ := fun n => ((sampleGraph W (n + 1))
    {G | ε ≤ |homDensityFin F G - homDensity F W|}).toReal
  let b : ℕ → ℝ := fun n => 2 * Real.exp (((n + 1 : ℕ) : ℝ) * c)
  have hb : Summable b := by
    simpa only [b] using (summable_nat_add_iff 1).2 hgeometric
  have hab : ∀ᶠ n : ℕ in atTop, a n ≤ b n := by
    -- the side condition `2 q² ≤ ε (n + 1)` holds for large `n`
    filter_upwards [((tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds).const_mul_atTop
      hε).eventually_ge_atTop (2 * (q : ℝ) ^ 2)] with n hn
    have hn' : 2 * (Fintype.card V : ℝ) ^ 2 ≤ ε * ((n + 1 : ℕ) : ℝ) := by
      simpa only [q, Nat.cast_add, Nat.cast_one] using hn
    dsimp only [a, b]
    convert sampleGraph_homDensityFin_concentration F W hn' using 1
    dsimp only [c, q]
    push_cast
    ring_nf
  have ha : Summable a := hb.of_norm_bounded_eventually_nat
    (hab.mono fun n hn => by
      simpa only [a, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg] using hn)
  have hnn : Summable fun n => ((sampleGraph W (n + 1))
      {G | ε ≤ |homDensityFin F G - homDensity F W|}).toNNReal := by
    simpa only [a, ENNReal.toNNReal_toReal_eq] using ha.toNNReal
  have hsum := ENNReal.tsum_coe_ne_top_iff_summable.2 hnn
  convert hsum using 1
  simp only [ENNReal.coe_toNNReal (measure_ne_top _ _)]

/-- For a fixed finite graph `F` and `ε > 0`, the probabilities

`P(|t(F, G(n + 1, W)) - t(F, W)| ≥ ε)`

have finite total mass. Thus the corresponding events on the joint infinite sampling space are
eligible for the first Borel--Cantelli lemma. -/
theorem tsum_sampleGraph_homDensityFin_tail_ne_top {V : Type*} [Fintype V]
    (F : SimpleGraph V) [DecidableRel F.Adj] (W : Graphon Ω μ) {ε : ℝ} (hε : 0 < ε) :
    (∑' n : ℕ, (sampleGraph W (n + 1))
      {G | ε ≤ |homDensityFin F G - homDensity F W|}) ≠ ⊤ := by
  rcases Nat.eq_zero_or_pos (Fintype.card V) with hq | hq
  · let _ : IsEmpty V := Fintype.card_eq_zero_iff.mp hq
    exact tsum_sampleGraph_homDensityFin_tail_ne_top_of_isEmpty F W hε
  · exact tsum_sampleGraph_homDensityFin_tail_ne_top_of_card_pos hq F W hε

end SimpleGraph

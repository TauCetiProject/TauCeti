/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.Portmanteau
public import TauCeti.MeasureTheory.OptimalTransport.Cost.Mixture

/-!
# Bounded transport costs along weakly convergent marginals

A cost `c : X × X → ℝ≥0∞` that is bounded and vanishes uniformly near the diagonal — for every
`ε > 0` there is `δ > 0` with `c (x, y) ≤ ε` whenever `edist x y < δ` — measures how far apart two
laws are. This file proves that on a separable pseudometric space every such transport cost tends
to `0` along a weakly convergent family of probability measures: if `μᵢ ⇀ μ`, then
`transportCost c μᵢ μ → 0`. Bounded costs such as `min (edist x y) R ^ p` are the truncations
through which the convergence of Wasserstein distances is reduced to weak convergence and the
convergence of moments.

The proof transports mass cell by cell along a finite partition of the space. The deterministic
estimate `TauCeti.transportCost_le_sum_of_partition` bounds the transport cost of two measures of
equal mass by the cost inside matching cells, weighted by the second measure, plus the bound on the
cost times the mass by which the first measure exceeds the second cell by cell. For the
convergence statement the cells are the pieces cut out by finitely many small balls centred at
the points of a dense sequence, with radii chosen so that the limit law does not charge any of the
bounding spheres. The masses of such cells converge by the portmanteau theorem, so the excess mass
tends to `0`, while the balls leave only a small mass of the limit law outside them.

## Main statements

* `TauCeti.transportCost_le_mul_of_ae_mem` — two measures of equal mass concentrated on sets on
  whose product the cost is at most `η` have transport cost at most `η` times their mass;
* `TauCeti.transportCost_le_sum_of_partition` — the transport cost of two measures of equal mass
  is controlled by matching finite partitions of the two spaces;
* `TauCeti.tendsto_transportCost_of_tendsto` — a bounded cost vanishing uniformly near the
  diagonal has transport cost tending to `0` along a weakly convergent family.

## References

* C. Villani, *Optimal Transport: Old and New*, Grundlehren 338, Springer 2009, Theorem 6.9, where
  weak convergence together with convergence of moments is shown to give Wasserstein convergence.
* L. Ambrosio, N. Gigli and G. Savaré, *Gradient Flows in Metric Spaces and in the Space of
  Probability Measures*, 2nd edition, Birkhäuser 2008, Proposition 7.1.5.
* P. Billingsley, *Convergence of Probability Measures*, 2nd edition, Wiley 1999, Theorem 2.1, the
  portmanteau theorem for sets whose boundary is not charged by the limit law.
-/

public section

noncomputable section

open Filter Function MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace TauCeti

section Partition

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {c : X × Y → ℝ≥0∞}

/-- **Transport inside a cell.** Two measures of equal finite mass, concentrated on measurable sets
`A` and `B` on whose product the cost is at most `η`, have transport cost at most `η` times their
common mass. -/
theorem transportCost_le_mul_of_ae_mem {A : Set X} {B : Set Y} (hA : MeasurableSet A)
    (hB : MeasurableSet B) {η : ℝ≥0∞} (hc : ∀ x ∈ A, ∀ y ∈ B, c (x, y) ≤ η) {α : Measure X}
    {β : Measure Y} [IsFiniteMeasure α] (hαA : ∀ᵐ x ∂α, x ∈ A) (hβB : ∀ᵐ y ∂β, y ∈ B)
    (h : α univ = β univ) :
    transportCost c α β ≤ η * α univ := by
  -- Outside `A × B` the cost is dominated by an infinite penalty on a null set of one marginal.
  have hle : c ≤ fun z ↦ η + Aᶜ.indicator (fun _ ↦ ∞) z.1 + Bᶜ.indicator (fun _ ↦ ∞) z.2 := by
    rintro ⟨x, y⟩
    by_cases hx : x ∈ A
    · by_cases hy : y ∈ B
      · simpa [hx, hy] using hc x hx y hy
      · simp [hy]
    · simp [hx]
  have hαA' : α Aᶜ = 0 := ae_iff.1 hαA
  have hβB' : β Bᶜ = 0 := ae_iff.1 hβB
  calc transportCost c α β
      ≤ transportCost (fun z ↦ (fun _ ↦ η) z + Aᶜ.indicator (fun _ ↦ ∞) z.1 +
          Bᶜ.indicator (fun _ ↦ ∞) z.2) α β := transportCost_mono hle
    _ = η * α univ := by
        rw [transportCost_add_split (measurable_const.indicator hA.compl)
          (measurable_const.indicator hB.compl), transportCost_const (exists_isCoupling_iff.2 h),
          lintegral_indicator_const hA.compl, lintegral_indicator_const hB.compl, hαA', hβB']
        simp

/-- Splitting each piece of a finite measurable partition by a factor `s i ≤ 1` splits the measure
into a scaled part and a remainder. -/
private theorem eq_sum_smul_restrict_add {Z : Type*} [MeasurableSpace Z] {ι : Type*} [Fintype ι]
    {A : ι → Set Z} (hAm : ∀ i, MeasurableSet (A i)) (hAd : Pairwise (Disjoint on A))
    (hAu : (⋃ i, A i) = univ) {s : ι → ℝ≥0∞} (hs : ∀ i, s i ≤ 1) (μ : Measure Z) :
    μ = ∑ i, s i • μ.restrict (A i) + ∑ i, (1 - s i) • μ.restrict (A i) := by
  rw [← Finset.sum_add_distrib]
  conv_lhs => rw [← Measure.restrict_univ (μ := μ), ← hAu, Measure.restrict_iUnion hAd hAm,
    Measure.sum_fintype]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← add_smul, add_tsub_cancel_of_le (hs i), one_smul]

/-- **Transport along matching partitions.** Let `A` and `B` be finite measurable partitions of
`X` and `Y` indexed by the same type, such that the cost is at most `η i` on `A i × B i` and at
most `M` everywhere. Then two measures of equal finite mass have transport cost at most the sum of
the `η i` weighted by the masses `ν (B i)`, plus `M` times the total mass by which `μ` exceeds `ν`
cell by cell.

The plan matches the common mass `min (μ (A i)) (ν (B i))` inside each cell and moves the remaining
mass arbitrarily, at cost at most `M` per unit of mass. -/
theorem transportCost_le_sum_of_partition {ι : Type*} [Fintype ι] {A : ι → Set X}
    {B : ι → Set Y} (hAm : ∀ i, MeasurableSet (A i)) (hBm : ∀ i, MeasurableSet (B i))
    (hAd : Pairwise (Disjoint on A)) (hBd : Pairwise (Disjoint on B)) (hAu : (⋃ i, A i) = univ)
    (hBu : (⋃ i, B i) = univ) {η : ι → ℝ≥0∞} (hc : ∀ i, ∀ x ∈ A i, ∀ y ∈ B i, c (x, y) ≤ η i)
    {M : ℝ≥0∞} (hM : ∀ z, c z ≤ M) (μ : Measure X) (ν : Measure Y) [IsFiniteMeasure μ]
    (h : μ univ = ν univ) :
    transportCost c μ ν ≤ ∑ i, η i * ν (B i) + M * ∑ i, (μ (A i) - ν (B i)) := by
  have : IsFiniteMeasure ν := ⟨h ▸ measure_lt_top μ univ⟩
  -- the common mass of the two measures in each cell, and the matching scaling factors
  set m : ι → ℝ≥0∞ := fun i ↦ min (μ (A i)) (ν (B i)) with hm
  set s : ι → ℝ≥0∞ := fun i ↦ m i / μ (A i) with hs
  set t : ι → ℝ≥0∞ := fun i ↦ m i / ν (B i) with ht
  have hs1 (i : ι) : s i ≤ 1 := ENNReal.div_le_of_le_mul (by rw [one_mul]; exact min_le_left _ _)
  have ht1 (i : ι) : t i ≤ 1 := ENNReal.div_le_of_le_mul (by rw [one_mul]; exact min_le_right _ _)
  have hsμ (i : ι) : s i * μ (A i) = m i := by
    rcases eq_or_ne (μ (A i)) 0 with h0 | h0
    · simp [hm, h0]
    · exact ENNReal.div_mul_cancel h0 (measure_ne_top _ _)
  have htν (i : ι) : t i * ν (B i) = m i := by
    rcases eq_or_ne (ν (B i)) 0 with h0 | h0
    · simp [hm, h0]
    · exact ENNReal.div_mul_cancel h0 (measure_ne_top _ _)
  -- the matched parts `α`, `β` and the remainders `α'`, `β'`
  set α : ι → Measure X := fun i ↦ s i • μ.restrict (A i)
  set α' : ι → Measure X := fun i ↦ (1 - s i) • μ.restrict (A i)
  set β : ι → Measure Y := fun i ↦ t i • ν.restrict (B i)
  set β' : ι → Measure Y := fun i ↦ (1 - t i) • ν.restrict (B i)
  have hμ : μ = ∑ i, α i + ∑ i, α' i := eq_sum_smul_restrict_add hAm hAd hAu hs1 μ
  have hν : ν = ∑ i, β i + ∑ i, β' i := eq_sum_smul_restrict_add hBm hBd hBu ht1 ν
  have hα_univ (i : ι) : α i univ = m i := by
    simp only [α, Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ, univ_inter,
      smul_eq_mul, hsμ]
  have hβ_univ (i : ι) : β i univ = m i := by
    simp only [β, Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ, univ_inter,
      smul_eq_mul, htν]
  have hα'_univ (i : ι) : α' i univ = μ (A i) - ν (B i) := by
    simp only [α', Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ, univ_inter,
      smul_eq_mul]
    rw [ENNReal.sub_mul fun _ _ ↦ measure_ne_top _ _, one_mul, hsμ, hm, tsub_min]
  -- Inside each cell the matched parts are transported at cost at most `η i` per unit of mass.
  have hcell (i : ι) : transportCost c (α i) (β i) ≤ η i * ν (B i) := by
    have : IsFiniteMeasure (α i) :=
      ⟨by rw [hα_univ]; exact (min_le_left _ _).trans_lt (measure_lt_top _ _)⟩
    refine (transportCost_le_mul_of_ae_mem (hAm i) (hBm i) (hc i) ?_ ?_
      ((hα_univ i).trans (hβ_univ i).symm)).trans ?_
    · exact (Measure.ae_smul_measure (ae_restrict_mem (hAm i)) _)
    · exact (Measure.ae_smul_measure (ae_restrict_mem (hBm i)) _)
    · rw [hα_univ]
      gcongr
      exact min_le_right _ _
  -- The remainders have equal mass, and are transported at cost at most `M` per unit of mass.
  have hrest : (∑ i, α' i) univ = (∑ i, β' i) univ := by
    have hsum : (∑ i, α i) univ = (∑ i, β i) univ := by
      simp only [Measure.coe_finsetSum, Finset.sum_apply, hα_univ, hβ_univ]
    have hne : (∑ i, α i) univ ≠ ∞ := by
      simp only [Measure.coe_finsetSum, Finset.sum_apply, hα_univ]
      exact ENNReal.sum_ne_top.2 fun i _ ↦ ((min_le_left _ _).trans_lt (measure_lt_top _ _)).ne
    have htot : (∑ i, α i) univ + (∑ i, α' i) univ = (∑ i, β i) univ + (∑ i, β' i) univ := by
      rw [← Measure.add_apply, ← Measure.add_apply, ← hμ, ← hν, h]
    rwa [hsum, ENNReal.add_right_inj (hsum ▸ hne)] at htot
  calc transportCost c μ ν
      = transportCost c (∑ i, α i + ∑ i, α' i) (∑ i, β i + ∑ i, β' i) := by rw [← hμ, ← hν]
    _ ≤ transportCost c (∑ i, α i) (∑ i, β i) + transportCost c (∑ i, α' i) (∑ i, β' i) :=
        transportCost_add_le c _ _ _ _
    _ ≤ ∑ i, transportCost c (α i) (β i) + transportCost (fun _ ↦ M) (∑ i, α' i) (∑ i, β' i) :=
        add_le_add (transportCost_finset_sum_le _ c _ _) (transportCost_mono hM)
    _ ≤ ∑ i, η i * ν (B i) + M * ∑ i, (μ (A i) - ν (B i)) := by
        have : IsFiniteMeasure (∑ i, α' i) := ⟨by
          simp only [Measure.coe_finsetSum, Finset.sum_apply, hα'_univ]
          exact lt_top_iff_ne_top.2 (ENNReal.sum_ne_top.2 fun i _ ↦
            ne_top_of_le_ne_top (measure_ne_top μ (A i)) tsub_le_self)⟩
        rw [transportCost_const (exists_isCoupling_iff.2 hrest)]
        refine add_le_add (Finset.sum_le_sum fun i _ ↦ hcell i) (le_of_eq ?_)
        simp only [Measure.coe_finsetSum, Finset.sum_apply, hα'_univ]

end Partition

section WeakConvergence

variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  [TopologicalSpace.SeparableSpace X]

/-- A finite partition of `X` into pieces of `μ`-null boundary: all but the last piece lie in
balls of radius `r`, and the last piece has `μ`-mass at most `ε`. -/
private theorem exists_partition (μ : Measure X) [IsProbabilityMeasure μ] {r : ℝ} (hr : 0 < r)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ (N : ℕ) (A : Fin (N + 1) → Set X), (∀ i, MeasurableSet (A i)) ∧
      Pairwise (Disjoint on A) ∧ (⋃ i, A i) = univ ∧ (∀ i, μ (frontier (A i)) = 0) ∧
      (∀ i : Fin (N + 1), i ≠ Fin.last N → ∃ x, A i ⊆ Metric.ball x r) ∧
      μ (A (Fin.last N)) ≤ ε := by
  have := nonempty_of_isProbabilityMeasure μ
  obtain ⟨u, hu⟩ := TopologicalSpace.exists_dense_seq X
  obtain ⟨ρ, ⟨hρ0, hρr⟩, hρ⟩ := μ.exists_forall_null_frontier_thickening (fun k ↦ {u k}) hr
  simp only [Metric.thickening_singleton] at hρ
  -- The union of the first `N` balls exhausts the space, so its complement becomes small.
  set G : ℕ → Set X := fun N ↦ ⋃ k < N, Metric.ball (u k) ρ
  have hG : Tendsto (fun N ↦ μ (G N)ᶜ) atTop (𝓝 0) := by
    have hlim := tendsto_measure_iInter_atTop (μ := μ) (s := fun N ↦ (G N)ᶜ)
      (fun N ↦ (MeasurableSet.biUnion (to_countable _)
        fun _ _ ↦ measurableSet_ball).compl.nullMeasurableSet)
      (fun M N hMN ↦ compl_subset_compl.2 <| biUnion_subset_biUnion_left fun k hk ↦
        lt_of_lt_of_le hk hMN) ⟨0, measure_ne_top _ _⟩
    have hempty : ⋂ N, (G N)ᶜ = ∅ := by
      rw [← compl_iUnion, compl_empty_iff, eq_univ_iff_forall]
      intro x
      obtain ⟨k, hk⟩ := (Metric.denseRange_iff.1 hu) x ρ hρ0
      exact mem_iUnion.2 ⟨k + 1, mem_iUnion₂.2 ⟨k, Nat.lt_succ_self k, Metric.mem_ball.2 hk⟩⟩
    simpa only [comp_def, hempty, measure_empty] using hlim
  obtain ⟨N, hN⟩ := (hG.eventually (ge_mem_nhds hε)).exists
  -- The cells: the first `N` balls made disjoint, followed by the rest of the space.
  set f : Fin (N + 1) → Set X := fun i ↦
    if (i : ℕ) < N then Metric.ball (u i) ρ else univ with hf
  have hfm (i : Fin (N + 1)) : MeasurableSet (f i) := by
    simp only [hf]
    split_ifs
    exacts [measurableSet_ball, MeasurableSet.univ]
  have hff (i : Fin (N + 1)) : μ (frontier (f i)) = 0 := by
    simp only [hf]
    split_ifs
    exacts [hρ _, by simp]
  refine ⟨N, disjointed f, fun i ↦ disjointedRec (p := MeasurableSet)
    (fun t j ht ↦ ht.diff (hfm j)) (hfm i), disjoint_disjointed f, ?_, fun i ↦ ?_, fun i hi ↦ ?_,
    ?_⟩
  · rw [iUnion_disjointed, eq_univ_iff_forall]
    exact fun x ↦ mem_iUnion.2 ⟨Fin.last N, by simp [hf]⟩
  · refine disjointedRec (p := fun t ↦ μ (frontier t) = 0) (fun t j ht ↦ ?_) (hff i)
    rw [sdiff_eq]
    exact null_frontier_inter ht (by rw [frontier_compl]; exact hff j)
  · have hiN : (i : ℕ) < N := by simpa using Fin.val_lt_last hi
    refine ⟨u i, (disjointed_subset f i).trans ?_⟩
    simp only [hf, hiN, ite_true]
    exact Metric.ball_subset_ball hρr.le
  · refine le_trans (measure_mono fun x hx ↦ ?_) hN
    rw [disjointed_eq_inter_compl] at hx
    simp only [mem_inter_iff, mem_iInter, mem_compl_iff] at hx
    simp only [G, mem_compl_iff, mem_iUnion, not_exists]
    intro k hk hxk
    refine hx.2 ⟨k, by omega⟩ (Fin.mk_lt_of_lt_val (by simpa using hk)) ?_
    simp [hf, hk, hxk]

/-- **Bounded transport costs along weak convergence.** On a separable pseudometric space, let
`c : X × X → ℝ≥0∞` be a bounded cost vanishing uniformly near the diagonal: for every `ε > 0`
there is `δ > 0` such that `c (x, y) ≤ ε` whenever `edist x y < δ`. If probability measures `μᵢ`
converge weakly to `μ`, then the transport cost of `c` from `μᵢ` to `μ` tends to `0`. -/
theorem tendsto_transportCost_of_tendsto {c : X × X → ℝ≥0∞} {M : ℝ≥0∞} (hM_top : M ≠ ∞)
    (hM : ∀ z, c z ≤ M) (hc : ∀ ε > 0, ∃ δ > 0, ∀ x y, edist x y < δ → c (x, y) ≤ ε)
    {γ : Type*} {L : Filter γ} {μs : γ → ProbabilityMeasure X} {μ : ProbabilityMeasure X}
    (h : Tendsto μs L (𝓝 μ)) :
    Tendsto (fun i ↦ transportCost c (μs i : Measure X) (μ : Measure X)) L (𝓝 0) := by
  refine ENNReal.tendsto_nhds_zero.2 fun ε hε ↦ ?_
  have hε3 : 0 < ε / 3 := ENNReal.div_pos hε.ne' ENNReal.ofNat_ne_top
  obtain ⟨δ, hδ, hcδ⟩ := hc (ε / 3) hε3
  obtain ⟨r, -, hr, hrδ⟩ := ENNReal.lt_iff_exists_real_btwn.1 hδ
  rw [ENNReal.ofReal_pos] at hr
  -- A partition whose last cell carries mass at most `ε / (3 M)` for the limit law, so that the
  -- cost of the last cell is at most `ε / 3`.
  obtain ⟨κ, hκ, hMκ⟩ : ∃ κ > 0, M * κ ≤ ε / 3 :=
    ⟨ε / 3 / M, ENNReal.div_pos hε3.ne' hM_top, ENNReal.mul_div_le⟩
  obtain ⟨N, A, hAm, hAd, hAu, hAf, hAball, hAlast⟩ :=
    exists_partition (μ : Measure X) (half_pos hr) hκ
  set η : Fin (N + 1) → ℝ≥0∞ := fun i ↦ if i = Fin.last N then M else ε / 3 with hη
  have hcA (i : Fin (N + 1)) : ∀ x ∈ A i, ∀ y ∈ A i, c (x, y) ≤ η i := by
    intro x hx y hy
    by_cases hi : i = Fin.last N
    · simpa [hη, hi] using hM (x, y)
    · obtain ⟨z, hz⟩ := hAball i hi
      simp only [hη, hi, ite_false]
      refine hcδ x y (lt_of_lt_of_le ?_ hrδ.le)
      rw [edist_dist, ENNReal.ofReal_lt_ofReal_iff hr]
      have := (dist_triangle x z y).trans_lt
        (add_lt_add (Metric.mem_ball.1 (hz hx)) (Metric.mem_ball'.1 (hz hy)))
      linarith
  -- The weighted cell costs of the limit law are at most `2 ε / 3`.
  have hsum : ∑ i, η i * (μ : Measure X) (A i) ≤ ε / 3 + ε / 3 := by
    have hsplit (i : Fin (N + 1)) : η i * (μ : Measure X) (A i) ≤
        ε / 3 * (μ : Measure X) (A i) +
          if i = Fin.last N then M * (μ : Measure X) (A i) else 0 := by
      by_cases hi : i = Fin.last N <;> simp [hη, hi]
    calc ∑ i, η i * (μ : Measure X) (A i)
        ≤ ∑ i, (ε / 3 * (μ : Measure X) (A i) +
            if i = Fin.last N then M * (μ : Measure X) (A i) else 0) :=
          Finset.sum_le_sum fun i _ ↦ hsplit i
      _ = ε / 3 * (μ : Measure X) univ + M * (μ : Measure X) (A (Fin.last N)) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite_eq' Finset.univ,
            ← tsum_fintype (L := .unconditional _), ← measure_iUnion hAd hAm, hAu]
          simp only [Finset.mem_univ, ite_true]
      _ ≤ ε / 3 + ε / 3 := by
          rw [measure_univ, mul_one]
          gcongr
          exact (mul_le_mul_right hAlast M).trans hMκ
  -- The excess mass tends to `0` by the portmanteau theorem for cells with null boundary.
  have hexcess : Tendsto (fun j ↦ M * ∑ i, ((μs j : Measure X) (A i) - (μ : Measure X) (A i)))
      L (𝓝 0) := by
    have hcell (i : Fin (N + 1)) : Tendsto
        (fun j ↦ (μs j : Measure X) (A i) - (μ : Measure X) (A i)) L (𝓝 0) := by
      simpa using ENNReal.Tendsto.sub
        (ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' h (hAf i))
        (tendsto_const_nhds (x := (μ : Measure X) (A i))) (Or.inl (measure_ne_top _ _))
    simpa using ENNReal.Tendsto.const_mul (tendsto_finsetSum _ fun i _ ↦ hcell i)
      (Or.inr hM_top)
  filter_upwards [hexcess.eventually (ge_mem_nhds hε3)] with j hj
  calc transportCost c (μs j : Measure X) (μ : Measure X)
      ≤ ∑ i, η i * (μ : Measure X) (A i) +
          M * ∑ i, ((μs j : Measure X) (A i) - (μ : Measure X) (A i)) :=
        transportCost_le_sum_of_partition hAm hAm hAd hAd hAu hAu hcA hM _ _ (by simp)
    _ ≤ ε / 3 + ε / 3 + ε / 3 := add_le_add hsum hj
    _ = ε := ENNReal.add_thirds ε

end WeakConvergence

end TauCeti

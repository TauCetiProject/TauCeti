/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.RestrictPartition
public import TauCeti.MeasureTheory.OptimalTransport.Cost.Mixture

/-!
# Transport costs along finite partitions

Two measures of equal finite mass can be transported cell by cell along matching finite
measurable partitions of the two spaces. The deterministic estimate
`TauCeti.transportCost_le_sum_of_partition` bounds their transport cost by the cost inside
matching cells, weighted by the second measure, plus a bound on the cost times the mass by which
the first measure exceeds the second cell by cell. The plan matches the common mass inside each
cell (`TauCeti.transportCost_le_mul_of_ae_mem`) and moves the remaining mass arbitrarily; the
estimate combines with the subadditivity of the transport cost in its marginals.

## Main statements

* `TauCeti.transportCost_le_mul_of_ae_mem` — two measures of equal mass concentrated on sets on
  whose product the cost is at most `η` have transport cost at most `η` times their mass;
* `TauCeti.transportCost_le_sum_of_partition` — the transport cost of two measures of equal mass
  is controlled by matching finite partitions of the two spaces.
-/

public section

noncomputable section

open Function MeasureTheory Set
open scoped ENNReal

namespace TauCeti

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
  have hμ : μ = ∑ i, α i + ∑ i, α' i :=
    Measure.eq_sum_smul_restrict_add_sum_one_sub_smul_restrict hAm hAd hAu hs1 μ
  have hν : ν = ∑ i, β i + ∑ i, β' i :=
    Measure.eq_sum_smul_restrict_add_sum_one_sub_smul_restrict hBm hBd hBu ht1 ν
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

end TauCeti

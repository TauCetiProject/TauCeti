/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Ergodic.MeasureEntropy.CoverCount
import TauCeti.Data.EReal.Operations
import TauCeti.Dynamics.Ergodic.MeasureEntropy.FinitePartition
import TauCeti.Dynamics.Ergodic.MeasureEntropy.Iterate
import TauCeti.Dynamics.TopologicalEntropy.Basic
import TauCeti.Dynamics.TopologicalEntropy.Iterate
import TauCeti.MeasureTheory.Measure.Regular
import TauCeti.Topology.UniformSpace.Compact

/-!
# Goodwyn's inequality

For a continuous map `T` of a compact uniform space (for instance a compact metric space) and a
`T`-invariant weakly regular Borel probability measure `μ`, the measure entropy is at most the
topological entropy: `h_μ(T) ≤ h_top(T)`, with `h_top(T) = coverEntropy T univ`
(`TauCeti.measureEntropy_le_coverEntropy`). Finite Borel measures on pseudo-metrizable spaces are
weakly regular, so the regularity hypothesis is automatic for compact metric spaces.

The proof follows Sarig's: a finite label `a` is approximated by its restriction `ζ` to closed sets
`F i ⊆ a ⁻¹' {i}` covering all but `δ` of the measure. An entourage `U` separating the `F i`
separates the `Sum.inl` values of `ζ`, so a dynamical cover of `X` by `U` at time `n` with
`r_n` points gives at most `r_n * 2 ^ n` itineraries of length `n`, and the counting step in
`TauCeti.Dynamics.Ergodic.MeasureEntropy.CoverCount` bounds the entropy rate of `ζ` by
`log 2 + liminf (log r_n) / n` (`TauCeti.IsInlSeparated.partitionEntropyRate_le_log_two_add`).
Adding the cost `H(a | ζ) ≤ δ log (card ι)` of the restriction and letting `δ → 0` gives
`h_μ(T) ≤ log 2 + h_top(T)` for every measure-preserving `T`
(`TauCeti.measureEntropy_le_log_two_add_coverEntropy`). Applied to `T^[k]`, whose measure and
topological entropies are `k` times those of `T`, this gives
`h_μ(T) ≤ (log 2) / k + h_top(T)` for all `k ≥ 1`.

## Main results

* `TauCeti.IsInlSeparated.partitionEntropyRate_le_log_two_add`: the rate step,
  `h(T, ζ) ≤ log 2 + coverEntropyInfEntourage T univ U` for a label `ζ` whose `Sum.inl` values
  are separated by `U`.
* `TauCeti.measureEntropy_le_log_two_add_coverEntropy`: `h_μ(T) ≤ log 2 + h_top(T)`.
* `TauCeti.measureEntropy_le_coverEntropy`: **Goodwyn's inequality** `h_μ(T) ≤ h_top(T)`.

## References

* O. Sarig, *Lecture Notes on Ergodic Theory*, 2023, §4.6.3, pp. 122–123.
-/

public section

open Function MeasureTheory Set Dynamics Filter ExpGrowth
open scoped ENNReal Uniformity Topology

namespace TauCeti

variable {X ι : Type*}

section RateStep

variable [MeasurableSpace X] {μ : Measure X} [IsZeroOrProbabilityMeasure μ] [MeasurableSpace ι]
  [MeasurableSingletonClass ι] {T : X → X} {ζ : X → ι ⊕ Unit} {U : SetRel X X}

/-- For a nonempty space and an entourage `U` separating the `Sum.inl` values of a measurable
label `ζ`, the entropy rate of `ζ` is at most `log (2 ^ n * r_n) / n` at every time `n ≥ 1`, where
`r_n = coverMincard T univ U n`. -/
theorem IsInlSeparated.partitionEntropyRate_le_log_div [Nonempty X] (hT : Measurable T)
    (hζ : Measurable ζ) (h : IsInlSeparated ζ U) {n : ℕ} (hn : n ≠ 0) :
    (partitionEntropyRate μ T ζ : EReal) ≤
      ENNReal.log (2 ^ n * (coverMincard T univ U n : ℝ≥0∞)) / n := by
  have hn' : (0 : EReal) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  rcases eq_top_or_lt_top (coverMincard T univ U n) with htop | hfin
  · rw [htop, ENat.toENNReal_top, ENNReal.mul_top (by positivity), ENNReal.log_top,
      EReal.top_div_of_pos_ne_top hn' (EReal.natCast_ne_top n)]
    exact le_top
  obtain ⟨s, hs, hcard⟩ := (coverMincard_finite_iff T univ U n).1 hfin
  have hpos : 0 < s.card := by
    obtain ⟨x⟩ := ‹Nonempty X›
    obtain ⟨y, hy, -⟩ := hs (mem_univ x)
    exact Finset.card_pos.2 ⟨y, hy⟩
  have hone : (1 : ℝ) ≤ s.card * 2 ^ n := by
    have h1 : (1 : ℝ) ≤ s.card := by exact_mod_cast hpos
    have h2 : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ one_le_two
    nlinarith
  have hlog : 0 ≤ Real.log (s.card * 2 ^ n) / n :=
    div_nonneg (Real.log_nonneg hone) n.cast_nonneg
  have key : partitionEntropyRate μ T ζ ≤ ENNReal.ofReal (Real.log (s.card * 2 ^ n) / n) := by
    refine (partitionEntropyRate_le_div (Nat.pos_of_ne_zero hn) μ T ζ).trans ?_
    rw [ENNReal.ofReal_div_of_pos (by exact_mod_cast Nat.pos_of_ne_zero hn),
      ENNReal.ofReal_natCast]
    gcongr
    exact countablePartitionEntropy_iteratedPartitionLabel_le_ofReal_log_card_mul_two_pow hT hζ h
      hs
  refine ((EReal.coe_ennreal_le_coe_iff_le_ofReal hlog).2 key).trans_eq ?_
  have hval : (2 : ℝ≥0∞) ^ n * ((s.card : ℕ∞) : ℝ≥0∞) = ENNReal.ofReal (s.card * 2 ^ n) := by
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    simp [mul_comm]
  rw [← hcard, hval, ENNReal.log_ofReal_of_pos (by linarith), EReal.coe_div, EReal.coe_natCast]

/-- **The rate step of Goodwyn's inequality.** For a nonempty space and an entourage `U`
separating the `Sum.inl` values of a measurable label `ζ`,
`h(T, ζ) ≤ log 2 + coverEntropyInfEntourage T univ U`. -/
theorem IsInlSeparated.partitionEntropyRate_le_log_two_add [Nonempty X] (hT : Measurable T)
    (hζ : Measurable ζ) (h : IsInlSeparated ζ U) :
    (partitionEntropyRate μ T ζ : EReal) ≤ Real.log 2 + coverEntropyInfEntourage T univ U := by
  have hl2 : ENNReal.log 2 = Real.log 2 := by
    simpa using ENNReal.log_ofReal_of_pos (x := 2) two_pos
  have h1 : (partitionEntropyRate μ T ζ : EReal) ≤
      expGrowthInf ((fun n : ℕ ↦ (2 : ℝ≥0∞) ^ n) * fun n ↦ (coverMincard T univ U n : ℝ≥0∞)) := by
    rw [expGrowthInf]
    refine le_liminf_of_le (by isBoundedDefault) (eventually_atTop.2 ⟨1, fun n hn ↦ ?_⟩)
    exact h.partitionEntropyRate_le_log_div hT hζ (Nat.one_le_iff_ne_zero.1 hn)
  refine h1.trans ((expGrowthInf_mul_le ?_ ?_).trans_eq ?_) <;> rw [expGrowthSup_pow, hl2]
  · exact .inl (EReal.coe_ne_bot _)
  · exact .inl (EReal.coe_ne_top _)
  · rw [coverEntropyInfEntourage]

end RateStep

section Bound

variable [UniformSpace X] [CompactSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  {μ : Measure X} [IsProbabilityMeasure μ] [μ.WeaklyRegular] {T : X → X}

/-- For a measure-preserving map `T` of a compact uniform space with a weakly regular Borel
probability measure, and a real number `t` equal to the topological entropy of `T`, every
measurable finite label has entropy rate at most `log 2 + t`. -/
private theorem partitionEntropyRate_le_ofReal_log_two_add (hT : MeasurePreserving T μ μ) {n : ℕ}
    {a : X → Fin n} (ha : Measurable a) {t : ℝ} (ht : coverEntropy T univ = t) :
    partitionEntropyRate μ T a ≤ ENNReal.ofReal (Real.log 2 + t) := by
  have hX : Nonempty X := nonempty_of_isProbabilityMeasure μ
  have ht0 : 0 ≤ t := by exact_mod_cast ht ▸ coverEntropy_nonneg T univ_nonempty
  have hc0 : 0 ≤ Real.log 2 + t := add_nonneg (Real.log_nonneg one_le_two) ht0
  set L := ENNReal.ofReal (Real.log n)
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ ↦ ?_
  -- Choose `δ ≠ 0` with `δ * log n ≤ ε`.
  obtain ⟨δ, hδ0, hδ⟩ : ∃ δ : ℝ≥0∞, δ ≠ 0 ∧ δ * L ≤ ε := by
    rcases eq_or_ne L 0 with hL | hL
    · exact ⟨1, one_ne_zero, by simp [hL]⟩
    · exact ⟨ε / L, ENNReal.div_ne_zero.2 ⟨by exact_mod_cast hε.ne', ENNReal.ofReal_ne_top⟩,
        (ENNReal.div_mul_cancel hL ENNReal.ofReal_ne_top).le⟩
  obtain ⟨F, hFc, hFa, hμF⟩ := ha.exists_isClosed_measure_compl_iUnion_le (μ := μ) hδ0
  have hdisj : Pairwise (Disjoint on F) := fun i j hij ↦
    disjoint_left.2 fun x hi hj ↦ hij ((hFa i hi).symm.trans (hFa j hj))
  obtain ⟨U, hU, hUdisj⟩ :=
    exists_mem_uniformity_disjoint_image (fun i ↦ (hFc i).isCompact) hFc hdisj
  have hFm : MeasurableSet (⋃ i, F i) := MeasurableSet.iUnion fun i ↦ (hFc i).measurableSet
  have hζ := measurable_restrictLabel ha hFm
  have hrate : partitionEntropyRate μ T (restrictLabel a (⋃ i, F i)) ≤
      ENNReal.ofReal (Real.log 2 + t) := by
    rw [← EReal.coe_ennreal_le_coe_iff_le_ofReal hc0, EReal.coe_add, ← ht]
    refine ((isInlSeparated_restrictLabel_iUnion hFa hUdisj).partitionEntropyRate_le_log_two_add
      hT.measurable hζ).trans ?_
    gcongr
    exact (coverEntropyInfEntourage_le_coverEntropyInf T univ hU).trans
      (coverEntropyInf_le_coverEntropy T univ)
  have hcost : conditionalPartitionEntropy μ a (restrictLabel a (⋃ i, F i)) ≤ δ * L := by
    refine (conditionalPartitionEntropy_restrictLabel_le ha hFm).trans ?_
    rw [Fintype.card_fin]
    gcongr
  calc partitionEntropyRate μ T a
      ≤ partitionEntropyRate μ T (restrictLabel a (⋃ i, F i)) +
          conditionalPartitionEntropy μ a (restrictLabel a (⋃ i, F i)) :=
        partitionEntropyRate_le_add_conditionalPartitionEntropy hT ha hζ
    _ ≤ ENNReal.ofReal (Real.log 2 + t) + ε := add_le_add hrate (hcost.trans hδ)

/-- For a measure-preserving map `T` of a compact uniform space with a weakly regular Borel
probability measure, and a real number `t` equal to the topological entropy of `T`,
`h_μ(T) ≤ log 2 + t`. -/
private theorem measureEntropy_le_ofReal_log_two_add (hT : MeasurePreserving T μ μ) {t : ℝ}
    (ht : coverEntropy T univ = t) :
    measureEntropy μ T ≤ ENNReal.ofReal (Real.log 2 + t) := by
  rw [measureEntropy_eq_iSup_fin hT]
  exact iSup₂_le fun _ _ ↦ iSup_le fun ha ↦ partitionEntropyRate_le_ofReal_log_two_add hT ha ht

/-- For a measure-preserving map `T` of a compact uniform space with a weakly regular Borel
probability measure, `h_μ(T) ≤ log 2 + h_top(T)`. -/
theorem measureEntropy_le_log_two_add_coverEntropy (hT : MeasurePreserving T μ μ) :
    (measureEntropy μ T : EReal) ≤ Real.log 2 + coverEntropy T univ := by
  have hX : Nonempty X := nonempty_of_isProbabilityMeasure μ
  obtain htop | ⟨t, ht0, ht⟩ := coverEntropy_eq_top_or_exists_eq_coe T univ_nonempty
  · rw [htop, EReal.coe_add_top]
    exact le_top
  rw [ht, ← EReal.coe_add,
    EReal.coe_ennreal_le_coe_iff_le_ofReal (add_nonneg (Real.log_nonneg one_le_two) ht0)]
  exact measureEntropy_le_ofReal_log_two_add hT ht

/-- **Goodwyn's inequality.** For a continuous map `T` of a compact uniform space (for instance a
compact metric space) and a `T`-invariant weakly regular Borel probability measure `μ`, the
measure entropy is at most the topological entropy: `h_μ(T) ≤ coverEntropy T univ`. -/
theorem measureEntropy_le_coverEntropy (hT : MeasurePreserving T μ μ) (hTc : Continuous T) :
    (measureEntropy μ T : EReal) ≤ coverEntropy T univ := by
  have hX : Nonempty X := nonempty_of_isProbabilityMeasure μ
  obtain htop | ⟨t, ht0, ht⟩ := coverEntropy_eq_top_or_exists_eq_coe T univ_nonempty
  · rw [htop]
    exact le_top
  rw [ht, EReal.coe_ennreal_le_coe_iff_le_ofReal ht0]
  -- Apply the bound with `log 2` to `T^[k]` and divide by `k`.
  have hk (k : ℕ) (hk0 : k ≠ 0) :
      measureEntropy μ T ≤ ENNReal.ofReal (Real.log 2 / k + t) := by
    have hkpos : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk0
    have htk : coverEntropy T^[k] univ = ((k * t : ℝ) : EReal) := by
      rw [coverEntropy_iterate_of_compactSpace hTc hk0, ht]
      norm_cast
    have h := measureEntropy_le_ofReal_log_two_add (hT.iterate k) htk
    rw [measureEntropy_iterate hT] at h
    have hdiv : Real.log 2 / k + t = (Real.log 2 + k * t) / k := by
      field_simp
    rw [hdiv, ENNReal.ofReal_div_of_pos hkpos,
      ENNReal.le_div_iff_mul_le (Or.inl (by simpa using hk0)) (by simp)]
    simpa [mul_comm] using h
  have hlim : Tendsto (fun k : ℕ ↦ ENNReal.ofReal (Real.log 2 / k + t)) atTop
      (𝓝 (ENNReal.ofReal t)) := by
    refine ENNReal.tendsto_ofReal ?_
    simpa using (tendsto_const_div_atTop_nhds_zero_nat (Real.log 2)).add_const t
  exact ge_of_tendsto hlim (eventually_atTop.2 ⟨1, fun k hk1 ↦ hk k (by omega)⟩)

end Bound

end TauCeti

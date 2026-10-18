/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Hypergeometric.Basic
public import TauCeti.Probability.Quantile.Discrete
public import Mathlib.Topology.Instances.EReal.Lemmas

/-!
# Quantiles of hypergeometric laws

For a population of size `N` with `K` marked objects and a sample of size `n`, the possible
counts run from `n - (N - K)` to `min K n`. At an interior probability level, the lower
quantile of the real-cast hypergeometric law is the least count in this interval whose
explicit cumulative sum reaches the level. Equality at a cumulative jump selects that count.

The quantile bounds include the deterministic cases: no marked objects, an empty sample,
an entirely marked population, and sampling the whole population. Both one-sided limits
are the corresponding support endpoints, including when those endpoints coincide.

The least-crossing proof uses `MeasureTheory.Measure.isLeast_quantile_map_natCast`; the
support bounds use the exact singleton support of the hypergeometric law.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set Topology

namespace TauCeti.Probability

variable {N K n : ℕ} {u : ℝ}

/-- Every interior hypergeometric quantile lies between the least and greatest possible
marked counts. -/
theorem quantile_map_cast_hypergeometricMeasure_mem_Icc (hK : K ≤ N) (hn : n ≤ N)
    (hu : u ∈ Ioo 0 1) :
    ((hypergeometricMeasure N K n).map (Nat.cast : ℕ → ℝ)).quantile u ∈
      Icc ((n - (N - K) : ℕ) : ℝ) ((min K n : ℕ) : ℝ) := by
  let _ := isProbabilityMeasure_hypergeometricMeasure hK hn
  apply ordConnected_Icc.quantile_mem _ hu.1 hu.2
  apply (ae_map_iff (by fun_prop) measurableSet_Icc).2
  rw [ae_iff_of_countable]
  intro k hk
  have hs := (hypergeometricMeasure_singleton_ne_zero_iff hK hn k).mp hk
  have hl : n - (N - K) ≤ k := by omega
  exact ⟨by exact_mod_cast hl, by exact_mod_cast le_min hs.1 hs.2.1⟩

/-- A hypergeometric quantile is the least supported count whose finite cumulative sum
reaches the level. The sum has no sample-size guard because all its indices are supported
above by `min K n`. -/
@[simp]
theorem quantile_map_cast_hypergeometricMeasure_eq_iff (hK : K ≤ N) (hn : n ≤ N)
    (hu : u ∈ Ioo 0 1) (k : ℕ) :
    ((hypergeometricMeasure N K n).map (Nat.cast : ℕ → ℝ)).quantile u = k ↔
      IsLeast {j : ℕ | j ∈ Icc (n - (N - K)) (min K n) ∧
        u ≤ ∑ i ∈ Finset.Iic j,
          (K.choose i : ℝ) * ((N - K).choose (n - i) : ℝ) / (N.choose n : ℝ)} k := by
  let _ := isProbabilityMeasure_hypergeometricMeasure hK hn
  have hcum (j : ℕ) (hj : j ≤ min K n) :
      (hypergeometricMeasure N K n).real (Iic j) =
        ∑ i ∈ Finset.Iic j,
          (K.choose i : ℝ) * ((N - K).choose (n - i) : ℝ) / (N.choose n : ℝ) := by
    rw [← Iic_def, hypergeometricMeasure_real_Iic_eq_sum hK hn]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Finset.mem_Iic] at hi
    simp [hi.trans (hj.trans (min_le_right K n))]
  have hleast := Measure.isLeast_quantile_map_natCast (hypergeometricMeasure N K n) hu
  have hmem := quantile_map_cast_hypergeometricMeasure_mem_Icc hK hn hu
  rw [Measure.quantile_map_natCast_eq_floor (hypergeometricMeasure N K n) hu] at hmem
  have hmem' :
      ⌊((hypergeometricMeasure N K n).map (Nat.cast : ℕ → ℝ)).quantile u⌋₊ ∈
        Icc (n - (N - K)) (min K n) := by
    constructor
    · exact_mod_cast hmem.1
    · exact_mod_cast hmem.2
  have hs : IsLeast {j : ℕ | j ∈ Icc (n - (N - K)) (min K n) ∧
      u ≤ ∑ i ∈ Finset.Iic j,
        (K.choose i : ℝ) * ((N - K).choose (n - i) : ℝ) / (N.choose n : ℝ)}
      ⌊((hypergeometricMeasure N K n).map (Nat.cast : ℕ → ℝ)).quantile u⌋₊ := by
    refine ⟨⟨hmem', ?_⟩, fun j hj ↦ hleast.2 ?_⟩
    · rw [← hcum _ hmem'.2]
      exact hleast.1
    · simpa only [mem_ofPred_eq, hcum j hj.1.2] using hj.2
  rw [hs.isLeast_iff_eq, ← Nat.cast_inj (R := ℝ),
    ← Measure.quantile_map_natCast_eq_floor (hypergeometricMeasure N K n) hu]

/-- An empty sample has hypergeometric quantile zero. -/
@[simp]
theorem quantile_map_cast_hypergeometricMeasure_sample_zero (hK : K ≤ N)
    (hu : u ∈ Ioo 0 1) :
    ((hypergeometricMeasure N K 0).map (Nat.cast : ℕ → ℝ)).quantile u = 0 := by
  have h := quantile_map_cast_hypergeometricMeasure_mem_Icc hK (Nat.zero_le N) hu
  simpa only [Nat.zero_sub, min_zero, Nat.cast_zero, Icc_self, mem_singleton_iff] using h

/-- With no marked objects, every hypergeometric quantile is zero. -/
@[simp]
theorem quantile_map_cast_hypergeometricMeasure_marked_zero (hn : n ≤ N)
    (hu : u ∈ Ioo 0 1) :
    ((hypergeometricMeasure N 0 n).map (Nat.cast : ℕ → ℝ)).quantile u = 0 := by
  have h := quantile_map_cast_hypergeometricMeasure_mem_Icc (Nat.zero_le N) hn hu
  simpa only [Nat.sub_zero, Nat.sub_eq_zero_of_le hn, zero_min, Nat.cast_zero,
    Icc_self, mem_singleton_iff] using h

/-- If the whole population is marked, the count and its quantiles equal the sample size. -/
@[simp]
theorem quantile_map_cast_hypergeometricMeasure_marked_all (hn : n ≤ N)
    (hu : u ∈ Ioo 0 1) :
    ((hypergeometricMeasure N N n).map (Nat.cast : ℕ → ℝ)).quantile u = n := by
  have h := quantile_map_cast_hypergeometricMeasure_mem_Icc le_rfl hn hu
  simpa only [Nat.sub_self, Nat.sub_zero, min_eq_right hn, Icc_self,
    mem_singleton_iff] using h

/-- Sampling the whole population gives quantiles equal to the number of marked objects. -/
@[simp]
theorem quantile_map_cast_hypergeometricMeasure_sample_all (hK : K ≤ N)
    (hu : u ∈ Ioo 0 1) :
    ((hypergeometricMeasure N K N).map (Nat.cast : ℕ → ℝ)).quantile u = K := by
  have h := quantile_map_cast_hypergeometricMeasure_mem_Icc hK le_rfl hu
  simpa only [Nat.sub_sub_self hK, min_eq_left hK, Icc_self, mem_singleton_iff] using h

/-- As the level tends to zero from above, hypergeometric quantiles tend to the smallest
possible count, which can be positive when the sample must contain marked objects. -/
theorem tendsto_quantile_map_cast_hypergeometricMeasure_nhdsGT_zero (hK : K ≤ N)
    (hn : n ≤ N) :
    Tendsto (fun u ↦
      (((hypergeometricMeasure N K n).map (Nat.cast : ℕ → ℝ)).quantile u : EReal))
      (𝓝[>] 0) (𝓝 ((n - (N - K) : ℕ) : EReal)) := by
  let _ := isProbabilityMeasure_hypergeometricMeasure hK hn
  have hmass : 0 < (hypergeometricMeasure N K n).real {n - (N - K)} :=
    ENNReal.toReal_pos
      ((hypergeometricMeasure_singleton_ne_zero_iff hK hn _).2 (by omega))
      (measure_ne_top _ _)
  have hpos : 0 < (hypergeometricMeasure N K n).real (Iic (n - (N - K))) :=
    hmass.trans_le (measureReal_mono (singleton_subset_iff.mpr self_mem_Iic))
  apply tendsto_const_nhds.congr'
  filter_upwards [Ioo_mem_nhdsGT (lt_min hpos zero_lt_one)] with u hu
  have hu' : u ∈ Ioo (0 : ℝ) 1 := ⟨hu.1, hu.2.trans_le (min_le_right _ _)⟩
  have hle : ((hypergeometricMeasure N K n).map (Nat.cast : ℕ → ℝ)).quantile u ≤
      ((n - (N - K) : ℕ) : ℝ) := by
    rw [Measure.quantile_le_iff _ hu'.1 hu'.2, Measure.cdf_map_natCast _ (Nat.cast_nonneg _),
      Nat.floor_natCast]
    exact (hu.2.trans_le (min_le_left _ _)).le
  exact (congrArg (fun x : ℝ ↦ (x : EReal))
    (le_antisymm hle (quantile_map_cast_hypergeometricMeasure_mem_Icc hK hn hu').1)).symm

/-- As the level tends to one from below, hypergeometric quantiles tend to the greatest
possible count. This includes all deterministic boundary laws. -/
theorem tendsto_quantile_map_cast_hypergeometricMeasure_nhdsLT_one (hK : K ≤ N)
    (hn : n ≤ N) :
    Tendsto (fun u ↦
      (((hypergeometricMeasure N K n).map (Nat.cast : ℕ → ℝ)).quantile u : EReal))
      (𝓝[<] 1) (𝓝 ((min K n : ℕ) : EReal)) := by
  let _ := isProbabilityMeasure_hypergeometricMeasure hK hn
  -- A zero maximum makes the entire support a singleton.
  by_cases hzero : min K n = 0
  · apply tendsto_const_nhds.congr'
    filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with u hu
    have h := quantile_map_cast_hypergeometricMeasure_mem_Icc hK hn hu
    have hq := Measure.quantile_map_natCast_nonneg (hypergeometricMeasure N K n) hu
    have heq : ((hypergeometricMeasure N K n).map (Nat.cast : ℕ → ℝ)).quantile u = 0 :=
      le_antisymm (by simpa [hzero] using h.2) hq
    simp [heq, hzero]
  -- Above the cumulative mass just before the final atom, the quantile is the maximum.
  have hpos : 0 < min K n := Nat.pos_of_ne_zero hzero
  have hmass : 0 < (hypergeometricMeasure N K n).real {min K n} :=
    ENNReal.toReal_pos
      ((hypergeometricMeasure_singleton_ne_zero_iff hK hn _).2 (by omega))
      (measure_ne_top _ _)
  have htail : 0 < (hypergeometricMeasure N K n).real ((Iic (min K n - 1))ᶜ) :=
    hmass.trans_le (measureReal_mono (singleton_subset_iff.mpr (by simp; omega)))
  have hlt : (hypergeometricMeasure N K n).real (Iic (min K n - 1)) < 1 := by
    rw [measureReal_compl measurableSet_Iic, probReal_univ] at htail
    linarith
  apply tendsto_const_nhds.congr'
  filter_upwards [Ioo_mem_nhdsLT (max_lt hlt zero_lt_one)] with u hu
  have hu' : u ∈ Ioo (0 : ℝ) 1 := ⟨(le_max_right _ _).trans_lt hu.1, hu.2⟩
  have hq : ((min K n - 1 : ℕ) : ℝ) <
      ((hypergeometricMeasure N K n).map (Nat.cast : ℕ → ℝ)).quantile u := by
    rw [Measure.lt_quantile_iff _ hu'.1 hu'.2,
      Measure.cdf_map_natCast _ (Nat.cast_nonneg _), Nat.floor_natCast]
    exact (le_max_left _ _).trans_lt hu.1
  rw [Measure.quantile_map_natCast_eq_floor (hypergeometricMeasure N K n) hu'] at hq
  have hnat : min K n ≤
      ⌊((hypergeometricMeasure N K n).map (Nat.cast : ℕ → ℝ)).quantile u⌋₊ := by
    have : min K n - 1 <
        ⌊((hypergeometricMeasure N K n).map (Nat.cast : ℕ → ℝ)).quantile u⌋₊ := by
      exact_mod_cast hq
    omega
  have hlo : ((min K n : ℕ) : ℝ) ≤
      ((hypergeometricMeasure N K n).map (Nat.cast : ℕ → ℝ)).quantile u := by
    rw [Measure.quantile_map_natCast_eq_floor (hypergeometricMeasure N K n) hu']
    exact_mod_cast hnat
  exact (congrArg (fun x : ℝ ↦ (x : EReal))
    (le_antisymm (quantile_map_cast_hypergeometricMeasure_mem_Icc hK hn hu').2 hlo)).symm

end TauCeti.Probability

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.PointProcess.Poisson.Basic
public import TauCeti.MeasureTheory.Measure.NNReal

import TauCeti.MeasureTheory.Measure.AtomlessStandardBorel.Transport
import TauCeti.Probability.Distributions.Poisson.SmallRate
import Mathlib.Order.Interval.Set.Union

/-!
# Simplicity of Poisson random measures with atomless intensity

A Poisson random measure with σ-finite intensity having null singletons on a countably
separated measurable space almost surely has mass at most one at every location,
simultaneously. In particular, this gives simplicity of temporal Poisson random measures
with homogeneous or inhomogeneous σ-finite intensity having null singletons, without
pathwise integrality or local finiteness hypotheses on the realizations. Simplicity rules
out multiplicities in point configurations and, together with local finiteness and no point
at zero, supports passing between a temporal point measure and strictly ordered occurrence
times.

The assertion is not obtained by intersecting the individual full-measure events at
uncountably many locations. Finite intensity pieces are injected into Cantor space and
transported to a constant multiple of Lebesgue measure on `(0,1]`. There a multiple point
belongs to a cell with at least two occurrences at every equal-mesh subdivision. The
Poisson factorial-moment bound makes the probability of any such cell tend to zero.
Outer measures handle the possibly nonmeasurable event that a multiple point exists.

See G. Last and M. Penrose, *Lectures on the Poisson Process*, Cambridge University
Press, 2018, Chapters 6–7. The subdivision argument also parallels the existing
`ae_count_le_add_one_of_small_time` for natural-valued count processes; here it works
on measures, using natural-valued versions only for the countably many mesh cells.
-/

public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

namespace TauCeti.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

private theorem measure_exists_multiple_singleton_Ioc_eq_zero
    {N : Ω → Measure ℝ≥0} {r : ℝ≥0}
    (h : IsPoissonRandomMeasure P N
      ((r : ℝ≥0∞) • nnvolume.restrict (Ioc 0 1))) :
    P {ω | ∃ t ∈ Ioc 0 1, 1 < N ω {t}} = 0 := by
  let := h.isProbabilityMeasure
  let δ (n : ℕ) := 1 / (n : ℝ≥0)
  let C (n k : ℕ) := Ioc ((k : ℝ≥0) * δ n) ((k : ℝ≥0) * δ n + δ n)
  have hrate (n : ℕ) (i : Fin n) :
      ((r : ℝ≥0∞) • nnvolume.restrict (Ioc 0 1)) (C n i) = (r / n : ℝ≥0) := by
    have hn : 0 < (n : ℝ≥0) := by exact_mod_cast Nat.zero_lt_of_lt i.isLt
    have hi : (i : ℝ≥0) + 1 ≤ n := by exact_mod_cast i.isLt
    have hu : (i : ℝ≥0) * δ n + δ n ≤ 1 := by
      calc (i : ℝ≥0) * δ n + δ n = ((i : ℝ≥0) + 1) * δ n := by ring
        _ = ((i : ℝ≥0) + 1) / n := by simp only [δ, mul_one_div]
        _ ≤ 1 := (div_le_one hn).mpr hi
    have hsub : C n i ⊆ Ioc 0 1 := fun t ht ↦
      ⟨lt_of_le_of_lt (by positivity) ht.1, ht.2.trans hu⟩
    simp only [smul_apply, Measure.restrict_apply measurableSet_Ioc,
      inter_eq_left.mpr hsub, C, nnvolume_Ioc, add_tsub_cancel_left, smul_eq_mul,
      ← ENNReal.coe_mul]
    simp only [δ, mul_one_div]
  have hfin (n : ℕ) (i : Fin n) :
      ((r : ℝ≥0∞) • nnvolume.restrict (Ioc 0 1)) (C n i) < ∞ := by
    rw [hrate]
    exact ENNReal.coe_lt_top
  -- Recover natural-valued cell counts to apply the existing small-rate limit.
  let X (n : ℕ) (i : Fin n) (ω : Ω) := ⌊(N ω (C n i)).toNNReal⌋₊
  have hX (n : ℕ) (i : Fin n) : HasLaw (X n i) (poissonMeasure (r / n)) P := by
    simpa only [hrate, ENNReal.toNNReal_coe] using
      h.hasLaw_natFloor (A := C n i) measurableSet_Ioc (hfin n i)
  have hcount (n : ℕ) : ∀ᵐ ω ∂P, ∀ i : Fin n, (X n i ω : ℝ≥0∞) = N ω (C n i) :=
    ae_all_iff.mpr fun i ↦ h.ae_natCast_natFloor_eq measurableSet_Ioc (hfin n i)
  rw [← measureReal_eq_zero_iff]
  apply le_antisymm _ measureReal_nonneg
  refine ge_of_tendsto (tendsto_measureReal_exists_two_le_of_hasLaw_poissonMeasure
    r hX) (eventually_atTop.2 ⟨1, fun n hn ↦ ?_⟩)
  -- On the full-measure count-recovery event, a multiple point forces a bad mesh cell.
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono_ae
  filter_upwards [hcount n] with ω hω
  rintro ⟨t, ht, hmass⟩
  have ht' : t ∈ Ioc ((0 : ℝ≥0) * δ n) ((n : ℝ≥0) * δ n) := by
    simpa [δ, Nat.ne_zero_of_lt hn] using ht
  obtain ⟨k, hk, hkt⟩ := mem_iUnion₂.mp (Ioc_subset_biUnion_Ioc n
    (fun k ↦ (k : ℝ≥0) * δ n) (by simpa using ht'))
  have hle : N ω {t} ≤ N ω (C n k) := by
    apply measure_mono (singleton_subset_iff.mpr ?_)
    simpa only [C, Nat.cast_add, Nat.cast_one, add_mul, one_mul] using hkt
  refine ⟨⟨k, Finset.mem_range.mp hk⟩, ?_⟩
  have : (1 : ℝ≥0∞) < X n ⟨k, Finset.mem_range.mp hk⟩ ω := by
    simpa only [hω] using hmass.trans_le hle
  exact Nat.succ_le_of_lt (by exact_mod_cast this)

private theorem ae_forall_singleton_le_one_restrict_Ioc
    {N : Ω → Measure ℝ≥0} {r : ℝ≥0}
    (h : IsPoissonRandomMeasure P N
      ((r : ℝ≥0∞) • nnvolume.restrict (Ioc 0 1))) :
    ∀ᵐ ω ∂P, ∀ t, N ω {t} ≤ 1 := by
  have hae : ∀ᵐ ω ∂P, ¬∃ t ∈ Ioc 0 1, 1 < N ω {t} := by
    simpa only [ae_iff, not_not] using measure_exists_multiple_singleton_Ioc_eq_zero h
  have houtside : ∀ᵐ ω ∂P, N ω (Ioc 0 1)ᶜ = 0 := by
    have hlaw := h.hasLaw (A := (Ioc 0 1)ᶜ) measurableSet_Ioc.compl (by simp)
    have hlaw' : HasLaw (fun ω ↦ N ω (Ioc 0 1)ᶜ) (Measure.dirac 0) P := by
      simpa [poissonMeasure_zero] using hlaw
    exact hlaw'.ae_eq_of_dirac
  filter_upwards [hae, houtside] with ω hω hout t
  by_cases ht : t ∈ Ioc 0 1
  · exact not_lt.mp fun hmass ↦ hω ⟨t, ht, hmass⟩
  · exact (measure_mono (singleton_subset_iff.mpr ht)).trans (hout.le.trans zero_le_one)

private theorem ae_forall_singleton_le_one_of_isFiniteMeasure
    {X : Type*} [MeasurableSpace X] [MeasurableSpace.CountablySeparated X]
    {N : Ω → Measure X} {Λ : Measure X} [IsFiniteMeasure Λ] [NullSingletonClass Λ]
    (h : IsPoissonRandomMeasure P N Λ) : ∀ᵐ ω ∂P, ∀ x, N ω {x} ≤ 1 := by
  -- Cantor space supplies a standard Borel source even when X itself is not standard Borel.
  obtain ⟨f, hf, hfinj⟩ :=
    MeasurableSpace.measurable_injection_nat_bool_of_countablySeparated X
  let μ := Λ.map f
  have : NullSingletonClass μ := Measure.nullSingletonClass_map_of_injective hf hfinj
  let r := (μ univ).toNNReal
  obtain ⟨g, hg⟩ := μ.exists_measurePreserving_of_nullSingleton_of_measure_univ_eq
    ((r : ℝ≥0∞) • nnvolume.restrict (Ioc 0 1)) (by simp [r])
  have hmap := (h.map hf).map hg.measurable
  rw [hg.map_eq] at hmap
  filter_upwards [ae_forall_singleton_le_one_restrict_Ioc hmap] with ω hω x
  calc N ω {x} ≤ (N ω).map f {f x} := by
        simpa only [image_singleton] using
          Measure.le_map_apply_image hf.aemeasurable ({x} : Set X)
    _ ≤ ((N ω).map f).map g {g (f x)} := by
        simpa only [image_singleton] using
          Measure.le_map_apply_image hg.measurable.aemeasurable ({f x} : Set (ℕ → Bool))
    _ ≤ 1 := hω _

/-- A Poisson random measure with σ-finite intensity having null singletons on a countably
separated measurable space has no multiple points almost surely. The bound holds for every
location on one event of full measure, without any pathwise integrality or finiteness
hypothesis. -/
theorem IsPoissonRandomMeasure.ae_forall_singleton_le_one
    {X : Type*} [MeasurableSpace X] [MeasurableSpace.CountablySeparated X]
    {N : Ω → Measure X} {Λ : Measure X} [SigmaFinite Λ] [NullSingletonClass Λ]
    (h : IsPoissonRandomMeasure P N Λ) : ∀ᵐ ω ∂P, ∀ x, N ω {x} ≤ 1 := by
  have hpiece (m : ℕ) : ∀ᵐ ω ∂P, ∀ x,
      ((N ω).restrict (spanningSets Λ m)) {x} ≤ 1 := by
    have : IsFiniteMeasure (Λ.restrict (spanningSets Λ m)) :=
      isFiniteMeasure_restrict.mpr (measure_spanningSets_lt_top Λ m).ne
    exact ae_forall_singleton_le_one_of_isFiniteMeasure
      (h.restrict (measurableSet_spanningSets Λ m))
  filter_upwards [ae_all_iff.mpr hpiece] with ω hω x
  obtain ⟨m, hm⟩ := mem_iUnion.mp ((iUnion_spanningSets Λ) ▸ mem_univ x)
  simpa only [Measure.restrict_apply' (measurableSet_spanningSets Λ m),
    inter_eq_left.mpr (singleton_subset_iff.mpr hm)] using hω m x

/-- A homogeneous temporal Poisson random measure is almost surely simple, including
at the origin and at rate zero. No additional intensity instances are needed. -/
theorem IsPoissonRandomMeasure.ae_forall_singleton_le_one_smul_nnvolume
    {N : Ω → Measure ℝ≥0} {r : ℝ≥0}
    (h : IsPoissonRandomMeasure P N ((r : ℝ≥0∞) • nnvolume)) :
    ∀ᵐ ω ∂P, ∀ t, N ω {t} ≤ 1 := by
  let := nnvolume.isLocallyFiniteMeasure_smul (c := (r : ℝ≥0∞)) ENNReal.coe_ne_top
  have : NullSingletonClass ((r : ℝ≥0∞) • nnvolume) := ⟨fun t ↦ by simp [smul_apply]⟩
  exact h.ae_forall_singleton_le_one

end TauCeti.Probability

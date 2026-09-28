/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Space
import Mathlib.Probability.Distributions.Geometric

/-!
# Finite support can fail to be dense for the infinite Wasserstein distance

On a countably infinite space with distance one between distinct points, every probability law
has a finite `∞`-moment, but a full-support law is at least distance one from every finitely
supported law. This gives a concrete failure of the finite-support density theorem for finite
Wasserstein exponents at the endpoint. The full-support witness is Mathlib's geometric law.

The separation step uses `TauCeti.eq_of_pairwise_edist_ge_of_wassersteinEDist_top_lt`.
The general Wasserstein conventions follow Villani, *Optimal Transport: Old and New*, Chapter 6.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace TauCeti

/-- The natural numbers with distance one between distinct points. -/
structure UnitDiscreteNat where
  /-- The underlying natural number. -/
  val : ℕ
  deriving DecidableEq

instance : Countable UnitDiscreteNat :=
  Countable.of_equiv ℕ
    ⟨UnitDiscreteNat.mk, UnitDiscreteNat.val, (by intro n; rfl), (by intro x; cases x; rfl)⟩
instance : TopologicalSpace UnitDiscreteNat := ⊥
instance : DiscreteTopology UnitDiscreteNat := ⟨rfl⟩

instance : MetricSpace UnitDiscreteNat :=
  MetricSpace.ofDistTopology (fun x y ↦ if x = y then 0 else 1)
    (by intro x; simp)
    (by intro x y; simp [eq_comm])
    (by
      intro x y z
      by_cases hxy : x = y
      · subst y; simp
      by_cases hyz : y = z
      · subst z; simp
      simp [hxy, hyz]
      split_ifs <;> norm_num)
    (by
      intro s; simp only [isOpen_discrete, true_iff]
      intro x hx; refine ⟨1, by norm_num, ?_⟩
      intro y hy
      by_cases h : x = y
      · exact h ▸ hx
      simp [h] at hy)
    (by intro x y; simp)

instance : MeasurableSpace UnitDiscreteNat := ⊤
instance : BorelSpace UnitDiscreteNat := ⟨borel_eq_top_of_discrete.symm⟩

instance : Infinite UnitDiscreteNat := Infinite.of_injective UnitDiscreteNat.mk (by
  intro a b h; exact congrArg UnitDiscreteNat.val h)

/-- Distance in the unit discrete metric. -/
@[simp] theorem UnitDiscreteNat.dist_eq (x y : UnitDiscreteNat) :
    dist x y = if x = y then 0 else 1 := rfl

/-- The unit discrete metric is complete: every Cauchy sequence is eventually constant. -/
instance : CompleteSpace UnitDiscreteNat := by
  refine Metric.complete_of_cauchySeq_tendsto fun u hu ↦ ?_
  obtain ⟨N, hN⟩ := (Metric.cauchySeq_iff'.1 hu) 1 (by norm_num)
  refine ⟨u N, tendsto_atTop_of_eventually_const (i₀ := N) (fun n hn ↦ ?_)⟩
  have hlt := hN n hn
  by_contra hne
  simp [UnitDiscreteNat.dist_eq, hne] at hlt

/-- Extended distance in the unit discrete metric. -/
@[simp] theorem UnitDiscreteNat.edist_eq (x y : UnitDiscreteNat) :
    edist x y = if x = y then 0 else 1 := by
  by_cases h : x = y
  · subst y; simp
  · simp [edist_dist, UnitDiscreteNat.dist_eq, h]

private lemma edist_eq_one_of_ne {x y : UnitDiscreteNat} (h : x ≠ y) :
    edist x y = 1 := by
  simp [UnitDiscreteNat.edist_eq, h]

private lemma edist_le_one (x y : UnitDiscreteNat) : edist x y ≤ 1 := by
  by_cases h : x = y
  · simp [h]
  · simp [edist_eq_one_of_ne h]

private noncomputable def half : unitInterval := ⟨1 / 2, by norm_num, by norm_num⟩

private noncomputable def geometricLaw : ProbabilityMeasure UnitDiscreteNat :=
  ⟨(geometricMeasure half).map UnitDiscreteNat.mk, inferInstance⟩

private lemma geometricLaw_singleton_pos (x : UnitDiscreteNat) :
    0 < (geometricLaw : Measure UnitDiscreteNat) {x} := by
  have hμ : (geometricLaw : Measure UnitDiscreteNat) =
      (geometricMeasure half).map UnitDiscreteNat.mk := rfl
  rw [hμ, Measure.map_apply Measurable.of_discrete MeasurableSet.of_discrete]
  have hset : UnitDiscreteNat.mk ⁻¹' ({x} : Set UnitDiscreteNat) = {x.val} := by
    ext n; cases x; simp
  rw [hset]
  have hp0 : half ≠ 0 := by
    intro h
    have hv := congrArg (fun p : unitInterval ↦ (p : ℝ)) h
    norm_num [half] at hv
  have hp1 : half ≠ 1 := by
    intro h
    have hv := congrArg (fun p : unitInterval ↦ (p : ℝ)) h
    norm_num [half] at hv
  rw [geometricMeasure_singleton hp0]
  exact ENNReal.ofReal_pos.mpr (geometricMeasure_pos hp0 hp1 x.val)

private lemma geometricLaw_finiteMoment :
    HasFiniteMoment ∞ (geometricLaw : Measure UnitDiscreteNat) := by
  refine hasFiniteMoment_def.2 ⟨⟨0⟩, MemLp.of_enorm_bound
    measurable_edist_right.aestronglyMeasurable (C := 1) (by simp) ?_⟩
  filter_upwards [] with x
  simpa only [enorm_eq_self] using edist_le_one ⟨0⟩ x

private noncomputable def geometricWassersteinLaw : WassersteinSpace ∞ UnitDiscreteNat :=
  WassersteinSpace.mk geometricLaw geometricLaw_finiteMoment

private theorem one_le_edist_geometricLaw_of_finite_support
    (ν : WassersteinSpace ∞ UnitDiscreteNat) (s : Finset UnitDiscreteNat)
    (hν : ∀ᵐ y ∂(ν : Measure UnitDiscreteNat), y ∈ s) :
    (1 : ℝ≥0∞) ≤ edist geometricWassersteinLaw ν := by
  by_contra h
  have hsep : Pairwise (fun x y : UnitDiscreteNat ↦ (1 : ℝ≥0∞) ≤ edist x y) := by
    intro x y hxy
    simp [edist_eq_one_of_ne hxy]
  have hlt := lt_of_not_ge h
  have hcoe : WassersteinSpace.toProbabilityMeasure geometricWassersteinLaw = geometricLaw :=
    WassersteinSpace.coe_mk _ _
  rw [WassersteinSpace.edist_def, hcoe] at hlt
  have heq : (geometricLaw : Measure UnitDiscreteNat) = (ν : Measure UnitDiscreteNat) :=
    eq_of_pairwise_edist_ge_of_wassersteinEDist_top_lt hsep hlt
  obtain ⟨x, -, hx⟩ :=
    (Set.infinite_univ : (Set.univ : Set UnitDiscreteNat).Infinite).exists_notMem_finset s
  have hzero : (ν : Measure UnitDiscreteNat) {x} = 0 := by
    have hnull : (ν : Measure UnitDiscreteNat) (s : Set UnitDiscreteNat)ᶜ = 0 := mem_ae_iff.mp hν
    exact measure_mono_null (by
      simpa only [Set.singleton_subset_iff, Set.mem_compl_iff, Finset.mem_coe] using hx) hnull
  have hpos := geometricLaw_singleton_pos x
  rw [heq] at hpos
  exact (ne_of_gt hpos) hzero

/-- Finitely supported laws are not dense in the infinite-exponent Wasserstein space over
an infinite countable space with unit distance between distinct points. -/
theorem WassersteinSpace.not_dense_setOfPred_ae_mem_finset_top_unitDiscreteNat :
    ¬ Dense {ν : WassersteinSpace ∞ UnitDiscreteNat |
      ∃ s : Finset UnitDiscreteNat,
        ((ν : ProbabilityMeasure UnitDiscreteNat) : Measure UnitDiscreteNat)
          ((s : Set UnitDiscreteNat)ᶜ) = 0} := by
  intro hd
  obtain ⟨ν, hball, ⟨s, hs⟩⟩ :=
    (Metric.dense_iff.mp hd geometricWassersteinLaw 1 (by norm_num))
  have hsep := one_le_edist_geometricLaw_of_finite_support ν s (mem_ae_iff.mpr hs)
  have hdist : dist geometricWassersteinLaw ν < 1 := by
    rw [dist_comm]
    exact Metric.mem_ball.mp hball
  have hed : edist geometricWassersteinLaw ν < 1 := by
    rwa [edist_dist, ENNReal.ofReal_lt_one]
  exact not_lt_of_ge hsep hed

end TauCeti

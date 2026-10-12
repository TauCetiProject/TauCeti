/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Space
-- Proof-only: the bounded prefix metric on Baire sequences and a full-support probability law
-- on the natural numbers.
import Mathlib.Probability.Distributions.Geometric
import Mathlib.Topology.MetricSpace.PiNat

/-!
# Finite support is not dense at the infinite Wasserstein exponent

Finitely supported laws need not be dense in `P_∞`, even over a complete separable metric space.
The counterexample uses Baire sequences `ℕ → ℕ` with Mathlib's bounded prefix metric
`PiNat.metricSpaceNatNat`. Constant sequences are pairwise one unit apart, while the whole ground
space has diameter at most one. Pushing a nondegenerate geometric law forward to the constant
sequences therefore gives an element of `P_∞` that stays at least one unit from every finitely
supported law.

The statement locally selects the compatible prefix metric on `ℕ → ℕ`, because Mathlib
deliberately does not register this noncanonical metric as a global instance. This keeps the
example from installing a competing metric on function spaces.

## Main statement

* `TauCeti.WassersteinSpace.not_dense_setOfPred_ae_mem_finset_top_baire` — for the bounded
  complete prefix metric compatible with the product topology on Baire sequences, finitely
  supported laws are not dense in `P_∞`.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology

namespace TauCeti.WassersteinSpace

/-- **Finite support need not be dense in `P_∞`.** There is a complete bounded metric compatible
with the product topology on Baire sequences `ℕ → ℕ` for which the probability laws carried by a
finite set are not dense in the infinite-exponent Wasserstein space.

The metric is Mathlib's prefix metric: two different sequences have distance `2⁻ⁿ`, where `n` is
their first differing coordinate. The witness law is a geometric mixture of the constant
sequences. Every finite set of target sequences omits the zeroth coordinate of some constant
sequence of positive mass, and moving that mass into the target set costs exactly one. -/
theorem not_dense_setOfPred_ae_mem_finset_top_baire :
    letI : MetricSpace (ℕ → ℕ) := PiNat.metricSpaceNatNat
    ¬ Dense {μ : WassersteinSpace ∞ (ℕ → ℕ) |
      ∃ s : Finset (ℕ → ℕ),
        ((μ : ProbabilityMeasure (ℕ → ℕ)) : Measure (ℕ → ℕ)) ((s : Set (ℕ → ℕ))ᶜ) = 0} := by
  let _ : MetricSpace (ℕ → ℕ) := PiNat.metricSpaceNatNat
  let p : unitInterval := ⟨1 / 2, by constructor <;> norm_num⟩
  have hp0 : p ≠ 0 := by
    intro h
    have := congrArg (fun q : unitInterval ↦ (q : ℝ)) h
    norm_num [p] at this
  have hp1 : p ≠ 1 := by
    intro h
    have := congrArg (fun q : unitInterval ↦ (q : ℝ)) h
    norm_num [p] at this
  let c : ℕ → (ℕ → ℕ) := fun n _ ↦ n
  have hc : Measurable c := Measurable.of_eval fun _ ↦ measurable_id
  let μ : Measure (ℕ → ℕ) := (geometricMeasure p).map c
  have hμprob : IsProbabilityMeasure μ := by
    dsimp only [μ]
    infer_instance
  have hμmom : TauCeti.HasFiniteMoment ∞ μ := by
    rw [TauCeti.hasFiniteMoment_def]
    refine ⟨0, memLp_top_of_bound_enorm measurable_edist_right.aestronglyMeasurable 1
      (.of_forall fun y ↦ ?_)⟩
    rw [enorm_eq_self, edist_dist]
    exact_mod_cast PiNat.dist_le_one (0 : ℕ → ℕ) y
  let μW : WassersteinSpace ∞ (ℕ → ℕ) := mk ⟨μ, hμprob⟩ hμmom
  intro hdense
  rw [EMetric.dense_iff] at hdense
  obtain ⟨ν, hνball, s, hνs⟩ := hdense μW 1 (by norm_num)
  rw [Metric.mem_eball, edist_comm, edist_def] at hνball
  obtain ⟨π, hπ, hπnorm⟩ := wassersteinEDist_lt_iff.mp hνball
  have hπess : eLpNormEssSup (fun z : (ℕ → ℕ) × (ℕ → ℕ) ↦ edist z.1 z.2) π < 1 :=
    eLpNormEssSup_le_eLpNorm_top.trans_lt hπnorm
  have hdist : ∀ᵐ z ∂π, edist z.1 z.2 < 1 :=
    (ae_le_eLpNormEssSup (f := fun z : (ℕ → ℕ) × (ℕ → ℕ) ↦ edist z.1 z.2)
      (μ := π)).mono fun _ hz ↦ hz.trans_lt hπess
  have hsnd : ∀ᵐ z ∂π, z.2 ∈ s := by
    rw [ae_iff]
    have h : π.snd ((s : Set (ℕ → ℕ))ᶜ) = 0 := by rw [hπ.snd_eq]; exact hνs
    rwa [Measure.snd_apply s.measurableSet.compl] at h
  obtain ⟨n, hnsub⟩ := Finset.exists_nat_subset_range (s.image fun x ↦ x 0)
  have hn : n ∉ s.image fun x ↦ x 0 := fun hn ↦ by simpa using hnsub hn
  have hfst_ne : ∀ᵐ z ∂π, z.1 ≠ c n := by
    filter_upwards [hdist, hsnd] with z hzdist hzs
    intro hz
    have hcoord : z.2 0 ≠ n := by
      intro h
      apply hn
      rw [Finset.mem_image]
      exact ⟨z.2, hzs, by simpa [c] using h⟩
    have hne : c n ≠ z.2 := fun h ↦ hcoord (by simpa [c] using (congrFun h 0).symm)
    have hfirst : PiNat.firstDiff (c n) z.2 = 0 := by
      by_contra hzero
      have heq := PiNat.apply_eq_of_lt_firstDiff (Nat.pos_of_ne_zero hzero)
      exact hcoord (by simpa [c] using heq.symm)
    have : edist (c n) z.2 = 1 := by
      rw [edist_dist, PiNat.dist_eq_of_ne hne, hfirst]
      norm_num
    exact (not_lt_of_ge this.ge) (hz ▸ hzdist)
  have hπzero : π (Prod.fst ⁻¹' {c n}) = 0 := by
    have h := mem_ae_iff.mp hfst_ne
    have hset : {z : (ℕ → ℕ) × (ℕ → ℕ) | z.1 ≠ c n}ᶜ = Prod.fst ⁻¹' {c n} := by
      ext z
      simp
    rwa [hset] at h
  have hcoe : (μW : ProbabilityMeasure (ℕ → ℕ)) = ⟨μ, hμprob⟩ := by
    dsimp only [μW]
    exact coe_mk _ _
  have hπfst : π.fst = μ := by
    calc
      π.fst = ((μW : ProbabilityMeasure (ℕ → ℕ)) : Measure (ℕ → ℕ)) := hπ.fst_eq
      _ = μ := congrArg ProbabilityMeasure.toMeasure hcoe
  have hμzero : μ {c n} = 0 := by
    calc
      μ {c n} = π.fst {c n} := by rw [hπfst]
      _ = π (Prod.fst ⁻¹' {c n}) := Measure.fst_apply (MeasurableSet.singleton _)
      _ = 0 := hπzero
  have hμpos : μ {c n} ≠ 0 := by
    dsimp only [μ]
    rw [Measure.map_apply hc (MeasurableSet.singleton _)]
    have hpreimage : c ⁻¹' {c n} = {n} := by
      ext k
      simp only [mem_preimage, mem_singleton_iff]
      constructor
      · intro h
        simpa [c] using congrFun h 0
      · rintro rfl
        rfl
    rw [hpreimage, geometricMeasure_singleton hp0]
    exact (ENNReal.ofReal_pos.mpr (geometricMeasure_pos (p := p)
      hp0 hp1 n)).ne'
  exact hμpos hμzero

end TauCeti.WassersteinSpace

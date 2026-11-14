/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Process.HittingTime
public import Mathlib.Probability.Process.Indistinguishable
public import Mathlib.Topology.Metrizable.CompletelyMetrizable
public import Mathlib.Topology.Sequences
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable

/-!
# Everywhere-continuous measurable versions of stochastic processes

An almost-surely continuous process whose fixed-time evaluations are almost everywhere strongly
measurable need not have measurable evaluations or continuous sample paths on exceptional outcomes.
On a raw measurable space without completeness, replacing the process on an unmeasurable null set
can destroy measurability, while separate fixed-time measurable representatives need not assemble
into continuous paths.

When the time index is separable and Fréchet–Urysohn and the state space is completely metrizable,
choosing fixed-time strongly measurable representatives along a countable dense time sequence,
passing to sequential limits at every time via `Filter.limUnder`, and resetting paths to a constant
value on a measurable null superset `MeasureTheory.toMeasurable` of the exceptional event produces
an indistinguishable process whose evaluations are strongly measurable at every time and whose
sample paths are continuous everywhere. When the process almost surely takes a deterministic value
at a reference time, using that value on the exceptional set makes the version take it on every
sample path.

Indistinguishable processes also have almost everywhere equal `MeasureTheory.hittingAfter` times
for every target set, without path regularity or measurability assumptions.
-/

public section

open Filter MeasureTheory ProbabilityTheory Set TopologicalSpace
open scoped Topology

namespace ProbabilityTheory.Indistinguishable

/-- Indistinguishable processes have almost everywhere equal first hitting times of any set after
any starting time. -/
theorem hittingAfter_ae_eq {ι Ω E : Type*} [ConditionallyCompleteLinearOrder ι]
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X Y : ι → Ω → E}
    (h : X ≡ᵐ[P] Y) (s : Set E) (a : ι) :
    hittingAfter X s a =ᵐ[P] hittingAfter Y s a := by
  classical
  filter_upwards [h] with ω hω
  rw [hittingAfter_def, hittingAfter_def]
  simp_rw [hω]

end ProbabilityTheory.Indistinguishable

namespace TauCeti.Probability

section Version

variable {ι Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  [TopologicalSpace ι] [SeparableSpace ι] [FrechetUrysohnSpace ι]
  [TopologicalSpace E] [IsCompletelyMetrizableSpace E]

private theorem exists_stronglyMeasurable_continuous_indist_aux [Nonempty ι] [Nonempty E]
    {X : ι → Ω → E} (hX : ∀ t, AEStronglyMeasurable (X t) P)
    (hc : ∀ᵐ ω ∂P, Continuous (X · ω)) (e₀ : E) {q : Ω → Prop} (hq : ∀ᵐ ω ∂P, q ω) :
    ∃ Y : ι → Ω → E, (∀ t, StronglyMeasurable (Y t)) ∧ (∀ ω, Continuous (Y · ω)) ∧
      (∀ ω, (q ω ∧ ∀ t, Y t ω = X t ω) ∨ ∀ t, Y t ω = e₀) ∧ Y ≡ᵐ[P] X := by
  classical
  let d : ℕ → ι := denseSeq ι
  have hlim (t : ι) : ∃ k : ℕ → ℕ, Tendsto (fun n ↦ d (k n)) atTop (𝓝 t) := by
    obtain ⟨u, hu_mem, hu_lim⟩ := mem_closure_iff_seq_limit.mp (denseRange_denseSeq ι t)
    choose k hk using fun n ↦ mem_range.mp (hu_mem n)
    exact ⟨k, (funext hk).symm ▸ hu_lim⟩
  choose seq hseq using hlim
  let M (k : ℕ) : Ω → E := (hX (d k)).mk (X (d k))
  have hM_ae : ∀ᵐ ω ∂P, ∀ k : ℕ, M k ω = X (d k) ω :=
    ae_all_iff.mpr fun k ↦ (hX (d k)).ae_eq_mk.symm
  let G : Set Ω := {ω | Continuous (X · ω) ∧ q ω ∧ ∀ k : ℕ, M k ω = X (d k) ω}
  have hG : ∀ᵐ ω ∂P, ω ∈ G := by
    filter_upwards [hc, hq, hM_ae] with ω h₁ h₂ h₃ using ⟨h₁, h₂, h₃⟩
  let N : Set Ω := toMeasurable P Gᶜ
  have hN_meas : MeasurableSet N := measurableSet_toMeasurable P Gᶜ
  have hN_null : P N = 0 := by
    rw [measure_toMeasurable]
    exact ae_iff.mp (hG.mono fun _ h ↦ h)
  let Y (t : ι) (ω : Ω) : E :=
    if ω ∈ N then e₀ else limUnder atTop (fun n ↦ M (seq t n) ω)
  have hωG {ω : Ω} (hω : ω ∉ N) : ω ∈ G := by
    by_contra hnot
    exact hω (subset_toMeasurable P Gᶜ hnot)
  have hY_eq {ω : Ω} (hω : ω ∉ N) (t : ι) : Y t ω = X t ω := by
    have htend : Tendsto (fun n ↦ M (seq t n) ω) atTop (𝓝 (X t ω)) := by
      simpa only [Function.comp_def, (hωG hω).2.2] using ((hωG hω).1.tendsto t).comp (hseq t)
    simp only [Y, ite_eq_right hω, htend.limUnder_eq]
  refine ⟨Y, fun t ↦ ?_, fun ω ↦ ?_, fun ω ↦ ?_, ?_⟩
  · exact stronglyMeasurable_const.ite hN_meas
      (StronglyMeasurable.limUnder fun n ↦ (hX (d (seq t n))).stronglyMeasurable_mk)
  · by_cases hω : ω ∈ N
    · simpa only [Y, ite_eq_left hω] using continuous_const
    · simpa only [funext (hY_eq hω)] using (hωG hω).1
  · by_cases hω : ω ∈ N
    · exact Or.inr fun t ↦ by simp only [Y, ite_eq_left hω]
    · exact Or.inl ⟨(hωG hω).2.1, hY_eq hω⟩
  · filter_upwards [compl_mem_ae_iff.mpr hN_null] with ω hω t
    exact hY_eq hω t

/-- An almost-surely continuous process with almost everywhere strongly measurable fixed-time
evaluations has an indistinguishable version whose fixed-time evaluations are strongly measurable
and whose sample paths are continuous everywhere. -/
theorem exists_stronglyMeasurable_continuous_indist {X : ι → Ω → E}
    (hX : ∀ t, AEStronglyMeasurable (X t) P) (hc : ∀ᵐ ω ∂P, Continuous (X · ω)) :
    ∃ Y : ι → Ω → E, (∀ t, StronglyMeasurable (Y t)) ∧ (∀ ω, Continuous (Y · ω)) ∧
      Y ≡ᵐ[P] X := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨X, fun t ↦ (IsEmpty.false t).elim,
      fun _ ↦ continuous_iff_continuousAt.mpr fun t ↦ (IsEmpty.false t).elim, .rfl⟩
  rcases isEmpty_or_nonempty E with hE | hE
  · exact ⟨X, fun _ ↦ .of_subsingleton_cod, fun _ ↦ continuous_of_const fun _ _ ↦
      Subsingleton.elim _ _, .rfl⟩
  obtain ⟨Y, hYm, hYc, -, hYX⟩ := exists_stronglyMeasurable_continuous_indist_aux hX hc
    (Classical.arbitrary E) (Eventually.of_forall fun _ ↦ True.intro)
  exact ⟨Y, hYm, hYc, hYX⟩

/-- An almost-surely continuous process with almost everywhere strongly measurable evaluations
that almost surely takes a deterministic value `e₀` at `t₀` has an indistinguishable version that
is strongly measurable at every time, continuous on every path, and equal to `e₀` at `t₀` on every
path. -/
theorem exists_stronglyMeasurable_continuous_eval_eq_indist {X : ι → Ω → E}
    (hX : ∀ t, AEStronglyMeasurable (X t) P) (hc : ∀ᵐ ω ∂P, Continuous (X · ω))
    (t₀ : ι) (e₀ : E) (h0 : ∀ᵐ ω ∂P, X t₀ ω = e₀) :
    ∃ Y : ι → Ω → E, (∀ t, StronglyMeasurable (Y t)) ∧ (∀ ω, Continuous (Y · ω)) ∧
      (∀ ω, Y t₀ ω = e₀) ∧ Y ≡ᵐ[P] X := by
  have : Nonempty ι := ⟨t₀⟩
  have : Nonempty E := ⟨e₀⟩
  obtain ⟨Y, hYm, hYc, hYq, hYX⟩ :=
    exists_stronglyMeasurable_continuous_indist_aux hX hc e₀ h0
  refine ⟨Y, hYm, hYc, fun ω ↦ ?_, hYX⟩
  rcases hYq ω with ⟨hX0, hYeq⟩ | hYconst
  · exact (hYeq t₀).trans hX0
  · exact hYconst t₀

end Version

end TauCeti.Probability

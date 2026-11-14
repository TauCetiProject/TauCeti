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

An almost-surely continuous process with almost everywhere strongly measurable fixed-time
evaluations need not have measurable evaluations or continuous sample paths on exceptional outcomes.
When the time index is separable and Fréchet–Urysohn and the state space is completely metrizable,
choosing strongly measurable representatives along `TopologicalSpace.denseSeq`, passing to
sequential limits via `Filter.limUnder`, and resetting paths to a constant on a measurable null
superset (`MeasureTheory.toMeasurable`) produces an indistinguishable version that is strongly
measurable at every time and continuous on every path, and takes any almost-sure deterministic
initial value everywhere.

Indistinguishable processes also have almost everywhere equal `MeasureTheory.hittingAfter` times.
-/

public section

open Filter MeasureTheory ProbabilityTheory Set TopologicalSpace
open scoped Topology

namespace ProbabilityTheory.Indistinguishable

/-- Post-composing indistinguishable processes with a function preserves indistinguishability. -/
theorem comp {ι Ω E F : Type*} {_ : MeasurableSpace Ω} {P : Measure Ω} {X Y : ι → Ω → E}
    (h : X ≡ᵐ[P] Y) (f : E → F) : (fun t ω ↦ f (X t ω)) ≡ᵐ[P] (fun t ω ↦ f (Y t ω)) :=
  h.mono fun _ hω t ↦ congrArg f (hω t)

/-- Indistinguishable processes have almost everywhere equal first hitting times of any set after
any starting time. -/
theorem hittingAfter_ae_eq {ι Ω E : Type*} [ConditionallyCompleteLinearOrder ι]
    {_ : MeasurableSpace Ω} {P : Measure Ω} {X Y : ι → Ω → E}
    (h : X ≡ᵐ[P] Y) (s : Set E) (a : ι) :
    hittingAfter X s a =ᵐ[P] hittingAfter Y s a := by
  classical
  exact h.mono fun _ hω ↦ by simp only [hittingAfter_def, hω]

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
  have hseq_ex (t : ι) : ∃ k : ℕ → ℕ, Tendsto (fun n ↦ d (k n)) atTop (𝓝 t) := by
    obtain ⟨u, hu_mem, hu_lim⟩ := mem_closure_iff_seq_limit.mp (denseRange_denseSeq ι t)
    choose k hk using fun n ↦ mem_range.mp (hu_mem n)
    exact ⟨k, (funext hk).symm ▸ hu_lim⟩
  choose seq hseq using hseq_ex
  let M (k : ℕ) : Ω → E := (hX (d k)).mk (X (d k))
  let G : Set Ω := {ω | Continuous (X · ω) ∧ q ω ∧ ∀ k : ℕ, M k ω = X (d k) ω}
  let N : Set Ω := toMeasurable P Gᶜ
  have hN_null : P N = 0 := by
    rw [measure_toMeasurable, ← mem_ae_iff]
    filter_upwards [hc, hq, ae_all_iff.mpr fun k ↦ (hX (d k)).ae_eq_mk.symm] with _ h₁ h₂ h₃
    exact ⟨h₁, h₂, h₃⟩
  let Y (t : ι) (ω : Ω) : E := if ω ∈ N then e₀ else limUnder atTop (fun n ↦ M (seq t n) ω)
  refine ⟨Y, fun t ↦ stronglyMeasurable_const.ite (measurableSet_toMeasurable P Gᶜ)
    (StronglyMeasurable.limUnder fun n ↦ (hX (d (seq t n))).stronglyMeasurable_mk), ?_⟩
  have hωG' {ω : Ω} (hω : ω ∉ N) : ω ∈ G := by
    by_contra hnot; exact hω (subset_toMeasurable P Gᶜ hnot)
  have hY_eq {ω : Ω} (hω : ω ∉ N) (t : ι) : Y t ω = X t ω := by
    have ht : Tendsto (fun n ↦ M (seq t n) ω) atTop (𝓝 (X t ω)) := by
      simpa only [Function.comp_def, (hωG' hω).2.2] using ((hωG' hω).1.tendsto t).comp (hseq t)
    simp only [Y, ite_eq_right hω, ht.limUnder_eq]
  refine ⟨fun ω ↦ ?_, fun ω ↦ ?_, eventually_of_mem (compl_mem_ae_iff.mpr hN_null) fun _ ↦ hY_eq⟩
  · by_cases hω : ω ∈ N
    · simpa only [Y, ite_eq_left hω] using continuous_const
    · simpa only [funext (hY_eq hω)] using (hωG' hω).1
  · exact if hω : ω ∈ N then Or.inr fun t ↦ by simp only [Y, ite_eq_left hω]
      else Or.inl ⟨(hωG' hω).2.1, hY_eq hω⟩

/-- An almost-surely continuous process with almost everywhere strongly measurable fixed-time
evaluations has an indistinguishable version whose fixed-time evaluations are strongly measurable
and whose sample paths are continuous everywhere. -/
theorem exists_stronglyMeasurable_continuous_indist {X : ι → Ω → E}
    (hX : ∀ t, AEStronglyMeasurable (X t) P) (hc : ∀ᵐ ω ∂P, Continuous (X · ω)) :
    ∃ Y : ι → Ω → E, (∀ t, StronglyMeasurable (Y t)) ∧ (∀ ω, Continuous (Y · ω)) ∧
      Y ≡ᵐ[P] X := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨X, isEmptyElim, fun _ ↦ continuous_iff_continuousAt.mpr isEmptyElim, .rfl⟩
  rcases isEmpty_or_nonempty E with hE | hE
  · exact ⟨X, fun _ ↦ .of_subsingleton_cod,
      fun _ ↦ continuous_of_const fun _ _ ↦ Subsingleton.elim _ _, .rfl⟩
  obtain ⟨Y, hYm, hYc, -, hYX⟩ := exists_stronglyMeasurable_continuous_indist_aux hX hc
    (Classical.arbitrary E) (.of_forall fun _ ↦ True.intro)
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
  have : Nonempty ι := ⟨t₀⟩; have : Nonempty E := ⟨e₀⟩
  obtain ⟨Y, hYm, hYc, hYq, hYX⟩ := exists_stronglyMeasurable_continuous_indist_aux hX hc e₀ h0
  exact ⟨Y, hYm, hYc, fun ω ↦ (hYq ω).elim (fun h ↦ (h.2 t₀).trans h.1) (· t₀), hYX⟩

end Version

end TauCeti.Probability

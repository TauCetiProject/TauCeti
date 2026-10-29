/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Process.PathLaw.Mixture
public import TauCeti.Probability.Exchangeability.PathSpace.Law.Basic
public import TauCeti.Probability.DeFinetti.Representation
import TauCeti.Probability.Exchangeability.ConditionallyIID.Construct
import TauCeti.Probability.Exchangeability.PathSpace.Law.Bridge

/-!
# Exchangeability and representation of i.i.d. mixtures

Every de Finetti barycenter of a probability mixing law is an exchangeable path law. Conversely,
over a standard Borel state space, every exchangeable probability law is the barycenter of a
unique probability mixing law. This file connects the general path-law mixture construction in
`TauCeti.Probability.Process.PathLaw.Mixture` to those symmetry and representation results.

The affine correspondence packaging these results, and its restriction to point masses, is in
`TauCeti.Probability.DeFinetti.Correspondence`.

## Main results

* `exchangeableLaw_deFinettiBarycenter` — a mixture of i.i.d. laws is exchangeable.
* `ExchangeableLaw.existsUnique_mixingLaw` — an exchangeable probability law is the barycenter
  of exactly one probability mixing law.

## References

* Olav Kallenberg, *Probabilistic Symmetries and Invariance Principles*, Springer, 2005,
  Chapter 1, Theorem 1.1.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace Probability

variable {α : Type*} [MeasurableSpace α]

/-- **A barycenter is an exchangeable path law.** Drawing `P` from `π` and then an i.i.d.
`P`-sequence produces a law invariant under every permutation of the time coordinate.

The witness is the canonical conditionally i.i.d. construction `iidMixtureLaw π id`, whose
coordinate process is exchangeable and whose path law is this barycenter. -/
theorem exchangeableLaw_deFinettiBarycenter {π : Measure (ProbabilityMeasure α)}
    [IsProbabilityMeasure π] : ExchangeableLaw (Measure.deFinettiBarycenter π) := by
  have := isProbabilityMeasure_iidMixtureLaw (π := π) (P := id) measurable_id
  have hX := exchangeable_iidMixtureLaw (π := π) (P := id) measurable_id
  have hcoord : ∀ n, AEMeasurable
      (fun ω : ProbabilityMeasure α × (ℕ → α) => ω.2 n) (iidMixtureLaw π id) :=
    fun n => ((measurable_pi_apply n).comp measurable_snd).aemeasurable
  have hlaw := (exchangeable_iff_exchangeableLaw_pathLaw
    (X := fun n (ω : ProbabilityMeasure α × (ℕ → α)) => ω.2 n) hcoord).mp hX
  rw [pathLaw_iidMixtureLaw (π := π) (P := id) measurable_id] at hlaw
  simpa [Measure.deFinettiBarycenter_def] using hlaw

/-- **The mixing law of an exchangeable path law.** Over a standard Borel state space, an
exchangeable probability measure on `ℕ → α` is the de Finetti barycenter of exactly one mixing
law.

This is the path-law form of `deFinetti_mixture`, obtained by taking the coordinate process of
`ρ` itself: existence is de Finetti's theorem and uniqueness is injectivity of the mixture. Like
`deFinetti_mixture`, it needs no nonemptiness hypothesis on the state space. -/
theorem ExchangeableLaw.existsUnique_mixingLaw [StandardBorelSpace α] {ρ : Measure (ℕ → α)}
    [IsProbabilityMeasure ρ] (hρ : ExchangeableLaw ρ) :
    ∃! π : ProbabilityMeasure (ProbabilityMeasure α), ρ = Measure.deFinettiBarycenter π := by
  have hcoord : ∀ n, Measurable fun x : ℕ → α => x n := fun n => measurable_pi_apply n
  have hpath : pathLaw ρ (fun n (x : ℕ → α) => x n) = ρ := by simp [pathLaw_def]
  have hexch : Exchangeable ρ (fun n (x : ℕ → α) => x n) :=
    (exchangeable_iff_exchangeableLaw_pathLaw fun n => (hcoord n).aemeasurable).2
      (by simpa [pathLaw_def] using hρ)
  simpa [hpath, Measure.deFinettiBarycenter_def] using
    deFinetti_mixture hexch fun n => (hcoord n).aemeasurable

end Probability

end TauCeti

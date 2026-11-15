/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Process.Indistinguishable
public import Mathlib.Topology.Separation.Hausdorff
-- Private: `exists_countable_dense` is used only inside proofs.
import Mathlib.Topology.Bases

/-!
# Indistinguishability of modifications with continuous paths

Modifications (`∀ t, X t =ᵐ[P] Y t`) agree at each fixed index outside an index-dependent null set,
whereas indistinguishable processes (`X ≡ᵐ[P] Y`) agree simultaneously at all indices outside a
single common null set. These notions coincide when the index type is countable, and also when the
index space is separable, the state space is Hausdorff, and both processes have almost-surely
continuous sample paths.

## Main results

* `ProbabilityTheory.indist_iff_forall_ae_eq`: on a countable index type, indistinguishability is
  equivalent to modification.
* `ProbabilityTheory.indist_of_ae_continuous_of_dense`: two processes with almost-surely continuous
  paths in a `T2Space` that agree almost everywhere at each point of a countable dense set are
  indistinguishable.
* `ProbabilityTheory.indist_of_ae_continuous` and
  `ProbabilityTheory.indist_iff_forall_ae_eq_of_ae_continuous`: on a separable index space,
  modifications with almost-surely continuous `T2Space`-valued paths are indistinguishable.

## References

* Ioannis Karatzas and Steven E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, Problem 1.1.5.
-/

public section

open MeasureTheory Set TopologicalSpace

namespace ProbabilityTheory

variable {ι Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X Y : ι → Ω → E}

/-- On a countable index type, two processes are indistinguishable if and only if they are
modifications of one another. -/
theorem indist_iff_forall_ae_eq [Countable ι] :
    X ≡ᵐ[P] Y ↔ ∀ t, X t =ᵐ[P] Y t :=
  ⟨fun h t ↦ h.ae_eq_eval t, fun h ↦ ae_all_iff.mpr h⟩

/-- Two processes taking values in a Hausdorff space with almost-surely continuous sample paths are
indistinguishable as soon as they agree almost everywhere at each point of a countable dense set of
indices. -/
theorem indist_of_ae_continuous_of_dense [TopologicalSpace ι] [TopologicalSpace E] [T2Space E]
    {D : Set ι} (hDc : D.Countable) (hDd : Dense D)
    (hX : ∀ᵐ ω ∂P, Continuous (X · ω)) (hY : ∀ᵐ ω ∂P, Continuous (Y · ω))
    (heq : ∀ t ∈ D, X t =ᵐ[P] Y t) :
    X ≡ᵐ[P] Y := by
  filter_upwards [hX, hY, (ae_ball_iff hDc).mpr heq] with ω hcX hcY hD t
  exact congrFun (Continuous.ext_on hDd hcX hcY hD) t

/-- On a separable index space, modifications with almost-surely continuous sample paths in a
Hausdorff space are indistinguishable. -/
theorem indist_of_ae_continuous [TopologicalSpace ι] [SeparableSpace ι]
    [TopologicalSpace E] [T2Space E]
    (hX : ∀ᵐ ω ∂P, Continuous (X · ω)) (hY : ∀ᵐ ω ∂P, Continuous (Y · ω))
    (heq : ∀ t, X t =ᵐ[P] Y t) :
    X ≡ᵐ[P] Y := by
  obtain ⟨D, hDc, hDd⟩ := exists_countable_dense ι
  exact indist_of_ae_continuous_of_dense hDc hDd hX hY fun t _ ↦ heq t

/-- On a separable index space, two processes with almost-surely continuous sample paths in a
Hausdorff space are indistinguishable if and only if they are modifications of each other. -/
theorem indist_iff_forall_ae_eq_of_ae_continuous [TopologicalSpace ι] [SeparableSpace ι]
    [TopologicalSpace E] [T2Space E]
    (hX : ∀ᵐ ω ∂P, Continuous (X · ω)) (hY : ∀ᵐ ω ∂P, Continuous (Y · ω)) :
    X ≡ᵐ[P] Y ↔ ∀ t, X t =ᵐ[P] Y t :=
  ⟨fun h t ↦ h.ae_eq_eval t, indist_of_ae_continuous hX hY⟩

end ProbabilityTheory

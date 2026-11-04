/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.NoetherianType.Quotient
public import TauCeti.RingTheory.Huber.TopologicallyFiniteType.Complete

import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Noetherian

/-!
# Noetherian type and Huber's standing class ascend along homomorphisms topologically of finite type

Let `A` be a Huber ring of noetherian type (or in Huber's standing class) and `φ : A → B` a ring
homomorphism topologically of finite type, so that `B` is an open quotient of the completion of a
weighted restricted power-series ring `A⟨X₁, …, Xₖ⟩_T` with finite weights `Tᵢ`. Then `B` is again
of noetherian type, and stays in Huber's standing class when `A` is (Huber 1994, Corollary 3.4;
Huber 1996, (1.1.1); Wedhorn, Proposition 6.35 and Remark 6.37(1)). This is the form in which
the finiteness hypotheses of Huber's theory reach rational localisations and algebras topologically
of finite type.

The defining alternatives are treated separately.

* If `A` is a strongly noetherian Tate ring, `B` is Tate, complete and Hausdorff, and strongly
  noetherian (`TauCeti.Huber.IsTopologicallyFiniteType.isStronglyNoetherian`).
* If `A` has a noetherian ring of definition `A₀` with ideal of definition `I`, the ring of
  definition `A₀⟨X⟩_T` of `A⟨X⟩_T` is not noetherian in general, but modulo its ideal of
  definition `I⟨X⟩_T` it is a quotient of the polynomial ring over `A₀` in one variable for each
  weighted variable `t Xᵢ` with `t ∈ Tᵢ`. Since the weights are finite, `A₀⟨X⟩_T ⧸ I⟨X⟩_T` is
  noetherian, so the completed ring of definition `Â₀,T` is noetherian
  (`TauCeti.Huber.PairOfDefinition.isNoetherianRing_weighted_completion_ringOfDefinition`). If `A`
  is also finite type over `A₀`, adjoining the images of a finite generating set of `A` together
  with the variables `X₁, …, Xₖ` to `Â₀,T` produces an open subring containing the constants and
  variables, hence the whole completed weighted algebra
  (`TauCeti.Huber.mem_of_mem_nhds_of_forall_weightedX_mem`). Passing along the open quotient map to
  `B` preserves both noetherianity of the ring of definition and finite generation over it.
* If `A` is discrete, `A⟨X⟩_T` and its completion are discrete, so any open quotient `B` is
  discrete as well (`TauCeti.Huber.IsTopologicallyFiniteType.discreteTopology`).

No completeness is assumed of `A` or of `B`.

## Main results

* `TauCeti.Huber.IsTopologicallyFiniteType.exists_pairOfDefinition_isNoetherianRing`: an algebra
  topologically of finite type over a Huber ring with a noetherian ring of definition has a
  noetherian ring of definition.
* `TauCeti.Huber.IsTopologicallyFiniteType.exists_pairOfDefinition_isNoetherianRing_and_finiteType`:
  finite generation over a noetherian ring of definition likewise ascends along homomorphisms
  topologically of finite type.
* `TauCeti.Huber.IsTopologicallyFiniteType.discreteTopology`: over a discrete base, any target of a
  homomorphism topologically of finite type is discrete.
* `TauCeti.Huber.IsNoetherianType.of_isTopologicallyFiniteType`: noetherian type ascends along
  homomorphisms topologically of finite type.
* `TauCeti.Huber.IsHuberStandard.of_isTopologicallyFiniteType`: Huber's standing class ascends
  along homomorphisms topologically of finite type.

## References

* R. Huber, *A generalization of formal schemes and rigid analytic varieties*, Math. Z. 217
  (1994), §3, Corollary 3.4.
* R. Huber, *Étale Cohomology of Rigid Analytic Varieties and Adic Spaces*, (1.1.1) and §1.2.
* T. Wedhorn, *Adic Spaces*, Proposition 6.35 and Remark 6.37.
-/

public section

open UniformSpace

namespace TauCeti.Huber

variable {A : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]
  {B : Type*} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] {φ : A →+* B}

/-- **A noetherian ring of definition ascends along a homomorphism topologically of finite type**
(Huber, Corollary 3.4(iii); Wedhorn, Proposition 6.35). If `A` has a noetherian ring of definition
and `φ : A → B` is topologically of finite type, then `B` has a noetherian ring of definition. -/
theorem IsTopologicallyFiniteType.exists_pairOfDefinition_isNoetherianRing
    (P : PairOfDefinition A) [IsNoetherianRing P.ringOfDefinition]
    (hφ : IsTopologicallyFiniteType φ) :
    ∃ Q : PairOfDefinition B, IsNoetherianRing Q.ringOfDefinition := by
  obtain ⟨k, T, hTfin, hT, π, hπ, -⟩ := isTopologicallyFiniteType_iff.mp hφ
  have := P.isNoetherianRing_weighted_completion_ringOfDefinition hT hTfin
  exact ⟨(P.weighted hT).completion.map π hπ, inferInstance⟩

/-- **Finite generation over a noetherian ring of definition ascends along a homomorphism
topologically of finite type**: if `A` is finite type over a noetherian ring of definition and
`φ : A → B` is topologically of finite type, then `B` is finite type over a noetherian ring of
definition. -/
theorem IsTopologicallyFiniteType.exists_pairOfDefinition_isNoetherianRing_and_finiteType
    (P : PairOfDefinition A) [IsNoetherianRing P.ringOfDefinition]
    [Algebra.FiniteType P.ringOfDefinition A] (hφ : IsTopologicallyFiniteType φ) :
    ∃ Q : PairOfDefinition B,
      IsNoetherianRing Q.ringOfDefinition ∧ Algebra.FiniteType Q.ringOfDefinition B := by
  obtain ⟨k, T, hTfin, hT, π, hπ, -⟩ := isTopologicallyFiniteType_iff.mp hφ
  have := P.isNoetherianRing_weighted_completion_ringOfDefinition hT hTfin
  have := P.finiteType_weighted_completion hT
  exact ⟨(P.weighted hT).completion.map π hπ, inferInstance, inferInstance⟩

/-- **Discrete topology ascends along homomorphisms topologically of finite type**: over a discrete
ring `A`, every weighted restricted power-series ring `A⟨X⟩_T` and its completion are discrete, so
any open quotient `B` is discrete as well. -/
theorem IsTopologicallyFiniteType.discreteTopology [DiscreteTopology A]
    (hφ : IsTopologicallyFiniteType φ) : DiscreteTopology B := by
  obtain ⟨k, T, _, hT, π, hπ, -⟩ := isTopologicallyFiniteType_iff.mp hφ
  let W := weightedRestrictedSubring T hT
  have : DiscreteUniformity W := DiscreteUniformity.of_discreteTopology
  have : DiscreteTopology (Completion W) :=
    (Homeomorph.mk (Completion.completeRingEquivSelf W).toEquiv
      (Completion.uniformContinuous_completeRingEquivSelf W).continuous
      (Completion.uniformContinuous_completeRingEquivSelf_symm W).continuous).symm.discreteTopology
  have h0 : IsOpen ({0} : Set B) := by
    simpa using hπ.isOpenMap ({0} : Set (Completion W)) (isOpen_discrete _)
  exact discreteTopology_iff_isOpen_singleton_zero.mpr h0

/-- **Noetherian type ascends along homomorphisms topologically of finite type** (Huber,
Corollary 3.4; Wedhorn, Proposition 6.35 and Remark 6.37(1)). If `A` is a Huber ring of
noetherian type and `φ : A → B` is topologically of finite type, then `B` is of noetherian type.
Neither `A` nor `B` needs to be complete. -/
theorem IsNoetherianType.of_isTopologicallyFiniteType [IsHuberRing A] [IsNoetherianType A]
    [IsHuberRing B] (hφ : IsTopologicallyFiniteType φ) : IsNoetherianType B := by
  refine IsNoetherianType.elim ‹_› (fun P _ ↦ ?_) fun _ _ ↦ ?_
  · obtain ⟨Q, hQ⟩ := hφ.exists_pairOfDefinition_isNoetherianRing P
    exact .of_pairOfDefinition Q hQ
  · -- `B` is Tate, and complete and Hausdorff for its additive uniformity, so strongly noetherian
    have := hφ.isTateRing
    let _ : UniformSpace B := IsTopologicalAddGroup.rightUniformSpace B
    have : IsUniformAddGroup B := isUniformAddGroup_of_addCommGroup
    have := hφ.completeSpace
    have := hφ.t2Space
    have := hφ.isStronglyNoetherian
    infer_instance

/-- **Huber's standing class ascends along homomorphisms topologically of finite type**
(Huber 1996, (1.1.1) and §1.2). If `A` is in Huber's standing class and `φ : A → B` is
topologically of finite type into a Huber ring `B`, then `B` is in Huber's standing class. Neither
`A` nor `B` needs to be complete. -/
theorem IsHuberStandard.of_isTopologicallyFiniteType [IsHuberRing A] [IsHuberStandard A]
    [IsHuberRing B] (hφ : IsTopologicallyFiniteType φ) : IsHuberStandard B := by
  refine IsHuberStandard.elim ‹_› (fun P _ _ ↦ ?_) (fun _ _ ↦ ?_) fun _ ↦ ?_
  · obtain ⟨Q, hQ, hfg⟩ := hφ.exists_pairOfDefinition_isNoetherianRing_and_finiteType P
    exact .of_pairOfDefinition Q hQ hfg
  · have := hφ.isTateRing
    let _ : UniformSpace B := IsTopologicalAddGroup.rightUniformSpace B
    have : IsUniformAddGroup B := isUniformAddGroup_of_addCommGroup
    have := hφ.completeSpace
    have := hφ.t2Space
    have := hφ.isStronglyNoetherian
    infer_instance
  · have := hφ.discreteTopology
    infer_instance

end TauCeti.Huber

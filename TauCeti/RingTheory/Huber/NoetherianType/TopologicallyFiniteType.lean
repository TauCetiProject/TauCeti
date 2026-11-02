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
# Noetherian type ascends along homomorphisms topologically of finite type

Let `A` be a Huber ring of noetherian type and `φ : A → B` a ring homomorphism topologically of
finite type, so that `B` is an open quotient of the completion of a weighted restricted
power-series ring `A⟨X₁, …, Xₖ⟩_T` with finite weights `Tᵢ`. Then `B` is again of noetherian type
(Huber, Corollary 3.4; Wedhorn, Proposition 6.35 and Remark 6.37(1)). This is the form in which
the noetherian hypothesis of Huber's sheafiness theorem reaches rational localisations and
algebras topologically of finite type.

The two alternatives defining noetherian type are treated separately.

* If `A` is a strongly noetherian Tate ring, `B` is Tate, complete and Hausdorff, and strongly
  noetherian (`TauCeti.Huber.IsTopologicallyFiniteType.isStronglyNoetherian`).
* If `A` has a noetherian ring of definition `A₀` with ideal of definition `I`, the ring of
  definition `A₀⟨X⟩_T` of `A⟨X⟩_T` is not noetherian in general, but modulo its ideal of
  definition `I⟨X⟩_T` it is a quotient of the polynomial ring over `A₀` in one variable for each
  weighted variable `t Xᵢ` with `t ∈ Tᵢ`: the coefficients of a restricted series lie in the
  weights times `I` for all but finitely many indices, and the remaining finitely many monomials
  are polynomials in the weighted variables. Since the weights are finite, `A₀⟨X⟩_T ⧸ I⟨X⟩_T` is
  noetherian, so the completed ring of definition is noetherian, being adically complete for a
  finitely generated ideal with noetherian quotient
  (`TauCeti.Huber.PairOfDefinition.isNoetherianRing_weighted_completion_ringOfDefinition`). Its
  image under the presentation is a noetherian ring of definition of `B`.

No completeness is assumed of `A` or of `B`.

## Main results

* `TauCeti.Huber.IsTopologicallyFiniteType.exists_pairOfDefinition_isNoetherianRing`: an algebra
  topologically of finite type over a Huber ring with a noetherian ring of definition has a
  noetherian ring of definition.
* `TauCeti.Huber.IsNoetherianType.of_isTopologicallyFiniteType`: noetherian type ascends along
  homomorphisms topologically of finite type.

## References

* R. Huber, *A generalization of formal schemes and rigid analytic varieties*, Math. Z. 217
  (1994), §3, Corollary 3.4.
* T. Wedhorn, *Adic Spaces*, Proposition 6.35 and Remark 6.37.
-/

public section

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

end TauCeti.Huber

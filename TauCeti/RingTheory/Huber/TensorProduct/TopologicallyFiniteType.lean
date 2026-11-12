/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.TensorProduct.Presentation
public import TauCeti.RingTheory.Huber.TensorProduct.Symmetry
public import TauCeti.RingTheory.Huber.TopologicallyFiniteType.Basic
public import TauCeti.Topology.Maps.OpenQuotient

/-!
# Completed base change of homomorphisms topologically of finite type

Let `A → B` be an adic homomorphism of Huber rings and `A → C` a homomorphism topologically of
finite type (`TauCeti.Huber.IsTopologicallyFiniteType`), presented by an open quotient map
`π : A⟨X⟩_T → C` out of the completed weighted restricted power series with finite weights `T`.
Then the coprojection `B → C ⊗̂_A B` is again topologically of finite type: base change of `π`
is an open quotient map `B⟨X⟩_{λ(T)} → C ⊗̂_A B` out of the completed weighted restricted power
series over `B` with the image weights
(`TauCeti.Huber.CompletedTensor.isOpenQuotientMap_baseChangePresentation`), and these weights are
again finite.

This is the stability of topological finite type under completed base change that fibre
products of adic spaces along morphisms locally of weakly finite type, and the noetherian-type
and sheafiness statements for such completed tensor products, are built on.

## Main results

* `TauCeti.Huber.CompletedTensor.isTopologicallyFiniteType_inr`: if `A → C` is topologically of
  finite type, so is the right coprojection `B → C ⊗̂_A B`.
* `TauCeti.Huber.CompletedTensor.isTopologicallyFiniteType_inl`: if `A → C` is topologically of
  finite type, so is the left coprojection `B → B ⊗̂_A C`.

## References

* R. Huber, *A generalization of formal schemes and rigid analytic varieties*, Math. Z. 217
  (1994), §3, Lemma 3.5 and the proof of Proposition 3.7.
* R. Huber, *Étale cohomology of rigid analytic varieties and adic spaces*, Aspects of
  Mathematics E30 (1996), §1.2, proof of Proposition 1.2.2.
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic], §8.6, proof of Theorem 8.56.
-/

public section

namespace TauCeti.Huber.CompletedTensor

variable {A B C : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
  [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsHuberRing B]
  [CommRing C] [TopologicalSpace C] [IsTopologicalRing C]
  [Algebra A B] [Algebra A C] [hAB : IsAdicHom (algebraMap A B)] [IsAdicHom (algebraMap A C)]

/-- **Completed base change preserves topological finite type.** If `A → C` is topologically of
finite type and `A → B` is adic, then the right coprojection `B → C ⊗̂_A B` is topologically of
finite type. A presentation `A⟨X⟩_T → C` with finite weights `T` base changes to a presentation
`B⟨X⟩_{λ(T)} → C ⊗̂_A B` with the image weights.

The adicness of `A → C` is part of the data needed to form `C ⊗̂_A B`; it follows from the
finite type hypothesis by `TauCeti.Huber.IsTopologicallyFiniteType.isAdicHom`. -/
theorem isTopologicallyFiniteType_inr (h : IsTopologicallyFiniteType (algebraMap A C)) :
    IsTopologicallyFiniteType (inr A C B) := by
  obtain ⟨k, T, hTfin, hT, π, hπ, hcomm⟩ := isTopologicallyFiniteType_iff.mp h
  refine isTopologicallyFiniteType_iff.mpr ⟨k, fun i ↦ algebraMap A B '' T i,
    fun i ↦ (hTfin i).image _, hAB.isWeightFamily_image hT, _,
    isOpenQuotientMap_baseChangePresentation B hcomm hπ, ?_⟩
  ext b
  simp [algebraMap_completion_weightedRestrictedSubring_apply]

/-- If `A → C` is topologically of finite type and `A → B` is adic, then the left coprojection
`B → B ⊗̂_A C` is topologically of finite type. This is
`TauCeti.Huber.CompletedTensor.isTopologicallyFiniteType_inr` transported along the exchange of
the two factors. -/
theorem isTopologicallyFiniteType_inl (h : IsTopologicallyFiniteType (algebraMap A C)) :
    IsTopologicallyFiniteType (inl A B C) := by
  have hq : IsOpenQuotientMap (comm A C B).toRingHom := by
    rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
    exact (isHomeomorph_comm A C B).isOpenQuotientMap
  have h' := (isTopologicallyFiniteType_inr h).comp_isOpenQuotientMap hq
  convert h' using 1
  ext b
  simp

end TauCeti.Huber.CompletedTensor

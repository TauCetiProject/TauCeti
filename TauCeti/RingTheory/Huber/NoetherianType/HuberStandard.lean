/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.NoetherianType.Basic

import Mathlib.RingTheory.FiniteType
import TauCeti.RingTheory.Huber.Adic

/-!
# Huber's standing class of f-adic rings

Huber's theory of unramified, smooth, and étale morphisms uses a standing class of f-adic rings.
A ring belongs to this class when it is finite type over a noetherian ring of definition, is a
strongly noetherian Tate ring, or has the discrete topology.

This condition is stronger than being of noetherian type: the first alternative additionally
requires finite generation over the ring of definition, which makes the ambient ring noetherian
(`Algebra.FiniteType.isNoetherianRing`), whereas the third alternative admits non-noetherian
discrete rings. The declarations below record the three ways to enter the class, show that every
ring in the standing class is of noetherian type, and establish invariance of the class under
bicontinuous ring isomorphisms.

## References

* R. Huber, *Étale Cohomology of Rigid Analytic Varieties and Adic Spaces*, (1.1.1).
-/

public section

namespace TauCeti.Huber

variable (A : Type*) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]

/-- A Huber ring is in **Huber's standing class** if it is finite type over a noetherian ring of
definition, is a strongly noetherian Tate ring, or has the discrete topology. -/
@[mk_iff]
class IsHuberStandard : Prop where
  /-- The three alternatives defining Huber's standing class. -/
  out : (∃ P : PairOfDefinition A,
      IsNoetherianRing P.ringOfDefinition ∧ Algebra.FiniteType P.ringOfDefinition A) ∨
    (IsTateRing A ∧ IsStronglyNoetherian A) ∨ DiscreteTopology A

section HuberRing

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]

/-- A Huber ring finite type over a noetherian ring of definition is in Huber's standing class. -/
theorem IsHuberStandard.of_pairOfDefinition (P : PairOfDefinition A)
    (hP : IsNoetherianRing P.ringOfDefinition)
    (hfinite : Algebra.FiniteType P.ringOfDefinition A) : IsHuberStandard A :=
  ⟨Or.inl ⟨P, hP, hfinite⟩⟩

/-- Eliminate membership in Huber's standing class by treating its three defining alternatives. -/
theorem IsHuberStandard.elim {P : Prop} (hA : IsHuberStandard A)
    (hfinite : ∀ Q : PairOfDefinition A, IsNoetherianRing Q.ringOfDefinition →
      Algebra.FiniteType Q.ringOfDefinition A → P)
    (htate : IsTateRing A → IsStronglyNoetherian A → P)
    (hdiscrete : DiscreteTopology A → P) : P := by
  rcases hA.out with ⟨Q, hQ, hAQ⟩ | ⟨hTate, hStrong⟩ | hDiscrete
  · exact hfinite Q hQ hAQ
  · exact htate hTate hStrong
  · exact hdiscrete hDiscrete

/-- Every Huber ring in Huber's standing class is of noetherian type. -/
theorem IsHuberStandard.isNoetherianType [hA : IsHuberStandard A] : IsNoetherianType A :=
  hA.elim
    (fun Q hQ _ ↦ IsNoetherianType.of_pairOfDefinition Q hQ)
    (fun hTate hStrong ↦ ⟨Or.inr ⟨hTate, hStrong⟩⟩)
    fun hDiscrete ↦ by
      let _ : DiscreteTopology A := hDiscrete
      infer_instance

/-- Every noetherian Huber ring whose topology is `I`-adic is in Huber's standing class: `(A, I)` is
a pair of definition whose ring of definition is all of `A`. -/
theorem IsHuberStandard.of_isAdic [IsNoetherianRing A] {I : Ideal A} (hI : IsAdic I) :
    IsHuberStandard A := by
  have hfg : I.FG := IsNoetherian.noetherian I
  refine .of_pairOfDefinition (.adic I hI hfg) ?_ ?_
  · rw [PairOfDefinition.adic_ringOfDefinition]
    exact isNoetherianRing_of_ringEquiv A Subring.topEquiv.symm
  · refine ⟨⟨(∅ : Finset A), eq_top_iff.mpr fun x _ ↦ ?_⟩⟩
    have hx : x ∈ (PairOfDefinition.adic I hI hfg).ringOfDefinition := by
      rw [PairOfDefinition.adic_ringOfDefinition]
      trivial
    exact (Algebra.adjoin (PairOfDefinition.adic I hI hfg).ringOfDefinition _).algebraMap_mem
      ⟨x, hx⟩

end HuberRing

section TateRing

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsTateRing A]

/-- A strongly noetherian Tate ring is in Huber's standing class. -/
instance IsHuberStandard.of_isStronglyNoetherian [IsStronglyNoetherian A] : IsHuberStandard A :=
  ⟨Or.inr (Or.inl ⟨inferInstance, inferInstance⟩)⟩

end TateRing

section DiscreteRing

variable {A : Type*} [CommRing A] [TopologicalSpace A] [DiscreteTopology A]

/-- Every discrete commutative ring is in Huber's standing class, with no noetherianity or finite
generation assumption on the ring itself. -/
instance IsHuberStandard.of_discreteTopology : IsHuberStandard A :=
  ⟨Or.inr (Or.inr inferInstance)⟩

end DiscreteRing

section Transport

variable {A B : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
  [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsHuberRing B]

/-- **Huber's standing class transports along a bicontinuous ring isomorphism.** Continuity of both
`e` and `e.symm` is required, since a `RingEquiv` is purely algebraic. -/
theorem IsHuberStandard.of_ringEquiv [hA : IsHuberStandard A] (e : A ≃+* B)
    (he : Continuous e) (he' : Continuous e.symm) : IsHuberStandard B := by
  let hhomeo : A ≃ₜ B := Homeomorph.mk e.toEquiv he he'
  refine hA.elim (fun P _ _ ↦ ?_) (fun _ hStrong ↦ ?_) fun _ ↦ ?_
  · have hf : IsOpenQuotientMap (e : A →+* B) := hhomeo.isOpenQuotientMap
    have hnoeth : IsNoetherianRing (P.map (e : A →+* B) hf).ringOfDefinition := by
      have hr : ((e : A →+* B).comp P.ringOfDefinition.subtype).range =
          (P.map (e : A →+* B) hf).ringOfDefinition := by
        ext; simp
      exact hr ▸ inferInstance
    exact .of_pairOfDefinition (P.map (e : A →+* B) hf) hnoeth inferInstance
  · have : IsTateRing B := IsTateRing.of_continuous he (φ := (e : A →+* B))
    have : IsStronglyNoetherian B := (isStronglyNoetherian_congr e he he').mp hStrong
    infer_instance
  · have : DiscreteTopology B := hhomeo.discreteTopology
    infer_instance

/-- **Huber's standing class is invariant under bicontinuous ring isomorphisms.** -/
theorem isHuberStandard_congr (e : A ≃+* B) (he : Continuous e) (he' : Continuous e.symm) :
    IsHuberStandard A ↔ IsHuberStandard B :=
  ⟨fun _ ↦ IsHuberStandard.of_ringEquiv e he he',
    fun _ ↦ IsHuberStandard.of_ringEquiv e.symm he' he⟩

end Transport

end TauCeti.Huber

end

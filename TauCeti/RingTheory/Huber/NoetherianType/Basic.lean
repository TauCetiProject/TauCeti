/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.StronglyNoetherian

import Mathlib.RingTheory.Adjoin.FG

/-!
# Huber rings of noetherian type

A Huber ring is of noetherian type when it either has a noetherian ring of definition or is a
strongly noetherian Tate ring. This is the pair of hypotheses in Huber's sheafiness theorem.

The two alternatives are genuinely needed. In particular, an arbitrary discrete ring need not be
noetherian, but it has its prime subring as a noetherian ring of definition and is therefore of
noetherian type. The results here provide the basic introduction and elimination API for this
class.

## References

* R. Huber, *A generalization of formal schemes and rigid analytic varieties*, Theorem 2.2.
* T. Wedhorn, *Adic Spaces*, Remark 6.37.
-/

public section

namespace TauCeti.Huber

variable (A : Type*) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]

/-- A Huber ring is **of noetherian type** if it has a noetherian ring of definition, or if it is
a strongly noetherian Tate ring. -/
@[mk_iff]
class IsNoetherianType : Prop where
  /-- The disjunction defining a Huber ring of noetherian type. -/
  out : (∃ P : PairOfDefinition A, IsNoetherianRing P.ringOfDefinition) ∨
    (IsTateRing A ∧ IsStronglyNoetherian A)

section HuberRing

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]

/-- A noetherian ring of definition makes a Huber ring of noetherian type. -/
theorem IsNoetherianType.of_pairOfDefinition (P : PairOfDefinition A)
    (hP : IsNoetherianRing P.ringOfDefinition) : IsNoetherianType A :=
  ⟨Or.inl ⟨P, hP⟩⟩

/-- Eliminate noetherian type by treating its noetherian-ring-of-definition and strongly
noetherian Tate alternatives. -/
theorem IsNoetherianType.elim {P : Prop} (hA : IsNoetherianType A)
    (hrod : ∀ Q : PairOfDefinition A, IsNoetherianRing Q.ringOfDefinition → P)
    (htate : IsTateRing A → IsStronglyNoetherian A → P) : P := by
  rcases hA.out with ⟨Q, hQ⟩ | ⟨hTate, hStrong⟩
  · exact hrod Q hQ
  · exact htate hTate hStrong

end HuberRing

section TateRing

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsTateRing A]

/-- A strongly noetherian Tate ring is of noetherian type. -/
instance IsNoetherianType.of_isStronglyNoetherian [IsStronglyNoetherian A] :
    IsNoetherianType A :=
  ⟨Or.inr ⟨inferInstance, inferInstance⟩⟩

end TateRing

section DiscreteRing

variable {A : Type*} [CommRing A] [TopologicalSpace A] [DiscreteTopology A]

/-- Every discrete commutative ring is of noetherian type, even when the ring itself is not
noetherian: its prime subring is a noetherian ring of definition. -/
instance IsNoetherianType.of_discreteTopology : IsNoetherianType A := by
  have h : IsNoetherianRing (⊥ : Subring A) := by
    rw [← Subring.closure_empty]
    exact is_noetherian_subring_closure (∅ : Set A) Set.finite_empty
  exact .of_pairOfDefinition
    { ringOfDefinition := ⊥
      isOpen_ringOfDefinition := isOpen_discrete _
      idealOfDefinition := ⊥
      fg_idealOfDefinition := Submodule.fg_bot
      isAdic_idealOfDefinition := is_bot_adic_iff.mpr inferInstance }
    h

end DiscreteRing

end TauCeti.Huber

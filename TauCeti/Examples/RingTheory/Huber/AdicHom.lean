/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.RingTheory.Huber.AdicHom.Completion
import TauCeti.RingTheory.Huber.Padic.Field
import TauCeti.RingTheory.Huber.TopologicallyFiniteType.Adic

/-!
# Examples of adic homomorphisms

The inclusion `ℤ_[p] → ℚ_[p]` is adic although its source is not Tate. In contrast,
`ℤ → ℤ_[p]`, with the discrete topology on `ℤ`, is continuous but not adic. These examples
separate adicness from continuity and test the intrinsic criterion using open ideals.

The generic examples construct an adic map from compatible pairs of definition and consume
its boundedness and continuity properties with the caller's ring and topology instances.

## References

* T. Wedhorn, *Adic Spaces*, Definition 6.23 and Example 6.24.
-/

open Topology
open TauCeti.Huber

section Generic

variable {A B : Type*} [CommRing A] [CommRing B]
  [TopologicalSpace A] [TopologicalSpace B]

-- Compatible pairs introduce the opaque predicate without unfolding its class body.
example (f : A →+* B) (P : PairOfDefinition A) (Q : PairOfDefinition B)
    (h : ∀ a ∈ P.ringOfDefinition, f a ∈ Q.ringOfDefinition)
    (hI : P.idealOfDefinition.map (f.restrict _ _ h) = Q.idealOfDefinition) :
    IsAdicHom f :=
  isAdicHom_iff.mpr ⟨P, Q, h, hI⟩

variable [IsTopologicalRing A] [IsTopologicalRing B]

example (f : A →+* B) [IsAdicHom f] : Continuous f :=
  IsAdicHom.continuous inferInstance

example (f : A →+* B) [IsAdicHom f] {S : Set A} (hS : IsBounded S) :
    IsBounded (f '' S) :=
  IsAdicHom.isBounded_image inferInstance hS

-- A finite type presentation supplies the target Huber structure internally.
example [IsHuberRing A] (f : A →+* B) (hf : IsTopologicallyFiniteType f) :
    IsAdicHom f :=
  hf.isAdicHom

-- The zero ring is permitted as target, without any separation or nontriviality assumption.
example [IsHuberRing A] [Subsingleton B] (f : A →+* B) : IsAdicHom f := by
  apply IsAdicHom.of_continuous_isOpen_map continuous_of_indiscreteTopology
  exact fun _ _ ↦ isOpen_discrete _

end Generic

-- Completion uses the caller's compatible additive uniformity.
example {A : Type*} [CommRing A] [UniformSpace A] [IsUniformAddGroup A]
    [IsTopologicalRing A] [IsHuberRing A] :
    IsAdicHom (UniformSpace.Completion.coeRingHom : A →+* UniformSpace.Completion A) :=
  IsAdicHom.coeRingHom

section Padic

variable {p : ℕ} [Fact p.Prime]

-- A non-Tate source can have an adic inclusion into a Tate field.
example : IsAdicHom (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p]) := by
  apply IsAdicHom.of_continuous_isOpen_map
  · exact continuous_subtype_val
  · intro I hI
    have hI0 : I ≠ ⊥ := IsDiscreteValuationRing.isOpen_iff.mp hI
    have hmap : I.map PadicInt.Coe.ringHom ≠ ⊥ :=
      (Ideal.map_eq_bot_iff_of_injective Subtype.coe_injective).not.mpr hI0
    rw [(Ideal.eq_bot_or_top (I.map PadicInt.Coe.ringHom)).resolve_left hmap]
    exact isOpen_univ

-- The source is discrete, so continuity imposes no p-adic condition on its target.
example : Continuous (Int.castRingHom ℤ_[p]) := continuous_of_discreteTopology

-- Adicness would carry the open zero ideal to an open zero ideal in ℤ_[p].
example : ¬ IsAdicHom (Int.castRingHom ℤ_[p]) := by
  intro hf
  have hopen := hf.isOpen_map (I := ⊥) (isOpen_discrete _)
  have hzero : IsOpen ((⊥ : Ideal ℤ_[p]) : Set ℤ_[p]) := by simpa using hopen
  exact (IsDiscreteValuationRing.isOpen_iff.mp hzero) rfl

end Padic

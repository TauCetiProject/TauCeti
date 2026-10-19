/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Rep.Basic
public import TauCeti.RepresentationTheory.Homological.ContCohomology.SmoothDiscrete.Basic

/-!
# Algebraic representations with the discrete topology

`discreteTopRepFunctor` equips an algebraic representation with the discrete topology, without
changing its module, action, or morphisms, so it is fully faithful. Over a discrete group its
values are smooth. Restricting these objects along continuous maps to discrete quotients supplies
smooth coefficient objects for continuous cohomology.

The construction retains Mathlib's `Rep` and `TopRep` carriers; it only supplies the topology
and continuity proofs. Ring coefficients are required by Mathlib's `TopRep`.
-/

public section

namespace TauCeti

open CategoryTheory

universe u v w

variable (R : Type u) [Ring R] [TopologicalSpace R] [DiscreteTopology R]
  (G : Type v) [Monoid G]

/-- An algebraic representation with the discrete topology on its underlying module.
The body is exposed so the pointwise action equation can use elements of `A.V` directly. -/
@[expose] def discreteTopRep (A : Rep.{w} R G) : TopRep.{w} R G :=
  letI : TopologicalSpace A.V := ⊥
  letI : DiscreteTopology A.V := ⟨rfl⟩
  letI : ContinuousSMul R A.V := ⟨continuous_of_discreteTopology⟩
  TopRep.of <| ContRepresentation.ofMonoidHom
    { toFun g := ⟨A.ρ g, continuous_of_discreteTopology⟩
      map_one' := by ext a; simp
      map_mul' g h := by ext a; exact congrArg (fun f : Module.End R A.V ↦ f a) (A.ρ.map_mul g h) }

/-- Equipping a representation with the discrete topology preserves its underlying module. -/
@[simp]
theorem discreteTopRep_V (A : Rep.{w} R G) : (discreteTopRep R G A).V = A.V :=
  (rfl)

/-- The action of `discreteTopRep` is the original algebraic action. -/
@[simp]
theorem discreteTopRep_ρ_apply (A : Rep.{w} R G) (g : G) (a : A.V) :
    (discreteTopRep R G A).ρ g a = A.ρ g a :=
  (rfl)

/-- Discrete topology is part of the output of `discreteTopRep`. -/
instance (A : Rep.{w} R G) : DiscreteTopology (discreteTopRep R G A).V :=
  ⟨rfl⟩

/-- Equip every algebraic representation and intertwining map with the discrete topology.
The body is exposed so the pointwise morphism equation can use the original algebraic carriers. -/
@[expose] def discreteTopRepFunctor : Rep.{w} R G ⥤ TopRep.{w} R G where
  obj := discreteTopRep R G
  map {A B} f :=
    { hom' :=
        { toContinuousLinearMap := ⟨f.hom.toLinearMap, continuous_of_discreteTopology⟩
          isIntertwining' g := by
            ext a
            exact Rep.hom_comm_apply f g a } }
  map_id A := by ext a; rfl
  map_comp f g := by ext a; rfl

/-- Equipping intertwining maps with continuity proofs preserves addition. -/
instance : (discreteTopRepFunctor R G).Additive where
  map_add := by intros; ext a; rfl

/-- The functor sends an object to its discrete topological representation. -/
@[simp]
theorem discreteTopRepFunctor_obj (A : Rep.{w} R G) :
    (discreteTopRepFunctor R G).obj A = discreteTopRep R G A :=
  (rfl)

/-- The functor leaves the underlying intertwining map unchanged. -/
@[simp]
theorem discreteTopRepFunctor_map_apply {A B : Rep.{w} R G} (f : A ⟶ B) (a : A.V) :
    ((discreteTopRepFunctor R G).map f).hom a = f.hom a :=
  (rfl)

/-- Equipping representations with the discrete topology is faithful: it leaves the underlying
linear maps unchanged. -/
instance : (discreteTopRepFunctor R G).Faithful where
  map_injective {_ _} f g h := by
    ext a
    exact congr(($h).hom a)

/-- Equipping representations with the discrete topology is full: every intertwining map between
discrete modules is continuous. -/
instance : (discreteTopRepFunctor R G).Full where
  map_surjective {A B} f :=
    ⟨ConcreteCategory.ofHom (C := Rep R G) (f.hom.toContinuousLinearMap.toLinearMap
      |>.intertwiningMap_of_isIntertwiningMap A.ρ B.ρ (TopRep.hom_comm_apply f)), by ext a; rfl⟩

/-- A representation of a discrete monoid on a discrete module is smooth. -/
theorem isSmoothDiscrete_discreteTopRep [TopologicalSpace G] [DiscreteTopology G]
    (A : Rep.{w} R G) : IsSmoothDiscrete R (discreteTopRep R G A) :=
  ⟨inferInstance, fun _ ↦ isOpen_discrete _⟩

section Quotient

variable (H : Type v) [Group H]

/-- A discrete topological representation on which a normal subgroup acts trivially is the
inflation of an algebraic representation of the quotient, with its discrete topology. -/
theorem exists_discreteTopRep_res_iso (X : TopRep.{w} R H) [DiscreteTopology X.V]
    (V : Subgroup H) [V.Normal] (hV : ∀ g ∈ V, ∀ x : X.V, X.ρ g x = x) :
    ∃ A : Rep.{w} R (H ⧸ V),
      Nonempty (TopRep.res (QuotientGroup.mk' V) (discreteTopRep R (H ⧸ V) A) ≅ X) := by
  let A : Rep R (H ⧸ V) := Rep.of <| QuotientGroup.lift V X.ρ.toRepresentation fun g hg ↦ by
    ext x
    exact hV g hg x
  -- The descended representation has the same module as `X`. The quotient-lift equation
  -- makes the identity maps intertwining; their continuity uses the two discrete topologies.
  refine ⟨A, ⟨?_, ?_, ?_, ?_⟩⟩
  · exact { hom' :=
      { toContinuousLinearMap := ⟨LinearMap.id, continuous_of_discreteTopology⟩
        isIntertwining' g := by ext x; rfl } }
  · exact { hom' :=
      { toContinuousLinearMap := ⟨LinearMap.id, continuous_of_discreteTopology⟩
        isIntertwining' g := by ext x; rfl } }
  · ext x
    rfl
  · ext x
    rfl

end Quotient

end TauCeti

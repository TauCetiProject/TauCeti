/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.SmoothDiscrete.Basic
public import TauCeti.RepresentationTheory.Smooth.Category

/-!
# Smooth representations as discrete continuous representations

Give the ring `A` the discrete topology and let `G` be a topological group. A smooth
representation `V` of `G` over `A` becomes an object of `TopRep A G` by giving its underlying
module the discrete topology: every operator is then continuous, and the point stabilizers are
open because `V` is smooth. This file shows that this is an equivalence of categories
`TauCeti.SmoothRep.equivSmoothDiscreteTopRep : SmoothRep A G ≌ SmoothDiscreteTopRep A G`, which
keeps underlying modules, actions and morphisms.

The equivalence factors through the category `TauCeti.DiscreteRep A G` of discrete `G`-modules
with continuous `G`-action: `TauCeti.SmoothRep.equivDiscreteRep` puts the discrete topology on a
smooth representation and reads its action as a `DistribMulAction`, and Tau Ceti's
`TauCeti.discreteRepEquivSmoothTopRep` carries that to the smooth discrete objects of
`TopRep A G`. On a discrete module smoothness and continuity of the action are the same condition
(Mathlib's `continuousSMul_iff_stabilizer_isOpen`).

## Main definitions

* `TauCeti.SmoothRep.toDiscreteRep`, `TauCeti.SmoothRep.ofDiscreteRep`: the two functors between
  `SmoothRep A G` and `DiscreteRep A G`.
* `TauCeti.SmoothRep.equivDiscreteRep`: the equivalence `SmoothRep A G ≌ DiscreteRep A G`.
* `TauCeti.SmoothRep.equivSmoothDiscreteTopRep`: the equivalence
  `SmoothRep A G ≌ SmoothDiscreteTopRep A G`.
* `TauCeti.SmoothRep.equivSmoothDiscreteTopRepCompForget`: the equivalence is compatible with the
  forgetful functors to types.

## References

* J. Bernstein, *Representations of p-adic groups*, Harvard lectures 1992, written by
  K. Rumelhart, Chapter I, §1.3, Important Example and Fact, p. 10.
-/

@[expose] public section

open CategoryTheory Representation

universe w u v

namespace TauCeti

namespace SmoothRep

variable (A : Type u) [Ring A] [TopologicalSpace A] (G : Type v) [Group G] [TopologicalSpace G]

section OfDiscreteRep

variable {A G}

/-- A discrete `G`-module with continuous action is a smooth representation: the stabilizer of a
point of a discrete space under a continuous action is open. -/
instance isSmooth_discreteRep_ρ (X : DiscreteRep.{u, v, w} A G) : IsSmooth X.ρ :=
  ⟨fun v ↦ stabilizer_isOpen G v⟩

variable (A G) in
/-- Discrete `G`-modules with continuous action as smooth representations: forget the topology
and keep the representation `X.ρ`. -/
def ofDiscreteRep : DiscreteRep.{u, v, w} A G ⥤ SmoothRep.{w} A G where
  obj X := of X.ρ
  map f := ObjectProperty.homMk (Rep.ofHom f)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- `ofDiscreteRep` keeps the underlying module. -/
@[simp] lemma ofDiscreteRep_obj_obj_V (X : DiscreteRep.{u, v, w} A G) :
    ((ofDiscreteRep A G).obj X).obj.V = X.V :=
  (rfl)

/-- `ofDiscreteRep` keeps the action. -/
@[simp] lemma ofDiscreteRep_obj_obj_ρ_apply (X : DiscreteRep.{u, v, w} A G) (g : G) (x : X.V) :
    ((ofDiscreteRep A G).obj X).obj.ρ g x = g • x :=
  (rfl)

/-- `ofDiscreteRep` sends a morphism to its underlying linear map. -/
@[simp] lemma ofDiscreteRep_map_hom_hom_apply {X Y : DiscreteRep.{u, v, w} A G} (f : X ⟶ Y)
    (x : X.V) : ((ofDiscreteRep A G).map f).hom.hom x = f.toLinearMap x :=
  (rfl)

end OfDiscreteRep

variable [DiscreteTopology A] [IsTopologicalGroup G]

section ToDiscreteRep

variable {A G}

/-- The smooth representation `V`, with the discrete topology on its underlying module and the
action `g • v = ρ(g) v`, as a discrete `G`-module with continuous `G`-action. The action is
continuous because the module is discrete and every point stabilizer is open. -/
def toDiscreteRepObj (V : SmoothRep.{w} A G) : DiscreteRep.{u, v, w} A G :=
  letI : TopologicalSpace V.obj := ⊥
  haveI : DiscreteTopology V.obj := ⟨rfl⟩
  letI : DistribMulAction G V.obj := .compHom V.obj V.obj.ρ
  { V := V.obj
    smulCommClass := ⟨fun g a v ↦ map_smul (V.obj.ρ g) a v⟩
    continuousSMulRing := ⟨continuous_of_discreteTopology⟩
    continuousSMul := continuousSMul_iff_stabilizer_isOpen.2 fun v ↦
      IsSmooth.isOpen_stabilizer (ρ := V.obj.ρ) v }

/-- The underlying module of `toDiscreteRepObj V` is that of `V`. -/
@[simp] lemma toDiscreteRepObj_V (V : SmoothRep.{w} A G) : (toDiscreteRepObj V).V = V.obj :=
  (rfl)

/-- In `toDiscreteRepObj V`, the action of `g` is the operator `ρ(g)` of `V`. -/
@[simp] lemma toDiscreteRepObj_smul (V : SmoothRep.{w} A G) (g : G) (v : (toDiscreteRepObj V).V) :
    g • v = V.obj.ρ g (v : V.obj) :=
  (rfl)

/-- The representation carried by `toDiscreteRepObj V` is the representation of `V`. -/
@[simp] lemma toDiscreteRepObj_ρ (V : SmoothRep.{w} A G) : (toDiscreteRepObj V).ρ = V.obj.ρ :=
  (rfl)

end ToDiscreteRep

/-- Smooth representations as discrete `G`-modules with continuous action: the discrete topology
on the underlying module, the action read off from the representation, and every morphism acting
as itself. -/
def toDiscreteRep : SmoothRep.{w} A G ⥤ DiscreteRep.{u, v, w} A G where
  obj := toDiscreteRepObj
  map {V W} f := (f.hom.hom : V.obj.ρ.IntertwiningMap W.obj.ρ)
  map_id _ := rfl
  map_comp _ _ := rfl

variable {A G}

/-- `toDiscreteRep` keeps the underlying module. -/
@[simp] lemma toDiscreteRep_obj_V (V : SmoothRep.{w} A G) :
    ((toDiscreteRep A G).obj V).V = V.obj :=
  (rfl)

/-- `toDiscreteRep` sends a morphism to its underlying linear map. -/
@[simp] lemma toDiscreteRep_map_toLinearMap_apply {V W : SmoothRep.{w} A G} (f : V ⟶ W)
    (v : V.obj) : ((toDiscreteRep A G).map f).toLinearMap v = f.hom.hom v :=
  (rfl)

variable (A G)

/-- **Smooth representations are the discrete `G`-modules with continuous action.** Over a
discrete ring `A`, putting the discrete topology on a smooth representation is an equivalence
between `SmoothRep A G` and `DiscreteRep A G`. Both round trips return the module and the action
they started from, so every component of the unit and of the counit is an identity. -/
def equivDiscreteRep : SmoothRep.{w} A G ≌ DiscreteRep.{u, v, w} A G :=
  .mk (toDiscreteRep A G) (ofDiscreteRep A G)
    (NatIso.ofComponents (fun V ↦ ObjectProperty.isoMk _ (Iso.refl V.obj)) fun _ ↦ rfl)
    (NatIso.ofComponents
      (fun X ↦
        { hom := (Representation.IntertwiningMap.id X.ρ : X.ρ.IntertwiningMap X.ρ)
          inv := (Representation.IntertwiningMap.id X.ρ : X.ρ.IntertwiningMap X.ρ)
          hom_inv_id := rfl
          inv_hom_id := rfl })
      fun _ ↦ rfl)

/-- The functor of `equivDiscreteRep` is `toDiscreteRep`. -/
@[simp] lemma equivDiscreteRep_functor : (equivDiscreteRep A G).functor = toDiscreteRep A G :=
  (rfl)

/-- The inverse of `equivDiscreteRep` is `ofDiscreteRep`. -/
@[simp] lemma equivDiscreteRep_inverse : (equivDiscreteRep A G).inverse = ofDiscreteRep A G :=
  (rfl)

/-- **Smooth representations as discrete continuous representations.** Over a discrete ring `A`,
sending a smooth representation to the same module with the discrete topology and the same action
is an equivalence between `SmoothRep A G` and the smooth discrete objects of `TopRep A G`. It is
the composite of `equivDiscreteRep` with Tau Ceti's `discreteRepEquivSmoothTopRep`. -/
def equivSmoothDiscreteTopRep : SmoothRep.{w} A G ≌ SmoothDiscreteTopRep.{u, v, w} A G :=
  (equivDiscreteRep A G).trans (discreteRepEquivSmoothTopRep A G)

variable {A G}

/-- The functor of `equivSmoothDiscreteTopRep` keeps the underlying module. -/
@[simp] lemma equivSmoothDiscreteTopRep_functor_obj_obj_V (V : SmoothRep.{w} A G) :
    ((equivSmoothDiscreteTopRep A G).functor.obj V).obj.V = V.obj :=
  (rfl)

/-- The functor of `equivSmoothDiscreteTopRep` keeps the action. -/
@[simp] lemma equivSmoothDiscreteTopRep_functor_obj_obj_ρ_apply (V : SmoothRep.{w} A G) (g : G)
    (v : V.obj) : ((equivSmoothDiscreteTopRep A G).functor.obj V).obj.ρ g v = V.obj.ρ g v :=
  (rfl)

/-- The functor of `equivSmoothDiscreteTopRep` sends a morphism `f` to the morphism acting as
`f`. -/
@[simp] lemma equivSmoothDiscreteTopRep_functor_map_hom_hom_apply {V W : SmoothRep.{w} A G}
    (f : V ⟶ W) (v : V.obj) :
    ((equivSmoothDiscreteTopRep A G).functor.map f).hom.hom v = f.hom.hom v :=
  (rfl)

/-- The inverse of `equivSmoothDiscreteTopRep` keeps the underlying module. -/
@[simp] lemma equivSmoothDiscreteTopRep_inverse_obj_obj_V
    (X : SmoothDiscreteTopRep.{u, v, w} A G) :
    ((equivSmoothDiscreteTopRep A G).inverse.obj X).obj.V = X.obj.V :=
  (rfl)

/-- The inverse of `equivSmoothDiscreteTopRep` keeps the action. -/
@[simp] lemma equivSmoothDiscreteTopRep_inverse_obj_obj_ρ_apply
    (X : SmoothDiscreteTopRep.{u, v, w} A G) (g : G) (x : X.obj.V) :
    ((equivSmoothDiscreteTopRep A G).inverse.obj X).obj.ρ g x = X.obj.ρ g x :=
  (rfl)

/-- The inverse of `equivSmoothDiscreteTopRep` sends a morphism `f` to the morphism acting as
`f`. -/
@[simp] lemma equivSmoothDiscreteTopRep_inverse_map_hom_hom_apply
    {X Y : SmoothDiscreteTopRep.{u, v, w} A G} (f : X ⟶ Y) (x : X.obj.V) :
    ((equivSmoothDiscreteTopRep A G).inverse.map f).hom.hom x = f.hom.hom x :=
  (rfl)

variable (A G)

/-- **Compatibility with forgetting.** The equivalence `equivSmoothDiscreteTopRep` commutes with
the forgetful functors to types, by the identity of underlying sets. -/
def equivSmoothDiscreteTopRepCompForget :
    (equivSmoothDiscreteTopRep A G).functor ⋙ smoothDiscreteι A G ⋙ forget (TopRep.{w} A G) ≅
      ι A G ⋙ forget (Rep.{w} A G) :=
  NatIso.ofComponents (fun V ↦ Iso.refl V.obj.V) fun _ ↦ rfl

end SmoothRep

end TauCeti

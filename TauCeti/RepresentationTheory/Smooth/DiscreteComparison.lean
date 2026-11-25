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
* `TauCeti.SmoothRep.equivSmoothDiscreteTopRepCompForget₂`,
  `TauCeti.SmoothRep.equivSmoothDiscreteTopRepCompForget`: the equivalence is compatible with the
  forgetful functors to `A`-modules and to types.

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

/-- Smooth representations as discrete `G`-modules with continuous action: the discrete topology
on the underlying module, the action `g • v = ρ(g) v`, and every morphism acting as itself. The
action is continuous because the module is discrete and every point stabilizer is open. -/
def toDiscreteRep : SmoothRep.{w} A G ⥤ DiscreteRep.{u, v, w} A G where
  obj V :=
    letI : TopologicalSpace V.obj := ⊥
    haveI : DiscreteTopology V.obj := ⟨rfl⟩
    letI : DistribMulAction G V.obj := .compHom V.obj V.obj.ρ
    { V := V.obj
      smulCommClass := ⟨fun g a v ↦ map_smul (V.obj.ρ g) a v⟩
      continuousSMulRing := ⟨continuous_of_discreteTopology⟩
      continuousSMul := continuousSMul_iff_stabilizer_isOpen.2 fun v ↦
        IsSmooth.isOpen_stabilizer (ρ := V.obj.ρ) v }
  map {V W} f := (f.hom.hom : V.obj.ρ.IntertwiningMap W.obj.ρ)
  map_id _ := rfl
  map_comp _ _ := rfl

variable {A G}

/-- `toDiscreteRep` keeps the underlying module. -/
@[simp] lemma toDiscreteRep_obj_V (V : SmoothRep.{w} A G) :
    ((toDiscreteRep A G).obj V).V = V.obj :=
  (rfl)

/-- In `(toDiscreteRep A G).obj V`, the action of `g` is the operator `ρ(g)` of `V`. -/
@[simp] lemma toDiscreteRep_obj_smul (V : SmoothRep.{w} A G) (g : G)
    (v : ((toDiscreteRep A G).obj V).V) : g • v = V.obj.ρ g (v : V.obj) :=
  (rfl)

/-- The representation carried by `(toDiscreteRep A G).obj V` is the representation of `V`. -/
@[simp] lemma toDiscreteRep_obj_ρ (V : SmoothRep.{w} A G) :
    ((toDiscreteRep A G).obj V).ρ = V.obj.ρ :=
  (rfl)

/-- `toDiscreteRep` sends a morphism to its underlying linear map. -/
@[simp] lemma toDiscreteRep_map_toLinearMap_apply {V W : SmoothRep.{w} A G} (f : V ⟶ W)
    (v : V.obj) : ((toDiscreteRep A G).map f).toLinearMap v = f.hom.hom v :=
  (rfl)

variable (A G)

/-- **Smooth representations are the discrete `G`-modules with continuous action.** Over a
discrete ring `A`, putting the discrete topology on a smooth representation is an equivalence
between `SmoothRep A G` and `DiscreteRep A G`. Both round trips return the module and the action
they started from: every component of the unit is an identity morphism, and every component of
the counit is the identity intertwining map, the round trip replacing the topology of a discrete
module by `⊥`. -/
@[simps! functor inverse unitIso_hom_app unitIso_inv_app counitIso_hom_app counitIso_inv_app]
def equivDiscreteRep : SmoothRep.{w} A G ≌ DiscreteRep.{u, v, w} A G where
  functor := toDiscreteRep A G
  inverse := ofDiscreteRep A G
  unitIso := NatIso.ofComponents (fun V ↦ Iso.refl V) fun _ ↦ rfl
  counitIso := NatIso.ofComponents
    (fun X ↦
      { hom := (Representation.IntertwiningMap.id X.ρ : X.ρ.IntertwiningMap X.ρ)
        inv := (Representation.IntertwiningMap.id X.ρ : X.ρ.IntertwiningMap X.ρ)
        hom_inv_id := rfl
        inv_hom_id := rfl })
    fun _ ↦ rfl
  functor_unitIso_comp _ := rfl

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

/-- Every component of the unit of `equivSmoothDiscreteTopRep` is an identity morphism. -/
@[simp] lemma equivSmoothDiscreteTopRep_unitIso_hom_app (V : SmoothRep.{w} A G) :
    (equivSmoothDiscreteTopRep A G).unitIso.hom.app V = 𝟙 V :=
  (rfl)

/-- Every component of the inverse of the unit of `equivSmoothDiscreteTopRep` is an identity
morphism. -/
@[simp] lemma equivSmoothDiscreteTopRep_unitIso_inv_app (V : SmoothRep.{w} A G) :
    (equivSmoothDiscreteTopRep A G).unitIso.inv.app V = 𝟙 V :=
  (rfl)

/-- Every component of the counit of `equivSmoothDiscreteTopRep` acts as the identity of the
underlying module. This is not a simp lemma: the elaborated left-hand side carries the source and
target objects as `Functor.comp_obj` and `Functor.id_obj` terms, which `simp` rewrites first. -/
lemma equivSmoothDiscreteTopRep_counitIso_hom_app_hom_hom_apply
    (X : SmoothDiscreteTopRep.{u, v, w} A G) (x : X.obj.V) :
    ((equivSmoothDiscreteTopRep A G).counitIso.hom.app X).hom.hom x = x :=
  (rfl)

/-- Every component of the inverse of the counit of `equivSmoothDiscreteTopRep` acts as the
identity of the underlying module. Like
`TauCeti.SmoothRep.equivSmoothDiscreteTopRep_counitIso_hom_app_hom_hom_apply`, this is not a simp
lemma. -/
lemma equivSmoothDiscreteTopRep_counitIso_inv_app_hom_hom_apply
    (X : SmoothDiscreteTopRep.{u, v, w} A G) (x : X.obj.V) :
    ((equivSmoothDiscreteTopRep A G).counitIso.inv.app X).hom.hom x = x :=
  (rfl)

variable (A G)

/-- **Compatibility with forgetting to `A`-modules.** The equivalence
`equivSmoothDiscreteTopRep` commutes with the forgetful functors to `ModuleCat A`, by the identity
of underlying modules. On `TopRep A G` the forgetful functor passes through Mathlib's
`Action (TopModuleCat A) G`, as Mathlib has no direct `forget₂` from `TopRep A G`. -/
@[simps! hom_app inv_app]
def equivSmoothDiscreteTopRepCompForget₂ :
    (equivSmoothDiscreteTopRep A G).functor ⋙ smoothDiscreteι A G ⋙ TopRep.toActionTopModFunc ⋙
        Action.forget (TopModuleCat.{w} A) G ⋙ forget₂ (TopModuleCat.{w} A) (ModuleCat.{w} A) ≅
      ι A G ⋙ forget₂ (Rep.{w} A G) (ModuleCat.{w} A) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) fun _ ↦ rfl

/-- **Compatibility with forgetting.** The equivalence `equivSmoothDiscreteTopRep` commutes with
the forgetful functors to types, by the identity of underlying sets. -/
@[simps! hom_app inv_app]
def equivSmoothDiscreteTopRepCompForget :
    (equivSmoothDiscreteTopRep A G).functor ⋙ smoothDiscreteι A G ⋙ forget (TopRep.{w} A G) ≅
      ι A G ⋙ forget (Rep.{w} A G) :=
  NatIso.ofComponents (fun V ↦ Iso.refl V.obj.V) fun _ ↦ rfl

end SmoothRep

end TauCeti

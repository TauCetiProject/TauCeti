/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Continuous.TopRep
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Action.Limits

/-!
# Products of topological representations

The product of a family of topological representations carries the pointwise action and product
topology. This construction exposes that representation as an object of `TopRep`, so it can be
used with the full-subcategory constructions built on topological representations.

## Main declarations

* `TopRep.pi`: the pointwise product representation, with projections `TopRep.piπ` and
  universal maps `TopRep.piLift`.
* `TopRep.piFanIsLimit`: the fan of projections from `TopRep.pi` is a limit fan.
* `TopRep` has all limits, transported from `Action (TopModuleCat R) G`.
* `TopRep.piIsoPi`: the categorical product is isomorphic to the pointwise product.
-/

public section

universe u v w

namespace TopRep

open CategoryTheory CategoryTheory.Limits

variable {R : Type u} [Ring R] [TopologicalSpace R]
variable {G : Type v} [Monoid G]

/-- The pointwise product representation, with the product topology on its underlying module. -/
@[expose] def pi {ι : Type w} (X : ι → TopRep R G) : TopRep R G :=
  let ρ : ContRepresentation R G (∀ i, (X i).V) := {
    toMonoidHom := {
      toFun g := ContinuousLinearMap.pi fun i =>
        (X i).ρ g ∘L ContinuousLinearMap.proj i
      map_one' := by
        ext x i
        simp
      map_mul' g h := by
        ext x i
        simp
    }
  }
  TopRep.of ρ

/-- The underlying module of a pointwise product is the pointwise product of the underlying
modules. -/
theorem pi_V {ι : Type w} (X : ι → TopRep R G) :
    (pi X).V = ∀ i, (X i).V := rfl

/-- The action on a product representation is pointwise. -/
@[simp]
theorem pi_ρ_apply {ι : Type w} (X : ι → TopRep R G) (g : G) (x : (pi X).V) (i : ι) :
    (pi X).ρ g x i = (X i).ρ g (x i) :=
  rfl

/-- The stabilizer of a point in a pointwise product is the intersection of its coordinate
stabilizers. -/
theorem pi_stabilizer_eq_iInter {ι : Type w} (X : ι → TopRep R G)
    (x : (pi X).V) :
    {g : G | (pi X).ρ g x = x} = ⋂ i, {g : G | (X i).ρ g (x i) = x i} := by
  ext g
  simp only [Set.mem_ofPred_eq, Set.mem_iInter]
  -- Equality in `pi X` is coordinatewise, and `pi_ρ_apply` holds by `rfl`.
  exact funext_iff

/-- The product representation has a discrete underlying topology when the index type is finite
and each factor has a discrete underlying topology. -/
instance pi_discreteTopology {ι : Type w} [Finite ι] (X : ι → TopRep R G)
    [∀ i, DiscreteTopology (X i).V] : DiscreteTopology (pi X).V :=
  Pi.discreteTopology

/-- The projection from a product representation to one of its factors. -/
def piπ {ι : Type w} (X : ι → TopRep R G) (i : ι) : pi X ⟶ X i :=
  TopRep.ofHom {
    toContinuousLinearMap := ContinuousLinearMap.proj i
    isIntertwining' g := by
      ext x
      exact pi_ρ_apply X g x i
  }

/-- Evaluation of a product projection. -/
@[simp] theorem piπ_hom_apply {ι : Type w} (X : ι → TopRep R G) (i : ι)
    (x : (pi X).V) : (piπ X i).hom x = x i := by rfl

/-- The morphism into a product representation whose components are a given family of
equivariant continuous linear maps. -/
def piLift {ι : Type w} {A : TopRep R G} (X : ι → TopRep R G)
    (f : ∀ i, A ⟶ X i) : A ⟶ pi X :=
  TopRep.ofHom {
    toContinuousLinearMap := ContinuousLinearMap.pi fun i => (f i).hom.toContinuousLinearMap
    isIntertwining' g := by
      ext x i
      exact (f i).hom.isIntertwining g x
  }

/-- Evaluation of a map into a product. -/
@[simp] theorem piLift_hom_apply {ι : Type w} {A : TopRep R G}
    (X : ι → TopRep R G) (f : ∀ i, A ⟶ X i) (a : A.V) (i : ι) :
    (piLift X f).hom a i = (f i).hom a := by rfl

/-- The component of `piLift` at any factor is the specified map. -/
@[reassoc (attr := simp)]
theorem piLift_piπ {ι : Type w} {A : TopRep R G} (X : ι → TopRep R G)
    (f : ∀ i, A ⟶ X i) (i : ι) : piLift X f ≫ piπ X i = f i := by
  ext x
  rfl

/-- Morphisms into a product are determined by their components. -/
@[ext] theorem pi_hom_ext {ι : Type w} {A : TopRep R G} (X : ι → TopRep R G)
    {f g : A ⟶ pi X} (h : ∀ i, f ≫ piπ X i = g ≫ piπ X i) : f = g := by
  ext x
  funext i
  exact congrArg (fun q : A ⟶ X i => q.hom x) (h i)

/-- The fan of projections from the pointwise product. -/
abbrev piFan {ι : Type w} (X : ι → TopRep R G) : Fan X :=
  Fan.mk (pi X) (piπ X)

/-- The cone point of the pointwise product fan is the pointwise product representation. -/
@[simp] theorem piFan_pt {ι : Type w} (X : ι → TopRep R G) : (piFan X).pt = pi X := rfl

/-- The projections of the pointwise product fan are the product projections. -/
@[simp] theorem piFan_proj {ι : Type w} (X : ι → TopRep R G) (i : ι) :
    (piFan X).proj i = piπ X i := rfl

/-- The pointwise product fan is a limit. -/
def piFanIsLimit {ι : Type w} (X : ι → TopRep R G) : IsLimit (piFan X) :=
  Fan.IsLimit.mk _ (fun s => piLift X s.proj)
    (fun s i => piLift_piπ X s.proj i)
    (fun s _ hm => pi_hom_ext X fun i => (hm i).trans (piLift_piπ X s.proj i).symm)

/-- Topological representations admit all limits, by equivalence with continuous actions on
topological modules. -/
instance : HasLimits (TopRep.{w} R G) :=
  Adjunction.has_limits_of_equivalence (TopRep.toActionTopModFunc (k := R) (G := G))

/-- The categorical product is isomorphic to the pointwise product representation. -/
noncomputable def piIsoPi {ι : Type w} (X : ι → TopRep R G) : ∏ᶜ X ≅ pi X :=
  limit.isoLimitCone ⟨piFan X, piFanIsLimit X⟩

/-- The comparison from the categorical product to the pointwise product intertwines the
projections. -/
@[reassoc (attr := simp)]
theorem piIsoPi_hom_piπ {ι : Type w} (X : ι → TopRep R G) (i : ι) :
    (piIsoPi X).hom ≫ piπ X i = Pi.π X i :=
  limit.isoLimitCone_hom_π ⟨piFan X, piFanIsLimit X⟩ ⟨i⟩

/-- The inverse comparison from the pointwise product intertwines the categorical projections. -/
@[reassoc (attr := simp)]
theorem piIsoPi_inv_π {ι : Type w} (X : ι → TopRep R G) (i : ι) :
    (piIsoPi X).inv ≫ Pi.π X i = piπ X i :=
  limit.isoLimitCone_inv_π ⟨piFan X, piFanIsLimit X⟩ ⟨i⟩

end TopRep

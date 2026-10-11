/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Continuous.TopRep
public import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# Products of topological representations

The product of a family of topological representations carries the pointwise action and product
topology. This construction exposes that representation as an object of `TopRep`, so it can be
used with the full-subcategory constructions built on topological representations.
-/

public section

universe u v w

namespace TopRep

open CategoryTheory CategoryTheory.Limits

variable {R : Type u} [Ring R] [TopologicalSpace R]
variable {G : Type v} [Monoid G]

/-- The pointwise product representation, with the product topology on its underlying module. -/
@[expose]
def pi {ι : Type w} (X : ι → TopRep R G) : TopRep R G :=
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

/-- The action on a product representation is pointwise. -/
@[simp]
theorem pi_ρ_apply {ι : Type w} (X : ι → TopRep R G) (g : G) (x : ∀ i, (X i).V) (i : ι) :
    (pi X).ρ g x i = (X i).ρ g (x i) := by
  rfl

/-- The projection from a product representation to one of its factors. -/
@[expose] def piπ {ι : Type w} (X : ι → TopRep R G) (i : ι) : pi X ⟶ X i :=
  TopRep.ofHom {
    toContinuousLinearMap := ContinuousLinearMap.proj i
    isIntertwining' g := by
      ext x
      exact pi_ρ_apply X g x i
  }

/-- Evaluation of a product projection. -/
@[simp] theorem piπ_hom_apply {ι : Type w} (X : ι → TopRep R G) (i : ι)
    (x : (pi X).V) : (piπ X i).hom x = x i := rfl

/-- The morphism into a product representation whose components are a given family of
equivariant continuous linear maps. -/
@[expose] def piLift {ι : Type w} {A : TopRep R G} (X : ι → TopRep R G)
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
    (piLift X f).hom a i = (f i).hom a := rfl

/-- The component of `piLift` at any factor is the specified map. -/
@[simp]
theorem piLift_comp_piπ {ι : Type w} {A : TopRep R G} (X : ι → TopRep R G)
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
@[expose] def piFan {ι : Type w} (X : ι → TopRep R G) : Fan X :=
  Fan.mk (pi X) (piπ X)

/-- The pointwise product fan is a limit. -/
def piFanIsLimit {ι : Type w} (X : ι → TopRep R G) : IsLimit (piFan X) :=
  Fan.IsLimit.mk _ (fun s => piLift X s.proj)
    (fun s i => piLift_comp_piπ X s.proj i)
    (fun s _ hm => pi_hom_ext X (fun i => (hm i).trans
      (piLift_comp_piπ X s.proj i).symm))

/-- Topological representations admit products indexed by types in their universe. -/
instance : HasProducts.{w} (TopRep.{w} R G) := fun _ =>
  { has_limit F := HasLimit.mk
      ⟨(Cone.postcompose Discrete.natIsoFunctor.inv).obj
        (piFan fun i => F.obj ⟨i⟩),
        (IsLimit.postcomposeInvEquiv _ _).symm
          (piFanIsLimit fun i => F.obj ⟨i⟩)⟩ }

/-- Topological representations admit finite categorical products. -/
instance : HasFiniteProducts (TopRep.{w} R G) :=
  hasFiniteProducts_of_hasProducts.{w} _

end TopRep

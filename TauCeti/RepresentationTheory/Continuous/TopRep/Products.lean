/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Continuous.TopRep

/-!
# Products of topological representations

The product of a family of topological representations carries the pointwise action and product
topology. This construction exposes that representation as an object of `TopRep`, so it can be
used with the full-subcategory constructions built on topological representations.
-/

public section

universe u v w

namespace TopRep

open CategoryTheory

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
def piπ {ι : Type w} (X : ι → TopRep R G) (i : ι) : pi X ⟶ X i :=
  TopRep.ofHom {
    toContinuousLinearMap := ContinuousLinearMap.proj i
    isIntertwining' g := by
      ext x
      -- Expose the product operator so the composition with the projection can simplify.
      change (ContinuousLinearMap.pi (fun j =>
        (X j).ρ g ∘L ContinuousLinearMap.proj j) x) i =
          (X i).ρ g ((ContinuousLinearMap.proj i) x)
      simp
  }

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

/-- The component of `piLift` at any factor is the specified map. -/
@[simp]
theorem piLift_comp_piπ {ι : Type w} {A : TopRep R G} (X : ι → TopRep R G)
    (f : ∀ i, A ⟶ X i) (i : ι) : piLift X f ≫ piπ X i = f i := by
  ext x
  rfl

/-- Morphisms into a product are determined by their components. -/
theorem pi_hom_ext {ι : Type w} {A : TopRep R G} (X : ι → TopRep R G)
    {f g : A ⟶ pi X} (h : ∀ i, f ≫ piπ X i = g ≫ piπ X i) : f = g := by
  ext x
  funext i
  exact congrArg (fun q : A ⟶ X i => q.hom x) (h i)

end TopRep

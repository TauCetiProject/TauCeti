/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Continuous.TopRep.Products
public import TauCeti.RepresentationTheory.Homological.ContCohomology.SmoothDiscrete.Basic

/-!
# Finite products of smooth discrete representations

Finite products of smooth discrete representations remain smooth discrete. The finite-index
hypothesis is needed for the product topology to be discrete.
-/

public section

universe u v w

namespace TauCeti.SmoothDiscreteTopRep

open CategoryTheory

attribute [local instance] TopRep.distribMulAction

variable {R : Type u} [Ring R] [TopologicalSpace R]
variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The finite pointwise product of smooth discrete representations. -/
def pi {ι : Type w} [Finite ι] (X : ι → SmoothDiscreteTopRep R G) :
    SmoothDiscreteTopRep R G := by
  let Y : TopRep R G := TopRep.pi fun i => (X i).obj
  letI : ∀ i, DiscreteTopology (X i).obj.V := fun i => (X i).property.discreteTopology
  have hdisc : DiscreteTopology (∀ i, (X i).obj.V) := by
    infer_instance
  -- The carrier of `TopRep.pi` is definitionally this dependent function space.
  letI : DiscreteTopology Y.V := hdisc
  letI : ∀ i, ContinuousSMul G (X i).obj.V := fun i => (X i).property.continuousSMul
  have hsmulPi : ContinuousSMul G (∀ i, (X i).obj.V) := by
    infer_instance
  exact ⟨Y, (isSmoothDiscrete_iff_continuousSMul Y).2 hsmulPi⟩

/-- The projection from a finite smooth discrete product to one of its factors. -/
def piπ {ι : Type w} [Finite ι] (X : ι → SmoothDiscreteTopRep R G) (i : ι) :
    pi X ⟶ X i :=
  ObjectProperty.homMk (TopRep.piπ (fun j => (X j).obj) i)

/-- The morphism into a finite smooth discrete product determined by its component maps. -/
def piLift {ι : Type w} [Finite ι] {A : SmoothDiscreteTopRep R G}
    (X : ι → SmoothDiscreteTopRep R G) (f : ∀ i, A ⟶ X i) : A ⟶ pi X :=
  ObjectProperty.homMk (TopRep.piLift (fun i => (X i).obj) fun i => (f i).hom)

/-- The component of `piLift` at each factor is its specified morphism. -/
@[simp]
theorem piLift_comp_piπ {ι : Type w} [Finite ι] {A : SmoothDiscreteTopRep R G}
    (X : ι → SmoothDiscreteTopRep R G) (f : ∀ i, A ⟶ X i) (i : ι) :
    piLift X f ≫ piπ X i = f i := by
  apply ObjectProperty.hom_ext
  exact TopRep.piLift_comp_piπ (fun j => (X j).obj) (fun j => (f j).hom) i

/-- Morphisms into a finite smooth discrete product are determined by their components. -/
theorem pi_hom_ext {ι : Type w} [Finite ι] {A : SmoothDiscreteTopRep R G}
    (X : ι → SmoothDiscreteTopRep R G) {f g : A ⟶ pi X}
    (h : ∀ i, f ≫ piπ X i = g ≫ piπ X i) : f = g := by
  apply ObjectProperty.hom_ext
  apply TopRep.pi_hom_ext
  intro i
  exact congrArg (fun q : A ⟶ X i => q.hom) (h i)

end TauCeti.SmoothDiscreteTopRep

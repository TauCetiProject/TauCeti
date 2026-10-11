/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Continuous.TopRep.Products
public import TauCeti.RepresentationTheory.Homological.ContCohomology.SmoothDiscrete.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts

/-!
# Finite products of smooth discrete representations

Finite products of smooth discrete representations remain smooth discrete. The finite-index
hypothesis is needed for the product topology to be discrete.
-/

public section

universe u v w

namespace TauCeti.SmoothDiscreteTopRep

open CategoryTheory CategoryTheory.Limits

attribute [local instance] TopRep.distribMulAction

variable {R : Type u} [Ring R] [TopologicalSpace R]
variable {G : Type v} [Monoid G] [TopologicalSpace G]

/-- Finite pointwise products preserve smooth discreteness over a topological monoid. -/
lemma _root_.TauCeti.IsSmoothDiscrete.pi {ι : Type w} [Finite ι]
    (X : ι → TopRep R G) (h : ∀ i, IsSmoothDiscrete R (X i)) :
    IsSmoothDiscrete R (TopRep.pi X) := by
  have hdisc : ∀ i, DiscreteTopology (X i).V := fun i => (h i).discreteTopology
  refine ⟨?_, fun x => ?_⟩
  · change DiscreteTopology (∀ i, (X i).V)
    exact @Pi.discreteTopology _ _ _ _ hdisc
  have hstab : {g : G | (TopRep.pi X).ρ g x = x} =
      ⋂ i, {g : G | (X i).ρ g (x i) = x i} := by
    ext g
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    constructor
    · intro hg i
      exact (TopRep.pi_ρ_apply X g x i).symm.trans (congrFun hg i)
    · intro hg
      apply funext
      intro i
      exact (TopRep.pi_ρ_apply X g x i).trans (hg i)
  rw [hstab]
  exact isOpen_iInter_of_finite (fun i => (h i).stabilizer_isOpen (x i))

/-- The finite pointwise product of smooth discrete representations. -/
@[expose] def pi {ι : Type w} [Finite ι] (X : ι → SmoothDiscreteTopRep R G) :
    SmoothDiscreteTopRep R G :=
  ⟨TopRep.pi fun i => (X i).obj, IsSmoothDiscrete.pi _ (fun i => (X i).property)⟩

/-- The underlying topological representation of the finite product. -/
@[simp] theorem pi_obj {ι : Type w} [Finite ι]
    (X : ι → SmoothDiscreteTopRep R G) :
    (pi X).obj = TopRep.pi (fun i => (X i).obj) := rfl

/-- The projection from a finite smooth discrete product to one of its factors. -/
@[expose] def piπ {ι : Type w} [Finite ι] (X : ι → SmoothDiscreteTopRep R G) (i : ι) :
    pi X ⟶ X i :=
  ObjectProperty.homMk (TopRep.piπ (fun j => (X j).obj) i)

/-- The underlying map of a finite product projection. -/
@[simp] theorem piπ_hom {ι : Type w} [Finite ι]
    (X : ι → SmoothDiscreteTopRep R G) (i : ι) :
    (piπ X i).hom = TopRep.piπ (fun j => (X j).obj) i := rfl

/-- The morphism into a finite smooth discrete product determined by its component maps. -/
@[expose] def piLift {ι : Type w} [Finite ι] {A : SmoothDiscreteTopRep R G}
    (X : ι → SmoothDiscreteTopRep R G) (f : ∀ i, A ⟶ X i) : A ⟶ pi X :=
  ObjectProperty.homMk (TopRep.piLift (fun i => (X i).obj) fun i => (f i).hom)

/-- The underlying map into a finite product. -/
@[simp] theorem piLift_hom {ι : Type w} [Finite ι] {A : SmoothDiscreteTopRep R G}
    (X : ι → SmoothDiscreteTopRep R G) (f : ∀ i, A ⟶ X i) :
    (piLift X f).hom = TopRep.piLift (fun i => (X i).obj) (fun i => (f i).hom) := rfl

/-- The component of `piLift` at each factor is its specified morphism. -/
@[simp]
theorem piLift_comp_piπ {ι : Type w} [Finite ι] {A : SmoothDiscreteTopRep R G}
    (X : ι → SmoothDiscreteTopRep R G) (f : ∀ i, A ⟶ X i) (i : ι) :
    piLift X f ≫ piπ X i = f i := by
  apply ObjectProperty.hom_ext
  exact TopRep.piLift_comp_piπ (fun j => (X j).obj) (fun j => (f j).hom) i

/-- Morphisms into a finite smooth discrete product are determined by their components. -/
@[ext] theorem pi_hom_ext {ι : Type w} [Finite ι] {A : SmoothDiscreteTopRep R G}
    (X : ι → SmoothDiscreteTopRep R G) {f g : A ⟶ pi X}
    (h : ∀ i, f ≫ piπ X i = g ≫ piπ X i) : f = g := by
  apply ObjectProperty.hom_ext
  apply TopRep.pi_hom_ext
  intro i
  exact congrArg (fun q : A ⟶ X i => q.hom) (h i)

/-- The fan of projections from the finite smooth discrete product. -/
def piFan {ι : Type w} [Finite ι] (X : ι → SmoothDiscreteTopRep R G) : Fan X :=
  Fan.mk (pi X) (piπ X)

/-- The finite smooth discrete product fan is a limit. -/
def piFanIsLimit {ι : Type w} [Finite ι]
    (X : ι → SmoothDiscreteTopRep R G) : IsLimit (piFan X) :=
  Fan.IsLimit.mk _ (fun s => piLift X s.proj)
    (fun s i => piLift_comp_piπ X s.proj i)
    (fun s _ hm => pi_hom_ext X (fun i => (hm i).trans
      (piLift_comp_piπ X s.proj i).symm))

/-- Smooth discreteness is preserved by isomorphisms of topological representations. -/
instance : ObjectProperty.IsClosedUnderIsomorphisms
    (fun X : TopRep.{w} R G => IsSmoothDiscrete R X) where
  of_iso e hX := by
    refine IsSmoothDiscrete.of_injective e.inv ?_ hX
    intro x y h
    have hh := congrArg (fun z => e.hom.hom z) h
    simpa using hh

/-- Smooth discreteness is closed under finite categorical products. -/
instance (ι : Type) [Finite ι] : ObjectProperty.IsClosedUnderLimitsOfShape
    (fun X : TopRep.{w} R G => IsSmoothDiscrete R X) (Discrete ι) :=
  ObjectProperty.IsClosedUnderLimitsOfShape.mk' (by
    rintro _ ⟨F, hF⟩
    let X : ι → TopRep.{w} R G := fun i => F.obj ⟨i⟩
    have hp : IsSmoothDiscrete R (TopRep.pi X) := IsSmoothDiscrete.pi X (fun i => hF ⟨i⟩)
    let e₁ : TopRep.pi X ≅ limit (Discrete.functor X) :=
      (TopRep.piFanIsLimit X).conePointUniqueUpToIso (limit.isLimit _)
    let e₂ : limit (Discrete.functor X) ≅ limit F :=
      HasLimit.isoOfNatIso (Discrete.natIso fun j => Iso.refl (F.obj j))
    exact ObjectProperty.prop_of_iso _ (e₁.trans e₂) hp)

/-- The smooth discrete predicate is closed under finite products. -/
instance : ObjectProperty.IsClosedUnderFiniteProducts
    (fun X : TopRep.{w} R G => IsSmoothDiscrete R X) :=
  ObjectProperty.IsClosedUnderFiniteProducts.of_isClosedUnderLimitsOfShape
    (fun _ _ => inferInstance)

end TauCeti.SmoothDiscreteTopRep

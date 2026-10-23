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
  · exact TopRep.pi_discreteTopology X hdisc
  rw [TopRep.pi_stabilizer_eq_iInter X x]
  exact isOpen_iInter_of_finite (fun i => (h i).stabilizer_isOpen (x i))

/-- Smooth discreteness is closed under finite products. -/
instance : ObjectProperty.IsClosedUnderFiniteProducts
    (fun X : TopRep.{w} R G => IsSmoothDiscrete R X) :=
  ObjectProperty.IsClosedUnderFiniteProducts.of_isClosedUnderLimitsOfShape
    (fun (ι : Type w) [Finite ι] =>
      ObjectProperty.IsClosedUnderLimitsOfShape.mk' (by
    rintro _ ⟨F, hF⟩
    let X : ι → TopRep.{w} R G := fun i => F.obj ⟨i⟩
    have hp : IsSmoothDiscrete R (TopRep.pi X) := IsSmoothDiscrete.pi X (fun i => hF ⟨i⟩)
    let e : limit (Discrete.functor X) ≅ TopRep.pi X := TopRep.piIsoPi X
    let e₂ : limit (Discrete.functor X) ≅ limit F :=
      HasLimit.isoOfNatIso (Discrete.natIso fun j => Iso.refl (F.obj j))
    exact ObjectProperty.prop_of_iso _ (e.symm.trans e₂) hp))

end TauCeti.SmoothDiscreteTopRep

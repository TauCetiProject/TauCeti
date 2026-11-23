/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Continuous.TopRep.Products
import TauCeti.Topology.Category.TopCat.MappingSpace

/-!
# Limits of coinduced representations and invariants

The invariants functor is right adjoint to the trivial-action functor, and hence preserves
limits. This is the topological counterpart of Mathlib's `Rep.invariantsAdjunction`.
For a locally compact group, `coind₁Functor` also preserves limits because its underlying
topological space is the compact-open mapping space, a right adjoint on `TopCat`.
-/

public section

noncomputable section

open CategoryTheory Limits

universe u v w

namespace TopRep

variable (R : Type u) [Ring R] [TopologicalSpace R]

/-- Equip a topological module with the trivial representation. -/
@[expose, simps]
def trivialFunctor (G : Type v) [Monoid G] : TopModuleCat.{w} R ⥤ TopRep.{w} R G where
  obj X := of (ContRepresentation.trivial R G X)
  map f := ofHom ⟨f.hom, fun _ ↦ rfl⟩

variable (G : Type v) [Group G]

/-- Taking invariant vectors is right adjoint to equipping a module with the trivial action. -/
def invariantsAdjunction : trivialFunctor.{u, v, w} R G ⊣ invariantsFunctor R G where
  unit := { app X := TopModuleCat.ofHom <|
      (ContinuousLinearMap.id R X).codRestrict _ fun _ _ ↦ rfl }
  counit := { app X := ofHom ⟨X.ρ.invariants.subtypeL,
    fun g ↦ by ext x; exact (x.property g).symm⟩ }

/-- The invariants adjunction restricts the codomain of an equivariant map to invariant vectors. -/
@[simp↓]
theorem invariantsAdjunction_homEquiv_apply_hom_apply
    {X : TopModuleCat.{w} R} {Y : TopRep.{w} R G}
    (f : (trivialFunctor R G).obj X ⟶ Y) (x : X) :
    (((invariantsAdjunction R G).homEquiv X Y f).hom x : Y) = f.hom x := (rfl)

/-- The inverse invariants adjunction includes the invariant vectors into the representation. -/
@[simp↓]
theorem invariantsAdjunction_homEquiv_symm_apply_hom_apply
    {X : TopModuleCat.{w} R} {Y : TopRep.{w} R G}
    (f : X ⟶ (invariantsFunctor R G).obj Y) (x : X) :
    (((invariantsAdjunction R G).homEquiv X Y).symm f).hom x = (f.hom x : Y) := (rfl)

/-- The invariants functor preserves limits as a right adjoint. -/
instance : (invariantsFunctor (k := R) (G := G) :
    TopRep.{w} R G ⥤ TopModuleCat.{w} R).IsRightAdjoint :=
  (invariantsAdjunction R G).isRightAdjoint

variable [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]

/-- Coinduction preserves limits over a locally compact group, by the exponential law. -/
instance coind₁Functor_preservesLimits : PreservesLimits (coind₁Functor.{u, v, v} R G) := by
  let U : TopRep.{v} R G ⥤ TopModuleCat.{v} R :=
    toActionTopModFunc ⋙ Action.forget (TopModuleCat.{v} R) G
  let T := forget₂ (TopModuleCat.{v} R) TopCat
  let : ReflectsLimits T := reflectsLimits_of_reflectsIsomorphisms
  let : ReflectsLimits U := inferInstance
  let : (TopCat.mappingSpace (TopCat.of G)).IsRightAdjoint :=
    (TopCat.tensorLeftAdjunction (TopCat.of G)).isRightAdjoint
  have e : (coind₁Functor R G ⋙ U) ⋙ T ≅ (U ⋙ T) ⋙ TopCat.mappingSpace (TopCat.of G) :=
    NatIso.ofComponents (fun X ↦ Iso.refl _) (fun f ↦ by ext F; rfl)
  have : PreservesLimits ((coind₁Functor R G ⋙ U) ⋙ T) :=
    preservesLimits_of_natIso e.symm
  have : PreservesLimits (coind₁Functor R G ⋙ U) :=
    preservesLimits_of_reflects_of_preserves _ T
  exact preservesLimits_of_reflects_of_preserves _ U

end TopRep

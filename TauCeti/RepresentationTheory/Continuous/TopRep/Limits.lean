/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Continuous.TopRep.Products
import TauCeti.Topology.Category.TopCat.MappingSpace
import Mathlib.Topology.Category.TopCat.ULift

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

universe u v w t₁ t₂

namespace TopRep

variable (R : Type u) [Ring R] [TopologicalSpace R]

/-- Equip a topological module with the trivial representation. -/
@[expose, simps obj]
def trivialFunctor (G : Type v) [Monoid G] : TopModuleCat.{w} R ⥤ TopRep.{w} R G where
  obj X := of (ContRepresentation.trivial R G X)
  map f := ofHom ⟨f.hom, fun _ ↦ rfl⟩

/-- The trivial-action functor acts on maps by their original continuous linear map. -/
@[simp]
theorem trivialFunctor_map_hom_apply (G : Type v) [Monoid G]
    {X Y : TopModuleCat.{w} R} (f : X ⟶ Y) (x : X) :
    ((trivialFunctor R G).map f).hom x = f.hom x := (rfl)

variable (G : Type v) [Group G]

/-- Taking invariant vectors is right adjoint to equipping a module with the trivial action. -/
def invariantsAdjunction : trivialFunctor.{u, v, w} R G ⊣ invariantsFunctor R G where
  unit := { app X := TopModuleCat.ofHom <|
      (ContinuousLinearMap.id R X).codRestrict _ fun _ _ ↦ rfl }
  counit := { app X := ofHom ⟨X.ρ.invariants.subtypeL,
    fun g ↦ by ext x; exact (x.property g).symm⟩ }

/-- The unit includes each vector as an invariant vector for the trivial action. -/
@[simp↓]
theorem coe_invariantsAdjunction_unit_app_hom_apply (X : TopModuleCat.{w} R) (x : X) :
    (((invariantsAdjunction R G).unit.app X).hom x).val = x := (rfl)

/-- The counit includes invariant vectors into their ambient representation. -/
@[simp↓]
theorem invariantsAdjunction_counit_app_hom_apply (X : TopRep.{w} R G)
    (x : X.ρ.invariants) :
    ((invariantsAdjunction R G).counit.app X).hom x = (x : X) := (rfl)

/-- The invariants adjunction restricts the codomain of an equivariant map to invariant vectors. -/
@[simp↓]
theorem coe_invariantsAdjunction_homEquiv_apply_hom_apply
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

/-- Coinduction preserves limits of diagrams whose object type is small in the source carrier
universe. -/
instance coind₁Functor_preservesLimitsOfSize [UnivLE.{t₂, w}] :
    PreservesLimitsOfSize.{t₁, t₂} (coind₁Functor.{u, v, w} R G) := by
  refine ⟨fun {J} _ ↦ ?_⟩
  let U : TopRep.{max v w} R G ⥤ TopModuleCat.{max v w} R :=
    toActionTopModFunc ⋙ Action.forget (TopModuleCat.{max v w} R) G
  let U₀ : TopRep.{w} R G ⥤ TopModuleCat.{w} R :=
    toActionTopModFunc ⋙ Action.forget (TopModuleCat.{w} R) G
  let T₀ := forget₂ (TopModuleCat.{w} R) TopCat
  let T := forget₂ (TopModuleCat.{max v w} R) TopCat
  let : HasLimitsOfSize.{t₁, t₂} (ModuleCat.{w} R) := ModuleCat.hasLimitsOfSize
  let : UnivLE.{t₂, max v w} := UnivLE.trans.{t₂, w, max v w}
  let : HasLimitsOfSize.{t₁, t₂} (ModuleCat.{max v w} R) :=
    ModuleCat.hasLimitsOfSize.{t₁, t₂, max v w, u}
  let : PreservesLimitsOfShape J T₀ := inferInstance
  let : PreservesLimitsOfShape J U₀ := inferInstance
  let : ReflectsLimitsOfShape J T := reflectsLimitsOfShape_of_reflectsIsomorphisms
  let : ReflectsLimitsOfShape J U := inferInstance
  let : LocallyCompactSpace (ULift.{w} G) :=
    (Homeomorph.ulift : ULift.{w} G ≃ₜ G).isOpenEmbedding.locallyCompactSpace
  let : (TopCat.mappingSpace (TopCat.of (ULift.{w} G))).IsRightAdjoint :=
    (TopCat.tensorLeftAdjunction (TopCat.of (ULift.{w} G))).isRightAdjoint
  have e : (coind₁Functor R G ⋙ U) ⋙ T ≅
      ((U₀ ⋙ T₀) ⋙ TopCat.uliftFunctor.{v}) ⋙ TopCat.mappingSpace (TopCat.of (ULift.{w} G)) :=
    NatIso.ofComponents
      (fun X ↦ TopCat.isoOfHomeo
        (Homeomorph.ulift.symm.arrowCongr (TopCat.of X.V).uliftFunctorObjHomeo))
      (fun {X Y} f ↦ by
        ext F
        apply ContinuousMap.ext
        intro g
        -- The source of the comparison is the compact-open space of maps into `X`.
        change C(G, X.V) at F
        let liftedMap := TopCat.uliftFunctor.{v}.map (T₀.map (U₀.map f))
        let liftedF :=
          (Homeomorph.ulift.symm.arrowCongr ((U₀ ⋙ T₀).obj X).uliftFunctorObjHomeo) F
        -- The component precomposes by `ULift.down` and postcomposes by `ULift.up`.
        calc
          _ = ULift.up (ContRepresentation.coind₁Map f.hom F g.down) := rfl
          _ = ULift.up (f.hom (F g.down)) := congrArg ULift.up
            (ContRepresentation.coind₁ResMap_apply (ContinuousMonoidHom.id G) f.hom F g.down)
          _ = _ := congrArg (fun K : C(ULift.{w} G, ULift.{v} Y.V) ↦ K g)
            (TopCat.mappingSpace_map_hom_apply (TopCat.of (ULift.{w} G)) liftedMap liftedF).symm)
  have : PreservesLimitsOfShape J ((coind₁Functor R G ⋙ U) ⋙ T) :=
    preservesLimitsOfShape_of_natIso e.symm
  have : PreservesLimitsOfShape J (coind₁Functor R G ⋙ U) :=
    preservesLimitsOfShape_of_reflects_of_preserves _ T
  exact preservesLimitsOfShape_of_reflects_of_preserves _ U

/-- Coinduction preserves limits over a locally compact group, by the exponential law. -/
instance (priority := low) coind₁Functor_preservesLimits :
    PreservesLimits (coind₁Functor.{u, v, max v w} R G) :=
  coind₁Functor_preservesLimitsOfSize.{u, v, max v w, max v w, max v w} R G

end TopRep

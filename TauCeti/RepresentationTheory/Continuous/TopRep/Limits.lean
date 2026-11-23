/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Continuous.TopRep.Products
public import Mathlib.RepresentationTheory.Homological.ContCohomology.Functoriality
public import TauCeti.Topology.Category.TopCat.MappingSpace
public import Mathlib.Topology.Category.TopCat.ULift

/-!
# Limits of coinduced representations and invariants

The invariants functor is right adjoint to the trivial-action functor, and hence preserves
limits. This is the topological counterpart of Mathlib's `Rep.invariantsAdjunction`.
For a locally compact group, `coind₁Functor` also preserves limits because its underlying
topological space is the compact-open mapping space, a right adjoint on `TopCat`.
Each degree of the coinduced resolution, packaged as `TopRep.resolutionFunctor`, consequently
preserves limits as well.
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

/-- The trivial-action functor equips a continuous linear map with trivial equivariance. -/
@[simp]
theorem trivialFunctor_map_hom (G : Type v) [Monoid G]
    {X Y : TopModuleCat.{w} R} (f : X ⟶ Y) :
    ((trivialFunctor R G).map f).hom = ⟨f.hom, fun _ ↦ rfl⟩ := (rfl)

/-- The trivial-action functor acts on maps by their original continuous linear map. -/
@[simp↓]
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

variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- The functor taking a representation to a fixed degree of its coinduced resolution. -/
@[expose, simps -isSimp obj map]
def resolutionFunctor (n : ℕ) :
    TopRep.{max v w} R G ⥤ TopRep.{max v w} R G where
  obj X := resolutionX X n
  map f := _root_.ContinuousCohomology.resolutionMap (ContinuousMonoidHom.id G) f n
  map_id X := _root_.ContinuousCohomology.resolutionMap_id X n
  map_comp f g := _root_.ContinuousCohomology.resolutionMap_comp
    (ContinuousMonoidHom.id G) (ContinuousMonoidHom.id G) f g n

attribute [simp] resolutionFunctor_obj
-- Let the generic functor laws simplify identities and composites first.
attribute [simp low] resolutionFunctor_map

private def coind₁FunctorCompForgetIsoApp (X : TopRep.{w} R G) :
    TopCat.of C(G, X.V) ≅ TopCat.of C(ULift.{w} G, ULift.{v} X.V) :=
  TopCat.isoOfHomeo
    (Homeomorph.ulift.symm.arrowCongr (TopCat.of X.V).uliftFunctorObjHomeo)

/-- After forgetting the representation and module structures, coinduction is the compact-open
mapping-space functor, with universe lifts on its source and target. The identification holds
over any topological group. -/
def coind₁FunctorCompForgetIso :
    (coind₁Functor.{u, v, w} R G ⋙
      (toActionTopModFunc ⋙ Action.forget (TopModuleCat.{max v w} R) G)) ⋙
        forget₂ (TopModuleCat.{max v w} R) TopCat ≅
    ((toActionTopModFunc ⋙ Action.forget (TopModuleCat.{w} R) G) ⋙
      forget₂ (TopModuleCat.{w} R) TopCat ⋙ TopCat.uliftFunctor.{v}) ⋙
        TopCat.mappingSpace (TopCat.of (ULift.{w} G)) :=
  NatIso.ofComponents (coind₁FunctorCompForgetIsoApp R G) (fun {X Y} f ↦ by
    ext F
    apply ContinuousMap.ext
    intro g
    -- Pin the carrier to its compact-open mapping space before computing the functor map.
    change C(G, X.V) at F
    let liftedMap := TopCat.uliftFunctor.{v}.map
      ((forget₂ (TopModuleCat.{w} R) TopCat).map
        ((toActionTopModFunc ⋙ Action.forget (TopModuleCat.{w} R) G).map f))
    let liftedF := (coind₁FunctorCompForgetIsoApp R G X).hom.hom F
    calc
      -- The component transports a map along the two ulift homeomorphisms.
      _ = ULift.up (ContRepresentation.coind₁Map f.hom F g.down) := (rfl)
      _ = ULift.up (f.hom (F g.down)) := congrArg ULift.up
        (ContRepresentation.coind₁ResMap_apply (ContinuousMonoidHom.id G) f.hom F g.down)
      _ = _ := congrArg (fun K : C(ULift.{w} G, ULift.{v} Y.V) ↦ K g)
        (TopCat.mappingSpace_map_hom_apply (TopCat.of (ULift.{w} G)) liftedMap liftedF).symm)

/-- The forward component lifts a continuous map by evaluating it at the lowered argument. -/
@[simp↓]
theorem coind₁FunctorCompForgetIso_hom_app_hom_apply (X : TopRep.{w} R G)
    (F : C(G, X.V)) (g : ULift.{w} G) :
    DFunLike.coe (F := C(ULift.{w} G, ULift.{v} X.V))
      (((coind₁FunctorCompForgetIso R G).hom.app X).hom F) g = ULift.up (F g.down) := (rfl)

/-- The inverse component lowers a lifted continuous map after evaluating at a lifted argument. -/
@[simp↓]
theorem coind₁FunctorCompForgetIso_inv_app_hom_apply (X : TopRep.{w} R G)
    (F : C(ULift.{w} G, ULift.{v} X.V)) (g : G) :
    DFunLike.coe (F := C(G, X.V))
      (((coind₁FunctorCompForgetIso R G).inv.app X).hom F) g = (F (ULift.up g)).down := (rfl)

variable [LocallyCompactSpace G]

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
  have : PreservesLimitsOfShape J ((coind₁Functor R G ⋙ U) ⋙ T) :=
    preservesLimitsOfShape_of_natIso (coind₁FunctorCompForgetIso R G).symm
  have : PreservesLimitsOfShape J (coind₁Functor R G ⋙ U) :=
    preservesLimitsOfShape_of_reflects_of_preserves _ T
  exact preservesLimitsOfShape_of_reflects_of_preserves _ U

/-- Coinduction preserves limits over a locally compact group, by the exponential law. -/
instance (priority := low) coind₁Functor_preservesLimits :
    PreservesLimits (coind₁Functor.{u, v, max v w} R G) :=
  coind₁Functor_preservesLimitsOfSize.{u, v, max v w, max v w, max v w} R G

/-- Each degree of the coinduced resolution preserves limits over a locally compact group. -/
instance resolutionFunctor_preservesLimitsOfSize [UnivLE.{t₂, max v w}] (n : ℕ) :
    PreservesLimitsOfSize.{t₁, t₂} (resolutionFunctor.{u, v, w} R G n) := by
  induction n with
  | zero =>
    have e : 𝟭 (TopRep.{max v w} R G) ≅ resolutionFunctor R G 0 :=
      NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun f ↦ by
        -- In degree zero the resolution and its map are the original representation and map.
        change f ≫ 𝟙 _ = 𝟙 _ ≫ f
        simp only [Category.comp_id, Category.id_comp])
    exact preservesLimits_of_natIso e
  | succ n ih =>
    have := ih
    have e : resolutionFunctor R G n ⋙ coind₁Functor R G ≅
        resolutionFunctor R G (n + 1) :=
      NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun f ↦ by
        let g := _root_.ContinuousCohomology.resolutionMap (ContinuousMonoidHom.id G) f n
        -- Expose the map of the coinduction abbrev and the successor resolution map.
        change ofHom (ContRepresentation.coind₁Map g.hom) ≫ 𝟙 _ =
          𝟙 _ ≫ ofHom (ContRepresentation.coind₁ResMap (ContinuousMonoidHom.id G) g.hom)
        simp only [Category.comp_id, Category.id_comp]
        exact (congrArg ofHom (ContRepresentation.coind₁ResMap_id _)).symm)
    exact preservesLimits_of_natIso e

end TopRep

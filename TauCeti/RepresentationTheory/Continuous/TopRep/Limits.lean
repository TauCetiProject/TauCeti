/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Continuous.TopRep.Products
public import TauCeti.Topology.Category.TopCat.MappingSpace
public import Mathlib.Topology.Category.TopCat.ULift

/-!
# Limits of coinduced representations

For any topological group, `coind₁Functor` preserves limits of diagrams whose object type is
small in the source representation's carrier universe, with no restriction on the morphism
universe. Its underlying topological space is a compact-open mapping space, which preserves
limits for R₁ source spaces.
-/

public section

noncomputable section

open CategoryTheory Limits

universe u v w t₁ t₂

namespace TopRep

variable (R : Type u) [Ring R] [TopologicalSpace R]

variable (G : Type v) [Group G]

variable [TopologicalSpace G] [IsTopologicalGroup G]

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

/-- Coinduction over any topological group preserves limits of diagrams whose object type is
small in the source representation's carrier universe `w`. -/
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
  have : PreservesLimitsOfShape J ((coind₁Functor R G ⋙ U) ⋙ T) :=
    preservesLimitsOfShape_of_natIso (coind₁FunctorCompForgetIso R G).symm
  have : PreservesLimitsOfShape J (coind₁Functor R G ⋙ U) :=
    preservesLimitsOfShape_of_reflects_of_preserves _ T
  exact preservesLimitsOfShape_of_reflects_of_preserves _ U

/-- Coinduction over any topological group preserves small limits when the source representations
have carrier universe `max v w`, where `v` is the group's universe. Here both the diagram's object
and morphism universes are `max v w`. -/
instance (priority := low) coind₁Functor_preservesLimits :
    PreservesLimits (coind₁Functor.{u, v, max v w} R G) :=
  coind₁Functor_preservesLimitsOfSize.{u, v, max v w, max v w, max v w} R G

end TopRep

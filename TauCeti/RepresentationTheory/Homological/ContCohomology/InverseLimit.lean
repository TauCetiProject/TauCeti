/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Additive
public import TauCeti.RepresentationTheory.Continuous.TopRep.Limits
public import TauCeti.RepresentationTheory.Continuous.Invariants
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Resolution.Basic
public import Mathlib.Algebra.Homology.HomologicalComplexLimits

/-!
# Continuous cochains into inverse limits

Over any topological group, the canonical homogeneous continuous cochain functor preserves
limits of diagrams whose object type is small in the group universe, with no restriction on
the morphism universe. In particular, continuous cochains into an inverse limit
are the inverse limit of continuous cochains, with the comparison commuting with projections
and differentials. The instance
`continuousCochainsFunctorCompForget_preservesLimitsOfSize` gives the same preservation after
forgetting the cochain topologies, under the same size bound.
Use `CategoryTheory.Limits.preservesLimitIso` for the comparison and
`CategoryTheory.Limits.preservesLimitIso_hom_π` for its projections.

This is the cochain comparison underlying the inverse-limit discussion in K. Rubin,
*Euler Systems*, Appendix B, §2. We use Mathlib's homogeneous cochains, constructed by iterated
coinduction and invariants, and preservation of limits by compact-open mapping spaces.
The degree functors of the coinduced resolution, packaged as `TopRep.resolutionFunctor`,
preserve limits of diagrams whose object type is small in their carrier universe `max v w`,
the maximum of the group and caller carrier universes, again with no restriction on the
morphism universe.
-/

public section

noncomputable section

open CategoryTheory Limits TopRep

universe u v w t₁ t₂ w₁ w₂

namespace TopRep

variable (R : Type u) [Ring R] [TopologicalSpace R]
  (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Each degree of the coinduced resolution preserves limits of diagrams whose object type
is small in the carrier universe `max v w`, with no restriction on the morphism universe. -/
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

namespace TauCeti.ContinuousCohomology

variable (R : Type u) [Ring R] [TopologicalSpace R]
  (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Degree `n` homogeneous continuous cochains are the invariants of degree `n + 1` of the
coinduced resolution. The component objects are definitionally equal. -/
def resolutionFunctorCompInvariantsIso (n : ℕ) :
    resolutionFunctor R G (n + 1) ⋙ invariantsFunctor R G ≅
      continuousCochainsFunctor R G ⋙ HomologicalComplex.eval _ _ n :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun f ↦ by
    -- Expose the common degree component so simplification can compute the cochain map.
    change (invariantsFunctor R G).map ((resolutionFunctor R G (n + 1)).map f) ≫ 𝟙 _ =
      𝟙 _ ≫ ((continuousCochainsFunctor R G).map f).f n
    simp only [resolutionFunctor_map, continuousCochainsFunctor_map,
      ← mapHomologicalComplex_map_shiftedResolutionMap,
      Functor.mapHomologicalComplex_map_f, shiftedResolutionMap_f]
    exact (Category.comp_id _).trans (Category.id_comp _).symm)

-- The component equations are named rewrites because simplifying their identities across the
-- definitionally equal carriers prevents generic iso cancellation in importing modules.
/-- The degree comparison acts as the identity on the common invariant-vector module. -/
theorem resolutionFunctorCompInvariantsIso_hom_app (n : ℕ) (X : TopRep R G) :
    (resolutionFunctorCompInvariantsIso R G n).hom.app X = 𝟙 _ := (rfl)

/-- The inverse degree comparison acts as the identity on the common invariant-vector module. -/
theorem resolutionFunctorCompInvariantsIso_inv_app (n : ℕ) (X : TopRep R G) :
    (resolutionFunctorCompInvariantsIso R G n).inv.app X = 𝟙 _ := (rfl)

/-- Canonical homogeneous continuous cochains preserve limits of diagrams whose object type
is small in the group universe, with no restriction on the morphism universe. -/
instance continuousCochainsFunctor_preservesLimitsOfSize [UnivLE.{w₂, v}] :
    PreservesLimitsOfSize.{w₁, w₂} (continuousCochainsFunctor R G) where
  preservesLimitsOfShape {_J} _ := HomologicalComplex.preservesLimitsOfShape_of_eval _ fun n ↦
    preservesLimitsOfShape_of_natIso (resolutionFunctorCompInvariantsIso R G n)

/-- Canonical homogeneous continuous cochains preserve small limits. -/
instance continuousCochainsFunctor_preservesLimits :
    PreservesLimits (continuousCochainsFunctor R G) :=
  continuousCochainsFunctor_preservesLimitsOfSize R G

/-- After forgetting their topologies, continuous cochains preserve limits of diagrams whose
object type is small in the group universe, with no restriction on the morphism universe. -/
instance continuousCochainsFunctorCompForget_preservesLimitsOfSize [UnivLE.{w₂, v}] :
    PreservesLimitsOfSize.{w₁, w₂} (continuousCochainsFunctor R G ⋙
      (forget₂ (TopModuleCat.{v} R) (ModuleCat.{v} R)).mapHomologicalComplex
        (ComplexShape.up ℕ)) where
  preservesLimitsOfShape {J} _ := by
    let : HasLimitsOfSize.{w₁, w₂} (ModuleCat.{v} R) := ModuleCat.hasLimitsOfSize
    apply HomologicalComplex.preservesLimitsOfShape_of_eval
    intro n
    -- Evaluation of a mapped complex is definitionally evaluation followed by the module functor.
    change PreservesLimitsOfShape J
      ((continuousCochainsFunctor R G ⋙ HomologicalComplex.eval _ _ n) ⋙
        forget₂ (TopModuleCat.{v} R) (ModuleCat.{v} R))
    infer_instance

end TauCeti.ContinuousCohomology

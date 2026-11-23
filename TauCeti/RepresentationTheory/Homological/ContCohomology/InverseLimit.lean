/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Additive
public import TauCeti.RepresentationTheory.Continuous.TopRep.Limits
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-!
# Continuous cochains into inverse limits

Over a locally compact group, the canonical homogeneous continuous cochain functor preserves
limits of arbitrary small diagrams. In particular, continuous cochains into an inverse limit
are the inverse limit of continuous cochains, with the comparison commuting with projections
and differentials. The same statement holds after forgetting the topologies of the cochains.
Use `CategoryTheory.Limits.preservesLimitIso` for the comparison and
`CategoryTheory.Limits.preservesLimitIso_hom_π` for its projections.

This is the cochain comparison underlying the inverse-limit discussion in K. Rubin,
*Euler Systems*, Appendix B, §2. We use Mathlib's homogeneous cochains, constructed by iterated
coinduction and invariants, and the compact-open mapping-space adjunction.
-/

public section

noncomputable section

open CategoryTheory Limits TopRep

universe u v w₁ w₂

namespace TauCeti.ContinuousCohomology

variable (R : Type u) [Ring R] [TopologicalSpace R]
  (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

private def resolutionFunctor (n : ℕ) : TopRep.{v} R G ⥤ TopRep.{v} R G where
  obj X := resolutionX X n
  map f := _root_.ContinuousCohomology.resolutionMap (ContinuousMonoidHom.id G) f n
  map_id X := _root_.ContinuousCohomology.resolutionMap_id X n
  map_comp f g := _root_.ContinuousCohomology.resolutionMap_comp
    (ContinuousMonoidHom.id G) (ContinuousMonoidHom.id G) f g n

private lemma resolutionFunctor_preservesLimitsOfSize [LocallyCompactSpace G]
    [UnivLE.{w₂, v}] (n : ℕ) :
    PreservesLimitsOfSize.{w₁, w₂} (resolutionFunctor R G n) := by
  induction n with
  | zero =>
    have e : 𝟭 (TopRep.{v} R G) ≅ resolutionFunctor R G 0 :=
      -- The degree-zero resolution has the original representation as its object.
      NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun f ↦ by
        change f ≫ 𝟙 _ = 𝟙 _ ≫
          _root_.ContinuousCohomology.resolutionMap (ContinuousMonoidHom.id G) f 0
        rw [Category.comp_id, Category.id_comp]
        exact (_root_.ContinuousCohomology.resolutionMap_zero
          (ContinuousMonoidHom.id G) f).symm)
    exact preservesLimits_of_natIso e
  | succ n ih =>
    have := ih
    have : PreservesLimitsOfSize.{w₁, w₂} (coind₁Functor.{u, v, v} R G) :=
      coind₁Functor_preservesLimitsOfSize R G
    have e : resolutionFunctor R G n ⋙ coind₁Functor R G ≅ resolutionFunctor R G (n + 1) :=
      -- Successor resolution objects are defined by applying coinduction.
      NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun f ↦ by
        change ofHom (ContRepresentation.coind₁Map
          (_root_.ContinuousCohomology.resolutionMap (ContinuousMonoidHom.id G) f n).hom) ≫
            𝟙 _ = 𝟙 _ ≫
              _root_.ContinuousCohomology.resolutionMap (ContinuousMonoidHom.id G) f (n + 1)
        rw [Category.comp_id, Category.id_comp]
        exact (congrArg ofHom (ContRepresentation.coind₁ResMap_id _)).symm.trans
          (_root_.ContinuousCohomology.resolutionMap_succ
            (ContinuousMonoidHom.id G) f n).symm)
    exact preservesLimits_of_natIso e

/-- Canonical homogeneous continuous cochains preserve limits over a locally compact group. -/
instance continuousCochainsFunctor_preservesLimitsOfSize [LocallyCompactSpace G]
    [UnivLE.{w₂, v}] :
    PreservesLimitsOfSize.{w₁, w₂} (continuousCochainsFunctor R G) where
  preservesLimitsOfShape {J} _ := HomologicalComplex.preservesLimitsOfShape_of_eval _ fun n ↦ by
    have := resolutionFunctor_preservesLimitsOfSize.{u, v, w₁, w₂} R G (n + 1)
    have e : resolutionFunctor R G (n + 1) ⋙ invariantsFunctor R G ≅
        continuousCochainsFunctor R G ⋙ HomologicalComplex.eval _ _ n :=
      -- Homogeneous cochains are the invariants of the shifted resolution.
      NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun f ↦ by
        change (invariantsFunctor R G).map
          (_root_.ContinuousCohomology.resolutionMap (ContinuousMonoidHom.id G) f (n + 1)) ≫
            𝟙 _ = 𝟙 _ ≫ ((continuousCochainsFunctor R G).map f).f n
        rw [Category.comp_id, Category.id_comp, continuousCochainsFunctor_map,
          ← mapHomologicalComplex_map_shiftedResolutionMap]
        change (invariantsFunctor R G).map _ =
          (invariantsFunctor R G).map ((shiftedResolutionMap f).f n)
        rw [shiftedResolutionMap_f])
    exact preservesLimitsOfShape_of_natIso e

/-- Canonical homogeneous continuous cochains preserve limits over a locally compact group. -/
instance continuousCochainsFunctor_preservesLimits [LocallyCompactSpace G] :
    PreservesLimits (continuousCochainsFunctor R G) :=
  continuousCochainsFunctor_preservesLimitsOfSize R G

end TauCeti.ContinuousCohomology

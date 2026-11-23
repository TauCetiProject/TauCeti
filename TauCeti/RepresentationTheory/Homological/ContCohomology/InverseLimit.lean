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

/-- Degree `n` homogeneous continuous cochains are the invariants of degree `n + 1` of the
coinduced resolution. The component objects are definitionally equal. -/
def resolutionFunctorCompInvariantsIso (n : ℕ) :
    resolutionFunctor R G (n + 1) ⋙ invariantsFunctor R G ≅
      continuousCochainsFunctor R G ⋙ HomologicalComplex.eval _ _ n :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun f ↦ by
    rw [Functor.comp_map, Functor.comp_map, resolutionFunctor_map,
      HomologicalComplex.eval_map, continuousCochainsFunctor_map,
      ← mapHomologicalComplex_map_shiftedResolutionMap,
      Functor.mapHomologicalComplex_map_f, shiftedResolutionMap_f]
    exact (Category.comp_id _).trans (Category.id_comp _).symm)

/-- The degree comparison acts as the identity on the common invariant-vector module. -/
theorem resolutionFunctorCompInvariantsIso_hom_app (n : ℕ) (X : TopRep R G) :
    (resolutionFunctorCompInvariantsIso R G n).hom.app X = 𝟙 _ := (rfl)

/-- Canonical homogeneous continuous cochains preserve limits over a locally compact group. -/
instance continuousCochainsFunctor_preservesLimitsOfSize [LocallyCompactSpace G]
    [UnivLE.{w₂, v}] :
    PreservesLimitsOfSize.{w₁, w₂} (continuousCochainsFunctor R G) where
  preservesLimitsOfShape {_J} _ := HomologicalComplex.preservesLimitsOfShape_of_eval _ fun n ↦
    preservesLimitsOfShape_of_natIso (resolutionFunctorCompInvariantsIso R G n)

/-- Canonical homogeneous continuous cochains preserve limits over a locally compact group. -/
instance continuousCochainsFunctor_preservesLimits [LocallyCompactSpace G] :
    PreservesLimits (continuousCochainsFunctor R G) :=
  continuousCochainsFunctor_preservesLimitsOfSize R G

end TauCeti.ContinuousCohomology

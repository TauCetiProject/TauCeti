/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.RepresentationTheory.Homological.GroupHomology.Functoriality

/-!
# Additivity of the group-homology chains functor

Mathlib shows that the functor `groupHomology.chainsFunctor k G` sending a representation to its
complex of inhomogeneous chains preserves zero morphisms. This file shows that it is additive,
matching Mathlib's instance for its cohomological counterpart `groupCohomology.cochainsFunctor`.

## Main results

* `TauCeti.groupHomology.chainsFunctorAdditive`: the chains functor is additive.
-/

public noncomputable section

universe u

open CategoryTheory

namespace TauCeti.groupHomology

variable {R G : Type u} [CommRing R] [Group G]

/-- The functor from representations to inhomogeneous group-homology chains is additive. -/
noncomputable instance chainsFunctorAdditive :
    (_root_.groupHomology.chainsFunctor R G).Additive where
  map_add := by
    intro X Y f g
    -- `chainsFunctor.map` is `chainsMap (MonoidHom.id G)` by definition (`chainsFunctor_map`).
    -- Rewriting with that lemma is not enough: the sum in the goal would still carry the
    -- preadditive instance from the statement of `Functor.Additive`, which
    -- `HomologicalComplex.add_f_apply` does not match syntactically. Restating the goal
    -- elaborates both sums with the `HomologicalComplex` addition.
    change _root_.groupHomology.chainsMap (MonoidHom.id G) (f + g) =
      _root_.groupHomology.chainsMap (MonoidHom.id G) f +
        _root_.groupHomology.chainsMap (MonoidHom.id G) g
    refine HomologicalComplex.hom_ext _ _ fun i => ModuleCat.hom_ext ?_
    simp only [HomologicalComplex.add_f_apply, ModuleCat.hom_add,
      _root_.groupHomology.chainsMap_id_f_hom_eq_mapRange]
    refine Finsupp.lhom_ext fun x a => ?_
    simp only [Rep.add_hom, Representation.IntertwiningMap.add_toLinearMap,
      LinearMap.add_apply, Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single,
      Finsupp.single_add]

end TauCeti.groupHomology

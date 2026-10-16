/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Free.Yoneda
public import Mathlib.Topology.Sheaves.Flasque

/-!
# Injective sheaves of modules are flasque

An injective sheaf of modules over any sheaf of rings on a topological space has
surjective restriction maps. Thus its underlying abelian sheaf is flasque and can
be used as an acyclic coefficient in sheaf cohomology. Injectivity is taken in the
category of module sheaves, not in the category of abelian sheaves.

The argument extends a section along the monomorphism of free module sheaves
associated to an inclusion of opens. It follows the argument for abelian sheaves in
`TauCeti.Topology.isFlasque_of_injective`, using the module-valued free-Yoneda
correspondence.

## References

* The Stacks Project, Lemma 20.12.2 (Tag 09SX), injective modules are flasque.
* R. Hartshorne, *Algebraic Geometry*, III, Proposition 2.4.
-/

public section

open CategoryTheory TopologicalSpace

universe u

namespace SheafOfModules

variable {X : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}}

/-- An injective module sheaf has surjective restriction maps, regardless of its ring of
coefficients. -/
instance isFlasque_of_injective (M : SheafOfModules.{u} R) [Injective M] :
    TopCat.Presheaf.IsFlasque M.val.presheaf where
  epi {U V} i := by
    rw [AddCommGrpCat.epi_iff_surjective]
    intro s
    -- Keep the section in its module carrier while applying the free-module correspondence.
    change M.val.obj V at s
    refine ⟨freeYonedaEquiv R U.unop M
      (Injective.factorThru ((freeYonedaEquiv R V.unop M).symm s)
        ((freeYonedaFunctor R).map i.unop)), ?_⟩
    have h := freeYonedaEquiv_naturality R i.unop M
      (Injective.factorThru ((freeYonedaEquiv R V.unop M).symm s)
        ((freeYonedaFunctor R).map i.unop))
    rw [Injective.comp_factorThru, Equiv.apply_symm_apply] at h
    exact h.symm

end SheafOfModules

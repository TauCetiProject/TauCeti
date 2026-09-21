/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Induction.Inertia
public import TauCeti.RepresentationTheory.Induction.LiesOver

/-!
# Induction from the inertia group preserves lying over

For a normal subgroup `N` of `G`, an `N`-representation `V`, and its inertia group `inertia V`,
this file specialises `FDRep.LiesOver.indFDRep` to induction from `inertia V` to `G`: inducing a
representation of `inertia V` lying over `V` gives a representation of `G` that still lies over
`V`.  This is the "lies over" half of the forward map in the Clifford correspondence; the
irreducibility half is `FDRep.simple_indFDRep_of_inertia`.

## Main statements

* `FDRep.liesOver_indFDRep_of_inertia`: the inertia-group specialization of
  `FDRep.LiesOver.indFDRep`.

## References

* I. M. Isaacs, *Character Theory of Finite Groups*, Theorem 6.11.
* C. W. Curtis and I. Reiner, *Methods of Representation Theory, Vol. I*, §11.
-/

public section

open CategoryTheory

universe u

namespace FDRep

open TauCeti

variable {k G : Type u} [Field k] [Group G] {N : Subgroup G} [N.Normal]

/-- Inducing from the inertia group preserves occurrence of the chosen normal-subgroup
constituent.  This is the "lies over" half of the forward map in the Clifford correspondence. -/
theorem liesOver_indFDRep_of_inertia (V : FDRep k N) [(inertia V).FiniteIndex]
    (U : FDRep k (inertia V))
    (h : U.LiesOver (Subgroup.inclusion (le_inertia V)) V) :
    (indFDRep U).LiesOver N.subtype V := by
  have hInd := h.indFDRep
  have hcomp : (inertia V).subtype.comp (Subgroup.inclusion (le_inertia V)) = N.subtype := by
    ext
    rfl
  rw [hcomp] at hInd
  exact hInd

end FDRep

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Evens.Class
public import TauCeti.Topology.Algebra.Group.OpenSubgroup.IndexTwo

/-!
# The cohomology class of an index-two character

An open subgroup `U` of index two in a topological group `G` determines a continuous character
`G → Multiplicative (ZMod 2)`, equal to one precisely on `U`. This file places that character in
canonical continuous cohomology with trivial `𝔽₂` coefficients.

The definition is the class `TauCeti.ContCohomology.homClass` of the continuous character, which
uses the explicit degree-one comparison: the multiplicative character is first viewed as a
continuous additive `1`-cocycle by `TauCeti.ContCohomology.evensHomCocycle`, then its explicit
class is transported to Mathlib's canonical continuous cohomology object. This is the
character class that appears in the index-two exact sequence and in the norm-of-restriction
identity for the Evens norm.

## Main definition

* `OpenSubgroup.indexTwoCharacterClass`: the class in `H¹(G, 𝔽₂)` of the
  character whose kernel is `U`.

## Reference

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Chapter I,
  §§5–6, for the index-two character in restriction–corestriction sequences.
-/

public section

noncomputable section

open CategoryTheory TauCeti TauCeti.ContCohomology

namespace OpenSubgroup

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

local instance continuousSMul_trivialF2_character : ContinuousSMul G (trivialF2 G).V :=
  (isSmoothDiscrete_trivialF2 G).continuousSMul

/-- **The class of the character of an index-two open subgroup.** It is the class
`TauCeti.ContCohomology.homClass` of the continuous character `Subgroup.indexTwoCharacter`, whose
kernel is the subgroup. -/
noncomputable def indexTwoCharacterClass (U : OpenSubgroup G)
    (hU : U.toSubgroup.index = 2) : continuousCohomology 1 (trivialF2 G) :=
  homClass G (U.toSubgroup.indexTwoCharacter hU)
    (Subgroup.continuous_indexTwoCharacter hU U.isOpen')

/-- The index-two character class is obtained from the explicit class of the continuous character
by the degree-one comparison and the canonical identification of trivial coefficients. -/
theorem indexTwoCharacterClass_def (U : OpenSubgroup G)
    (hU : U.toSubgroup.index = 2) :
    indexTwoCharacterClass U hU =
      (eqToHom (congrArg (continuousCohomology 1) (ofDiscreteModule_trivialF2 G))).hom
        (explicitH1AddEquivContinuousCohomology G (trivialF2 G).V
          (evensHomCocycle (U.toSubgroup.indexTwoCharacter hU)
            (Subgroup.continuous_indexTwoCharacter hU U.isOpen'))) :=
  homClass_def G _ _

/-- The index-two character class depends only on the open subgroup, not on the proof that its
index is two. -/
theorem indexTwoCharacterClass_congr {U V : OpenSubgroup G}
    (hUV : U = V) (hU : U.toSubgroup.index = 2) (hV : V.toSubgroup.index = 2) :
    indexTwoCharacterClass U hU = indexTwoCharacterClass V hV := by
  subst V
  rfl

end OpenSubgroup

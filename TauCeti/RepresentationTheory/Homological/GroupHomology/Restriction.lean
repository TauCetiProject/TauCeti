/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.RepresentationTheory.FiniteIndex
public import Mathlib.RepresentationTheory.Homological.GroupHomology.Functoriality
public import Mathlib.RepresentationTheory.Homological.GroupHomology.Shapiro

/-!
# Restriction in group homology

Let `S` be a finite-index subgroup of a group `G`. Group homology has a restriction map

`H_n(G, M) ⟶ H_n(S, Resˢᴳ M)`.

Unlike the covariant map induced by the inclusion `S → G`, restriction goes against the group
homomorphism. It is obtained from the unit `M ⟶ Indˢᴳ Resˢᴳ M` of the finite-index
adjunction, followed by Shapiro's isomorphism
`H_n(G, Indˢᴳ Resˢᴳ M) ≃ H_n(S, Resˢᴳ M)`. This is the standard homological transfer;
transporting it across the negative-degree comparison gives restriction in Tate cohomology below
degree `-1`.

## Main definitions

* `TauCeti.groupHomology.res`: restriction from a group to a finite-index subgroup.

## References

* K. S. Brown, *Cohomology of Groups*, Chapter III, Sections 9–10.
* E. Artin and J. Tate, *Class Field Theory*, Chapter IV, §6.
-/

public noncomputable section

universe u

open CategoryTheory Rep

namespace TauCeti.groupHomology

variable {R G : Type u} [CommRing R] [Group G]

/-- Restriction in group homology from a group to a finite-index subgroup. It is the map induced
by the unit `M ⟶ Indˢᴳ Resˢᴳ M`, followed by the homological Shapiro isomorphism. -/
def res (M : Rep R G) (S : Subgroup G) [S.FiniteIndex] (n : ℕ) :
    _root_.groupHomology M n ⟶ _root_.groupHomology (Rep.res S.subtype M) n := by
  classical
  exact (_root_.groupHomology.functor R G n).map ((Rep.resIndAdjunction R S).unit.app M) ≫
    (_root_.groupHomology.indIso S (Rep.res S.subtype M) n).hom

end TauCeti.groupHomology

/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
public import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic
public import TauCeti.RepresentationTheory.Rep.Trivial

/-!
# The connecting class of a character

Let `G` be a finite group. A character `χ : Gᵃᵇ → ℚ/ℤ` is a homomorphism `G → ℚ/ℤ`, which is a
class in `H¹(G, ℚ/ℤ)` for the trivial action. The connecting map of the sequence
`0 → ℤ → ℚ → ℚ/ℤ → 0` of trivial `G`-modules sends it to a class `δχ ∈ H²(G, ℤ)`, which is read
in the Tate group of degree `2`.

As elsewhere in this development, `ℚ/ℤ` is the rational circle `AddCircle (1 : ℚ)`.

## Main definitions

* `TauCeti.TateCohomology.characterConnectingClass`: the connecting class `δχ ∈ H²(G, ℤ)` of a
  character `χ : Gᵃᵇ → ℚ/ℤ`, in the Tate group of degree `2`, as an additive map in `χ`.

## Main results

* `TauCeti.TateCohomology.characterConnectingClass_def`: `δχ` is the connecting map of
  `Rep.ratAddCircleShortComplex` applied to the class of `χ` in `H¹(G, ℚ/ℤ)`, read in Tate
  cohomology.

## References

* E. Artin and J. Tate, *Class Field Theory*, Chapter XIV, §3.
* J.-P. Serre, *Local Fields*, Chapter XI, §3.
-/

public noncomputable section

open CategoryTheory

namespace TauCeti.TateCohomology

variable (G : Type) [Group G] [Fintype G]

/-- The **connecting class** `δχ ∈ H²(G, ℤ)` of a character `χ : Gᵃᵇ → ℚ/ℤ` of a finite group `G`,
in the Tate group of degree `2`: the image of `χ`, as a class in `H¹(G, ℚ/ℤ)` for the trivial
action, under the connecting map of `0 → ℤ → ℚ → ℚ/ℤ → 0`. The character is read on `G` through
the abelianization map `G → Gᵃᵇ`. It is additive in the character. -/
def characterConnectingClass :
    (Additive (Abelianization G) →+ AddCircle (1 : ℚ)) →+ tateCohomology (Rep.trivial ℤ G ℤ) 2 :=
  ((_root_.TateCohomology.isoGroupCohomology 2).inv.app
      (Rep.trivial ℤ G ℤ)).hom.toAddMonoidHom.comp <|
    (groupCohomology.δ (Rep.ratAddCircleShortComplex_shortExact G) 1 2
        rfl).hom.toAddMonoidHom.comp <|
      (groupCohomology.H1IsoOfIsTrivial
          (Rep.trivial ℤ G (AddCircle (1 : ℚ)))).inv.hom.toAddMonoidHom.comp <|
        AddMonoidHom.compHom' Abelianization.of.toAdditive

/-- The connecting class of `χ` is the connecting map applied to the class of `G → Gᵃᵇ → ℚ/ℤ`
in `H¹(G, ℚ/ℤ)`, carried to Tate cohomology by the comparison of positive degrees. -/
theorem characterConnectingClass_def (χ : Additive (Abelianization G) →+ AddCircle (1 : ℚ)) :
    characterConnectingClass G χ =
      (_root_.TateCohomology.isoGroupCohomology 2).inv.app (Rep.trivial ℤ G ℤ)
        (groupCohomology.δ (Rep.ratAddCircleShortComplex_shortExact G) 1 2 rfl
          ((groupCohomology.H1IsoOfIsTrivial (Rep.trivial ℤ G (AddCircle (1 : ℚ)))).inv
            (χ.comp Abelianization.of.toAdditive))) :=
  (rfl)

end TauCeti.TateCohomology

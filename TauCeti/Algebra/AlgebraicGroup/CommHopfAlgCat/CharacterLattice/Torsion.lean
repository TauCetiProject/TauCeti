/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.HopfAlgebra.TensorProduct
public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.CharacterLattice.Basic
public import TauCeti.Algebra.AlgebraicGroup.Connected.CommHopfAlgCat
public import TauCeti.Algebra.AlgebraicGroup.GeometricallyReduced.CommHopfAlgCat
public import TauCeti.Algebra.AlgebraicGroup.Smooth.GeometricallyReduced
public import TauCeti.Algebra.Bialgebra.GroupLike.Torsion

/-!
# The characters of a geometrically reduced, geometrically connected affine group are torsion free

A geometric character of an affine group `Spec H` is a group-like element of the coordinate Hopf
algebra of its base change to an algebraic closure. This file proves that when `H` is
geometrically reduced and geometrically connected, no geometric character has finite order, and
records the corollary for a smooth geometrically connected affine group.

Over the algebraic closure the argument is a reduction to the diagonalizable case. Group-like
elements of a Hopf algebra over a field are linearly independent, so evaluation embeds the group
algebra on them into `H`. A subring of a reduced ring is reduced, and connectedness of a prime
spectrum descends along an injective ring homomorphism, so both hypotheses pass to that group
algebra, where
`TauCeti.isMulTorsionFree_of_isReduced_monoidAlgebra_of_connectedSpace` already rules out torsion.

Neither hypothesis can be dropped. Connectedness alone fails in characteristic `p`, where the
coordinate Hopf algebra of `μ_p` is connected, non-reduced, and carries a character of order `p`.
Reducedness alone fails for the constant group `ℤ/n` over a field containing a primitive `n`-th
root of unity: its coordinate algebra is reduced but disconnected, and it has characters of
order `n`.

Contravariantly, a homomorphism from `Spec H` to the diagonalizable group `D(M)` is a morphism of
coordinate bialgebras `k[M] ⟶ H`. Torsion-freeness therefore says that a smooth geometrically
connected affine group admits no nontrivial homomorphism to a diagonalizable group on a torsion
group, so in particular no nontrivial `μ_n`-quotient.

## Main declarations

* `TauCeti.CommHopfAlgCat.isMulTorsionFree_geometricCharacterGroup`: **the geometric character
  group of a geometrically reduced, geometrically connected commutative Hopf algebra is torsion
  free.**
* `TauCeti.CommHopfAlgCat.isMulTorsionFree_geometricCharacterGroup_of_smooth`: its corollary for a
  smooth geometrically connected affine group, whose coordinate algebra is geometrically reduced.
* `TauCeti.CommHopfAlgCat.isAddTorsionFree_additiveCharacterGroup` and
  `TauCeti.CommHopfAlgCat.isAddTorsionFree_additiveCharacterGroup_of_smooth`: their additive forms.

## References

* J. S. Milne, *Algebraic Groups* (2017), Definitions 12.14 and 12.17.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Chapter 2.
* T. A. Springer, *Linear Algebraic Groups*, Theorem 6.3.1.
-/

public section

open scoped TensorProduct

namespace TauCeti

universe u

section Geometric

variable {k : Type u} [Field k] (H : CommHopfAlgCat.{u} k)

namespace CommHopfAlgCat

/-- **The geometric character group of a geometrically reduced, geometrically connected
commutative Hopf algebra is torsion free.** -/
theorem isMulTorsionFree_geometricCharacterGroup
    (hred : geometricallyReducedCommHopfAlgProperty k H)
    (hconn : geometricallyConnectedCommHopfAlgProperty k H) :
    IsMulTorsionFree (CommHopfAlgCat.geometricCharacterGroup H) := by
  have _ := (Algebra.isGeometricallyReduced_field_iff k (H : Type u)).mp
    hred.isGeometricallyReduced
  have _ := hconn.connectedSpace_algebraicClosureBaseChange
  exact isMulTorsionFree_groupLike_of_isReduced_of_connectedSpace (AlgebraicClosure k)
    (AlgebraicClosure k ⊗[k] (H : Type u))

/-- The additive character group of a geometrically reduced, geometrically connected commutative
Hopf algebra has no additive torsion. -/
theorem isAddTorsionFree_additiveCharacterGroup
    (hred : geometricallyReducedCommHopfAlgProperty k H)
    (hconn : geometricallyConnectedCommHopfAlgProperty k H) :
    IsAddTorsionFree (CommHopfAlgCat.additiveCharacterGroup H) := by
  have _ := isMulTorsionFree_geometricCharacterGroup H hred hconn
  infer_instance

/-- **The character lattice of a smooth geometrically connected affine group is torsion free.**
Over a field, smoothness implies geometric reducedness of its coordinate algebra. -/
theorem isMulTorsionFree_geometricCharacterGroup_of_smooth
    (hsmooth : smoothCommHopfAlgProperty k H)
    (hconn : geometricallyConnectedCommHopfAlgProperty k H) :
    IsMulTorsionFree (CommHopfAlgCat.geometricCharacterGroup H) :=
  isMulTorsionFree_geometricCharacterGroup H
    (geometricallyReducedCommHopfAlgProperty_of_smooth k H hsmooth) hconn

/-- The additive character lattice of a smooth geometrically connected affine group has no
additive torsion. -/
theorem isAddTorsionFree_additiveCharacterGroup_of_smooth
    (hsmooth : smoothCommHopfAlgProperty k H)
    (hconn : geometricallyConnectedCommHopfAlgProperty k H) :
    IsAddTorsionFree (CommHopfAlgCat.additiveCharacterGroup H) :=
  isAddTorsionFree_additiveCharacterGroup H
    (geometricallyReducedCommHopfAlgProperty_of_smooth k H hsmooth) hconn

end CommHopfAlgCat

end Geometric

end TauCeti

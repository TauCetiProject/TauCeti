/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.AlmostSplit.RadicalQuotient
public import TauCeti.RepresentationTheory.Quiver.AuslanderReiten.Quiver

/-!
# Arrow counts from almost-split sequences

An almost-split sequence computes the incoming arrows at its final term and the outgoing
arrows at its initial term. Their counts are the dimensions of the corresponding morphism
spaces involving the middle term, modulo the categorical radical. Thus decomposing the middle
term supplies the data for computing these arrow counts.

The counts are dimensions over the ground field, matching the basis-indexed quiver
`irreducibleMorphismQuiver`. The formulas hold over any field, for any finite vertex set;
neither acyclicity nor finiteness of the arrow set is required.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*,
  Cambridge University Press (1995), V.5 and VII.1.
-/

public section

namespace TauCeti.irreducibleMorphismQuiver

open CategoryTheory

universe u v w t

variable {k : Type u} {Q : Type v} [Field k] [Quiver.{w} Q] [Finite Q]
  {S : ShortComplex (QuiverRep.{u, v, w, t} k Q)}

/-- The arrows into the final term of an almost-split sequence are counted by morphisms into
its middle term modulo the radical. -/
theorem card_arrows_of_almostSplit_right (hS : S.IsAlmostSplit)
    (hA : IsFinDim k Q S.X₁) (hC : IsFinDim k Q S.X₃)
    {X : QuiverRep.{u, v, w, t} k Q} (hX : IsFinDim k Q X) (hI : Indecomposable X) :
    Nat.card (of hX hI ⟶ of hC hS.isRightAlmostSplit_g.indecomposable) =
      Module.finrank k ((X ⟶ S.X₂) ⧸ jacobsonRadicalSubmodule k X S.X₂) := by
  have : IsLocalRing (End S.X₁) :=
    (QuiverRep.indecomposable_iff_isLocalRing_end hA).mp hS.isLeftAlmostSplit_f.indecomposable
  have : IsLocalRing (End S.X₃) :=
    (QuiverRep.indecomposable_iff_isLocalRing_end hC).mp hS.isRightAlmostSplit_g.indecomposable
  rw [card_arrows_of]
  exact (hS.rightRadicalQuotientEquiv k X).finrank_eq.symm

/-- The arrows out of the initial term of an almost-split sequence are counted by morphisms
out of its middle term modulo the radical. -/
theorem card_arrows_of_almostSplit_left (hS : S.IsAlmostSplit)
    (hA : IsFinDim k Q S.X₁) (hC : IsFinDim k Q S.X₃)
    {X : QuiverRep.{u, v, w, t} k Q} (hX : IsFinDim k Q X) (hI : Indecomposable X) :
    Nat.card (of hA hS.isLeftAlmostSplit_f.indecomposable ⟶ of hX hI) =
      Module.finrank k ((S.X₂ ⟶ X) ⧸ jacobsonRadicalSubmodule k S.X₂ X) := by
  have : IsLocalRing (End S.X₁) :=
    (QuiverRep.indecomposable_iff_isLocalRing_end hA).mp hS.isLeftAlmostSplit_f.indecomposable
  have : IsLocalRing (End S.X₃) :=
    (QuiverRep.indecomposable_iff_isLocalRing_end hC).mp hS.isRightAlmostSplit_g.indecomposable
  rw [card_arrows_of]
  exact (hS.leftRadicalQuotientEquiv k X).finrank_eq.symm

end TauCeti.irreducibleMorphismQuiver

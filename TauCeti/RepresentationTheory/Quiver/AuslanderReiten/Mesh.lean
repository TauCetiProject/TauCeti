/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.AuslanderReiten.Quiver
public import TauCeti.CategoryTheory.AlmostSplit.Components

/-!
# Arrow support in Auslander–Reiten meshes

An almost-split sequence `0 ⟶ A ⟶ B ⟶ C ⟶ 0` pairs the incoming arrows at `[C]` with the
outgoing arrows at `[A]`: an arrow `[X] ⟶ [C]` exists exactly when an arrow `[A] ⟶ [X]` exists.
This supplies the support of the translation-quiver mesh relation. The theorem works with the
actual isomorphism classes and arrows of `irreducibleMorphismQuiver`, over any field and with no
acyclicity assumption. It does not identify `A` with a chosen `D Tr C` or compute multiplicities.

## References

* M. Auslander, I. Reiten, S. Smalø, *Representation Theory of Artin Algebras*, V.5 and VII.1.
-/

public section

namespace TauCeti.irreducibleMorphismQuiver

open CategoryTheory

universe u v w t

variable {k : Type u} {Q : Type v} [Field k] [Quiver.{w} Q] [Finite Q]

/-- An almost-split sequence pairs the support of the incoming arrows at its right-hand
end with the support of the outgoing arrows at its left-hand end. -/
theorem nonempty_arrows_of_almostSplit_iff
    {S : ShortComplex (QuiverRep.{u, v, w, t} k Q)} (hS : S.IsAlmostSplit)
    (hA : IsFinDim k Q S.X₁) (hC : IsFinDim k Q S.X₃)
    {X : QuiverRep.{u, v, w, t} k Q} (hX : IsFinDim k Q X) (hI : Indecomposable X) :
    Nonempty (of hX hI ⟶ of hC hS.isRightAlmostSplit_g.indecomposable) ↔
      Nonempty (of hA hS.isLeftAlmostSplit_f.indecomposable ⟶ of hX hI) := by
  have : IsLocalRing (End S.X₁) :=
    (QuiverRep.indecomposable_iff_isLocalRing_end hA).mp hS.isLeftAlmostSplit_f.indecomposable
  have : IsLocalRing (End S.X₃) :=
    (QuiverRep.indecomposable_iff_isLocalRing_end hC).mp hS.isRightAlmostSplit_g.indecomposable
  rw [nonempty_arrows_of_iff, nonempty_arrows_of_iff]
  exact hS.exists_isIrreducibleMorphism_into_iff_out_of hI.1

end TauCeti.irreducibleMorphismQuiver

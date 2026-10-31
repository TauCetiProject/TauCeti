/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.AlmostSplit.RadicalQuotient
public import TauCeti.CategoryTheory.Preadditive.Radical.IrreducibleMorphismQuiver.Basic

/-!
# Arrow counts from almost-split sequences

Let `0 ⟶ A ⟶ B ⟶ C ⟶ 0` be an almost-split sequence in a balanced linear category over a
division ring `k`, with `A` and `C` having local endomorphism rings. In the quiver of irreducible
morphisms `TauCeti.IrreducibleMorphismQuiver k P`, the number of arrows `[X] ⟶ [C]` is the
dimension of `(X ⟶ B)` modulo the radical, and the number of arrows `[A] ⟶ [X]` is the dimension
of `(B ⟶ X)` modulo the radical
(`CategoryTheory.ShortComplex.IsAlmostSplit.rightRadicalQuotientEquiv` and
`CategoryTheory.ShortComplex.IsAlmostSplit.leftRadicalQuotientEquiv`). So the two counts agree as
soon as these two dimensions agree; in a Krull–Schmidt setting this is
`TauCeti.finrank_quotient_jacobsonRadicalSubmodule_comm_of_iso_biproduct`.
This is the multiplicity relation of the mesh of an almost-split sequence, before identifying its
initial term with an Auslander–Reiten translate of its final term.

## Main results

* `TauCeti.IrreducibleMorphismQuiver.card_arrows_of_almostSplit_right` and
  `TauCeti.IrreducibleMorphismQuiver.card_arrows_of_almostSplit_left`: the arrows into the final
  term and out of the initial term, counted through the middle term.
* `TauCeti.IrreducibleMorphismQuiver.card_arrows_of_almostSplit_right_eq_left`: equally many
  arrows `[X] ⟶ [C]` and `[A] ⟶ [X]`.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*,
  Cambridge University Press (1995), V.5 and VII.1.
-/

public section

namespace TauCeti.IrreducibleMorphismQuiver

open CategoryTheory

universe u v w

variable {C : Type u} [Category.{v} C] [Preadditive C] [Limits.HasBinaryBiproducts C] [Balanced C]
  {k : Type w} [DivisionRing k] [Linear k C] {P : ObjectProperty C} {S : ShortComplex C}
  [IsLocalRing (End S.X₁)] [IsLocalRing (End S.X₃)]

/-- The arrows into the final term of an almost-split sequence are counted by morphisms into
its middle term modulo the radical. -/
theorem card_arrows_of_almostSplit_right (hS : S.IsAlmostSplit) (hC : P S.X₃) {X : C} (hX : P X)
    (hI : Indecomposable X) :
    Nat.card (of k hX hI ⟶ of k hC hS.isRightAlmostSplit_g.indecomposable) =
      Module.finrank k ((X ⟶ S.X₂) ⧸ jacobsonRadicalSubmodule k X S.X₂) := by
  rw [card_arrows_of]
  exact (hS.rightRadicalQuotientEquiv k X).finrank_eq.symm

/-- The arrows out of the initial term of an almost-split sequence are counted by morphisms out
of its middle term modulo the radical. -/
theorem card_arrows_of_almostSplit_left (hS : S.IsAlmostSplit) (hA : P S.X₁) {X : C} (hX : P X)
    (hI : Indecomposable X) :
    Nat.card (of k hA hS.isLeftAlmostSplit_f.indecomposable ⟶ of k hX hI) =
      Module.finrank k ((S.X₂ ⟶ X) ⧸ jacobsonRadicalSubmodule k S.X₂ X) := by
  rw [card_arrows_of]
  exact (hS.leftRadicalQuotientEquiv k X).finrank_eq.symm

/-- **The mesh multiplicities of an almost-split sequence** `0 ⟶ A ⟶ B ⟶ C ⟶ 0`: there are
equally many arrows `[X] ⟶ [C]` and `[A] ⟶ [X]` whenever morphisms `X ⟶ B` and `B ⟶ X` have
the same dimension modulo the radical. -/
theorem card_arrows_of_almostSplit_right_eq_left (hS : S.IsAlmostSplit) (hA : P S.X₁)
    (hC : P S.X₃) {X : C} (hX : P X) (hI : Indecomposable X)
    (hcomm : Module.finrank k ((X ⟶ S.X₂) ⧸ jacobsonRadicalSubmodule k X S.X₂) =
      Module.finrank k ((S.X₂ ⟶ X) ⧸ jacobsonRadicalSubmodule k S.X₂ X)) :
    Nat.card (of k hX hI ⟶ of k hC hS.isRightAlmostSplit_g.indecomposable) =
      Nat.card (of k hA hS.isLeftAlmostSplit_f.indecomposable ⟶ of k hX hI) := by
  rw [card_arrows_of_almostSplit_right hS hC hX hI, card_arrows_of_almostSplit_left hS hA hX hI,
    hcomm]

end TauCeti.IrreducibleMorphismQuiver

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Preadditive.Radical.IrreducibleMorphismQuiver.AlmostSplit
public import TauCeti.RepresentationTheory.Quiver.AuslanderReiten.Quiver
public import TauCeti.RepresentationTheory.Quiver.Representation.Radical

/-!
# Arrow counts from almost-split sequences of quiver representations

In an almost-split sequence `0 ⟶ A ⟶ B ⟶ C ⟶ 0` of finite-dimensional representations of a
finite quiver, there are equally many arrows `[X] ⟶ [C]` and `[A] ⟶ [X]` in the quiver of
irreducible morphisms, for every finite-dimensional indecomposable `X`
(`TauCeti.QuiverRep.card_arrows_of_almostSplit_right_eq_left`). This is the multiplicity relation
for the mesh of an almost-split sequence, before identifying its left endpoint with the
Auslander–Reiten translate.

It specializes the general count
`TauCeti.IrreducibleMorphismQuiver.card_arrows_of_almostSplit_right_eq_left`: finite-dimensional
indecomposable representations have local endomorphism rings, and the Krull–Schmidt decomposition
of the middle term makes morphisms `X ⟶ B` and `B ⟶ X` equidimensional modulo the radical
(`TauCeti.QuiverRep.finrank_quotient_jacobsonRadicalSubmodule_comm`).

The counts are dimensions over the ground field, matching the basis-indexed quiver
`IrreducibleMorphismQuiver`. The formulas hold over any field, for any finite vertex set;
neither acyclicity nor finiteness of the arrow set is required.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*,
  Cambridge University Press (1995), V.5 and VII.1.
-/

public section

namespace TauCeti.QuiverRep

open CategoryTheory IrreducibleMorphismQuiver

universe u v w t

variable {k : Type u} {Q : Type v} [Field k] [Quiver.{w} Q] [Finite Q]
  {S : ShortComplex (QuiverRep.{u, v, w, t} k Q)}

/-- In an almost-split sequence `0 → A → B → C → 0`, there are equally many arrows `X → C`
and `A → X` for every finite-dimensional indecomposable `X`. -/
theorem card_arrows_of_almostSplit_right_eq_left (hS : S.IsAlmostSplit)
    (hA : IsFinDim k Q S.X₁) (hC : IsFinDim k Q S.X₃)
    {X : QuiverRep.{u, v, w, t} k Q} (hX : IsFinDim k Q X) (hI : Indecomposable X) :
    Nat.card (of k hX hI ⟶ of k hC hS.isRightAlmostSplit_g.indecomposable) =
      Nat.card (of k hA hS.isLeftAlmostSplit_f.indecomposable ⟶ of k hX hI) := by
  have : IsLocalRing (End S.X₁) :=
    (QuiverRep.indecomposable_iff_isLocalRing_end hA).mp hS.isLeftAlmostSplit_f.indecomposable
  have : IsLocalRing (End S.X₃) :=
    (QuiverRep.indecomposable_iff_isLocalRing_end hC).mp hS.isRightAlmostSplit_g.indecomposable
  have hB : IsFinDim k Q S.X₂ :=
    (isExtensionClosed_pointwiseFiniteDimensionalQuiverRepresentations k Q).prop_X₂
      ((ExactStructure.abelian_conflation _).mpr hS.shortExact) hA hC
  exact IrreducibleMorphismQuiver.card_arrows_of_almostSplit_right_eq_left hS hA hC hX hI
    (QuiverRep.finrank_quotient_jacobsonRadicalSubmodule_comm hX hI hB)

end TauCeti.QuiverRep

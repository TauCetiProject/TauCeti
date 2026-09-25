/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.RepresentationTheory.Homological.GroupHomology.LongExactSequence
public import TauCeti.RepresentationTheory.Homological.GroupHomology.Transfer.Basic

/-!
# Transfer commutes with the connecting map

Let `S` be a finite-index subgroup of a group `G` and `X` a short exact sequence of
`G`-representations. Restricting `X` to `S` keeps it short exact, and the transfer
`Hₙ(G, M) ⟶ Hₙ(S, Res_S M)` commutes with the connecting maps of the two long exact sequences:

`Hᵢ(G, X₃) ⟶ Hⱼ(G, X₁)`
`    ↓              ↓`
`Hᵢ(S, X₃) ⟶ Hⱼ(S, X₁)`

with `j + 1 = i`. This is what lets a statement about the transfer be moved up or down in degree
by dimension shifting.

## Main results

* `TauCeti.groupHomology.δ_comp_indIso_inv`: the inverse of Shapiro's isomorphism commutes with
  the connecting maps.
* `TauCeti.groupHomology.δ_comp_transfer`: the transfer commutes with the connecting maps.
-/

public section

universe u

open CategoryTheory Rep

namespace TauCeti.groupHomology

open _root_.groupHomology

variable {R G : Type u} [CommRing R] [Group G] (S : Subgroup G)

/-- **Shapiro's isomorphism commutes with the connecting maps.** For a short exact sequence `Y` of
`S`-representations, the inverse of `Hₙ(G, Ind_S^G Y) ≅ Hₙ(S, Y)` intertwines the connecting map
of `Y` with the connecting map of the induced sequence `Ind_S^G Y`. Exactness of `Ind_S^G Y` is a
hypothesis because Mathlib provides left exactness of induction only for finite-index `S`, where
`hIY` is `hY.map_of_exact _`. -/
@[reassoc]
theorem δ_comp_indIso_inv [DecidableEq G] {Y : ShortComplex (Rep.{u} R S)} (hY : Y.ShortExact)
    (hIY : (Y.map (indFunctor R S.subtype)).ShortExact) (i j : ℕ) (hij : j + 1 = i) :
    δ hY i j hij ≫ (indIso S Y.X₁ j).inv = (indIso S Y.X₃ i).inv ≫ δ hIY i j hij := by
  rw [indIso_inv, indIso_inv]
  -- The unit of induction–restriction applied to `Y` is a morphism `Y ⟶ Res_S Ind_S^G Y`. Pinning
  -- the free universe of `indResAdjunction` avoids seconds of universe unification.
  exact δ_naturality _ hY hIY (Y.mapNatTrans (indResAdjunction.{u} R S.subtype).unit) i j hij

/-- **The transfer commutes with the connecting maps.** For a finite-index subgroup `S ≤ G` and a
short exact sequence `X` of `G`-representations, the transfer intertwines the connecting map of
`X` with the connecting map of its restriction `Res_S X` to `S`. -/
@[reassoc]
theorem δ_comp_transfer [S.FiniteIndex] {X : ShortComplex (Rep.{u} R G)} (hX : X.ShortExact)
    (i j : ℕ) (hij : j + 1 = i) :
    δ hX i j hij ≫ transfer X.X₁ S j =
      transfer X.X₃ S i ≫ δ ((shortExact_res S.subtype).2 hX) i j hij := by
  classical
  have hIR := ((shortExact_res S.subtype).2 hX).map_of_exact (indFunctor R S.subtype)
  -- Cancel Shapiro's isomorphism, turning the transfer into the map induced by the unit.
  rw [← cancel_mono (indIso S _ j).inv, Category.assoc, Category.assoc, transfer_comp_indIso_inv]
  -- The objects appear both as `groupHomology _ n` and as `(functor R G n).obj _`, so the two
  -- squares are pasted as terms rather than by rewriting.
  exact
    -- The square of the unit `X ⟶ Ind Res X`: naturality of `δ` for a fixed group. Pinning the
    -- free universe of `resIndAdjunction` avoids seconds of universe unification.
    (δ_naturality (MonoidHom.id G) hX hIR
      (X.mapNatTrans (resIndAdjunction.{u, u, u} R S).unit) i j hij).trans <|
    -- The square of Shapiro's isomorphism.
    (transfer_comp_indIso_inv_assoc X.X₃ S i _).symm.trans <|
    congrArg (_ ≫ ·) (δ_comp_indIso_inv S _ hIR i j hij).symm

end TauCeti.groupHomology

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.FreeAction
public import TauCeti.AlgebraicTopology.Cellular.Resolution
public import TauCeti.AlgebraicTopology.EilenbergMacLane.Contractible

/-!
# The cellular resolution of an aspherical space

Let `p : E → B` be a quotient covering map for an action of a group `G` on a simply connected
space `E` over an aspherical base `(B, b)`.

* When `B` is a Hausdorff CW complex, the lift `p ⁻¹' univ` of its CW structure to `E` is
  contractible (`IsCoveringMap.contractibleSpace_preimage_univ_of_isAspherical`), and its cellular
  chains form a free resolution of `Rep.trivial k G k` (`TauCeti.cellularResolutionOfIsAspherical`).
* More generally, for *any* Hausdorff CW structure on `E` whose open cells are carried onto open
  cells of the same dimension by `G` and on whose cells `G` acts freely (the lifted CW structure
  always qualifies by `TauCeti.exists_smul_openCell_cellPreimage` and
  `TauCeti.eq_one_of_smul_openCell_cellPreimage`), `E` is contractible by Whitehead's theorem
  (`IsCoveringMap.contractibleSpace_univ_of_isAspherical`), and its augmented cellular chain
  complex forms a free resolution of `Rep.trivial k G k`
  (`TauCeti.cellActionResolutionOfIsAspherical`), free in degree `n` on the `G`-orbits of
  `n`-cells of `E` and, when `B` lies in the universe of `E`, on the `n`-cells of the induced CW
  structure on `B` (`TauCeti.quotientCellularChainRepIsoFree`).

In both cases `G` acts on the left on `E` by deck transformations through the given action of
`IsQuotientCoveringMap p G`: `IsQuotientCoveringMap.deckMulEquiv` (in
`TauCeti.AlgebraicTopology.UniversalCover.Deck.Quotient.ActingGroup`) identifies `G` with the group
of deck transformations of `p`, and Mathlib's `IsQuotientCoveringMap.fundamentalGroupEquiv`
identifies `G` with the opposite `(FundamentalGroup B b)ᵐᵒᵖ` of the fundamental group of `B`. On the
based-path universal cover `TauCeti.UniversalCover b`, `TauCeti.UniversalCover.smul_mk` makes a loop
class `γ` act on the left by prepending `γ⁻¹`, giving a left action of `FundamentalGroup B b`
itself.

## Main definitions

* `TauCeti.cellularResolutionOfIsAspherical`: the projective resolution of the trivial
  representation of `G` by the lifted cellular chains of a simply connected quotient covering of
  an aspherical CW complex.
* `TauCeti.cellActionResolutionOfIsAspherical`: the projective resolution of the trivial
  representation of `G` by the cellular chains of any free cellular `G`-CW structure on a simply
  connected quotient covering of an aspherical space.

## References

* K. S. Brown, *Cohomology of Groups*, GTM 87, Springer, 1982, Section I.4 and Section II.4.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 1.B.
-/

public section

noncomputable section

open CategoryTheory Set Topology Topology.RelCWComplex
open scoped Pointwise

universe w

namespace TauCeti

section Lifted

variable {E B : Type w} [TopologicalSpace E] [TopologicalSpace B] {p : E → B} {G : Type w}
  [Group G] [MulAction G E] (hG : IsQuotientCoveringMap p G) [T2Space B]
  [CWComplex (univ : Set B)] [SimplyConnectedSpace E] {b : B}
  (hb : IsAspherical B b) (k : Type w) [CommRing k]

/-- **The cellular resolution of an aspherical CW complex**: if `p : E → B` is a quotient covering
map for an action of `G` on a simply connected space `E`, and `B` is an aspherical Hausdorff CW
complex, then the cellular chains of the lift `p ⁻¹' univ` of the CW structure on `B` form a
projective resolution of the trivial representation of `G` over `k`. In degree `n` they are free
over `k[G]` with one generator for each `n`-cell of `B` (`TauCeti.cellularChainRepIsoFree`). -/
def cellularResolutionOfIsAspherical : ProjectiveResolution (Rep.trivial k G k) :=
  haveI := hG.isCoveringMap.contractibleSpace_preimage_univ_of_isAspherical hb
  cellularResolution univ hG k

/-- The complex of `TauCeti.cellularResolutionOfIsAspherical` is the lifted cellular chain
complex. -/
@[simp]
lemma cellularResolutionOfIsAspherical_complex :
    (cellularResolutionOfIsAspherical hG hb k).complex = cellularChainComplexRep univ hG k :=
  haveI := hG.isCoveringMap.contractibleSpace_preimage_univ_of_isAspherical hb
  cellularResolution_complex ..

-- As for `TauCeti.cellularResolution_π`, the public statement cannot unfold the unexposed body of
-- `TauCeti.cellularResolutionOfIsAspherical`, so it transports along
-- `cellularResolutionOfIsAspherical_complex`.
/-- The augmentation of `TauCeti.cellularResolutionOfIsAspherical` is that of the lifted cellular
chain complex. -/
@[simp]
lemma cellularResolutionOfIsAspherical_π :
    (cellularResolutionOfIsAspherical hG hb k).π =
      eqToHom (cellularResolutionOfIsAspherical_complex hG hb k) ≫
        cellularChainComplexRepAugmentation univ hG k :=
  haveI := hG.isCoveringMap.contractibleSpace_preimage_univ_of_isAspherical hb
  cellularResolution_π ..

end Lifted

section FreeCellAction

variable {E : Type w} {B : Type*} [TopologicalSpace E] [TopologicalSpace B] {p : E → B}
  {G : Type w} [Group G] [MulAction G E] (hG : IsQuotientCoveringMap p G) [T2Space E]
  [CWComplex (univ : Set E)]
  (hcell : ∀ (g : G) (n : ℕ) (i : cell (univ : Set E) n),
    ∃ j : cell (univ : Set E) n, g • openCell n i = openCell n j)
  (hfree : ∀ (g : G) (n : ℕ) (i : cell (univ : Set E) n),
    g • openCell n i = openCell n i → g = 1)
  [SimplyConnectedSpace E] {b : B} (hb : IsAspherical B b) (k : Type w) [CommRing k]

/-- **The cellular resolution from any free cellular CW cover of an aspherical space**: if
`p : E → B` is a quotient covering map for a `G`-action on a simply connected Hausdorff CW complex
`E` over an aspherical base `(B, b)`, and `G` acts freely on the cells of `E` carrying open cells
onto open cells of the same dimension, then the augmented cellular chain complex of `E` is a
projective resolution of `Rep.trivial k G k`. In degree `n` it is free over `k[G]` on the
`G`-orbits of `n`-cells of `E` (`TauCeti.cellActionChainRepIsoFreeOrbitQuotient`) and, when
`B : Type w`, on the `n`-cells of the orbit-space CW structure on `B`
(`TauCeti.quotientCellularChainRepIsoFree`). -/
def cellActionResolutionOfIsAspherical : ProjectiveResolution (Rep.trivial k G k) :=
  haveI := hG.toContinuousConstSMul
  haveI := hG.isCoveringMap.contractibleSpace_univ_of_isAspherical hb
  cellActionResolution (univ : Set E) hcell hfree k

/-- The complex of `TauCeti.cellActionResolutionOfIsAspherical` is the equivariant cellular chain
complex of `E`. -/
@[simp]
lemma cellActionResolutionOfIsAspherical_complex :
    haveI := hG.toContinuousConstSMul
    (cellActionResolutionOfIsAspherical hG hcell hfree hb k).complex =
      cellActionChainComplexRep (univ : Set E) hcell k :=
  haveI := hG.toContinuousConstSMul
  haveI := hG.isCoveringMap.contractibleSpace_univ_of_isAspherical hb
  cellActionResolution_complex ..

-- As for `TauCeti.cellActionResolution_π`, the public statement transports along
-- `cellActionResolutionOfIsAspherical_complex`.
/-- The augmentation of `TauCeti.cellActionResolutionOfIsAspherical` is that of the equivariant
cellular chain complex of `E`. -/
@[simp]
lemma cellActionResolutionOfIsAspherical_π :
    haveI := hG.toContinuousConstSMul
    (cellActionResolutionOfIsAspherical hG hcell hfree hb k).π =
      eqToHom (cellActionResolutionOfIsAspherical_complex hG hcell hfree hb k) ≫
        cellActionChainComplexRepAugmentation (univ : Set E) hcell k :=
  haveI := hG.toContinuousConstSMul
  haveI := hG.isCoveringMap.contractibleSpace_univ_of_isAspherical hb
  cellActionResolution_π ..

end FreeCellAction

end TauCeti

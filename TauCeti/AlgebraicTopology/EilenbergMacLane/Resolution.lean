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
# Cellular resolutions from simply connected covers of aspherical spaces

Let `p : E → B` be a quotient covering map for an action of a group `G` on a simply connected space
`E`, with `B` aspherical at a basepoint `b = p e`, so that `E` is a universal cover of `B` and `G`
acts on `E` by deck transformations (`IsQuotientCoveringMap.fundamentalGroupEquiv` identifies
`π₁(B, b)` with `Gᵐᵒᵖ`). Whenever `E` has CW type, it is contractible by Whitehead's theorem
(`IsCoveringMap.contractibleSpace_of_cwType_of_isAspherical`).

Two sources of `G`-equivariant CW structure on `E` yield projective resolutions of the trivial
representation `Rep.trivial k G k`:

1. **Lifted CW structure from the base** (`TauCeti.cellularResolutionOfIsAspherical`): if `B` is a
   Hausdorff CW complex, its lifted CW structure `TauCeti.cwComplexPreimage` on `p ⁻¹' univ` has
   characteristic maps strictly preserved by `G` (`TauCeti.smul_openCell_cellPreimage` and
   `TauCeti.eq_one_of_smul_openCell_cellPreimage`), and its cellular chains form a projective
   resolution free over `k[G]` on the cells of `B` (`TauCeti.cellularChainRepIsoFree`).
2. **Free cellular action on the total space**
   (`TauCeti.freeActionCellularResolutionOfIsAspherical`): if `E` itself is a Hausdorff CW complex
   on which `G` acts freely by open-cell-permuting translations (so `B` inherits the quotient CW
   structure `IsQuotientCoveringMap.cwComplexQuotient`), its cellular chains form a projective
   resolution (`TauCeti.cellActionResolution`) free over `k[G]` on the cell orbits
   (`TauCeti.cellActionChainRepIsoFreeOfOrbits`) and on chosen lifts of the cells of `B`
   (`TauCeti.quotientCellularChainRepIsoFree`), without requiring translations to preserve chosen
   characteristic maps strictly (compare `TauCeti.universalGSpaceCellularResolution` for the
   ordered simplicial CW structure on Milnor's join).

In both cases the left `G`-action on chains is induced directly by the given left action of `G` on
`E`; no inversion through `Gᵐᵒᵖ` intervenes.

## Main definitions

* `TauCeti.cellularResolutionOfIsAspherical`: projective resolution of `Rep.trivial k G k` from the
  lifted CW structure on a simply connected quotient covering of an aspherical CW complex `B`.
* `TauCeti.freeActionCellularResolutionOfIsAspherical`: projective resolution of
  `Rep.trivial k G k` from a free cellular `G`-CW structure on the total space `E` of a simply
  connected quotient covering of an aspherical space `B`.

## References

* K. S. Brown, *Cohomology of Groups*, GTM 87, Springer, 1982, Section I.4 and Section II.4.
* T. tom Dieck, *Transformation Groups*, de Gruyter, 1987, Section II.1.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 1.B.
-/

public section

noncomputable section

open CategoryTheory Set Topology Topology.RelCWComplex
open scoped Pointwise

universe w

namespace TauCeti

section BaseCW

variable {E B : Type w} [TopologicalSpace E] [TopologicalSpace B] {p : E → B} {G : Type w}
  [Group G] [MulAction G E] (hG : IsQuotientCoveringMap p G) [T2Space B]
  [CWComplex (univ : Set B)] [SimplyConnectedSpace E] {e : E} {b : B} (he : p e = b)
  (hb : IsAspherical B b) (k : Type w) [CommRing k]

/-- **The cellular resolution of an aspherical CW complex**: if `p : E → B` is a quotient covering
map for an action of `G` on a simply connected space `E`, and `B` is an aspherical Hausdorff CW
complex, then the cellular chains of the lift `p ⁻¹' univ` of the CW structure on `B` form a
projective resolution of the trivial representation of `G` over `k`. In degree `n` they are free
over `k[G]` with one generator for each `n`-cell of `B` (`TauCeti.cellularChainRepIsoFree`). -/
def cellularResolutionOfIsAspherical : ProjectiveResolution (Rep.trivial k G k) :=
  haveI := hG.isCoveringMap.contractibleSpace_preimage_univ_of_isAspherical he hb
  cellularResolution univ hG k

/-- The complex of `TauCeti.cellularResolutionOfIsAspherical` is the lifted cellular chain
complex. -/
@[simp]
lemma cellularResolutionOfIsAspherical_complex :
    (cellularResolutionOfIsAspherical hG he hb k).complex = cellularChainComplexRep univ hG k :=
  haveI := hG.isCoveringMap.contractibleSpace_preimage_univ_of_isAspherical he hb
  cellularResolution_complex ..

-- As for `TauCeti.cellularResolution_π`, the public statement cannot unfold the unexposed body of
-- `TauCeti.cellularResolutionOfIsAspherical`, so it transports along
-- `cellularResolutionOfIsAspherical_complex`.
/-- The augmentation of `TauCeti.cellularResolutionOfIsAspherical` is that of the lifted cellular
chain complex. -/
@[simp]
lemma cellularResolutionOfIsAspherical_π :
    (cellularResolutionOfIsAspherical hG he hb k).π =
      eqToHom (cellularResolutionOfIsAspherical_complex hG he hb k) ≫
        cellularChainComplexRepAugmentation univ hG k :=
  haveI := hG.isCoveringMap.contractibleSpace_preimage_univ_of_isAspherical he hb
  cellularResolution_π ..

end BaseCW

section TotalSpaceCW

variable {E : Type w} {B : Type*} [TopologicalSpace E] [T2Space E] [CWComplex (univ : Set E)]
  [TopologicalSpace B] {p : E → B} {G : Type w} [Group G] [MulAction G E]
  (hG : IsQuotientCoveringMap p G)
  (hcell : ∀ (g : G) (n : ℕ) (i : cell (univ : Set E) n),
    ∃ j : cell (univ : Set E) n, g • openCell n i = openCell n j)
  (hfree : ∀ (g : G) (n : ℕ) (i : cell (univ : Set E) n),
    g • openCell n i = openCell n i → g = 1)
  [SimplyConnectedSpace E] {e : E} {b : B} (he : p e = b) (hb : IsAspherical B b)
  (k : Type w) [CommRing k]

/-- **The cellular resolution from a free cellular covering of an aspherical space**: if `p : E → B`
is a quotient covering map for a free open-cell-permuting action of `G` on a simply connected
Hausdorff CW complex `E`, and `B` is aspherical at `b = p e`, then the cellular chains of
`univ : Set E` form a projective resolution of `Rep.trivial k G k`. In degree `n` they are free over
`k[G]` on the `G`-orbits of `n`-cells of `E` (`TauCeti.cellActionChainRepIsoFreeOfOrbits`), and on
chosen lifts of the `n`-cells of the orbit CW complex `B`
(`TauCeti.quotientCellularChainRepIsoFree`). -/
def freeActionCellularResolutionOfIsAspherical : ProjectiveResolution (Rep.trivial k G k) :=
  haveI := hG.toContinuousConstSMul
  haveI := hG.isCoveringMap.contractibleSpace_univ_of_isAspherical he hb
  cellActionResolution (univ : Set E) hcell hfree k

/-- The underlying chain complex of `TauCeti.freeActionCellularResolutionOfIsAspherical` is
`TauCeti.cellActionChainComplexRep`. -/
@[simp]
theorem freeActionCellularResolutionOfIsAspherical_complex :
    haveI := hG.toContinuousConstSMul
    (freeActionCellularResolutionOfIsAspherical hG hcell hfree he hb k).complex =
      cellActionChainComplexRep (univ : Set E) hcell k :=
  haveI := hG.toContinuousConstSMul
  haveI := hG.isCoveringMap.contractibleSpace_univ_of_isAspherical he hb
  cellActionResolution_complex ..

-- Under `module`, the public statement cannot unfold the unexposed body of
-- `TauCeti.freeActionCellularResolutionOfIsAspherical`, so it transports along
-- `freeActionCellularResolutionOfIsAspherical_complex`.
/-- The augmentation of `TauCeti.freeActionCellularResolutionOfIsAspherical` is
`TauCeti.cellActionChainComplexRepAugmentation`. -/
@[simp]
theorem freeActionCellularResolutionOfIsAspherical_π :
    haveI := hG.toContinuousConstSMul
    (freeActionCellularResolutionOfIsAspherical hG hcell hfree he hb k).π =
      eqToHom (freeActionCellularResolutionOfIsAspherical_complex hG hcell hfree he hb k) ≫
        cellActionChainComplexRepAugmentation (univ : Set E) hcell k :=
  haveI := hG.toContinuousConstSMul
  haveI := hG.isCoveringMap.contractibleSpace_univ_of_isAspherical he hb
  cellActionResolution_π ..

end TotalSpaceCW

end TauCeti

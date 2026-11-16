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
# Cellular resolutions of aspherical spaces

Let `p : E → B` be a quotient covering map for an action of a group `G` on a simply connected space
`E`, where `B` is aspherical, so that `E` is a universal cover of `B` and `G` is its group of deck
transformations (`IsQuotientCoveringMap.deckTransformationEquiv`; Mathlib's
`IsQuotientCoveringMap.fundamentalGroupEquiv` identifies `π₁(B, b)` with `Gᵐᵒᵖ`).

This file packages the resulting free cellular resolutions of the trivial representation
`Rep.trivial k G k` in two situations:

* **Lifted CW structure from the base** (`TauCeti.cellularResolutionOfIsAspherical`): when `B` is a
  Hausdorff CW complex, the lift `p ⁻¹' univ` of the CW structure on `B` is contractible
  (`IsCoveringMap.contractibleSpace_preimage_univ_of_isAspherical`), and its cellular chains form
  a projective resolution of `Rep.trivial k G k` (`TauCeti.cellularResolution`), free in degree `n`
  on one chosen lift of each `n`-cell of `B` (`TauCeti.cellularChainRepIsoFree`).
* **Arbitrary free cellular `G`-CW structure on the universal cover**
  (`TauCeti.cellActionResolutionOfIsAspherical`): when `E` itself carries a Hausdorff CW structure
  for which `G` permutes the open `n`-cells freely (without requiring translation to carry
  characteristic maps onto characteristic maps), `E` has CW type and is therefore contractible
  (`IsCoveringMap.contractibleSpace_univ_of_isAspherical_of_cwType`), and its cellular chains form
  a projective resolution of `Rep.trivial k G k` (`TauCeti.cellActionResolution`), free in degree
  `n` on any chosen lifts of the `n`-cells of the orbit-space CW structure on `B`
  (`TauCeti.cellActionRepIsoFreeOfQuotientCovering`).

## Main definitions

* `TauCeti.cellularResolutionOfIsAspherical`: the projective resolution of `Rep.trivial k G k` by
  the lifted cellular chains of a simply connected quotient covering of an aspherical CW complex.
* `TauCeti.cellActionResolutionOfIsAspherical`: the projective resolution of `Rep.trivial k G k`
  by the cellular chains of a simply connected universal cover of an aspherical space equipped with
  any free cellular `G`-CW structure.

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

end Lifted

section FreeAction

variable {E B : Type w} [TopologicalSpace E] [TopologicalSpace B] {p : E → B} {G : Type w}
  [Group G] [MulAction G E] (hG : IsQuotientCoveringMap p G) [T2Space E]
  [CWComplex (univ : Set E)] [SimplyConnectedSpace E] {e : E} {b : B} (he : p e = b)
  (hb : IsAspherical B b)
  (hcell : ∀ (g : G) (n : ℕ) (i : cell (univ : Set E) n),
    ∃ j : cell (univ : Set E) n, g • openCell n i = openCell n j)
  (hfree : ∀ (g : G) (n : ℕ) (i : cell (univ : Set E) n),
    g • openCell n i = openCell n i → g = 1)
  (k : Type w) [CommRing k]

/-- **The cellular resolution of an aspherical space from a free cellular `G`-CW structure on its
universal cover.** If `p : E → B` is a quotient covering map for a group `G` acting on a simply
connected Hausdorff CW complex `E`, `B` is aspherical at `b = p e`, and `G` permutes the open
`n`-cells of `E` freely, then `E` is contractible
(`IsCoveringMap.contractibleSpace_univ_of_isAspherical_of_cwType`), so the cellular chain complex
of `E` forms a projective resolution of `Rep.trivial k G k`. In degree `n` it is free over `k[G]`
with basis any chosen lifts of the `n`-cells of the orbit-space CW structure on `B`
(`TauCeti.cellActionRepIsoFreeOfQuotientCovering`). -/
def cellActionResolutionOfIsAspherical : ProjectiveResolution (Rep.trivial k G k) :=
  haveI := hG.toContinuousConstSMul
  haveI := hG.isCoveringMap.contractibleSpace_univ_of_isAspherical_of_cwType he hb
  cellActionResolution (univ : Set E) hcell hfree k

/-- The complex of `TauCeti.cellActionResolutionOfIsAspherical` is the equivariant cellular chain
complex of `E`. -/
@[simp]
theorem cellActionResolutionOfIsAspherical_complex :
    haveI := hG.toContinuousConstSMul
    (cellActionResolutionOfIsAspherical hG he hb hcell hfree k).complex =
      cellActionComplex (univ : Set E) hcell k :=
  haveI := hG.toContinuousConstSMul
  haveI := hG.isCoveringMap.contractibleSpace_univ_of_isAspherical_of_cwType he hb
  cellActionResolution_complex ..

-- As for `TauCeti.cellActionResolution_π`, the public statement cannot unfold the unexposed body
-- of `TauCeti.cellActionResolutionOfIsAspherical`, so it transports along
-- `cellActionResolutionOfIsAspherical_complex`.
/-- The augmentation of `TauCeti.cellActionResolutionOfIsAspherical` is that of the equivariant
cellular chain complex of `E`. -/
@[simp]
theorem cellActionResolutionOfIsAspherical_π :
    haveI := hG.toContinuousConstSMul
    (cellActionResolutionOfIsAspherical hG he hb hcell hfree k).π =
      eqToHom (cellActionResolutionOfIsAspherical_complex hG he hb hcell hfree k) ≫
        cellActionComplexAugmentation (univ : Set E) hcell k :=
  haveI := hG.toContinuousConstSMul
  haveI := hG.isCoveringMap.contractibleSpace_univ_of_isAspherical_of_cwType he hb
  cellActionResolution_π ..

end FreeAction

end TauCeti

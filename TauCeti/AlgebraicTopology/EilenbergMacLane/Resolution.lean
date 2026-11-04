/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.Resolution
public import TauCeti.AlgebraicTopology.EilenbergMacLane.Contractible

/-!
# The cellular resolution of an aspherical CW complex

Let `B` be an aspherical Hausdorff CW complex, and let `p : E → B` be a quotient covering map for
an action of a group `G` on a simply connected space `E`, so that `E` is a universal cover of `B`
and `G` its group of deck transformations. Then the lift `p ⁻¹' univ` of the CW structure on `B`
is contractible (`IsCoveringMap.contractibleSpace_preimage_univ_of_isAspherical`), so its cellular
chains, on which `G` acts by translating the lifted cells, form a free resolution of the trivial
representation of `G` (`TauCeti.cellularResolution`).

When `B` is a `K(G, 1)`, this is the resolution of the trivial `G`-module computing the group
homology and cohomology of `G` from the cells of `B`: in degree `n` it is free over `k[G]` with one
generator for each `n`-cell of `B`.

## Main definitions

* `TauCeti.cellularResolutionOfIsAspherical`: the projective resolution of the trivial
  representation of `G` by the lifted cellular chains of a simply connected quotient covering of
  an aspherical CW complex.

## References

* K. S. Brown, *Cohomology of Groups*, GTM 87, Springer, 1982, Section I.4 and Section II.4.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 1.B.
-/

public section

noncomputable section

open CategoryTheory Set Topology

universe w

namespace TauCeti

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

end TauCeti

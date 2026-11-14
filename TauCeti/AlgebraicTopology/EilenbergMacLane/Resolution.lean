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
representation of `G` (`TauCeti.cellularResolution`), and passing to `G`-coinvariants identifies the
cellular homology of `B` with `groupHomology (Rep.trivial k G k) n`
(`TauCeti.cellularHomologyIsoGroupHomologyOfIsAspherical`).

Conversely, if `E` itself is a simply connected Hausdorff CW complex carrying a free cellular
`G`-action with quotient covering map `p : E → B` onto an aspherical space `B`, then `E` is
contractible by Whitehead's theorem (`IsCoveringMap.contractibleSpace_of_cwType_of_isAspherical`),
its cellular chains form a projective resolution `TauCeti.freeCellularResolutionOfIsAspherical` of
`Rep.trivial k G k`, and equipping `B` with the orbit CW structure
`IsQuotientCoveringMap.cwComplexQuotient` identifies the cellular homology of `B` with
`groupHomology (Rep.trivial k G k) n`
(`IsQuotientCoveringMap.cellularHomologyIsoGroupHomologyOfIsAspherical`).

## Main definitions

* `TauCeti.cellularResolutionOfIsAspherical`: the projective resolution of `Rep.trivial k G k` by
  the lifted cellular chains of a simply connected quotient covering of an aspherical CW complex.
* `TauCeti.cellularHomologyIsoGroupHomologyOfIsAspherical`: the resulting isomorphism between the
  cellular homology of `B` and `groupHomology (Rep.trivial k G k) n`.
* `TauCeti.freeCellularResolutionOfIsAspherical`: the projective resolution of `Rep.trivial k G k`
  by the cellular chains of a simply connected free `G`-CW cover of an aspherical space.
* `IsQuotientCoveringMap.cellularHomologyIsoGroupHomologyOfIsAspherical`: the resulting isomorphism
  between the cellular homology of the orbit CW complex `B` and
  `groupHomology (Rep.trivial k G k) n`.

## References

* K. S. Brown, *Cohomology of Groups*, GTM 87, Springer, 1982, Section I.4 and Section II.4.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 1.B.
-/

public section

noncomputable section

open CategoryTheory Set Topology Topology.RelCWComplex

universe w

namespace TauCeti

section Preimage

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

/-- **The cellular homology of an aspherical Hausdorff CW complex is the group homology of its deck
transformation group.** -/
def cellularHomologyIsoGroupHomologyOfIsAspherical (n : ℕ) :
    (cellularChainComplex (univ : Set B) (ModuleCat.of k k)).homology n ≅
      groupHomology (Rep.trivial k G k) n :=
  haveI := hG.isCoveringMap.contractibleSpace_preimage_univ_of_isAspherical he hb
  cellularHomologyIsoGroupHomology univ hG k n

end Preimage

section FreeAction

open scoped Pointwise

variable {E B : Type w} [TopologicalSpace E] [T2Space E] [TopologicalSpace B]
  [CWComplex (univ : Set E)] [SimplyConnectedSpace E]
  {p : E → B} {G : Type w} [Group G] [MulAction G E] (hG : IsQuotientCoveringMap p G)
  (hcell : ∀ (g : G) (n : ℕ) (i : cell (univ : Set E) n),
    ∃ j : cell (univ : Set E) n, g • openCell n i = openCell n j)
  (hfree : ∀ (g : G) (n : ℕ) (i : cell (univ : Set E) n),
    g • openCell n i = openCell n i → g = 1)
  {e : E} {b : B} (he : p e = b) (hb : IsAspherical B b) (k : Type w) [CommRing k]

include hG hcell hfree he hb

/-- **Projective resolution of the trivial representation from a simply connected free `G`-CW cover
of an aspherical space.** Here `B` need not carry a pre-existing CW structure: `E` has CW type via
its own CW structure, hence is contractible by Whitehead's theorem. -/
def freeCellularResolutionOfIsAspherical : ProjectiveResolution (Rep.trivial k G k) :=
  haveI := hG.toContinuousConstSMul
  haveI := hG.isCoveringMap.contractibleSpace_univ_of_cwType_of_isAspherical he hb
  freeCellularResolution (univ : Set E) hcell hfree k

/-- The underlying chain complex of `TauCeti.freeCellularResolutionOfIsAspherical` is
`TauCeti.cellularSMulComplex`. -/
@[simp]
lemma freeCellularResolutionOfIsAspherical_complex :
    haveI := hG.toContinuousConstSMul
    (freeCellularResolutionOfIsAspherical hG hcell hfree he hb k).complex =
      cellularSMulComplex (univ : Set E) hcell k :=
  haveI := hG.toContinuousConstSMul
  haveI := hG.isCoveringMap.contractibleSpace_univ_of_cwType_of_isAspherical he hb
  freeCellularResolution_complex ..

/-- The augmentation of `TauCeti.freeCellularResolutionOfIsAspherical` is
`TauCeti.cellularSMulComplexAugmentation`. -/
@[simp]
lemma freeCellularResolutionOfIsAspherical_π :
    haveI := hG.toContinuousConstSMul
    (freeCellularResolutionOfIsAspherical hG hcell hfree he hb k).π =
      eqToHom (freeCellularResolutionOfIsAspherical_complex hG hcell hfree he hb k) ≫
        cellularSMulComplexAugmentation (univ : Set E) hcell k :=
  haveI := hG.toContinuousConstSMul
  haveI := hG.isCoveringMap.contractibleSpace_univ_of_cwType_of_isAspherical he hb
  freeCellularResolution_π ..

/-- **The cellular homology of the orbit CW complex of a simply connected free `G`-CW cover over an
aspherical base is group homology.** Equipping `B` with `IsQuotientCoveringMap.cwComplexQuotient`
identifies `H_n^{\mathrm{cell}}(B; k)` with `H_n(G, k)`. -/
def _root_.IsQuotientCoveringMap.cellularHomologyIsoGroupHomologyOfIsAspherical (n : ℕ) :
    letI := hG.cwComplexQuotient hcell hfree
    haveI := hG.t2Space_of_cwComplex hcell hfree
    (cellularChainComplex (univ : Set B) (ModuleCat.of k k)).homology n ≅
      groupHomology (Rep.trivial k G k) n :=
  haveI := hG.isCoveringMap.contractibleSpace_of_cwType_of_isAspherical he hb
  hG.cellularHomologyIsoGroupHomology hcell hfree k n

end FreeAction

end TauCeti

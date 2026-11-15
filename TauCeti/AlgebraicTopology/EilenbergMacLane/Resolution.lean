/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.FreeAction
public import TauCeti.AlgebraicTopology.Cellular.Resolution
public import TauCeti.AlgebraicTopology.EilenbergMacLane.Contractible
public import TauCeti.AlgebraicTopology.UniversalCover.Action

/-!
# Cellular resolutions from universal covers of aspherical spaces

Let `B` be an aspherical space at `b` and `p : E → B` a covering map from a simply connected space
`E` with `p e = b`. Whenever `E` carries a Hausdorff CW structure on `univ : Set E`, Whitehead's
theorem makes `univ : Set E` contractible (`IsCoveringMap.contractibleSpace_univ_of_isAspherical`).
This file packages the resulting projective resolutions of the trivial representation
`Rep.trivial k G k` in two complementary settings:

1. **Lifted CW structures** (`TauCeti.cellularResolutionOfIsAspherical`): when `B` is a Hausdorff
   CW complex and `hG : IsQuotientCoveringMap p G`, the lifted CW structure `p ⁻¹' univ` on `E`
   gives a projective resolution in `Rep k G`, free over `k[G]` in degree `n` on the `n`-cells of
   `B` (`TauCeti.cellularChainRepIsoFree`).
2. **Intrinsic free `G`-CW structures** (`TauCeti.cellActionResolutionOfIsAspherical`): when `E`
   itself carries any Hausdorff CW structure on `univ : Set E` whose open cells are continuously
   and freely permuted by `G`, its equivariant cellular chain complex
   `TauCeti.cellActionChainComplex` resolves `Rep.trivial k G k` (`TauCeti.cellActionResolution`).
   This covers both lifted CW structures (`TauCeti.smul_openCell_cellPreimage`,
   `TauCeti.eq_one_of_smul_openCell_cellPreimage_eq`) and `G`-CW structures constructed upstairs on
   `E` before descending to `B`, such as Milnor's simplicial join `TauCeti.universalGSpace` over
   `TauCeti.classifyingSpace` (`TauCeti.smul_openCell_universalGSpace`,
   `TauCeti.eq_one_of_smul_openCell_universalGSpace_eq`). When `p` is a quotient covering map for
   `G`, the degree-`n` term is free over `k[G]` on any chosen lifts of the `n`-cells of `B`
   (`IsQuotientCoveringMap.cellActionRepIsoFree`,
   `IsQuotientCoveringMap.cellActionRepIsoFreeQuotient`).

Specializing (2) to `TauCeti.UniversalCover b` yields `TauCeti.universalCoverCellActionResolution`,
a projective resolution of `Rep.trivial k (FundamentalGroup B b) k` for any CW structure on the
universal cover whose open cells are freely permuted by `FundamentalGroup B b`.

## Deck-action conventions

* For an abstract quotient covering map `hG : IsQuotientCoveringMap p G`, Mathlib's
  `IsQuotientCoveringMap.fundamentalGroupEquiv` identifies `G ≃* (FundamentalGroup B b)ᵐᵒᵖ` via
  monodromy (`g • e = hG.isCoveringMap.monodromy γ e`).
* On `TauCeti.UniversalCover b`, `FundamentalGroup B b = End (FundamentalGroupoid.mk b)` acts
  directly on the left by `g • mk x q = mk x (g⁻¹.toPath.trans q)`
  (`TauCeti.UniversalCover.smul_mk`). The inverse compensates for Mathlib's reversed `End`
  multiplication `(g * h).toPath = h.toPath.trans g.toPath`, so monodromy at `basepointLift b` is
  `g⁻¹ • basepointLift b` (`TauCeti.UniversalCover.monodromy_basepointLift`) and
  `TauCeti.universalCoverCellActionResolution` lives directly in `Rep k (FundamentalGroup B b)`
  without passing to the opposite group.

## Main definitions

* `TauCeti.cellularResolutionOfIsAspherical`: the projective resolution of `Rep.trivial k G k` by
  the lifted cellular chains of a simply connected quotient covering of an aspherical CW complex.
* `TauCeti.cellActionResolutionOfIsAspherical`: the projective resolution of `Rep.trivial k G k`
  from any simply connected Hausdorff CW cover of an aspherical space carrying a free cellular
  `G`-action on open cells.
* `TauCeti.universalCoverCellActionResolution`: specialization of
  `TauCeti.cellActionResolutionOfIsAspherical` to `TauCeti.UniversalCover b` with its left
  `FundamentalGroup B b`-action.

## References

* K. S. Brown, *Cohomology of Groups*, GTM 87, Springer, 1982, Section I.4 and Section II.4.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 1.B and Section 3.H.
-/

public section

noncomputable section

open scoped Pointwise
open CategoryTheory Set Topology

universe w

namespace TauCeti

section LiftedCW

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

end LiftedCW

section FreeActionCW

open Topology.RelCWComplex

variable {E B : Type w} [TopologicalSpace E] [T2Space E] [TopologicalSpace B]
  [CWComplex (univ : Set E)] [SimplyConnectedSpace E] {p : E → B} (hp : IsCoveringMap p)
  {G : Type w} [Group G] [MulAction G E] [ContinuousConstSMul G E]
  (hcell : ∀ (g : G) (n : ℕ) (i : cell (univ : Set E) n),
    ∃ j : cell (univ : Set E) n, g • openCell n i = openCell n j)
  (hfree : ∀ (g : G) (n : ℕ) (i : cell (univ : Set E) n),
    g • openCell n i = openCell n i → g = 1)
  {e : E} {b : B} (he : p e = b) (hb : IsAspherical B b) (k : Type w) [CommRing k]

/-- **The cellular resolution from a free `G`-CW cover of an aspherical space**: if `E` is a
simply connected Hausdorff CW complex carrying a continuous `G`-action that permutes open cells
freely, and `p : E → B` is a covering map onto a space aspherical at `b = p e`, then the
equivariant cellular chains of `E` form a projective resolution of `Rep.trivial k G k`. When `p` is
a quotient covering map for `G`, the degree-`n` term is free over `k[G]` on chosen lifts of the
`n`-cells of `B` (`IsQuotientCoveringMap.cellActionRepIsoFree`). -/
def cellActionResolutionOfIsAspherical : ProjectiveResolution (Rep.trivial k G k) :=
  haveI := hp.contractibleSpace_univ_of_isAspherical he hb
  cellActionResolution (univ : Set E) hcell hfree k

/-- The underlying complex of `TauCeti.cellActionResolutionOfIsAspherical` is
`TauCeti.cellActionChainComplex`. -/
@[simp]
lemma cellActionResolutionOfIsAspherical_complex :
    (cellActionResolutionOfIsAspherical hp hcell hfree he hb k).complex =
      cellActionChainComplex (univ : Set E) hcell k :=
  haveI := hp.contractibleSpace_univ_of_isAspherical he hb
  cellActionResolution_complex ..

-- As for `TauCeti.cellActionResolution_π`, a public statement cannot unfold the unexposed body of
-- `TauCeti.cellActionResolutionOfIsAspherical`, so it transports along
-- `cellActionResolutionOfIsAspherical_complex`.
/-- The augmentation of `TauCeti.cellActionResolutionOfIsAspherical` is
`TauCeti.cellActionChainComplexAugmentation`. -/
@[simp]
lemma cellActionResolutionOfIsAspherical_π :
    (cellActionResolutionOfIsAspherical hp hcell hfree he hb k).π =
      eqToHom (cellActionResolutionOfIsAspherical_complex hp hcell hfree he hb k) ≫
        cellActionChainComplexAugmentation (univ : Set E) hcell k :=
  haveI := hp.contractibleSpace_univ_of_isAspherical he hb
  cellActionResolution_π ..

end FreeActionCW

section UniversalCover

open Topology.RelCWComplex

variable {B : Type w} [TopologicalSpace B] [T2Space B] [LocallyPathConnectedSpace B]
  [SemilocallySimplyConnectedSpace B] {b : B}
  [CWComplex (univ : Set (UniversalCover b))]
  (hcell : ∀ (g : FundamentalGroup B b) (n : ℕ)
    (i : cell (univ : Set (UniversalCover b)) n),
    ∃ j : cell (univ : Set (UniversalCover b)) n, g • openCell n i = openCell n j)
  (hfree : ∀ (g : FundamentalGroup B b) (n : ℕ)
    (i : cell (univ : Set (UniversalCover b)) n),
    g • openCell n i = openCell n i → g = 1)
  (hb : IsAspherical B b) (k : Type w) [CommRing k]

/-- **The cellular resolution on the universal cover of an aspherical space**: for any CW
structure on `TauCeti.UniversalCover b` whose open cells are freely permuted by the left deck
action of `FundamentalGroup B b`, the equivariant cellular chain complex forms a projective
resolution of `Rep.trivial k (FundamentalGroup B b) k`. -/
def universalCoverCellActionResolution :
    ProjectiveResolution (Rep.trivial k (FundamentalGroup B b) k) :=
  haveI := (UniversalCover.isCoveringMap b).t2Space
  cellActionResolutionOfIsAspherical (UniversalCover.isCoveringMap b) hcell hfree
    (rfl : (UniversalCover.mk b (Path.Homotopic.Quotient.refl b)).proj = b) hb k

/-- The underlying complex of `TauCeti.universalCoverCellActionResolution` is
`TauCeti.cellActionChainComplex` on `TauCeti.UniversalCover b`. -/
@[simp]
lemma universalCoverCellActionResolution_complex :
    (universalCoverCellActionResolution hcell hfree hb k).complex =
      (haveI := (UniversalCover.isCoveringMap b).t2Space
      cellActionChainComplex (univ : Set (UniversalCover b)) hcell k) :=
  haveI := (UniversalCover.isCoveringMap b).t2Space
  cellActionResolutionOfIsAspherical_complex ..

/-- The augmentation of `TauCeti.universalCoverCellActionResolution` is
`TauCeti.cellActionChainComplexAugmentation` on `TauCeti.UniversalCover b`. -/
@[simp]
lemma universalCoverCellActionResolution_π :
    (universalCoverCellActionResolution hcell hfree hb k).π =
      (haveI := (UniversalCover.isCoveringMap b).t2Space
      eqToHom (universalCoverCellActionResolution_complex hcell hfree hb k) ≫
        cellActionChainComplexAugmentation (univ : Set (UniversalCover b)) hcell k) :=
  haveI := (UniversalCover.isCoveringMap b).t2Space
  cellActionResolutionOfIsAspherical_π ..

end UniversalCover

end TauCeti

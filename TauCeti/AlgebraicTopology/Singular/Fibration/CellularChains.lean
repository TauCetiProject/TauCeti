/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.LocalCoefficients.Coproduct
public import TauCeti.AlgebraicTopology.Singular.Fibration.FirstPage
public import TauCeti.AlgebraicTopology.Singular.Fibration.SerreLocalSystem

/-!
# The first page of the Serre spectral sequence as cellular chains with local coefficients

Let `p : E ⟶ B` be a Serre fibration and `C ⊆ B` a relative CW complex with skeleta `Xⁿ`. The
fibre homology `b ↦ Hq(p⁻¹(b); R)` is a local coefficient system on `B` with path-transport
monodromy (`TauCeti.TopCat.serreFiberLocalSystem`); write `Hq(F)` for its restriction to `C`
(`TauCeti.TopCat.serreFiberLocalSystemOn`). This file identifies, in every degree, the first page
of the Serre spectral sequence of `p` with the cellular chains of `C` with coefficients in `Hq(F)`:

`E¹_{n,q} = Hq+n(p⁻¹(Xⁿ), p⁻¹(Xⁿ⁻¹); R) ≅ Hn(Xⁿ, Xⁿ⁻¹; Hq(F))`

(`TauCeti.TopCat.serreChainsIso`, and on the page itself
`TauCeti.TopCat.serreSpectralSequenceFirstPageXIsoTwistedCellularChainGroup`). Cellular homology
with these coefficients is the homology `Hn(C, D; Hq(F))` of `C` relative to its base
(`TauCeti.twistedCellularSingularHomologyIso`), so this is the identification of the terms of the
first page on which the classical computation `E²_{n,q} ≅ Hn(B; Hq(F))` of the second page rests.
The comparison of the first differential with the cellular differential, which that computation
also needs, is not made here.

The identification is made cell by cell. Both sides are coproducts over the `n`-cells `j`, along
the characteristic maps `χⱼ`:

* `Hq+n(p⁻¹(Xⁿ), p⁻¹(Xⁿ⁻¹); R)` is the coproduct of the groups `Hq+n(Pⱼ, ∂Pⱼ; R)` of the pullback
  `Pⱼ` of `p` to the disk of `j`, relative to its part over the boundary sphere
  (`TauCeti.TopCat.isColimitCofanSingularHomologyPreimageSkeletonPair`);
* `Hn(Xⁿ, Xⁿ⁻¹; Hq(F))` is the coproduct of the groups `Hn(Dⁿ, Sⁿ⁻¹; χⱼ*Hq(F))` of the disk pair
  with the pulled-back coefficients
  (`TauCeti.isColimitCofanTwistedHomologyMapCharacteristicCellPairMap`).

Over a single cell the two summands agree (`TauCeti.TopCat.cellDiskPullbackPairTwistedIso`): both
are the fibre homology `Hq(p⁻¹(χⱼ(0)); R)` over the centre of the cell, the first by the
computation of the relative homology of a fibration over a disk
(`TauCeti.TopCat.cellDiskPullbackPairSingularHomologyIso`), the second because a local system on a
disk is constant (`TauCeti.twistedHomologyDiskBoundaryPairIso`). The global isomorphism is the one
induced on the coproducts, so it is characterized by its restriction to each cell
(`TauCeti.TopCat.singularHomologyMap_cellDiskPullbackPairMap_comp_serreChainsIso_hom`).

## Main definitions

* `TauCeti.TopCat.cellDiskPullbackPairTwistedIso`: `Hq+n(Pⱼ, ∂Pⱼ; R) ≅ Hn(Dⁿ, Sⁿ⁻¹; χⱼ*Hq(F))`.
* `TauCeti.TopCat.serreChainsIso`:
  `Hq+n(p⁻¹(Xⁿ), p⁻¹(Xⁿ⁻¹); R) ≅ Hn(Xⁿ, Xⁿ⁻¹; Hq(F))`.
* `TauCeti.TopCat.serreSpectralSequenceFirstPageXIsoTwistedCellularChainGroup`: the object
  `E¹_{n,q}` of the first page of the Serre spectral sequence is `Hn(Xⁿ, Xⁿ⁻¹; Hq(F))`.

## Main results

* `TauCeti.TopCat.singularHomologyMap_cellDiskPullbackPairMap_comp_serreChainsIso_hom`:
  on the contribution of the cell `j`, the identification is the one over the single cell,
  followed by the map induced by the characteristic map of `j`.

## References

* J.-P. Serre, *Homologie singulière des espaces fibrés. Applications*, Ann. of Math. 54 (1951),
  425–505, Chapter II.
* A. Hatcher,
  [*Spectral Sequences in Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/SSAT/SSch1.pdf),
  Chapter 1, the proof of Theorem 1.3 (the second page with local coefficients).
* J. McCleary, *A User's Guide to Spectral Sequences*, 2nd ed., Cambridge University Press, 2001,
  Theorem 5.2.
-/

public section

noncomputable section

open CategoryTheory Limits Set Topology Topology.RelCWComplex

universe u

namespace TauCeti

namespace TopCat

variable {E B : _root_.TopCat.{u}} {p : E ⟶ B} [T2Space B] {C D : Set B} [RelCWComplex C D]
  (hp : serreFibrations p) (R : Type u) [Ring R]

/-- **Over a single cell, the relative homology of a Serre fibration is the relative homology of
the disk with coefficients in the fibre homology.** For an `n`-cell `j` with characteristic map
`χⱼ`, the homology of the pullback `Pⱼ` of `p` to the disk of `j`, relative to its part over the
boundary sphere, is `Hq+n(Pⱼ, ∂Pⱼ; R) ≅ Hn(Dⁿ, Sⁿ⁻¹; χⱼ*Hq(F))`. Both are identified with the
fibre homology `Hq(p⁻¹(χⱼ(0)); R)` over the centre of the cell. -/
def cellDiskPullbackPairTwistedIso (n q : ℕ) (j : cell C n) :
    (cellDiskPullbackPair p C n j).singularHomology (ModuleCat.of R R) (q + n) ≅
      (diskBoundaryPair.{u} n).twistedHomology
        ((LocalCoefficientSystem.pullback (TopPair.Hom.fst (characteristicCellPairMap C j)).hom).obj
          (skeletonSystem C (serreFiberLocalSystemOn C R hp q) (n + 1))) n :=
  cellDiskPullbackPairSingularHomologyIso hp R n q j ≪≫
    (serreFiberLocalSystemObjIso hp (ModuleCat.of R R) q
      (FundamentalGroupoid.mk (map n j 0))).symm ≪≫
    eqToIso (congrArg (fun b : B ↦
      (serreFiberLocalSystem hp (ModuleCat.of R R) q).obj (FundamentalGroupoid.mk b))
        (coe_characteristicCellPairMap_fst_diskCenter C j).symm) ≪≫
    (twistedHomologyDiskBoundaryPairIso n
      ((LocalCoefficientSystem.pullback (TopPair.Hom.fst (characteristicCellPairMap C j)).hom).obj
        (skeletonSystem C (serreFiberLocalSystemOn C R hp q) (n + 1)))).symm

/-- `TauCeti.TopCat.cellDiskPullbackPairTwistedIso` is the identification of `Hq+n(Pⱼ, ∂Pⱼ; R)`
with the fibre homology over the centre of the cell, followed by the inverse identification of
`Hn(Dⁿ, Sⁿ⁻¹; χⱼ*Hq(F))` with the fibre of the coefficients over the centre of the disk. -/
lemma cellDiskPullbackPairTwistedIso_hom (n q : ℕ) (j : cell C n) :
    (cellDiskPullbackPairTwistedIso hp R n q j).hom =
      (cellDiskPullbackPairSingularHomologyIso hp R n q j).hom ≫
        (serreFiberLocalSystemObjIso hp (ModuleCat.of R R) q
          (FundamentalGroupoid.mk (map n j 0))).inv ≫
        eqToHom (congrArg (fun b : B ↦
          (serreFiberLocalSystem hp (ModuleCat.of R R) q).obj (FundamentalGroupoid.mk b))
            (coe_characteristicCellPairMap_fst_diskCenter C j).symm) ≫
        (twistedHomologyDiskBoundaryPairIso n
          ((LocalCoefficientSystem.pullback
            (TopPair.Hom.fst (characteristicCellPairMap C j)).hom).obj
            (skeletonSystem C (serreFiberLocalSystemOn C R hp q) (n + 1)))).inv :=
  (rfl)

variable (C) in
/-- **The first page of the Serre spectral sequence is the cellular chains with coefficients in the
fibre homology.** For a Serre fibration `p : E ⟶ B` and a relative CW complex `C ⊆ B` with skeleta
`Xⁿ`, `Hq+n(p⁻¹(Xⁿ), p⁻¹(Xⁿ⁻¹); R) ≅ Hn(Xⁿ, Xⁿ⁻¹; Hq(F))`, with coefficients in the local system
of fibre homology `b ↦ Hq(p⁻¹(b); R)` with its path-transport monodromy. On the contribution of
each `n`-cell it is `TauCeti.TopCat.cellDiskPullbackPairTwistedIso`
(`TauCeti.TopCat.singularHomologyMap_cellDiskPullbackPairMap_comp_serreChainsIso_hom`). -/
def serreChainsIso (n q : ℕ) :
    (preimageSkeletonPair p C n).singularHomology (ModuleCat.of R R) (q + n) ≅
      twistedCellularChainGroup.{u, u, u} C (serreFiberLocalSystemOn C R hp q) n :=
  (isColimitCofanSingularHomologyPreimageSkeletonPair C hp R n (q + n)).coconePointUniqueUpToIso
    ((IsColimit.precomposeHomEquiv
      (Discrete.natIso fun j ↦ cellDiskPullbackPairTwistedIso hp R n q j.as) _).symm
      (isColimitCofanTwistedHomologyMapCharacteristicCellPairMap C
        (serreFiberLocalSystemOn C R hp q) n))

variable (C) in
/-- **The identification of the first page with cellular chains, cell by cell.** On the
contribution `Hq+n(Pⱼ, ∂Pⱼ; R)` of an `n`-cell `j`, the isomorphism
`Hq+n(p⁻¹(Xⁿ), p⁻¹(Xⁿ⁻¹); R) ≅ Hn(Xⁿ, Xⁿ⁻¹; Hq(F))` is the identification
`Hq+n(Pⱼ, ∂Pⱼ; R) ≅ Hn(Dⁿ, Sⁿ⁻¹; χⱼ*Hq(F))` over the cell, followed by the map induced by the
characteristic map of `j`. -/
@[reassoc (attr := simp)]
theorem singularHomologyMap_cellDiskPullbackPairMap_comp_serreChainsIso_hom
    (n q : ℕ) (j : cell C n) :
    (cellDiskPullbackPair p C n j).singularHomologyMap (cellDiskPullbackPairMap p C n j)
        (ModuleCat.of R R) (q + n) ≫ (serreChainsIso C hp R n q).hom =
      (cellDiskPullbackPairTwistedIso hp R n q j).hom ≫
        TopPair.twistedHomologyMap (characteristicCellPairMap C j)
          (skeletonSystem C (serreFiberLocalSystemOn C R hp q) (n + 1)) n :=
  (isColimitCofanSingularHomologyPreimageSkeletonPair C hp R n (q + n)
    ).comp_coconePointUniqueUpToIso_hom _ ⟨j⟩

variable (C) in
/-- **The first page of the Serre spectral sequence is the cellular chains with coefficients in the
fibre homology.** For a Serre fibration `p : E ⟶ B` and a relative CW complex `C ⊆ B`, the object
of the first page (numbered `2`) of the Serre spectral sequence at `pq = (a, b)`, with `b = n - 1`
and `a + b = -(q + n)`, is the cellular chain group `Hn(Xⁿ, Xⁿ⁻¹; Hq(F))` with coefficients in the
local system of fibre homology. In the classical indexing this is `E¹_{n,q}`. -/
def serreSpectralSequenceFirstPageXIsoTwistedCellularChainGroup (n q : ℕ) (pq : ℤ × ℤ)
    (hb : pq.2 = n - 1) (ha : pq.1 + pq.2 = -(q + n : ℕ)) :
    ((serreSpectralSequence C p R).page 2).X pq ≅
      twistedCellularChainGroup.{u, u, u} C (serreFiberLocalSystemOn C R hp q) n :=
  filteredSpaceSpectralSequenceFirstPageXIso (ModuleCat.of R R) (monotone_preimageSkeleton p) pq
      pq.2 (pq.2 + 1) rfl rfl _ rfl (q + n) ha ≪≫
    eqToIso (congrArg (fun P : TopPair.{u} ↦ P.singularHomology (ModuleCat.of R R) (q + n))
      (ofInclusion_preimageSkeleton_eq_preimageSkeletonPair n pq.2 hb)) ≪≫
    serreChainsIso C hp R n q

variable (C) in
/-- The forward map of
`TauCeti.TopCat.serreSpectralSequenceFirstPageXIsoTwistedCellularChainGroup`: the first-page
identification of the filtered space, followed by the identification of the pair of consecutive
stages with `(p⁻¹(Xⁿ), p⁻¹(Xⁿ⁻¹))` and by `TauCeti.TopCat.serreChainsIso`. -/
lemma serreSpectralSequenceFirstPageXIsoTwistedCellularChainGroup_hom (n q : ℕ) (pq : ℤ × ℤ)
    (hb : pq.2 = n - 1) (ha : pq.1 + pq.2 = -(q + n : ℕ)) :
    (serreSpectralSequenceFirstPageXIsoTwistedCellularChainGroup C hp R n q pq hb ha).hom =
      (filteredSpaceSpectralSequenceFirstPageXIso (ModuleCat.of R R)
          (monotone_preimageSkeleton p) pq pq.2 (pq.2 + 1) rfl rfl (pq.1 + pq.2) rfl (q + n)
          ha).hom ≫
        eqToHom (congrArg (fun P : TopPair.{u} ↦ P.singularHomology (ModuleCat.of R R) (q + n))
          (ofInclusion_preimageSkeleton_eq_preimageSkeletonPair n pq.2 hb)) ≫
        (serreChainsIso C hp R n q).hom := by
  simp only [serreSpectralSequenceFirstPageXIsoTwistedCellularChainGroup, Iso.trans_hom,
    eqToIso.hom]

end TopCat

end TauCeti

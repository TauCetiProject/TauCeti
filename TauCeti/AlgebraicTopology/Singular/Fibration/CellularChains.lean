/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.LocalCoefficients.Coproduct
public import TauCeti.AlgebraicTopology.Singular.Fibration.FirstPage
public import TauCeti.AlgebraicTopology.Singular.Fibration.SerreLocalSystem
public import TauCeti.AlgebraicTopology.Singular.Fibration.TopCell
public import TauCeti.AlgebraicTopology.Cellular.LocalCoefficients.LocalHomology

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

The identification is compatible with localization at the centre `b = χⱼ(0)` of an `n`-cell `j`.
On the first page, the localization along the fibre over `b`,
`Hq+n(p⁻¹(Xⁿ), p⁻¹(Xⁿ⁻¹); R) ⟶ Hq+n(p⁻¹(Xⁿ), p⁻¹(Xⁿ ∖ {b}); R)`, is an isomorphism on the
contribution of `j` and vanishes on those of the other `n`-cells
(`TauCeti.AlgebraicTopology.Singular.Fibration.TopCell`); on cellular chains the localization
`Hn(Xⁿ, Xⁿ⁻¹; Hq(F)) ⟶ Hn(Xⁿ, Xⁿ ∖ {b}; Hq(F))` at `b` does the same
(`TauCeti.twistedCellularChainLocalization`). Identifying the two local homology groups through
the contribution of `j` (`TauCeti.TopCat.serreLocalHomologyIso`), the two localizations correspond
under `serreChainsIso`
(`TauCeti.TopCat.serreChainsIso_hom_comp_twistedCellularChainLocalization`). So the coefficient of
`j` of the cellular chain corresponding to a class of the first page is read off along the fibre
over the centre of `j`, which is how the first differential can be compared with the cellular
differential one target cell at a time.

## Main definitions

* `TauCeti.TopCat.cellDiskPullbackPairTwistedIso`: `Hq+n(Pⱼ, ∂Pⱼ; R) ≅ Hn(Dⁿ, Sⁿ⁻¹; χⱼ*Hq(F))`.
* `TauCeti.TopCat.serreChainsIso`:
  `Hq+n(p⁻¹(Xⁿ), p⁻¹(Xⁿ⁻¹); R) ≅ Hn(Xⁿ, Xⁿ⁻¹; Hq(F))`.
* `TauCeti.TopCat.serreSpectralSequenceFirstPageXIsoTwistedCellularChainGroup`: the object
  `E¹_{n,q}` of the first page of the Serre spectral sequence is `Hn(Xⁿ, Xⁿ⁻¹; Hq(F))`.
* `TauCeti.TopCat.serreLocalHomologyIso`: for the centre `b` of an `n`-cell,
  `Hq+n(p⁻¹(Xⁿ), p⁻¹(Xⁿ ∖ {b}); R) ≅ Hn(Xⁿ, Xⁿ ∖ {b}; Hq(F))`.

## Main results

* `TauCeti.TopCat.singularHomologyMap_cellDiskPullbackPairMap_comp_serreChainsIso_hom`:
  on the contribution of the cell `j`, the identification is the one over the single cell,
  followed by the map induced by the characteristic map of `j`.
* `TauCeti.TopCat.serreChainsIso_hom_comp_twistedCellularChainLocalization`: the identification is
  compatible with localization at the centre of a cell.

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

/-! ### Localization at the centre of a cell -/

section Localization

variable (C) in
/-- **The local homology along the fibre over the centre of a cell, with coefficients in the fibre
homology.** For the centre `b = χⱼ(0)` of an `n`-cell `j`, the local homology of `p⁻¹(Xⁿ)` along the
fibre over `b` is the local homology of `Xⁿ` at `b` with coefficients in `Hq(F)`:
`Hq+n(p⁻¹(Xⁿ), p⁻¹(Xⁿ ∖ {b}); R) ≅ Hn(Xⁿ, Xⁿ ∖ {b}; Hq(F))`. Both are identified with the
contribution of `j` to the cellular chains, through the localizations at `b`, and the two
contributions are identified by `TauCeti.TopCat.cellDiskPullbackPairTwistedIso`. -/
def serreLocalHomologyIso (n q : ℕ) (j : cell C n) (x : skeletonObj C (n + 1))
    (hx : (x : B) = map n j 0) :
    (preimageSkeletonComplFiberPair p C n (map n j 0)).singularHomology (ModuleCat.of R R)
        (q + n) ≅
      (TopPair.ofSubset ({x}ᶜ : Set (skeletonObj C (n + 1)))).twistedHomology
        (skeletonSystem C (serreFiberLocalSystemOn C R hp q) (n + 1)) n :=
  have := isIso_singularHomologyMap_cellDiskPullbackPairMap_comp_preimageSkeletonPairToComplFiber
    (j := j) (hp := hp) (M := ModuleCat.of R R) (k := q + n)
  have := isIso_twistedHomologyMap_characteristicCellPairMap_comp_twistedCellularChainLocalization
    C (serreFiberLocalSystemOn C R hp q) j x hx
  (asIso ((cellDiskPullbackPair p C n j).singularHomologyMap
      (cellDiskPullbackPairMap p C n j ≫
        preimageSkeletonPairToComplFiber p C n (map_zero_notMem_skeletonLT j))
      (ModuleCat.of R R) (q + n))).symm ≪≫
    cellDiskPullbackPairTwistedIso hp R n q j ≪≫
    asIso (TopPair.twistedHomologyMap (characteristicCellPairMap C j)
        (skeletonSystem C (serreFiberLocalSystemOn C R hp q) (n + 1)) n ≫
      twistedCellularChainLocalization C (serreFiberLocalSystemOn C R hp q) x
        (hx ▸ map_zero_notMem_skeletonLT j))

variable (C) in
/-- **The identification of the first page with cellular chains is compatible with localization at
the centre of a cell.** For the centre `b = χⱼ(0)` of an `n`-cell `j`, the isomorphism
`Hq+n(p⁻¹(Xⁿ), p⁻¹(Xⁿ⁻¹); R) ≅ Hn(Xⁿ, Xⁿ⁻¹; Hq(F))` of `TauCeti.TopCat.serreChainsIso`, followed by
the localization `Hn(Xⁿ, Xⁿ⁻¹; Hq(F)) ⟶ Hn(Xⁿ, Xⁿ ∖ {b}; Hq(F))` of cellular chains at `b`, is the
localization `Hq+n(p⁻¹(Xⁿ), p⁻¹(Xⁿ⁻¹); R) ⟶ Hq+n(p⁻¹(Xⁿ), p⁻¹(Xⁿ ∖ {b}); R)` along the fibre over
`b`, followed by `TauCeti.TopCat.serreLocalHomologyIso`. So the coefficient of `j` of the image of a
class under `serreChainsIso` is read off from the class along the fibre over the centre of `j`. -/
theorem serreChainsIso_hom_comp_twistedCellularChainLocalization (n q : ℕ) (j : cell C n)
    (x : skeletonObj C (n + 1)) (hx : (x : B) = map n j 0) :
    (serreChainsIso C hp R n q).hom ≫
        twistedCellularChainLocalization C (serreFiberLocalSystemOn C R hp q) x
          (hx ▸ map_zero_notMem_skeletonLT j) =
      (preimageSkeletonPair p C n).singularHomologyMap
          (preimageSkeletonPairToComplFiber p C n (map_zero_notMem_skeletonLT j))
          (ModuleCat.of R R) (q + n) ≫
        (serreLocalHomologyIso C hp R n q j x hx).hom := by
  refine (isColimitCofanSingularHomologyPreimageSkeletonPair C hp R n (q + n)).hom_ext
    fun ⟨k⟩ ↦ ?_
  simp only [Cofan.mk_ι_app]
  rw [singularHomologyMap_cellDiskPullbackPairMap_comp_serreChainsIso_hom_assoc,
    ← TopPair.singularHomologyMap_comp_assoc]
  by_cases hk : k = j
  · subst hk
    simp only [serreLocalHomologyIso, Iso.trans_hom, Iso.symm_hom, asIso_inv, asIso_hom,
      IsIso.hom_inv_id_assoc]
  · rw [twistedHomologyMap_characteristicCellPairMap_comp_twistedCellularChainLocalization_eq_zero
      C _ hk x (hx ▸ map_zero_mem_openCell n j), comp_zero,
      singularHomologyMap_cellDiskPullbackPairMap_comp_preimageSkeletonPairToComplFiber_eq_zero
        (j := j) hk, zero_comp]

end Localization

end TopCat

end TauCeti

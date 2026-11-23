/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.LocalCoefficients.Basic
public import TauCeti.AlgebraicTopology.Cellular.LocalCoefficients.Chains

/-!
# The cellular chain group with local coefficients is a coproduct of fibres, one per cell

Let `C ⊆ X` be a relative CW complex with skeleta `Xⁿ` and let `L` be a local coefficient system
on `C`. The cellular chain group `Hₙ(Xⁿ, Xⁿ⁻¹; L)` (`TauCeti.twistedCellularChainGroup`) is the
coproduct, over the `n`-cells `j`, of the fibres `L(χⱼ(0))` of `L` over the centres of the cells
(`TauCeti.twistedCellularChainGroupIso`). It is the local-coefficient form of the decomposition
`TauCeti.cellularChainGroupIso` of the cellular chain group into one copy of the coefficients per
cell, and it is built from the same ingredients.

The identification is induced by maps: on the summand of the cell `j`, the inverse is the
identification `Hₙ(Dⁿ, Sⁿ⁻¹; χⱼ*L) ≅ L(χⱼ(0))` followed by the map induced by the characteristic map
`χⱼ` (`TauCeti.ι_twistedCellularChainGroupIso_inv`). It combines four facts.

* The characteristic maps identify `Hₙ(Xⁿ, Xⁿ⁻¹; L)` with the relative homology of the disjoint
  union `∐ⱼ (Dⁿ, Sⁿ⁻¹)` of closed unit balls of the sup norm, with the pulled-back system
  (`TauCeti.isIso_twistedHomologyMap_characteristicPairMap`).
* That disjoint union is isomorphic, as a pair, to the disjoint union of copies of the Euclidean
  disk pair (`TauCeti.sigmaDiskBoundaryPairIso`).
* Relative twisted homology is additive (`TopPair.isColimitCofanTwistedHomology`).
* On the Euclidean disk pair, a local system is constant, and transport along the straight-line
  contraction onto the centre identifies `Hₙ(Dⁿ, Sⁿ⁻¹; L)` with `Hₙ(Dⁿ, Sⁿ⁻¹; L(0)) ≅ L(0)`
  (`TauCeti.twistedHomologyDiskBoundaryPairIso`).

For a fibration over a CW complex and the local system of fibre homology `b ↦ H_q(p⁻¹(b))`, the
summand of the cell `j` is the homology of the fibre over its centre. The first page of the Serre
spectral sequence is a coproduct of the same fibre homology groups, one per cell
(`TauCeti.TopCat.serreSpectralSequenceFirstPageXIsoSigma`).

## Main definitions

* `TauCeti.twistedCellularChainGroupIso`: `Hₙ(Xⁿ, Xⁿ⁻¹; L) ≅ ∐ⱼ L(χⱼ(0))`.

## Main results

* `TauCeti.ι_twistedCellularChainGroupIso_inv`: the inverse on the summand of a cell is
  induced by its characteristic map.

## References

* A. Hatcher, *Algebraic Topology*, Section 2.2, Lemma 2.34, and Section 3.H.
* G. W. Whitehead, *Elements of Homotopy Theory*, GTM 61, Springer, 1978, Chapter VI.
-/

public section

noncomputable section

open CategoryTheory Limits Topology Topology.RelCWComplex

universe w v u

namespace TauCeti

variable {R : Type u} [Ring R] {X : Type w} [TopologicalSpace X] [T2Space X] {D : Set X}
  (C : Set X) [RelCWComplex C D] (L : LocalCoefficientSystem.{u, w, max w v} R (TopCat.of C))

/-- **The cellular chain group with local coefficients is a coproduct of fibres, one per cell**:
`Hₙ(Xⁿ, Xⁿ⁻¹; L)` is the coproduct, over the `n`-cells `j`, of the fibres `L(χⱼ(0))` of `L` over
the centres of the cells. On the summand of `j` the inverse is induced by the characteristic map of
`j` (`TauCeti.ι_twistedCellularChainGroupIso_inv`). -/
def twistedCellularChainGroupIso (n : ℕ) :
    twistedCellularChainGroup C L n ≅
      ∐ fun j : cell C n ↦ L.obj (FundamentalGroupoid.mk
        ⟨map n j 0, openCell_subset_complex n j (map_zero_mem_openCell n j)⟩) :=
  have := isIso_twistedHomologyMap_characteristicPairMap C n n (skeletonSystem C L (n + 1))
  (asIso (TopPair.twistedHomologyMap (characteristicPairMap C n)
      (skeletonSystem C L (n + 1)) n)).symm ≪≫
    (asIso (TopPair.twistedHomologyMap (sigmaDiskBoundaryPairIso (cell C n) n).hom
      ((LocalCoefficientSystem.pullback (TopPair.Hom.fst (characteristicPairMap C n)).hom).obj
        (skeletonSystem C L (n + 1))) n)).symm ≪≫
    (TopPair.isColimitCofanTwistedHomology (fun _ : cell C n ↦ diskBoundaryPair.{w} n) _
      n).coconePointUniqueUpToIso (colimit.isColimit _) ≪≫
    Sigma.mapIso fun j ↦ twistedHomologyDiskBoundaryPairIso n
        ((LocalCoefficientSystem.pullback (TopPair.Hom.fst
          (TopPair.sigmaι (fun _ : cell C n ↦ diskBoundaryPair.{w} n) j)).hom).obj
          ((LocalCoefficientSystem.pullback
            (TopPair.Hom.fst (sigmaDiskBoundaryPairIso (cell C n) n).hom).hom).obj
            ((LocalCoefficientSystem.pullback (TopPair.Hom.fst (characteristicPairMap C n)).hom).obj
              (skeletonSystem C L (n + 1))))) ≪≫
      eqToIso (congrArg (fun x ↦ L.obj (FundamentalGroupoid.mk x))
        (Subtype.ext (coe_characteristicPairMap_sigmaDiskBoundaryPairIso_diskCenter C n j)))

/-- On the summand of the cell `j`, the inverse of `TauCeti.twistedCellularChainGroupIso` is
the identification `L(χⱼ(0)) ≅ Hₙ(Dⁿ, Sⁿ⁻¹; χⱼ*L)` followed by the map induced by the
characteristic map of `j`, read on the Euclidean disk pair. -/
@[reassoc]
lemma ι_twistedCellularChainGroupIso_inv (n : ℕ) (j : cell C n) :
    Sigma.ι (fun j : cell C n ↦ L.obj (FundamentalGroupoid.mk
        ⟨map n j 0, openCell_subset_complex n j (map_zero_mem_openCell n j)⟩)) j ≫
        (twistedCellularChainGroupIso C L n).inv =
      eqToHom (congrArg (fun x ↦ L.obj (FundamentalGroupoid.mk x)) (Subtype.ext
          (coe_characteristicPairMap_sigmaDiskBoundaryPairIso_diskCenter C n j)).symm) ≫
        (twistedHomologyDiskBoundaryPairIso n
          ((LocalCoefficientSystem.pullback (TopPair.Hom.fst
            (TopPair.sigmaι (fun _ : cell C n ↦ diskBoundaryPair.{w} n) j)).hom).obj
            ((LocalCoefficientSystem.pullback
              (TopPair.Hom.fst (sigmaDiskBoundaryPairIso (cell C n) n).hom).hom).obj
              ((LocalCoefficientSystem.pullback
                (TopPair.Hom.fst (characteristicPairMap C n)).hom).obj
                (skeletonSystem C L (n + 1)))))).inv ≫
        TopPair.twistedHomologyMap (TopPair.sigmaι (fun _ ↦ diskBoundaryPair.{w} n) j) _ n ≫
        TopPair.twistedHomologyMap (sigmaDiskBoundaryPairIso (cell C n) n).hom _ n ≫
        TopPair.twistedHomologyMap (characteristicPairMap C n) (skeletonSystem C L (n + 1)) n := by
  simp only [twistedCellularChainGroupIso, Iso.trans_inv, Sigma.ι_mapIso_inv_assoc,
    Category.assoc, Iso.symm_inv, asIso_hom]
  congr 2
  rw [colimit.comp_coconePointUniqueUpToIso_inv_assoc]
  rfl

end TauCeti

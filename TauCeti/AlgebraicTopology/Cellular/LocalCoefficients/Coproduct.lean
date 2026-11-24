/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.LocalCoefficients.Basic
public import TauCeti.AlgebraicTopology.Cellular.LocalCoefficients.Chains
public import TauCeti.AlgebraicTopology.Cellular.Boundary
public import TauCeti.AlgebraicTopology.Singular.Twisted.Zero

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

The coproduct can also be read directly through the characteristic maps, without identifying the
summands: the maps `Hₙ(Dⁿ, Sⁿ⁻¹; χⱼ*L) ⟶ Hₙ(Xⁿ, Xⁿ⁻¹; L)` induced by the characteristic maps of the
`n`-cells form a colimit cofan
(`TauCeti.isColimitCofanTwistedHomologyMapCharacteristicCellPairMap`). In degree zero the disk is a
point, and the legs are the classes of coefficients over the centres of the `0`-cells
(`TauCeti.isColimitCofanιTwistedHomology₀ZeroCellCenter`).

## Main definitions

* `TauCeti.twistedCellularChainGroupIso`: `Hₙ(Xⁿ, Xⁿ⁻¹; L) ≅ ∐ⱼ L(χⱼ(0))`.
* `TauCeti.isColimitCofanTwistedHomologyMapCharacteristicCellPairMap`: the cellular chain group is
  the coproduct of the relative homology of the disks of the cells, along the characteristic maps.
* `TauCeti.isColimitCofanιTwistedHomology₀ZeroCellCenter`: `H₀(X⁰, X⁻¹; L)` is the coproduct of
  the fibres of `L` over the centres of the `0`-cells, along the classes of coefficients.

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

/-! ### The legs of the characteristic maps -/

/-- **The cellular chain group with local coefficients is the coproduct of the contributions of
the cells.** The characteristic maps `(Dⁿ, Sⁿ⁻¹) ⟶ (Xⁿ, Xⁿ⁻¹)` of the `n`-cells exhibit
`Hₙ(Xⁿ, Xⁿ⁻¹; L)` as the coproduct of the `Hₙ(Dⁿ, Sⁿ⁻¹; χⱼ*L)`. -/
def isColimitCofanTwistedHomologyMapCharacteristicCellPairMap (n : ℕ) :
    IsColimit (Cofan.mk (twistedCellularChainGroup C L n) fun j : cell C n ↦
      TopPair.twistedHomologyMap (characteristicCellPairMap C j)
        (skeletonSystem C L (n + 1)) n) := by
  let g := (sigmaDiskBoundaryPairIso (cell C n) n).hom ≫ characteristicPairMap C n
  let K := (LocalCoefficientSystem.pullback (TopPair.Hom.fst g).hom).obj
    (skeletonSystem C L (n + 1))
  have hg := TopPair.twistedHomologyMap_comp (sigmaDiskBoundaryPairIso (cell C n) n).hom
    (characteristicPairMap C n) (skeletonSystem C L (n + 1)) n
  -- The factors are isomorphisms; instance search does not match the intermediate objects, which
  -- agree only up to unfolding the skeletal pair, so the composite instance is supplied.
  have : IsIso (TopPair.twistedHomologyMap g (skeletonSystem C L (n + 1)) n) :=
    hg ▸ @IsIso.comp_isIso _ _ _ _ _ _ _ inferInstance
      (@IsIso.comp_isIso _ _ _ _ _ _ _ inferInstance
        (isIso_twistedHomologyMap_characteristicPairMap C n n (skeletonSystem C L (n + 1))))
  -- The legs of the additivity cofan, precomposed with the identifications of the coefficients.
  let e : ∀ j : cell C n, (diskBoundaryPair.{w} n).twistedHomology
      ((LocalCoefficientSystem.pullback (TopPair.Hom.fst (characteristicCellPairMap C j)).hom).obj
        (skeletonSystem C L (n + 1))) n ≅
      (diskBoundaryPair.{w} n).twistedHomology
        ((LocalCoefficientSystem.pullback (TopPair.Hom.fst (TopPair.sigmaι _ j)).hom).obj K) n :=
    fun j ↦ asIso ((diskBoundaryPair.{w} n).twistedHomologyCoefficientMap
        (eqToHom (congrArg (fun f : diskBoundaryPair.{w} n ⟶ skeletonPair C n ↦
          (LocalCoefficientSystem.pullback (TopPair.Hom.fst f).hom).obj
            (skeletonSystem C L (n + 1))) (characteristicCellPairMap_def C j))) n) ≪≫
      asIso ((diskBoundaryPair.{w} n).twistedHomologyCoefficientMap
        (TopPair.fstPullbackCompIso (TopPair.sigmaι _ j) g (skeletonSystem C L (n + 1))).hom n)
  exact ((IsColimit.precomposeHomEquiv (Discrete.natIso fun j ↦ e j.as) _).symm
    (TopPair.isColimitCofanTwistedHomology (fun _ : cell C n ↦ diskBoundaryPair.{w} n) K
      n)).ofIsoColimit
    (Cofan.ext (c₂ := Cofan.mk (twistedCellularChainGroup C L n) fun j : cell C n ↦
        TopPair.twistedHomologyMap (characteristicCellPairMap C j) (skeletonSystem C L (n + 1)) n)
      (asIso (TopPair.twistedHomologyMap g (skeletonSystem C L (n + 1)) n)) fun j ↦ by
      -- The pulled-back systems are typed on `skeletonObj C (n + 1)` rather than on the ambient
      -- space of the pair, so the goal is not type-correct at instance transparency and `rw`/`simp`
      -- cannot reassociate; the composites are matched by unification.
      refine (Category.assoc _ _ _).trans ?_
      refine (Category.assoc _ _ _).trans ?_
      refine (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans
        (TopPair.twistedHomologyMap_comp _ _ _ n).symm)).trans ?_
      exact (TopPair.twistedHomologyMap_congr _
        (congrArg TopPair.Hom.fst (characteristicCellPairMap_def C j)) n).symm)

/-- On the disk `D⁰`, a point, the class of a coefficient over the centre is an isomorphism onto
the relative homology `H₀(D⁰, ∅; K)`. -/
private lemma isIso_ιTwistedHomology₀_comp_twistedHomologyπ_diskBoundaryPair_zero
    (K : LocalCoefficientSystem.{u, w, max w v} R (diskBoundaryPair.{w} 0).fst) :
    IsIso (LocalCoefficientSystem.ιTwistedHomology₀ K (diskCenter 0) ≫
      (diskBoundaryPair.{w} 0).twistedHomologyπ K 0) := by
  have hterm : IsTerminal (FundamentalGroupoid.mk (diskCenter.{w} 0)) :=
    IsTerminal.ofUniqueHom (fun x ↦ ⟦PathConnectedSpace.somePath x.as _⟧)
      fun _ _ ↦ Subsingleton.elim _ _
  have : IsIso (LocalCoefficientSystem.ιTwistedHomology₀ K (diskCenter 0)) :=
    (LocalCoefficientSystem.isColimitTwistedHomology₀Cocone K).isIso_ι_app_of_isTerminal _ hterm
  infer_instance

/-- **The cellular chain group in degree zero with local coefficients is the coproduct of the
fibres over the `0`-cells.** The classes of coefficients over the centres of the `0`-cells exhibit
`H₀(X⁰, X⁻¹; L)` as the coproduct of the fibres of `L` over these centres. -/
def isColimitCofanιTwistedHomology₀ZeroCellCenter :
    IsColimit (Cofan.mk (twistedCellularChainGroup C L 0) fun k : cell C 0 ↦
      LocalCoefficientSystem.ιTwistedHomology₀ (skeletonSystem C L 1) (zeroCellCenter C k) ≫
        (skeletonPair C 0).twistedHomologyπ (skeletonSystem C L (0 + 1)) 0) := by
  let e : ∀ k : cell C 0, (skeletonSystem C L 1).obj (FundamentalGroupoid.mk (zeroCellCenter C k)) ≅
      (diskBoundaryPair.{w} 0).twistedHomology
        ((LocalCoefficientSystem.pullback (TopPair.Hom.fst (characteristicCellPairMap C k)).hom).obj
          (skeletonSystem C L (0 + 1))) 0 :=
    fun k ↦ eqToIso (congrArg (fun z : skeletonObj C 1 ↦
      (skeletonSystem C L 1).obj (FundamentalGroupoid.mk z))
        (characteristicCellPairMap_fst_diskCenter C k).symm) ≪≫
      @asIso _ _ _ _ _ (isIso_ιTwistedHomology₀_comp_twistedHomologyπ_diskBoundaryPair_zero
        ((LocalCoefficientSystem.pullback (TopPair.Hom.fst (characteristicCellPairMap C k)).hom).obj
          (skeletonSystem C L (0 + 1))))
  refine ((IsColimit.precomposeHomEquiv (Discrete.natIso fun k ↦ e k.as) _).symm
    (isColimitCofanTwistedHomologyMapCharacteristicCellPairMap C L 0)).ofIsoColimit
    (Cofan.ext (Iso.refl _) fun k ↦ ?_)
  -- The leg at `k` is the class over the centre of `D⁰` pushed forward by the characteristic map.
  -- The pulled-back systems are typed on `skeletonObj C (0 + 1)` rather than on the ambient space
  -- of the pair, so the goal is not type-correct at instance transparency and `rw`/`simp` cannot
  -- reassociate; the composites are matched by unification.
  refine (Category.comp_id _).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·)
    (TopPair.twistedHomologyπ_naturality (characteristicCellPairMap C k) _ 0).symm))).trans ?_
  refine (congrArg (_ ≫ ·) ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _)
    (LocalCoefficientSystem.ιTwistedHomology₀_homologyMap _ _ _)))).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  exact congrArg (· ≫ _) (LocalCoefficientSystem.eqToHom_comp_ιTwistedHomology₀ _
    (characteristicCellPairMap_fst_diskCenter C k).symm)

end TauCeti

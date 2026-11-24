/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.Boundary
public import TauCeti.AlgebraicTopology.Cellular.LocalCoefficients.Chains
public import TauCeti.AlgebraicTopology.Singular.Twisted.DiskSphere

/-!
# The cellular differential of a `1`-cell with local coefficients

Let `C ⊆ X` be a relative CW complex with skeleta `Xⁿ` and let `L` be a local coefficient system
on `C`. For a `1`-cell `j`, the characteristic map `(D¹, S⁰) ⟶ (X¹, X⁰)` of `j`
(`TauCeti.characteristicCellPairMap`) carries `H₁(D¹, S⁰; χⱼ*L) ≅ L(χⱼ(0))` into the cellular chain
group `H₁(X¹, X⁰; L)`. The cellular differential `H₁(X¹, X⁰; L) ⟶ H₀(X⁰, X⁻¹; L)`
(`TauCeti.twistedCellularDifferential`) sends the image of a coefficient `a` over the centre of
`j` to the class of `a` transported along the cell to the endpoint `χⱼ(-e₀)`, minus the class of
`a` transported to the endpoint `χⱼ(e₀)`
(`TauCeti.twistedHomologyMap_characteristicCellPairMap_comp_twistedCellularDifferential_zero`).
The endpoints are the values of the attaching map of `j`
(`TauCeti.characteristicCellPairMap_snd`).

This is the local-coefficient form of `TauCeti.cellularIncidence_zero`: with constant coefficients
the transports are identities and the cellular boundary of a `1`-cell is the difference of its two
endpoints. With coefficients in the local system of fibre homology of a fibration over a CW
complex, it describes the differential into the column `p = 0` of the cellular chain complex
whose homology is `H_p(B; H_q(F))`.

## Main results

* `TauCeti.twistedHomologyMap_characteristicCellPairMap_comp_twistedCellularDifferential_zero`:
  the cellular differential of a `1`-cell with local coefficients.

## References

* A. Hatcher, *Algebraic Topology*, Section 2.2, the cellular boundary formula in degree one, and
  Section 3.H.
* G. W. Whitehead, *Elements of Homotopy Theory*, GTM 61, Springer, 1978, Chapter VI.
-/

public section

noncomputable section

open CategoryTheory Limits Topology

universe w v u

namespace TauCeti

variable {R : Type u} [Ring R]

section Cellular

open Topology.RelCWComplex LocalCoefficientSystem

variable {X : Type w} [TopologicalSpace X] [T2Space X] {D : Set X} (C : Set X) [RelCWComplex C D]
  (L : LocalCoefficientSystem.{u, w, max w v} R (TopCat.of C))

/-- The class of a coefficient at a point of the `0`-skeleton, read with coefficients restricted
from the `1`-skeleton, is its class with coefficients restricted from the complex. -/
private lemma ιTwistedHomology₀_skeletonPair_subspaceSystem_comp_twistedHomologyπ
    (y : skeletonObj C 1) :
    ιTwistedHomology₀ ((skeletonPair C 1).subspaceSystem (skeletonSystem C L (1 + 1))) y ≫
        (skeletonPair C 0).twistedHomologyπ _ 0 ≫
        (skeletonPair C 0).twistedHomologyCoefficientMap
          (skeletonPairSubspaceSystemIso C L 1).hom 0 =
      ιTwistedHomology₀ (skeletonSystem C L 1) y ≫ (skeletonPair C 0).twistedHomologyπ _ 0 := by
  -- The ambient space of `skeletonPair C 1` is `skeletonObj C (1 + 1)` only up to unfolding.
  erw [TopPair.twistedHomologyπ_comp_twistedHomologyCoefficientMap,
    ιTwistedHomology₀_coefficientMap_assoc, skeletonPairSubspaceSystemIso_hom_app]
  exact Category.id_comp _

/-- **The cellular differential of a `1`-cell with local coefficients.** For a `1`-cell `j` with
characteristic map `f : (D¹, S⁰) ⟶ (X¹, X⁰)`, the cellular differential sends the image under `f`
of a coefficient `a` over the centre of the disk to the class in `H₀(X⁰, X⁻¹; L)` of `a`
transported along the image of a path in the disk to the endpoint `f(-e₀)`, minus the class of `a`
transported to `f(e₀)`. The disk is simply connected, so any paths from its centre may be used;
the transport ends with the canonical identification `TopPair.subspaceSystemPullbackIso` of the
fibres over the endpoints, and the endpoints `f(∓e₀)` are the values of the attaching map of `j`
(`TauCeti.characteristicCellPairMap_snd`). -/
theorem twistedHomologyMap_characteristicCellPairMap_comp_twistedCellularDifferential_zero
    (j : cell C 1)
    (pMinus : FundamentalGroupoid.mk (diskCenter.{w} 1) ⟶
      FundamentalGroupoid.mk ((diskBoundaryPair.{w} 1).map sphereMinus))
    (pPlus : FundamentalGroupoid.mk (diskCenter.{w} 1) ⟶
      FundamentalGroupoid.mk ((diskBoundaryPair.{w} 1).map spherePlus)) :
    (twistedHomologyDiskBoundaryPairIso 1 ((LocalCoefficientSystem.pullback
          (TopPair.Hom.fst (characteristicCellPairMap C j)).hom).obj
            (skeletonSystem C L (1 + 1)))).inv ≫
        TopPair.twistedHomologyMap (characteristicCellPairMap C j) (skeletonSystem C L (1 + 1)) 1 ≫
        twistedCellularDifferential C L 0 =
      ((LocalCoefficientSystem.pullback (TopPair.Hom.fst (characteristicCellPairMap C j)).hom).obj
            (skeletonSystem C L (1 + 1))).map pMinus ≫
          (TopPair.subspaceSystemPullbackIso (characteristicCellPairMap C j)
            (skeletonSystem C L (1 + 1))).hom.app
            (FundamentalGroupoid.mk sphereMinus) ≫
          ιTwistedHomology₀ (skeletonSystem C L 1)
            (TopPair.Hom.snd (characteristicCellPairMap C j) sphereMinus) ≫
          (skeletonPair C 0).twistedHomologyπ _ 0 -
        ((LocalCoefficientSystem.pullback (TopPair.Hom.fst (characteristicCellPairMap C j)).hom).obj
            (skeletonSystem C L (1 + 1))).map pPlus ≫
          (TopPair.subspaceSystemPullbackIso (characteristicCellPairMap C j)
            (skeletonSystem C L (1 + 1))).hom.app
            (FundamentalGroupoid.mk spherePlus) ≫
          ιTwistedHomology₀ (skeletonSystem C L 1)
            (TopPair.Hom.snd (characteristicCellPairMap C j) spherePlus) ≫
          (skeletonPair C 0).twistedHomologyπ _ 0 := by
  have hd : twistedCellularDifferential C L 0 =
      (skeletonPair C 1).twistedHomologyδ (skeletonSystem C L (1 + 1)) 1 0 rfl ≫
        (skeletonPair C 0).twistedHomologyπ
          ((skeletonPair C 1).subspaceSystem (skeletonSystem C L (1 + 1))) 0 ≫
        (skeletonPair C 0).twistedHomologyCoefficientMap
          (skeletonPairSubspaceSystemIso C L 1).hom 0 :=
    twistedCellularDifferential_eq_twistedHomologyδ_comp_twistedHomologyπ C L 0
  -- The skeletal pairs and their coefficient systems agree with the generic statement only up to
  -- unfolding, so the steps are assembled as terms rather than by rewriting.
  refine (congrArg (fun t ↦ _ ≫ _ ≫ t) hd).trans
    ((twistedHomologyDiskBoundaryPairIso_one_inv_comp_twistedHomologyMap_twistedHomologyδ_assoc
        _ _ pMinus pPlus _).trans ((Preadditive.sub_comp _ _ _).trans (congrArg₂ (· - ·) ?_ ?_)))
  all_goals exact (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans
    (congrArg (_ ≫ ·)
      (ιTwistedHomology₀_skeletonPair_subspaceSystem_comp_twistedHomologyπ C L _))))

end Cellular

end TauCeti

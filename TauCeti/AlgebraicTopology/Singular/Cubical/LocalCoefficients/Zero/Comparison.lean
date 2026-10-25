/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Cubical.LocalCoefficients.Zero.Basic
public import TauCeti.AlgebraicTopology.Singular.Cubical.LocalCoefficients.Comparison.SingularToCubical
public import TauCeti.AlgebraicTopology.Singular.Twisted.Zero

/-!
# The comparison of cubical and simplicial chains in degree zero

The zeroth homology with local coefficients is the colimit of the local system over the
fundamental groupoid, both for the simplicial singular chains
(`TauCeti.LocalCoefficientSystem.twistedHomology₀IsoColimit`) and for the normalized cubical
chains (`TauCeti.LocalCoefficientSystem.normalizedTwistedCubicalHomology₀IsoColimit`).  The
comparison chain maps between the two theories are compatible with these identifications: on
zeroth homology they send the class of a coefficient at a point to the class of the same
coefficient at the same point.  Hence the two colimit identifications are intertwined by the
comparison maps, and the comparison is the identity of the colimit.

## Main statements

* `ιNormalizedTwistedCubicalHomology₀_comp_homologyMap_twistedCubicalToSingularMap` and
  `ιTwistedHomology₀_comp_homologyMap_twistedSingularToCubicalMap` (in the namespace
  `TauCeti.LocalCoefficientSystem`): the comparison maps send fibre classes to fibre classes.
* `TauCeti.LocalCoefficientSystem.homologyMap_twistedCubicalToSingularMap_comp_isoColimit_hom`,
  `TauCeti.LocalCoefficientSystem.homologyMap_twistedSingularToCubicalMap_comp_isoColimit_hom`:
  the compatibility of the two comparison maps with the colimit identifications.

## References

* J.-P. Serre, *Homologie singulière des espaces fibrés. Applications*, Ann. of Math. 54 (1951),
  Chapter II.
* A. Hatcher, *Algebraic Topology*, Section 3.H.
* `TauCeti/AlgebraicTopology/Singular/Twisted/Zero.lean` and
  `TauCeti/AlgebraicTopology/Singular/Cubical/LocalCoefficients/Zero/Basic.lean`: the two colimit
  identifications that are compared here.
* W. S. Massey, *Singular Homology Theory*, GTM 70, Springer, 1980, Chapters VII and XIV.
-/

public section

noncomputable section

open CategoryTheory

open scoped Simplicial

universe u v

namespace TauCeti.LocalCoefficientSystem

variable {R : Type u} [Ring R] {X : TopCat.{v}} (L : LocalCoefficientSystem.{u, v, v} R X)

/-- The comparison to simplicial chains sends the class of a coefficient in the fibre at `x` in
zeroth cubical homology to the class of the same coefficient in zeroth simplicial homology. -/
@[reassoc (attr := simp)]
theorem ιNormalizedTwistedCubicalHomology₀_comp_homologyMap_twistedCubicalToSingularMap (x : X) :
    ιNormalizedTwistedCubicalHomology₀ L x ≫
        HomologicalComplex.homologyMap (twistedCubicalToSingularMap L) 0 =
      ιTwistedHomology₀ L x := by
  refine ModuleCat.hom_ext (LinearMap.ext fun a ↦ ?_)
  -- Pass to `0`-chains, apply the comparison there, and pass back to homology.
  have h := ConcreteCategory.congr_hom
    (ChainComplex.pOpcycles_comp_isoHomologyι₀_inv_comp_homologyMap
      (twistedCubicalToSingularMap L))
    (NormalizedTwistedCubicalChain.ofCube L (ContinuousMap.const _ x) a)
  calc
    _ = (HomologicalComplex.homologyMap (twistedCubicalToSingularMap L) 0).hom
          ((L.normalizedTwistedCubicalChainComplex.pOpcycles 0 ≫
            L.normalizedTwistedCubicalChainComplex.isoHomologyι₀.inv)
              (NormalizedTwistedCubicalChain.ofCube L (ContinuousMap.const _ x) a)) :=
      congrArg _ (pOpcycles_comp_isoHomologyι₀_inv_ofCube L (ContinuousMap.const _ x) a).symm
    _ = ((twistedChainComplex L).pOpcycles 0 ≫ (twistedChainComplex L).isoHomologyι₀.inv)
          (normalizedTwistedCubicalToSingular L 0
            (NormalizedTwistedCubicalChain.ofCube L (ContinuousMap.const _ x) a)) :=
      h.trans (congrArg ((twistedChainComplex L).pOpcycles 0 ≫
        (twistedChainComplex L).isoHomologyι₀.inv).hom (ConcreteCategory.congr_hom
          (twistedCubicalToSingularMap_f (L := L) 0) _))
    _ = _ := (congrArg ((twistedChainComplex L).pOpcycles 0 ≫
        (twistedChainComplex L).isoHomologyι₀.inv).hom
      (normalizedTwistedCubicalToSingular_ofCube_const L x a)).trans
      (ConcreteCategory.congr_hom (ιTwistedHomology₀_def L x) a).symm

/-- The comparison to cubical chains sends the class of a coefficient in the fibre at `x` in
zeroth simplicial homology to the class of the same coefficient in zeroth cubical homology. -/
@[reassoc (attr := simp)]
theorem ιTwistedHomology₀_comp_homologyMap_twistedSingularToCubicalMap (x : X) :
    ιTwistedHomology₀ L x ≫ HomologicalComplex.homologyMap (twistedSingularToCubicalMap L) 0 =
      ιNormalizedTwistedCubicalHomology₀ L x := by
  refine ModuleCat.hom_ext (LinearMap.ext fun a ↦ ?_)
  have h := ConcreteCategory.congr_hom
    (ChainComplex.pOpcycles_comp_isoHomologyι₀_inv_comp_homologyMap
      (twistedSingularToCubicalMap L))
    (ιTwistedChainComplex L 0 (ULift.up (TopCat.ofHom (ContinuousMap.const _ x))) a)
  calc
    _ = (HomologicalComplex.homologyMap (twistedSingularToCubicalMap L) 0).hom
          (((twistedChainComplex L).pOpcycles 0 ≫ (twistedChainComplex L).isoHomologyι₀.inv)
            (ιTwistedChainComplex L 0 (ULift.up (TopCat.ofHom (ContinuousMap.const _ x))) a)) :=
      congrArg _ (ConcreteCategory.congr_hom (ιTwistedHomology₀_def L x) a)
    _ = (L.normalizedTwistedCubicalChainComplex.pOpcycles 0 ≫
          L.normalizedTwistedCubicalChainComplex.isoHomologyι₀.inv)
          ((twistedSingularToCubical L 0).hom
            (ιTwistedChainComplex L 0 (ULift.up (TopCat.ofHom (ContinuousMap.const _ x))) a)) :=
      h.trans (congrArg (L.normalizedTwistedCubicalChainComplex.pOpcycles 0 ≫
        L.normalizedTwistedCubicalChainComplex.isoHomologyι₀.inv).hom (ConcreteCategory.congr_hom
          (twistedSingularToCubicalMap_f (L := L) 0) _))
    _ = _ := (congrArg (L.normalizedTwistedCubicalChainComplex.pOpcycles 0 ≫
        L.normalizedTwistedCubicalChainComplex.isoHomologyι₀.inv).hom
      (twistedSingularToCubical_ιTwistedChainComplex_const L x a)).trans
      (pOpcycles_comp_isoHomologyι₀_inv_ofCube L (ContinuousMap.const _ x) a)

open Limits in
/-- **The comparison to simplicial chains is compatible with the colimit identifications.** On
zeroth homology it intertwines the identification of cubical homology with the colimit and the
identification of simplicial homology with the colimit. -/
@[reassoc (attr := simp)]
theorem homologyMap_twistedCubicalToSingularMap_comp_isoColimit_hom :
    HomologicalComplex.homologyMap (twistedCubicalToSingularMap L) 0 ≫
        (twistedHomology₀IsoColimit L).hom =
      (normalizedTwistedCubicalHomology₀IsoColimit L).hom := by
  apply normalizedTwistedCubicalHomology₀_hom_ext
  intro x
  rw [← Category.assoc,
    ιNormalizedTwistedCubicalHomology₀_comp_homologyMap_twistedCubicalToSingularMap,
    ιTwistedHomology₀_isoColimit_hom L (FundamentalGroupoid.mk x),
    ιNormalizedTwistedCubicalHomology₀_isoColimit_hom L (FundamentalGroupoid.mk x)]

open Limits in
/-- **The comparison to cubical chains is compatible with the colimit identifications.** On
zeroth homology it intertwines the identification of simplicial homology with the colimit and the
identification of cubical homology with the colimit. -/
@[reassoc (attr := simp)]
theorem homologyMap_twistedSingularToCubicalMap_comp_isoColimit_hom :
    HomologicalComplex.homologyMap (twistedSingularToCubicalMap L) 0 ≫
        (normalizedTwistedCubicalHomology₀IsoColimit L).hom =
      (twistedHomology₀IsoColimit L).hom := by
  apply twistedHomology₀_hom_ext
  intro x
  rw [← Category.assoc, ιTwistedHomology₀_comp_homologyMap_twistedSingularToCubicalMap,
    ιNormalizedTwistedCubicalHomology₀_isoColimit_hom L (FundamentalGroupoid.mk x),
    ιTwistedHomology₀_isoColimit_hom L (FundamentalGroupoid.mk x)]

end TauCeti.LocalCoefficientSystem

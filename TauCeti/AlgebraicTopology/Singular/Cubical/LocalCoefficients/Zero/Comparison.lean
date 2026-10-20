/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Cubical.LocalCoefficients.Zero.Basic
public import TauCeti.AlgebraicTopology.Singular.Cubical.LocalCoefficients.SingularToCubical
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

* `TauCeti.LocalCoefficientSystem.normalizedTwistedCubicalToSingular_ofCube_const`: on a point
  cube the comparison to simplicial chains is the inclusion of the point simplex.
* `TauCeti.LocalCoefficientSystem.ιNormalizedTwistedCubicalHomology₀_comp_homologyMap`: the
  comparison to simplicial chains sends fibre classes to fibre classes.
* `TauCeti.LocalCoefficientSystem.homologyMap_twistedCubicalToSingularMap_comp_isoColimit`,
  `TauCeti.LocalCoefficientSystem.homologyMap_twistedSingularToCubicalMap_comp_isoColimit`:
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

/-- On a point cube, the comparison to simplicial chains is the inclusion of the summand of the
point simplex. -/
theorem normalizedTwistedCubicalToSingular_ofCube_const (x : X)
    (a : L.obj (FundamentalGroupoid.mk x)) :
    normalizedTwistedCubicalToSingular L 0
        (NormalizedTwistedCubicalChain.ofCube L (ContinuousMap.const _ x) a) =
      ιTwistedChainComplex L 0 (ULift.up (TopCat.ofHom (ContinuousMap.const _ x))) a := by
  refine (normalizedTwistedCubicalToSingular_ofCube (L := L) (ContinuousMap.const _ x) a).trans
    ((twistedCubePushforward_apply (L := L) (ContinuousMap.const _ x) 0 _ a).trans
      ((congrArg (fun y ↦ twistedPushforward L (cubeToHom (ContinuousMap.const _ x))
        (cubeModelOrigin 0) 0 y a) (cubicalToSingularGen_zero (k := ULift.{v} ℤ))).trans ?_))
  rw [twistedPushforward_simplexChain_one (Z := cubeModel.{v} 0)]
  -- The simplex pushed forward along the point cube is the point simplex, and the transport
  -- from the origin of the model to itself is trivial.
  exact ιTwistedChainComplex_congr L
    ((TopCat.toSSet_map_app_toSSetObj₀Equiv_symm _ _).trans (by rfl))
    (map_pathClass_heq (L := L) (cubeToHom (ContinuousMap.const _ x)).hom
      (z := cubeModelOrigin 0) (Subsingleton.elim _ _) a)

/-- The comparison to simplicial chains sends the class of a coefficient in the fibre at `x` in
zeroth cubical homology to the class of the same coefficient in zeroth simplicial homology. -/
theorem ιNormalizedTwistedCubicalHomology₀_comp_homologyMap (x : X) :
    ιNormalizedTwistedCubicalHomology₀ L x ≫
        HomologicalComplex.homologyMap (twistedCubicalToSingularMap L) 0 =
      ιTwistedHomology₀ L x := by
  refine ModuleCat.hom_ext (LinearMap.ext fun a ↦ ?_)
  -- Evaluating at a coefficient: pass to `0`-chains, apply the comparison there, and pass back.
  have h := ConcreteCategory.congr_hom
    (ChainComplex.pOpcycles_comp_isoHomologyι₀_inv_comp_homologyMap
      (twistedCubicalToSingularMap L))
    (NormalizedTwistedCubicalChain.ofCube L (ContinuousMap.const _ x) a)
  refine (congrArg (HomologicalComplex.homologyMap (twistedCubicalToSingularMap L) 0).hom
    (pOpcycles_comp_isoHomologyι₀_inv_ofCube L (ContinuousMap.const _ x) a).symm).trans
    (h.trans ((congrArg ((twistedChainComplex L).pOpcycles 0 ≫
      (twistedChainComplex L).isoHomologyι₀.inv).hom
      ((ConcreteCategory.congr_hom (twistedCubicalToSingularMap_f (L := L) 0) _).trans
        (normalizedTwistedCubicalToSingular_ofCube_const L x a))).trans
      (ConcreteCategory.congr_hom (ιTwistedHomology₀_eq L x) a).symm))

open Limits in
/-- **The comparison to simplicial chains is compatible with the colimit identifications.** On
zeroth homology it intertwines the identification of cubical homology with the colimit and the
identification of simplicial homology with the colimit. -/
theorem homologyMap_twistedCubicalToSingularMap_comp_isoColimit :
    HomologicalComplex.homologyMap (twistedCubicalToSingularMap L) 0 ≫
        (twistedHomology₀IsoColimit L).hom =
      (normalizedTwistedCubicalHomology₀IsoColimit L).hom := by
  apply normalizedTwistedCubicalHomology₀_hom_ext
  intro x
  rw [← Category.assoc, ιNormalizedTwistedCubicalHomology₀_comp_homologyMap,
    ιTwistedHomology₀_isoColimit_hom L (FundamentalGroupoid.mk x),
    ιNormalizedTwistedCubicalHomology₀_isoColimit_hom L (FundamentalGroupoid.mk x)]

open Limits in
/-- **The comparison to cubical chains is compatible with the colimit identifications.** On
zeroth homology it intertwines the identification of simplicial homology with the colimit and the
identification of cubical homology with the colimit. -/
theorem homologyMap_twistedSingularToCubicalMap_comp_isoColimit :
    HomologicalComplex.homologyMap (twistedSingularToCubicalMap L) 0 ≫
        (normalizedTwistedCubicalHomology₀IsoColimit L).hom =
      (twistedHomology₀IsoColimit L).hom := by
  apply twistedHomology₀_hom_ext
  intro x
  refine ModuleCat.hom_ext (LinearMap.ext fun a ↦ ?_)
  -- The point simplex at `x`, and the image of `a` in the colimit after the comparison.
  set σ : (TopCat.toSSet.obj X) _⦋0⦌ := ULift.up (TopCat.ofHom (ContinuousMap.const _ x)) with hσ
  have hA : NormalizedTwistedCubicalChain.augment (colimit.cocone L)
      ((twistedSingularToCubical L 0).hom (ιTwistedChainComplex L 0 σ a)) =
        (colimit.cocone L).ι.app (FundamentalGroupoid.mk x) a :=
    (congrArg (NormalizedTwistedCubicalChain.augment (colimit.cocone L))
      ((twistedSingularToCubical_ιTwistedChainComplex L σ a).trans
        ((twistedSingularToCubicalSummand_apply L σ a).trans
          (congrArg (fun y ↦ NormalizedTwistedCubicalChain.pushforward
            (Z := simplexModel.{v} 0) L (simplexToHom σ).hom
            (SimplexCategory.toTopInitialVertex ⦋0⦌) 0 y a)
            (singularToCubicalGen_zero (k := ULift.{v} ℤ)))))).trans
      (NormalizedTwistedCubicalChain.augment_pushforward_ofCube (L := L)
        (f := (simplexToHom σ).hom) (z₀ := SimplexCategory.toTopInitialVertex ⦋0⦌)
        (colimit.cocone L) _ a)
  refine ((congrArg (normalizedTwistedCubicalHomology₀IsoColimit L).hom
    (congrArg (HomologicalComplex.homologyMap (twistedSingularToCubicalMap L) 0).hom
      (ConcreteCategory.congr_hom (ιTwistedHomology₀_eq L x) a))).trans
    ((congrArg (normalizedTwistedCubicalHomology₀IsoColimit L).hom
      (ConcreteCategory.congr_hom
        (ChainComplex.pOpcycles_comp_isoHomologyι₀_inv_comp_homologyMap
          (twistedSingularToCubicalMap L)) (ιTwistedChainComplex L 0 σ a))).trans
      ((congrArg (normalizedTwistedCubicalHomology₀IsoColimit L).hom
        (congrArg (L.normalizedTwistedCubicalChainComplex.pOpcycles 0 ≫
          L.normalizedTwistedCubicalChainComplex.isoHomologyι₀.inv).hom
          (ConcreteCategory.congr_hom (twistedSingularToCubicalMap_f (L := L) 0) _))).trans
        ((ConcreteCategory.congr_hom
          (pOpcycles_comp_normalizedTwistedCubicalHomology₀IsoColimit_hom L) _).trans
          hA)))).trans ?_
  exact (ConcreteCategory.congr_hom
    (ιTwistedHomology₀_isoColimit_hom L (FundamentalGroupoid.mk x)) a).symm

end TauCeti.LocalCoefficientSystem

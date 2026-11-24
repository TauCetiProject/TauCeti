/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Reduced
public import TauCeti.AlgebraicTopology.Singular.Twisted.Contractible
public import TauCeti.AlgebraicTopology.Singular.Twisted.Functoriality
public import TauCeti.AlgebraicTopology.Singular.Twisted.Zero
import TauCeti.AlgebraicTopology.Singular.IntervalGenerator
import TauCeti.AlgebraicTopology.Singular.Twisted.ConstantNaturality

/-!
# The connecting morphism of the `1`-disk with local coefficients

For a local coefficient system `L` on the disk `D¹`, the relative homology `H₁(D¹, S⁰; L)` is the
fibre `L(0)` of `L` over the centre (`TauCeti.twistedHomologyDiskBoundaryPairIso`). This file
computes the connecting morphism `H₁(D¹, S⁰; L) ⟶ H₀(S⁰; L)` in these terms: it sends a
coefficient `a` over the centre to the class of `a` transported to the endpoint `-e₀`, minus the
class of `a` transported to the endpoint `e₀`
(`TauCeti.twistedHomologyDiskBoundaryPairIso_one_inv_comp_twistedHomologyδ`). The disk is simply
connected, so the transports may be taken along any paths from the centre.

This is the local-coefficient form of the fact that the boundary of the generator of
`H₁(D¹, S⁰)` is the class `[-e₀] - [e₀]`
(`TauCeti.singularHomologyDiskBoundaryPairIso_inv_comp_singularHomologyδ` and
`TauCeti.reducedSingularHomologyTopCatSphereIso_zero_inv_ι`), and it is reduced to that fact in two
steps.

* On a pair whose ambient space is contractible, the identification of `L` with the constant
  system at a fibre turns the connecting morphism into the ordinary one with coefficients in that
  fibre (`TopPair.twistedHomologyIsoOfHomotopy_inv_comp_twistedHomologyδ`).
* For a constant system, the class of a coefficient at a point is the ordinary homology class of
  the point (`TauCeti.LocalCoefficientSystem.ιTwistedHomology₀_twistedHomologyConstantIso_hom`).

A map of pairs `f : (D¹, S⁰) ⟶ (X, A)` carries classes of coefficients at points of `S⁰` to classes
at their images, so the
connecting morphism of `(X, A)` sends the image under `f` of a coefficient over the centre of the
disk to the difference of its transports to `f(-e₀)` and `f(e₀)`
(`TauCeti.twistedHomologyDiskBoundaryPairIso_one_inv_comp_twistedHomologyMap_twistedHomologyδ`).
For the characteristic map of a `1`-cell of a CW complex this computes the cellular differential
out of degree one with local coefficients
(`TauCeti.AlgebraicTopology.Cellular.LocalCoefficients.EdgeIncidence`).

## Main results

* `TauCeti.twistedHomologyDiskBoundaryPairIso_one_inv_comp_twistedHomologyδ`: the connecting
  morphism of `(D¹, S⁰)` with local coefficients.
* `TauCeti.twistedHomologyDiskBoundaryPairIso_one_inv_comp_twistedHomologyMap_twistedHomologyδ`:
  the connecting morphism of a pair on the image of the `1`-disk under a map of pairs.
* `TopPair.twistedHomologyIsoOfHomotopy_inv_comp_twistedHomologyδ`: the connecting morphism of a
  pair with contractible ambient space through constant coefficients.

## References

* A. Hatcher, *Algebraic Topology*, Section 2.1, Example 2.23, and Section 3.H.
* G. W. Whitehead, *Elements of Homotopy Theory*, GTM 61, Springer, 1978, Chapter VI.
-/

public section

noncomputable section

open CategoryTheory Limits Topology

universe w v u

namespace TopPair

open TauCeti TauCeti.LocalCoefficientSystem

variable {R : Type u} [Ring R] (P : TopPair.{v}) {x : P.fst}
  (H : (ContinuousMap.id P.fst).Homotopy (ContinuousMap.const P.fst x))
  (L : LocalCoefficientSystem.{u, v, max v w} R P.fst)

/-- The connecting morphism of a pair with contractible ambient space, read through
`TopPair.twistedHomologyIsoOfHomotopy`: it is the ordinary connecting morphism with coefficients in
the fibre `L x`, followed by the identification of the restriction of the constant system with
the restriction of `L`. -/
lemma twistedHomologyIsoOfHomotopy_inv_comp_twistedHomologyδ (n m : ℕ) (h : m + 1 = n) :
    (P.twistedHomologyIsoOfHomotopy H L n).inv ≫ P.twistedHomologyδ L n m h =
      P.singularHomologyδ (L.obj (FundamentalGroupoid.mk x)) n m h ≫
        (LocalCoefficientSystem.twistedHomologyConstantIso P.snd _ m).inv ≫
        LocalCoefficientSystem.twistedHomologyCoefficientMap
          (pullbackConstantIso P.map.hom (L.obj (FundamentalGroupoid.mk x))).inv m ≫
        LocalCoefficientSystem.twistedHomologyCoefficientMap
          ((LocalCoefficientSystem.pullback P.map.hom).map (isoConstantOfHomotopy H L).inv) m := by
  have hc := P.twistedHomologyδ_naturality_coefficient (isoConstantOfHomotopy H L).inv n m h
  have hk := P.twistedHomologyδ_comp_twistedHomologyConstantIso_hom
    (L.obj (FundamentalGroupoid.mk x)) n m h
  have h1 : (P.twistedHomologyConstantIso (L.obj (FundamentalGroupoid.mk x)) n).inv ≫
      P.twistedHomologyδ _ n m h =
        P.singularHomologyδ (L.obj (FundamentalGroupoid.mk x)) n m h ≫
          (LocalCoefficientSystem.twistedHomologyConstantIso P.snd _ m).inv ≫
          LocalCoefficientSystem.twistedHomologyCoefficientMap
            (pullbackConstantIso P.map.hom (L.obj (FundamentalGroupoid.mk x))).inv m := by
    have hk' := hk =≫ ((LocalCoefficientSystem.twistedHomologyConstantIso P.snd _ m).inv ≫
      LocalCoefficientSystem.twistedHomologyCoefficientMap
        (pullbackConstantIso P.map.hom (L.obj (FundamentalGroupoid.mk x))).inv m)
    simp only [Category.assoc, Iso.hom_inv_id_assoc,
      ← LocalCoefficientSystem.twistedHomologyCoefficientMap_comp, Iso.hom_inv_id,
      LocalCoefficientSystem.twistedHomologyCoefficientMap_id, Category.comp_id] at hk'
    rw [Iso.inv_comp_eq]
    -- The two presentations of the homology of the subspace agree only definitionally, which
    -- blocks reassociating `hk'` by rewriting.
    exact hk'.trans (Category.assoc _ _ _)
  rw [twistedHomologyIsoOfHomotopy_inv, Category.assoc, ← hc, reassoc_of% h1]
  exact congrArg _ (Category.assoc _ _ _)

/-- A point class of the subspace of a pair with contractible ambient space, carried from constant
coefficients back to `L` along the identification of `TopPair.twistedHomologyIsoOfHomotopy`, is
the class of the coefficient transported along any path from the centre of the contraction. -/
private lemma singularHomology₀Section_comp_coefficientMap_isoConstantOfHomotopy_inv
    (y : P.snd) (q : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk (P.map y)) :
    singularHomology₀Section (L.obj (FundamentalGroupoid.mk x)) y ≫
        (LocalCoefficientSystem.twistedHomologyConstantIso P.snd _ 0).inv ≫
        LocalCoefficientSystem.twistedHomologyCoefficientMap
          (pullbackConstantIso P.map.hom (L.obj (FundamentalGroupoid.mk x))).inv 0 ≫
        LocalCoefficientSystem.twistedHomologyCoefficientMap
          ((LocalCoefficientSystem.pullback P.map.hom).map (isoConstantOfHomotopy H L).inv) 0 =
      L.map q ≫ ιTwistedHomology₀ (P.subspaceSystem L) y := by
  rw [singularHomology₀Section_twistedHomologyConstantIso_inv_assoc]
  -- The constant system restricted to the subspace and the constant system on the subspace have
  -- the same fibres only up to definitional unfolding.
  erw [ιTwistedHomology₀_coefficientMap_assoc, ιTwistedHomology₀_coefficientMap,
    pullbackConstantIso_inv_app, Category.id_comp, pullback_map_app]
  exact congrArg (· ≫ _) (isoConstantOfHomotopy_inv_app H L q)

omit L in
/-- A map of pairs carries the class of a coefficient at a point of the subspace to the class of
that coefficient at the image point, through the canonical identification of the restriction of
the pulled-back system with the pullback of the restricted system. -/
@[reassoc]
private lemma ιTwistedHomology₀_subspaceSystem_comp_twistedHomologyMap {Q : TopPair.{v}} (f : P ⟶ Q)
    (L : LocalCoefficientSystem.{u, v, max v w} R Q.fst) (y : P.snd) :
    ιTwistedHomology₀ (P.subspaceSystem ((LocalCoefficientSystem.pullback (Hom.fst f).hom).obj L))
        y ≫
        LocalCoefficientSystem.twistedHomologyCoefficientMap (subspaceSystemPullbackIso f L).hom 0 ≫
        LocalCoefficientSystem.twistedHomologyMap (Hom.snd f) (Q.subspaceSystem L) 0 =
      (subspaceSystemPullbackIso f L).hom.app (FundamentalGroupoid.mk y) ≫
        ιTwistedHomology₀ (Q.subspaceSystem L) (Hom.snd f y) := by
  rw [ιTwistedHomology₀_coefficientMap_assoc, ιTwistedHomology₀_homologyMap]

end TopPair

namespace TauCeti

variable {R : Type u} [Ring R]

open LocalCoefficientSystem in
/-- **The boundary of the `1`-disk with local coefficients.** Under the identification
`H₁(D¹, S⁰; L) ≅ L(0)` of `TauCeti.twistedHomologyDiskBoundaryPairIso`, the connecting morphism of
the pair `(D¹, S⁰)` sends a coefficient `a` over the centre to the class of `a` transported to the
endpoint `-e₀`, minus the class of `a` transported to the endpoint `e₀`. The disk is simply
connected, so the transports are along any paths from the centre. -/
@[reassoc]
theorem twistedHomologyDiskBoundaryPairIso_one_inv_comp_twistedHomologyδ
    (L : LocalCoefficientSystem.{u, v, max v w} R (diskBoundaryPair.{v} 1).fst)
    (pMinus : FundamentalGroupoid.mk (diskCenter.{v} 1) ⟶
      FundamentalGroupoid.mk ((diskBoundaryPair.{v} 1).map sphereMinus))
    (pPlus : FundamentalGroupoid.mk (diskCenter.{v} 1) ⟶
      FundamentalGroupoid.mk ((diskBoundaryPair.{v} 1).map spherePlus)) :
    (twistedHomologyDiskBoundaryPairIso 1 L).inv ≫
        (diskBoundaryPair.{v} 1).twistedHomologyδ L 1 0 =
      L.map pMinus ≫ ιTwistedHomology₀ ((diskBoundaryPair.{v} 1).subspaceSystem L) sphereMinus -
        L.map pPlus ≫ ιTwistedHomology₀ ((diskBoundaryPair.{v} 1).subspaceSystem L) spherePlus := by
  let P := diskBoundaryPair.{v} 1
  rw [twistedHomologyDiskBoundaryPairIso_inv, Category.assoc,
    P.twistedHomologyIsoOfHomotopy_inv_comp_twistedHomologyδ (diskContraction 1) L 1 0 rfl,
    ← Category.assoc, singularHomologyDiskBoundaryPairIso_inv_comp_singularHomologyδ]
  -- `TopCat.sphere 0` is the boundary of the `1`-disk.
  erw [reducedSingularHomologyTopCatSphereIso_zero_inv_ι]
  -- The disk `P.fst` and `TopCat.disk 1` agree only definitionally, which blocks rewriting.
  exact (Preadditive.sub_comp _ _ _).trans (congrArg₂ (· - ·)
    (P.singularHomology₀Section_comp_coefficientMap_isoConstantOfHomotopy_inv
      (diskContraction 1) L sphereMinus pMinus)
    (P.singularHomology₀Section_comp_coefficientMap_isoConstantOfHomotopy_inv
      (diskContraction 1) L spherePlus pPlus))

open LocalCoefficientSystem in
/-- **The boundary of the image of the `1`-disk with local coefficients.** For a map of pairs
`f : (D¹, S⁰) ⟶ (X, A)`, the connecting morphism of `(X, A)` sends the image under `f` of the class
of a coefficient `a` over the centre of the disk to the class of `a` transported to `f(-e₀)`, minus
the class of `a` transported to `f(e₀)`, in the homology of `A`. The transports are along the
images of any paths in the disk, followed by the canonical identification
`TopPair.subspaceSystemPullbackIso` of the fibres. -/
@[reassoc]
theorem twistedHomologyDiskBoundaryPairIso_one_inv_comp_twistedHomologyMap_twistedHomologyδ
    {Q : TopPair.{v}} (f : diskBoundaryPair.{v} 1 ⟶ Q)
    (L : LocalCoefficientSystem.{u, v, max v w} R Q.fst)
    (pMinus : FundamentalGroupoid.mk (diskCenter.{v} 1) ⟶
      FundamentalGroupoid.mk ((diskBoundaryPair.{v} 1).map sphereMinus))
    (pPlus : FundamentalGroupoid.mk (diskCenter.{v} 1) ⟶
      FundamentalGroupoid.mk ((diskBoundaryPair.{v} 1).map spherePlus)) :
    (twistedHomologyDiskBoundaryPairIso 1
        ((LocalCoefficientSystem.pullback (TopPair.Hom.fst f).hom).obj L)).inv ≫
        TopPair.twistedHomologyMap f L 1 ≫ Q.twistedHomologyδ L 1 0 rfl =
      ((LocalCoefficientSystem.pullback (TopPair.Hom.fst f).hom).obj L).map pMinus ≫
          (TopPair.subspaceSystemPullbackIso f L).hom.app (FundamentalGroupoid.mk sphereMinus) ≫
          ιTwistedHomology₀ (Q.subspaceSystem L) (TopPair.Hom.snd f sphereMinus) -
        ((LocalCoefficientSystem.pullback (TopPair.Hom.fst f).hom).obj L).map pPlus ≫
          (TopPair.subspaceSystemPullbackIso f L).hom.app (FundamentalGroupoid.mk spherePlus) ≫
          ιTwistedHomology₀ (Q.subspaceSystem L) (TopPair.Hom.snd f spherePlus) := by
  -- The disk `(diskBoundaryPair 1).fst` is `TopCat.disk 1` only up to unfolding, so the rewrites
  -- below go through `erw`.
  erw [← TopPair.twistedHomologyδ_naturality f L 1 0 rfl,
    twistedHomologyDiskBoundaryPairIso_one_inv_comp_twistedHomologyδ_assoc _ pMinus pPlus,
    Preadditive.sub_comp, Category.assoc, Category.assoc,
    TopPair.ιTwistedHomology₀_subspaceSystem_comp_twistedHomologyMap,
    TopPair.ιTwistedHomology₀_subspaceSystem_comp_twistedHomologyMap]
  -- The two sides differ only in the implicit middle object of the composites: the fibre of
  -- `(diskBoundaryPair 1).subspaceSystem` at a point of `S⁰` is by definition the fibre of the
  -- ambient system at its image in the disk.
  rfl

end TauCeti

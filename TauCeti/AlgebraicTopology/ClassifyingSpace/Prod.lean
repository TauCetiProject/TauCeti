/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ClassifyingSpace.Homology
public import TauCeti.AlgebraicTopology.EilenbergMacLane.WeakHomotopyEquivalence
public import TauCeti.AlgebraicTopology.FundamentalGroup.Product
public import TauCeti.AlgebraicTopology.Singular.Homotopy.WeakHomotopyEquivalence
public import TauCeti.AlgebraicTopology.Singular.Kunneth.Basic
public import TauCeti.RepresentationTheory.Homological.GroupHomology.Functoriality

/-!
# The classifying space of a product of groups

For groups `G` and `H`, the two coordinate projections of `G × H` induce maps of Milnor
classifying spaces, which together form the comparison map

`B(G × H) ⟶ BG × BH`

(`TauCeti.classifyingSpaceProdMap`). Both sides are Eilenberg--Mac Lane spaces of type
`K(G × H, 1)`, and under the identifications of their fundamental groups with `G × H` the comparison
map induces the identity
(`TauCeti.classifyingSpaceFundamentalGroupMulEquiv_prodCongr_prodMulEquiv_mapOfEq`). So it is a weak
homotopy equivalence (`TauCeti.isWeakHomotopyEquivalence_classifyingSpaceProdMap`) and induces
isomorphisms on singular homology with coefficients in any commutative ring.

Over a commutative semisimple ring `k`, for instance a field, the Künneth theorem then computes the
homology of `B(G × H)` from those of `BG` and `BH`
(`TauCeti.classifyingSpaceProdSingularHomologyIso`):

`Hₙ(B(G × H); k) ≅ ⨁_{p + q = n} Hₚ(BG; k) ⊗ H_q(BH; k)`.

In particular, if `BG` and `BH` have the `k`-homology of a point, so does `B(G × H)`
(`TauCeti.subsingleton_classifyingSpace_prod_singularHomology`), and the same holds for the group
homology of `G × H` with trivial coefficients `k`
(`TauCeti.subsingleton_groupHomology_prod`). With `k = 𝔽₂` this is the step from finitely many
mod-two acyclic factors to their product in the proof that `K(A, 1) = B(Multiplicative A)` is
mod-two acyclic for every `ℤ[1/2]`-module `A`: a finitely generated `ℤ[1/2]`-module is a finite
product of copies of `ℤ[1/2]` and of finite cyclic groups of odd order.

## Main declarations

* `TauCeti.classifyingSpaceProdMap`: the comparison map `B(G × H) ⟶ BG × BH`.
* `TauCeti.isWeakHomotopyEquivalence_classifyingSpaceProdMap`: it is a weak homotopy equivalence.
* `TauCeti.isIso_singularHomologyMap_classifyingSpaceProdMap`: it induces isomorphisms on singular
  homology.
* `TauCeti.classifyingSpaceProdSingularHomologyIso`: the Künneth formula for `B(G × H)` over a
  commutative semisimple ring.
* `TauCeti.subsingleton_classifyingSpace_prod_singularHomology` and
  `TauCeti.subsingleton_groupHomology_prod`: products of acyclic groups are acyclic.
* `TauCeti.subsingleton_groupHomology_multiplicative_prod`: the same for products of abelian
  groups, written additively.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 1.B, and
  Section 3.B, the Künneth formula.
* J.-P. Serre, *Groupes d'homotopie et classes de groupes abéliens*, Ann. of Math. 58 (1953),
  258--294.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory AlgebraicTopology

universe u

namespace TauCeti

variable (G H : Type u) [Group G] [Group H]

/-- The comparison map `B(G × H) ⟶ BG × BH` of Milnor classifying spaces, whose coordinates are
the maps induced by the two coordinate projections of `G × H`. -/
def classifyingSpaceProdMap :
    C(classifyingSpace (G × H), classifyingSpace G × classifyingSpace H) :=
  (MonoidHom.fst G H).classifyingSpaceMap.prodMk (MonoidHom.snd G H).classifyingSpaceMap

@[simp]
theorem classifyingSpaceProdMap_apply (x : classifyingSpace (G × H)) :
    classifyingSpaceProdMap G H x =
      ((MonoidHom.fst G H).classifyingSpaceMap x, (MonoidHom.snd G H).classifyingSpaceMap x) :=
  (rfl)

/-- The comparison map preserves the chosen base points. -/
theorem classifyingSpaceProdMap_basepoint :
    classifyingSpaceProdMap G H (classifyingSpaceBasepoint (G × H)) =
      (classifyingSpaceBasepoint G, classifyingSpaceBasepoint H) := by
  simp

/-- **The comparison map induces the identity on fundamental groups.** Under the identifications
`classifyingSpaceFundamentalGroupMulEquiv` of the fundamental groups of the classifying spaces with
the groups, and the identification `FundamentalGroup.prodMulEquiv` of the fundamental group of a
product, the map induced by `classifyingSpaceProdMap G H` is the identity of `G × H`. -/
theorem classifyingSpaceFundamentalGroupMulEquiv_prodCongr_prodMulEquiv_mapOfEq
    (γ : FundamentalGroup (classifyingSpace (G × H)) (classifyingSpaceBasepoint (G × H))) :
    ((classifyingSpaceFundamentalGroupMulEquiv G).prodCongr
        (classifyingSpaceFundamentalGroupMulEquiv H))
      (FundamentalGroup.prodMulEquiv _ _
        (FundamentalGroup.mapOfEq (classifyingSpaceProdMap G H)
          (classifyingSpaceProdMap_basepoint G H) γ)) =
      classifyingSpaceFundamentalGroupMulEquiv (G × H) γ := by
  -- Each coordinate of the comparison map is the map induced by a coordinate projection.
  have hfst : FundamentalGroup.map ContinuousMap.fst _
      (FundamentalGroup.mapOfEq (classifyingSpaceProdMap G H)
        (classifyingSpaceProdMap_basepoint G H) γ) =
      FundamentalGroup.mapOfEq (MonoidHom.fst G H).classifyingSpaceMap
        (MonoidHom.fst G H).classifyingSpaceMap_basepoint γ := by
    rw [← FundamentalGroup.mapOfEq_rfl, FundamentalGroup.mapOfEq_comp]
    exact FundamentalGroup.mapOfEq_congr (ContinuousMap.ext fun _ ↦ rfl) _ _ γ
  have hsnd : FundamentalGroup.map ContinuousMap.snd _
      (FundamentalGroup.mapOfEq (classifyingSpaceProdMap G H)
        (classifyingSpaceProdMap_basepoint G H) γ) =
      FundamentalGroup.mapOfEq (MonoidHom.snd G H).classifyingSpaceMap
        (MonoidHom.snd G H).classifyingSpaceMap_basepoint γ := by
    rw [← FundamentalGroup.mapOfEq_rfl, FundamentalGroup.mapOfEq_comp]
    exact FundamentalGroup.mapOfEq_congr (ContinuousMap.ext fun _ ↦ rfl) _ _ γ
  rw [FundamentalGroup.prodMulEquiv_apply, hfst, hsnd]
  exact Prod.ext ((MonoidHom.fst G H).classifyingSpaceFundamentalGroupMulEquiv_mapOfEq γ)
    ((MonoidHom.snd G H).classifyingSpaceFundamentalGroupMulEquiv_mapOfEq γ)

/-- **`B(G × H)` is weakly equivalent to `BG × BH`.** Both are aspherical, and the comparison map
induces the identity of `G × H` on fundamental groups. -/
theorem isWeakHomotopyEquivalence_classifyingSpaceProdMap :
    (classifyingSpaceProdMap G H).IsWeakHomotopyEquivalence := by
  refine (IsAspherical.isWeakHomotopyEquivalence_iff
    (isEilenbergMacLaneSpaceOne_classifyingSpace (G × H)).isAspherical
    ((isEilenbergMacLaneSpaceOne_classifyingSpace G).isAspherical.prod
      (isEilenbergMacLaneSpaceOne_classifyingSpace H).isAspherical)
    (classifyingSpaceProdMap_basepoint G H)).mpr ?_
  -- The induced map is the composite of the identifications of both sides with `G × H`.
  have h : ⇑(FundamentalGroup.mapOfEq (classifyingSpaceProdMap G H)
      (classifyingSpaceProdMap_basepoint G H)) =
      ((FundamentalGroup.prodMulEquiv _ _).trans
        ((classifyingSpaceFundamentalGroupMulEquiv G).prodCongr
          (classifyingSpaceFundamentalGroupMulEquiv H))).symm ∘
        classifyingSpaceFundamentalGroupMulEquiv (G × H) := by
    funext γ
    rw [Function.comp_apply, MulEquiv.eq_symm_apply, MulEquiv.trans_apply,
      classifyingSpaceFundamentalGroupMulEquiv_prodCongr_prodMulEquiv_mapOfEq]
  rw [h]
  exact (MulEquiv.bijective _).comp (MulEquiv.bijective _)

/-- The comparison map `B(G × H) ⟶ BG × BH` induces isomorphisms on singular homology with
coefficients in any commutative ring. -/
theorem isIso_singularHomologyMap_classifyingSpaceProdMap (k : Type u) [CommRing k] (n : ℕ) :
    IsIso (((singularHomologyFunctor (ModuleCat.{u} k) n).obj (ModuleCat.of k k)).map
      (TopCat.ofHom (classifyingSpaceProdMap G H) :
        TopCat.of (classifyingSpace (G × H)) ⟶
          TopCat.of (classifyingSpace G) ⊗ TopCat.of (classifyingSpace H))) :=
  (isWeakHomotopyEquivalence_classifyingSpaceProdMap G H).isIso_singularHomologyMap
    (ModuleCat.of k k) n

section Semisimple

variable (k : Type u) [CommRing k] [IsSemisimpleRing k]

/-- **The Künneth formula for the classifying space of a product.** Over a commutative semisimple
ring `k`, for instance a field, `Hₙ(B(G × H); k) ≅ ⨁_{p + q = n} Hₚ(BG; k) ⊗ H_q(BH; k)`, through
the comparison map `classifyingSpaceProdMap G H` and the Künneth isomorphism. -/
def classifyingSpaceProdSingularHomologyIso (n : ℕ) :
    ((singularChains k).obj (TopCat.of (classifyingSpace (G × H)))).homology n ≅
      GradedObject.Monoidal.tensorObj
        (fun p ↦ ((singularChains k).obj (TopCat.of (classifyingSpace G))).homology p)
        (fun q ↦ ((singularChains k).obj (TopCat.of (classifyingSpace H))).homology q) n :=
  -- `isIso_singularHomologyMap_classifyingSpaceProdMap` is a theorem rather than an instance,
  -- since its statement uses the monoidal product of `TopCat`, so it is supplied explicitly.
  @asIso _ _ _ _ _ (isIso_singularHomologyMap_classifyingSpaceProdMap G H k n) ≪≫
    (TopCat.singularHomologyKunnethUnitIso (TopCat.of (classifyingSpace G))
      (TopCat.of (classifyingSpace H)) n).symm

/-- The Künneth formula for `B(G × H)` is the map induced by the comparison map, followed by the
inverse of the Künneth isomorphism of `BG × BH`. -/
theorem classifyingSpaceProdSingularHomologyIso_hom (n : ℕ) :
    (classifyingSpaceProdSingularHomologyIso G H k n).hom =
      ((singularHomologyFunctor (ModuleCat.{u} k) n).obj (ModuleCat.of k k)).map
          (TopCat.ofHom (classifyingSpaceProdMap G H) :
            TopCat.of (classifyingSpace (G × H)) ⟶
              TopCat.of (classifyingSpace G) ⊗ TopCat.of (classifyingSpace H)) ≫
        (TopCat.singularHomologyKunnethUnitIso (TopCat.of (classifyingSpace G))
          (TopCat.of (classifyingSpace H)) n).inv :=
  (rfl)

/-- **A product of acyclic groups has an acyclic classifying space.** Over a commutative semisimple
ring `k`, for instance a field, if `BG` and `BH` have the `k`-homology of a point, then so does
`B(G × H)`. -/
theorem subsingleton_classifyingSpace_prod_singularHomology
    (hG : ∀ n, Subsingleton
      (((singularChains k).obj (TopCat.of (classifyingSpace G))).homology (n + 1)))
    (hH : ∀ n, Subsingleton
      (((singularChains k).obj (TopCat.of (classifyingSpace H))).homology (n + 1)))
    (n : ℕ) :
    Subsingleton
      (((singularChains k).obj (TopCat.of (classifyingSpace (G × H)))).homology (n + 1)) := by
  refine ModuleCat.subsingleton_of_isZero (IsZero.of_iso ?_
    (@asIso _ _ _ _ _ (isIso_singularHomologyMap_classifyingSpaceProdMap G H k (n + 1))))
  exact TopCat.isZero_singularHomology_tensor _ _
    (fun p ↦ @ModuleCat.isZero_of_subsingleton _ _ _ (hG p))
    (fun q ↦ @ModuleCat.isZero_of_subsingleton _ _ _ (hH q)) n

/-- **A product of acyclic groups is acyclic.** Over a commutative semisimple ring `k`, for
instance a field, if the group homology of `G` and of `H` with trivial coefficients `k` vanishes in
every positive degree, then so does that of `G × H`. -/
theorem subsingleton_groupHomology_prod
    (hG : ∀ n, Subsingleton (groupHomology (Rep.trivial k G k) (n + 1)))
    (hH : ∀ n, Subsingleton (groupHomology (Rep.trivial k H k) (n + 1))) (n : ℕ) :
    Subsingleton (groupHomology (Rep.trivial k (G × H) k) (n + 1)) :=
  -- Transport along the identifications `Hₙ(BG; k) ≅ Hₙ(G, k)` of all three groups.
  have := subsingleton_classifyingSpace_prod_singularHomology G H k
    (fun n ↦ (classifyingSpaceSingularHomologyIsoGroupHomology k G (n + 1)).toLinearEquiv
      |>.toEquiv.subsingleton)
    (fun n ↦ (classifyingSpaceSingularHomologyIsoGroupHomology k H (n + 1)).toLinearEquiv
      |>.toEquiv.subsingleton)
    n
  (classifyingSpaceSingularHomologyIsoGroupHomology k (G × H) (n + 1)).symm.toLinearEquiv
    |>.toEquiv.subsingleton

/-- The additive form of `TauCeti.subsingleton_groupHomology_prod`: over a commutative semisimple
ring `k`, a product of abelian groups that are acyclic with trivial coefficients `k` is acyclic. -/
theorem subsingleton_groupHomology_multiplicative_prod {M N : Type u} [AddCommGroup M]
    [AddCommGroup N]
    (hM : ∀ n, Subsingleton (groupHomology (Rep.trivial k (Multiplicative M) k) (n + 1)))
    (hN : ∀ n, Subsingleton (groupHomology (Rep.trivial k (Multiplicative N) k) (n + 1)))
    (n : ℕ) : Subsingleton (groupHomology (Rep.trivial k (Multiplicative (M × N)) k) (n + 1)) :=
  have := subsingleton_groupHomology_prod (Multiplicative M) (Multiplicative N) k hM hN n
  (MulEquiv.prodMultiplicative M N).subsingleton_groupHomology

end Semisimple

end TauCeti

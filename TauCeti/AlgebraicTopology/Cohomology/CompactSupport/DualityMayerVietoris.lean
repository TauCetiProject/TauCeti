/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.HasGroupoid
public import TauCeti.AlgebraicTopology.Cohomology.CompactSupport.Duality
public import TauCeti.AlgebraicTopology.Cohomology.CompactSupport.MayerVietoris
public import TauCeti.AlgebraicTopology.SimplicialSet.Homology.MayerVietoris

/-!
# The duality map and the Mayer–Vietoris maps of open subsets

Let `M` be an `n`-manifold without boundary with an orientation `o`, let `L` be an abelian group,
and orient every open subset `W ⊆ M` by the restriction of `o`
(`TauCeti.HomologicalOrientation.comap`). Hatcher's proof of Poincaré duality for noncompact
manifolds (Lemma 3.36) compares, for open sets `U` and `V` of `M`, the Mayer–Vietoris sequence of
cohomology with compact supports with the Mayer–Vietoris sequence of singular homology through the
duality maps `D_W : Hᵖ_c(W; L) ⟶ H_q(W; L)`, `p + q = n`, of `U ∩ V`, `U`, `V` and `M`:

```
Hᵖ_c(U ∩ V) ⟶ Hᵖ_c(U) ⊞ Hᵖ_c(V) ⟶ Hᵖ_c(M) ⟶ Hᵖ⁺¹_c(U ∩ V)
     ↓                ↓                ↓              ↓
H_q(U ∩ V)  ⟶  H_q(U) ⊞ H_q(V)  ⟶  H_q(M)  ⟶  H_{q-1}(U ∩ V)
```

This file proves that the first two squares commute
(`TauCeti.HomologicalOrientation.compactSupportCohomologyMayerVietorisToBiprod_dualityMap` and
`TauCeti.HomologicalOrientation.compactSupportCohomologyMayerVietorisFromBiprod_dualityMap`). The
maps of both rows have the same signs: the first has components the maps induced by the inclusion
into `U` and minus the maps induced by the inclusion into `V`, the second is the sum of the maps
induced by the inclusions. Both squares are therefore componentwise instances of the naturality of
the duality map along open embeddings
(`TauCeti.HomologicalOrientation.compactSupportCohomologyExtend_dualityMap`), applied to the
inclusions of open subsets
(`TauCeti.HomologicalOrientation.compactSupportCohomologyExtend_inclusion'_dualityMap` and
`TauCeti.HomologicalOrientation.compactSupportCohomologyExtend_toTopCat_map_dualityMap`), once
the restriction of `o` to `W` and then to `V ⊆ W` is identified with its restriction to `V`
(`TauCeti.HomologicalOrientation.comap_comap_toTopCat_map`).

## Main results

* `TauCeti.HomologicalOrientation.compactSupportCohomologyExtend_toTopCat_map_dualityMap`:
  naturality of the duality maps for open sets `V ⊆ W` of `M`.
* `TauCeti.HomologicalOrientation.compactSupportCohomologyMayerVietorisToBiprod_dualityMap`: the
  square at `Hᵖ_c(U ∩ V) ⟶ Hᵖ_c(U) ⊞ Hᵖ_c(V)`.
* `TauCeti.HomologicalOrientation.compactSupportCohomologyMayerVietorisFromBiprod_dualityMap`:
  the square at `Hᵖ_c(U) ⊞ Hᵖ_c(V) ⟶ Hᵖ_c(M)`.

## Implementation notes

The open subsets are taken in `Opens (TopCat.of M)`, as for the Mayer–Vietoris sequence of
cohomology with compact supports (`TopCat.compactSupportCohomologyMayerVietorisToBiprod`), and
inherit the charted space structure of `M`
(`TopologicalSpace.Opens.instChartedSpaceToTopCatObj`). The homology row is written with the maps
of the Mayer–Vietoris sequence of simplicial sets (`SSet.mayerVietorisToBiprod` and
`SSet.mayerVietorisFromBiprod`), which are the first two maps of the Mayer–Vietoris sequence of
singular homology (`TopCat.mayerVietoris_exact₂`).

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3, the diagram of Mayer–Vietoris sequences in the proof of Lemma 3.36.
-/

public section

noncomputable section

open CategoryTheory Limits TopologicalSpace Topology Opens

namespace TopologicalSpace.Opens

/-- An open subset of a charted space, viewed as an object of `TopCat`, is a charted space. -/
instance instChartedSpaceToTopCatObj {H M : Type*} [TopologicalSpace H] [TopologicalSpace M]
    [ChartedSpace H M] (W : Opens (TopCat.of M)) :
    ChartedSpace H ((toTopCat (TopCat.of M)).obj W) :=
  TopologicalSpace.Opens.instChartedSpace (H := H) (M := M) W

end TopologicalSpace.Opens

namespace TauCeti

attribute [local instance] MonoidalPreadditive.monoidalLinearInt

namespace HomologicalOrientation

variable {M E : Type} [TopologicalSpace M] [T2Space M]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]
  {n : ℕ} (o : HomologicalOrientation M E n) (hn : Module.finrank ℝ E = n) (L : ModuleCat.{0} ℤ)

variable {p q : ℕ} (h : p + q = n)

/-- **Naturality of the duality map for an open subset**: for an open `W ⊆ M`, oriented by the
restriction of `o`, extending compactly supported classes from `W` to `M` and then applying the
duality map of `M` is applying the duality map of `W` and then pushing forward along the
inclusion. -/
@[reassoc]
theorem compactSupportCohomologyExtend_inclusion'_dualityMap (W : Opens (TopCat.of M)) :
    TopCat.compactSupportCohomologyExtend W.isOpenEmbedding p ≫ o.dualityMap hn L p q h =
      (o.comap W.isOpenEmbedding).dualityMap hn L p q h ≫
        ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) q).obj L).map
          (Opens.inclusion' W) :=
  o.compactSupportCohomologyExtend_dualityMap hn L (j := (Opens.inclusion' W).hom)
    W.isOpenEmbedding p q h

/-- Restricting the orientation of `M` to an open `W` and then to an open `V ⊆ W` is restricting
it to `V`. -/
lemma comap_comap_toTopCat_map {V W : Opens (TopCat.of M)} (hVW : V ≤ W) :
    (o.comap W.isOpenEmbedding).comap (isOpenEmbedding_toTopCat_map (homOfLE hVW)) =
      o.comap V.isOpenEmbedding := by
  rw [comap_comap]
  exact o.comap_congr _ _ rfl

/-- **Naturality of the duality map for nested open subsets**: for opens `V ⊆ W` of `M`, oriented
by the restrictions of `o`, extending compactly supported classes from `V` to `W` intertwines the
duality maps of `V` and `W` with the pushforward along the inclusion. -/
@[reassoc]
theorem compactSupportCohomologyExtend_toTopCat_map_dualityMap {V W : Opens (TopCat.of M)}
    (hVW : V ≤ W) :
    TopCat.compactSupportCohomologyExtend (isOpenEmbedding_toTopCat_map (homOfLE hVW)) p ≫
        (o.comap W.isOpenEmbedding).dualityMap hn L p q h =
      (o.comap V.isOpenEmbedding).dualityMap hn L p q h ≫
        ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) q).obj L).map
          ((Opens.toTopCat (TopCat.of M)).map (homOfLE hVW)) := by
  have := (o.comap W.isOpenEmbedding).compactSupportCohomologyExtend_dualityMap hn L
    (j := ((Opens.toTopCat (TopCat.of M)).map (homOfLE hVW)).hom)
    (isOpenEmbedding_toTopCat_map (homOfLE hVW)) p q h
  rwa [comap_comap_toTopCat_map] at this

variable (U V : Opens (TopCat.of M))

/-- **The duality maps commute with the first Mayer–Vietoris maps**: for opens `U` and `V` of
`M`, the map `Hᵖ_c(U ∩ V) ⟶ Hᵖ_c(U) ⊞ Hᵖ_c(V)` of the Mayer–Vietoris sequence of cohomology with
compact supports, followed by the duality maps of `U` and `V`, is the duality map of `U ∩ V`
followed by the map `H_q(U ∩ V) ⟶ H_q(U) ⊞ H_q(V)` of the Mayer–Vietoris sequence of singular
homology. Both maps have components the map induced by the inclusion into `U` and minus the map
induced by the inclusion into `V`. -/
@[reassoc]
theorem compactSupportCohomologyMayerVietorisToBiprod_dualityMap :
    TopCat.compactSupportCohomologyMayerVietorisToBiprod (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ L U V p ≫
        biprod.map ((o.comap U.isOpenEmbedding).dualityMap hn L p q h)
          ((o.comap V.isOpenEmbedding).dualityMap hn L p q h) =
      (o.comap (U ⊓ V).isOpenEmbedding).dualityMap hn L p q h ≫
        SSet.mayerVietorisToBiprod L
          (TopCat.toSSet.map ((Opens.toTopCat (TopCat.of M)).map (homOfLE inf_le_left)))
          (TopCat.toSSet.map ((Opens.toTopCat (TopCat.of M)).map (homOfLE inf_le_right))) q := by
  refine biprod.hom_ext _ _ ?_ ?_
  · refine (Category.assoc _ _ _).trans (Eq.trans ?_ (Category.assoc _ _ _).symm)
    -- The duality map of `W` lands in the homology of `TopCat.of W`, which is the homology of the
    -- object `W` of `TopCat` only up to unfolding, so `rw` cannot rewrite the composites.
    erw [biprod.map_fst, SSet.mayerVietorisToBiprod_fst,
      TopCat.compactSupportCohomologyMayerVietorisToBiprod_fst_assoc]
    exact o.compactSupportCohomologyExtend_toTopCat_map_dualityMap hn L h inf_le_left
  · refine (Category.assoc _ _ _).trans (Eq.trans ?_ (Category.assoc _ _ _).symm)
    erw [biprod.map_snd, SSet.mayerVietorisToBiprod_snd,
      TopCat.compactSupportCohomologyMayerVietorisToBiprod_snd_assoc, Preadditive.neg_comp,
      Preadditive.comp_neg, neg_inj]
    exact o.compactSupportCohomologyExtend_toTopCat_map_dualityMap hn L h inf_le_right

/-- **The duality maps commute with the second Mayer–Vietoris maps**: for opens `U` and `V` of
`M`, the map `Hᵖ_c(U) ⊞ Hᵖ_c(V) ⟶ Hᵖ_c(M)` of the Mayer–Vietoris sequence of cohomology with
compact supports, followed by the duality map of `M`, is the duality maps of `U` and `V` followed
by the map `H_q(U) ⊞ H_q(V) ⟶ H_q(M)` of the Mayer–Vietoris sequence of singular homology. Both
maps are the sums of the maps induced by the inclusions. -/
@[reassoc]
theorem compactSupportCohomologyMayerVietorisFromBiprod_dualityMap :
    TopCat.compactSupportCohomologyMayerVietorisFromBiprod (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ L U V
        p ≫ o.dualityMap hn L p q h =
      biprod.map ((o.comap U.isOpenEmbedding).dualityMap hn L p q h)
          ((o.comap V.isOpenEmbedding).dualityMap hn L p q h) ≫
        SSet.mayerVietorisFromBiprod L (TopCat.toSSet.map (Opens.inclusion' U))
          (TopCat.toSSet.map (Opens.inclusion' V)) q := by
  refine biprod.hom_ext' _ _ ?_ ?_
  · refine (TopCat.inl_compactSupportCohomologyMayerVietorisFromBiprod_assoc _ _ _ _ _ _ _).trans
      (Eq.trans ?_ (Category.assoc _ _ _))
    -- As in `compactSupportCohomologyMayerVietorisToBiprod_dualityMap`, `rw` cannot rewrite here.
    erw [biprod.inl_map, Category.assoc, SSet.inl_mayerVietorisFromBiprod]
    exact o.compactSupportCohomologyExtend_inclusion'_dualityMap hn L h U
  · refine (TopCat.inr_compactSupportCohomologyMayerVietorisFromBiprod_assoc _ _ _ _ _ _ _).trans
      (Eq.trans ?_ (Category.assoc _ _ _))
    erw [biprod.inr_map, Category.assoc, SSet.inr_mayerVietorisFromBiprod]
    exact o.compactSupportCohomologyExtend_inclusion'_dualityMap hn L h V

end HomologicalOrientation

end TauCeti

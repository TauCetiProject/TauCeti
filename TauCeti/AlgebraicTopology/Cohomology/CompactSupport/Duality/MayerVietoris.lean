/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.CompactSupport.Duality.Basic
public import TauCeti.AlgebraicTopology.Cohomology.CompactSupport.MayerVietoris
public import TauCeti.AlgebraicTopology.SimplicialSet.Homology.MayerVietoris

/-!
# The duality map and the Mayer–Vietoris maps of open subsets

Let `M` be an `n`-manifold without boundary with an orientation `o`, let `L` be an abelian group,
and orient every open subset `W ⊆ M` by the restriction of `o`
(`TauCeti.HomologicalOrientation.comap`). Hatcher's proof of Poincaré duality for noncompact
manifolds (Lemma 3.36) compares, for open sets `U` and `V` of `M` with `U ∪ V = M`, the
Mayer–Vietoris sequence of cohomology with compact supports with the Mayer–Vietoris sequence of
singular homology through the duality maps `D_W : Hᵖ_c(W; L) ⟶ H_q(W; L)`, `p + q = n`, of `U ∩ V`,
`U`, `V` and `M`:

```
Hᵖ_c(U ∩ V) ⟶ Hᵖ_c(U) ⊞ Hᵖ_c(V) ⟶ Hᵖ_c(M) ⟶ Hᵖ⁺¹_c(U ∩ V)
     ↓                ↓                ↓              ↓
H_q(U ∩ V)  ⟶  H_q(U) ⊞ H_q(V)  ⟶  H_q(M)  ⟶  H_{q-1}(U ∩ V)
```

The rows are the Mayer–Vietoris sequences of the cover `M = U ∪ V`, and their exactness uses that
cover assumption. This file proves that the first two squares commute
(`TauCeti.HomologicalOrientation.compactSupportCohomologyMayerVietorisToBiprod_dualityMap` and
`TauCeti.HomologicalOrientation.compactSupportCohomologyMayerVietorisFromBiprod_dualityMap`). The
maps of both rows have the same signs: the first has components the maps induced by the inclusion
into `U` and minus the maps induced by the inclusion into `V`, the second is the sum of the maps
induced by the inclusions. The two squares commute for arbitrary opens `U` and `V`, without the
cover assumption: they are componentwise instances of the naturality of the duality map along open
embeddings
(`TauCeti.HomologicalOrientation.compactSupportCohomologyExtend_dualityMap`), applied to the
inclusions of open subsets
(`TauCeti.HomologicalOrientation.compactSupportCohomologyExtend_inclusion'_dualityMap` and
`TauCeti.HomologicalOrientation.compactSupportCohomologyExtend_toTopCat_map_dualityMap`).

## Main results

* `TauCeti.HomologicalOrientation.compactSupportCohomologyMayerVietorisToBiprod_dualityMap`: the
  square at `Hᵖ_c(U ∩ V) ⟶ Hᵖ_c(U) ⊞ Hᵖ_c(V)`, for arbitrary opens `U` and `V`.
* `TauCeti.HomologicalOrientation.compactSupportCohomologyMayerVietorisFromBiprod_dualityMap`:
  the square at `Hᵖ_c(U) ⊞ Hᵖ_c(V) ⟶ Hᵖ_c(M)`, for arbitrary opens `U` and `V`.

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

namespace TauCeti

attribute [local instance] MonoidalPreadditive.monoidalLinearInt

namespace HomologicalOrientation

variable {M E : Type} [TopologicalSpace M] [T2Space M]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]
  {n : ℕ} (o : HomologicalOrientation M E n) (hn : Module.finrank ℝ E = n) (L : ModuleCat.{0} ℤ)

variable {p q : ℕ} (h : p + q = n)

variable (U V : Opens (TopCat.of M))

/-- **The duality maps commute with the first Mayer–Vietoris maps**: for any opens `U` and `V` of
`M`, not necessarily covering `M`, the map `Hᵖ_c(U ∩ V) ⟶ Hᵖ_c(U) ⊞ Hᵖ_c(V)` of the Mayer–Vietoris
sequence of cohomology with compact supports, followed by the duality maps of `U` and `V`, is the
duality map of `U ∩ V` followed by the map `H_q(U ∩ V) ⟶ H_q(U) ⊞ H_q(V)` of the Mayer–Vietoris
sequence of singular homology. Both maps have components the map induced by the inclusion into `U`
and minus the map induced by the inclusion into `V`. -/
@[reassoc]
theorem compactSupportCohomologyMayerVietorisToBiprod_dualityMap :
    TopCat.compactSupportCohomologyMayerVietorisToBiprod (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ L U V p ≫
        biprod.map ((o.comap U.isOpenEmbedding).dualityMap hn L p q h)
          ((o.comap V.isOpenEmbedding).dualityMap hn L p q h) =
      (o.comap (U ⊓ V).isOpenEmbedding).dualityMap hn L p q h ≫
        SSet.mayerVietorisToBiprod L
          (TopCat.toSSet.map ((Opens.toTopCat (TopCat.of M)).map (homOfLE inf_le_left)))
          (TopCat.toSSet.map ((Opens.toTopCat (TopCat.of M)).map (homOfLE inf_le_right))) q := by
  apply biprod.hom_ext
  · rw [Category.assoc, biprod.map_fst,
      TopCat.compactSupportCohomologyMayerVietorisToBiprod_fst_assoc,
      compactSupportCohomologyExtend_toTopCat_map_dualityMap, singularHomologyFunctor_obj_map]
    -- The duality map lands in `((singularHomologyFunctor _ q).obj L).obj X`, which is
    -- `(TopCat.toSSet.obj X).homology L q` only after unfolding `singularHomologyFunctor`, so the
    -- composite on the right is type-correct only up to that unfolding: `rw` cannot reassociate
    -- it, and `erw` is needed for these two steps.
    erw [Category.assoc, SSet.mayerVietorisToBiprod_fst]
  · rw [Category.assoc, biprod.map_snd,
      TopCat.compactSupportCohomologyMayerVietorisToBiprod_snd_assoc, Preadditive.neg_comp,
      compactSupportCohomologyExtend_toTopCat_map_dualityMap, singularHomologyFunctor_obj_map]
    -- As in the first component, only up to unfolding `singularHomologyFunctor`.
    erw [Category.assoc, SSet.mayerVietorisToBiprod_snd, Preadditive.comp_neg]

/-- **The duality maps commute with the second Mayer–Vietoris maps**: for any opens `U` and `V` of
`M`, not necessarily covering `M`, the map `Hᵖ_c(U) ⊞ Hᵖ_c(V) ⟶ Hᵖ_c(M)` of the Mayer–Vietoris
sequence of cohomology with compact supports, followed by the duality map of `M`, is the duality
maps of `U` and `V` followed by the map `H_q(U) ⊞ H_q(V) ⟶ H_q(M)` of the Mayer–Vietoris sequence of
singular homology. Both maps are the sums of the maps induced by the inclusions. -/
@[reassoc]
theorem compactSupportCohomologyMayerVietorisFromBiprod_dualityMap :
    TopCat.compactSupportCohomologyMayerVietorisFromBiprod (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ L U V
        p ≫ o.dualityMap hn L p q h =
      biprod.map ((o.comap U.isOpenEmbedding).dualityMap hn L p q h)
          ((o.comap V.isOpenEmbedding).dualityMap hn L p q h) ≫
        SSet.mayerVietorisFromBiprod L (TopCat.toSSet.map (Opens.inclusion' U))
          (TopCat.toSSet.map (Opens.inclusion' V)) q := by
  apply biprod.hom_ext'
  · rw [TopCat.inl_compactSupportCohomologyMayerVietorisFromBiprod_assoc,
      compactSupportCohomologyExtend_inclusion'_dualityMap, singularHomologyFunctor_obj_map]
    -- As in `compactSupportCohomologyMayerVietorisToBiprod_dualityMap`, the composite on the right
    -- is type-correct only up to unfolding `singularHomologyFunctor`.
    erw [biprod.inl_map_assoc, SSet.inl_mayerVietorisFromBiprod]
  · rw [TopCat.inr_compactSupportCohomologyMayerVietorisFromBiprod_assoc,
      compactSupportCohomologyExtend_inclusion'_dualityMap, singularHomologyFunctor_obj_map]
    erw [biprod.inr_map_assoc, SSet.inr_mayerVietorisFromBiprod]

end HomologicalOrientation

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Cap.MayerVietoris.Basic
public import TauCeti.AlgebraicTopology.Cohomology.CompactSupport.Duality.Basic
public import TauCeti.AlgebraicTopology.Cohomology.CompactSupport.MayerVietoris
public import TauCeti.AlgebraicTopology.SimplicialSet.Homology.MayerVietoris

import Mathlib.Algebra.FiveLemma

/-!
# The duality map and the Mayer–Vietoris sequences of open subsets

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

The third square, at the connecting maps, commutes up to the sign `(-1) ^ (p + 1)`
(`TauCeti.HomologicalOrientation.dualityMap_mayerVietorisδ`). With all three squares, the five
lemma gives the inductive step of Poincaré duality: if the duality maps of `U`, `V` and `U ∩ V` are
bijective in every degree, so is that of `M`
(`TauCeti.HomologicalOrientation.bijective_dualityMap_of_sup_eq_top`). At the end of the sequences,
in degree `p = n`, the homology row stops at `H₀(M)`, onto which `H₀(U) ⊞ H₀(V)` maps
surjectively, and the cohomology row continues with `Hⁿ⁺¹_c(U ∩ V)`; the five lemma then needs
`Hⁿ⁺¹_c(U ∩ V) = 0`, the degree `(n + 1, -1)` part of duality on `U ∩ V`. This vanishing passes from
`U`, `V` and `U ∩ V` to `M` by the Mayer–Vietoris sequence alone
(`TopCat.isZero_compactSupportCohomology_of_sup_eq_top`). For arbitrary open subsets `U` and `V` of
`M`, not necessarily covering it, the same holds for `U ∪ V`
(`TauCeti.HomologicalOrientation.bijective_dualityMap_comap_sup`), which is the union step of the
Mayer–Vietoris induction `TauCeti.mayerVietoris_induction`.

## Main results

* `TauCeti.HomologicalOrientation.compactSupportCohomologyMayerVietorisToBiprod_dualityMap`: the
  square at `Hᵖ_c(U ∩ V) ⟶ Hᵖ_c(U) ⊞ Hᵖ_c(V)`, for arbitrary opens `U` and `V`.
* `TauCeti.HomologicalOrientation.compactSupportCohomologyMayerVietorisFromBiprod_dualityMap`:
  the square at `Hᵖ_c(U) ⊞ Hᵖ_c(V) ⟶ Hᵖ_c(M)`, for arbitrary opens `U` and `V`.
* `TauCeti.HomologicalOrientation.bijective_dualityMap_of_sup_eq_top`: **Poincaré duality for an
  open cover by two sets**, from duality on `U`, `V` and `U ∩ V` and `Hⁿ⁺¹_c(U ∩ V) = 0`.
* `TauCeti.HomologicalOrientation.bijective_dualityMap_comap_sup`: the same for the union of two
  open subsets of `M`, with the restricted orientations.

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
  Section 3.3, the diagram of Mayer–Vietoris sequences in the proof of Lemma 3.36, and its step
  from `U`, `V` and `U ∩ V` to `U ∪ V` by the five lemma.
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


/-! ### Poincaré duality for the union of two open sets -/

section Union

variable {U V}

/-- If the duality maps of `U` and `V` are bijective, so is the map between the middle terms of the
two Mayer–Vietoris sequences that they form. -/
private lemma bijective_biprodMap_dualityMap
    (hDU : Function.Bijective ((o.comap U.isOpenEmbedding).dualityMap hn L p q h))
    (hDV : Function.Bijective ((o.comap V.isOpenEmbedding).dualityMap hn L p q h)) :
    Function.Bijective (biprod.map ((o.comap U.isOpenEmbedding).dualityMap hn L p q h)
      ((o.comap V.isOpenEmbedding).dualityMap hn L p q h)).hom := by
  have := (ConcreteCategory.isIso_iff_bijective _).2 hDU
  have := (ConcreteCategory.isIso_iff_bijective _).2 hDV
  have := isIso_of_mono_of_epi (biprod.map ((o.comap U.isOpenEmbedding).dualityMap hn L p q h)
    ((o.comap V.isOpenEmbedding).dualityMap hn L p q h))
  exact ConcreteCategory.bijective_of_isIso _

/-- `compactSupportCohomologyMayerVietorisToBiprod_dualityMap` as an equation of linear maps, the
form of the commuting squares in Mathlib's five lemma for modules. -/
private lemma toBiprod_comp_dualityMap :
    (SSet.mayerVietorisToBiprod L
        (TopCat.toSSet.map ((Opens.toTopCat (TopCat.of M)).map (homOfLE inf_le_left)))
        (TopCat.toSSet.map ((Opens.toTopCat (TopCat.of M)).map (homOfLE inf_le_right)))
        q).hom.comp ((o.comap (U ⊓ V).isOpenEmbedding).dualityMap hn L p q h).hom =
      (biprod.map ((o.comap U.isOpenEmbedding).dualityMap hn L p q h)
        ((o.comap V.isOpenEmbedding).dualityMap hn L p q h)).hom.comp
        (TopCat.compactSupportCohomologyMayerVietorisToBiprod (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ L
          U V p).hom :=
  LinearMap.ext fun x ↦ (ConcreteCategory.congr_hom
    (o.compactSupportCohomologyMayerVietorisToBiprod_dualityMap hn L h U V) x).symm

/-- `compactSupportCohomologyMayerVietorisFromBiprod_dualityMap` as an equation of linear maps. -/
private lemma fromBiprod_comp_dualityMap :
    (SSet.mayerVietorisFromBiprod L (TopCat.toSSet.map (Opens.inclusion' U))
        (TopCat.toSSet.map (Opens.inclusion' V)) q).hom.comp
        (biprod.map ((o.comap U.isOpenEmbedding).dualityMap hn L p q h)
          ((o.comap V.isOpenEmbedding).dualityMap hn L p q h)).hom =
      (o.dualityMap hn L p q h).hom.comp
        (TopCat.compactSupportCohomologyMayerVietorisFromBiprod (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ
          L U V p).hom :=
  LinearMap.ext fun x ↦ (ConcreteCategory.congr_hom
    (o.compactSupportCohomologyMayerVietorisFromBiprod_dualityMap hn L h U V) x).symm

/-- `compactSupportCohomologyMayerVietorisToBiprod_dualityMap` in degree `(p + 1, q)` as an
equation of linear maps, with both duality maps multiplied by the sign `(-1) ^ (p + 1)` of the
square of the connecting maps. -/
private lemma toBiprod_comp_neg_one_pow_zsmul_dualityMap {p q : ℕ} (h : p + 1 + q = n) :
    (SSet.mayerVietorisToBiprod L
        (TopCat.toSSet.map ((Opens.toTopCat (TopCat.of M)).map (homOfLE inf_le_left)))
        (TopCat.toSSet.map ((Opens.toTopCat (TopCat.of M)).map (homOfLE inf_le_right)))
        q).hom.comp (((-1 : ℤ) ^ (p + 1)) •
          ((o.comap (U ⊓ V).isOpenEmbedding).dualityMap hn L (p + 1) q h).hom) =
      (((-1 : ℤ) ^ (p + 1)) • (biprod.map
        ((o.comap U.isOpenEmbedding).dualityMap hn L (p + 1) q h)
        ((o.comap V.isOpenEmbedding).dualityMap hn L (p + 1) q h)).hom).comp
        (TopCat.compactSupportCohomologyMayerVietorisToBiprod (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ L
          U V (p + 1)).hom :=
  LinearMap.ext fun x ↦ (map_zsmul (SSet.mayerVietorisToBiprod L _ _ q).hom _ _).trans
    (congrArg (((-1 : ℤ) ^ (p + 1)) • ·)
      (LinearMap.congr_fun (o.toBiprod_comp_dualityMap hn L h) x))

/-- `HomologicalOrientation.dualityMap_mayerVietorisδ` as an equation of linear maps. -/
private lemma mayerVietorisδ_comp_dualityMap (hUV : U ⊔ V = ⊤) {p q : ℕ} (h : p + (q + 1) = n) :
    (TopCat.mayerVietorisδ L U.isOpen V.isOpen
        (congrArg (fun W : Opens (TopCat.of M) ↦ (W : Set (TopCat.of M))) hUV)
        (q + 1) q rfl).hom.comp (o.dualityMap hn L p (q + 1) h).hom =
      (((-1 : ℤ) ^ (p + 1)) •
        ((o.comap (U ⊓ V).isOpenEmbedding).dualityMap hn L (p + 1) q
          ((Nat.add_right_comm p 1 q).trans h)).hom).comp
        (TopCat.compactSupportCohomologyMayerVietorisδ (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ L U V
          hUV p (p + 1) rfl).hom :=
  LinearMap.ext fun x ↦
    ConcreteCategory.congr_hom (o.dualityMap_mayerVietorisδ L hn U V hUV p q h) x

/-- **Poincaré duality for the union of two open sets.** Let `M` be covered by open sets `U` and
`V`, oriented by the restrictions of `o`. If the duality maps of `U`, `V` and `U ∩ V` are bijective
in every degree and `Hⁿ⁺¹_c(U ∩ V; L)` vanishes, then the duality map
`Hᵖ_c(M; L) ⟶ H_q(M; L)`, `p + q = n`, of `M` is bijective.

The vanishing of `Hⁿ⁺¹_c(U ∩ V; L)` stands in for duality in degree `(n + 1, -1)`, where the
Mayer–Vietoris sequence of homology has ended: it is needed for `p = n`, and holds for every
`n`-manifold, as part of Poincaré duality. -/
theorem bijective_dualityMap_of_sup_eq_top (hUV : U ⊔ V = ⊤)
    (hDU : ∀ p q (h : p + q = n),
      Function.Bijective ((o.comap U.isOpenEmbedding).dualityMap hn L p q h))
    (hDV : ∀ p q (h : p + q = n),
      Function.Bijective ((o.comap V.isOpenEmbedding).dualityMap hn L p q h))
    (hDUV : ∀ p q (h : p + q = n),
      Function.Bijective ((o.comap (U ⊓ V).isOpenEmbedding).dualityMap hn L p q h))
    (hzero : IsZero (((Opens.toTopCat (TopCat.of M)).obj (U ⊓ V)).compactSupportCohomology
      (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ L (n + 1))) :
    Function.Bijective (o.dualityMap hn L p q h) := by
  have hUV' : (U : Set (TopCat.of M)) ∪ V = Set.univ :=
    congrArg (fun W : Opens (TopCat.of M) ↦ (W : Set (TopCat.of M))) hUV
  -- The two Mayer–Vietoris sequences, whose exactness is that of the rows of the five lemma.
  have hexact {S : ShortComplex (ModuleCat.{0} ℤ)} (hS : S.Exact) :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).1 hS
  have hc₁ := TopCat.compactSupportCohomologyMayerVietoris_exact₂ (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ
    L U V hUV p
  have hc₂ := TopCat.compactSupportCohomologyMayerVietoris_exact₃ (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ
    L U V hUV p (p + 1)
  rcases q with _ | q
  · -- For `q = 0` the homology sequence ends at `H₀(M)`, and `Hⁿ⁺¹_c(U ∩ V) = 0`: the rows end
    -- with surjections onto `Hⁿ_c(M)` and `H₀(M)`.
    obtain rfl : n = p := by omega
    exact LinearMap.bijective_of_surjective_of_bijective_of_right_exact _ _ _ _ _ _ _
      (o.toBiprod_comp_dualityMap hn L h) (o.fromBiprod_comp_dualityMap hn L h) (hexact hc₁)
      (hexact (TopCat.mayerVietoris_exact₂ L U.isOpen V.isOpen hUV' 0)) (hDUV n 0 h).2
      (o.bijective_biprodMap_dualityMap hn L h (hDU n 0 h) (hDV n 0 h))
      ((ModuleCat.epi_iff_surjective _).1 (hc₂.epi_f (hzero.eq_of_tgt _ _)))
      ((ModuleCat.epi_iff_surjective _).1 (TopCat.epi_mayerVietorisFromBiprod_zero L hUV'))
  · -- Otherwise the five lemma applies to the rows from `Hᵖ_c(U ∩ V)` to `Hᵖ⁺¹_c(U) ⊞ Hᵖ⁺¹_c(V)`
    -- and from `H_{q+1}(U ∩ V)` to `H_q(U) ⊞ H_q(V)`. The connecting square commutes up to the
    -- sign `(-1) ^ (p + 1)`, which is absorbed into the last two vertical maps.
    have h' : p + 1 + q = n := by omega
    exact LinearMap.bijective_of_surjective_of_bijective_of_bijective_of_injective _ _ _ _ _ _ _ _
      _ _ _ _ _ (o.toBiprod_comp_dualityMap hn L h) (o.fromBiprod_comp_dualityMap hn L h)
      (o.mayerVietorisδ_comp_dualityMap hn L hUV h)
      (o.toBiprod_comp_neg_one_pow_zsmul_dualityMap hn L h') (hexact hc₁) (hexact hc₂)
      (hexact (TopCat.compactSupportCohomologyMayerVietoris_exact₁ (ModuleCat.of ℤ (ULift.{0} ℤ))
        ℤ L U V hUV p (p + 1)))
      (hexact (TopCat.mayerVietoris_exact₂ L U.isOpen V.isOpen hUV' (q + 1)))
      (hexact (TopCat.mayerVietoris_exact₃ L U.isOpen V.isOpen hUV' (q + 1) q))
      (hexact (TopCat.mayerVietoris_exact₁ L U.isOpen V.isOpen hUV' (q + 1) q))
      (hDUV p (q + 1) h).2 (o.bijective_biprodMap_dualityMap hn L h (hDU _ _ h) (hDV _ _ h))
      (((isUnit_neg_one (α := ℤ)).pow (p + 1)).smul_bijective.comp (hDUV (p + 1) q h'))
      (((isUnit_neg_one (α := ℤ)).pow (p + 1)).smul_bijective.1.comp
        (o.bijective_biprodMap_dualityMap hn L h' (hDU _ _ h') (hDV _ _ h')).1)

/-- **Poincaré duality for the union of two open subsets.** If the duality maps of open subsets
`U`, `V` and `U ∩ V` of `M`, for the orientations pulled back from `M`, are bijective in every
degree and `Hⁿ⁺¹_c(U ∩ V; L)` vanishes, then the duality map `Hᵖ_c(U ∪ V; L) ⟶ H_q(U ∪ V; L)`,
`p + q = n`, is bijective. This is the union step of the Mayer–Vietoris induction for Poincaré
duality (`TauCeti.mayerVietoris_induction`). -/
theorem bijective_dualityMap_comap_sup {U V : Opens M}
    (hDU : ∀ p q (h : p + q = n),
      Function.Bijective ((o.comap U.isOpenEmbedding').dualityMap hn L p q h))
    (hDV : ∀ p q (h : p + q = n),
      Function.Bijective ((o.comap V.isOpenEmbedding').dualityMap hn L p q h))
    (hDUV : ∀ p q (h : p + q = n),
      Function.Bijective ((o.comap (U ⊓ V).isOpenEmbedding').dualityMap hn L p q h))
    (hzero : IsZero ((TopCat.of ↥(U ⊓ V)).compactSupportCohomology
      (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ L (n + 1))) :
    Function.Bijective ((o.comap (U ⊔ V).isOpenEmbedding').dualityMap hn L p q h) := by
  let i : C(↥(U ⊔ V), M) := ⟨Subtype.val, continuous_subtypeVal⟩
  have hinf : Opens.comap i U ⊓ Opens.comap i V = Opens.comap i (U ⊓ V) := (map_inf _ _ _).symm
  -- `U ∩ V`, read as an open subset of `U ∪ V`, is homeomorphic to `U ∩ V`, so its cohomology with
  -- compact supports vanishes in degree `n + 1` too.
  let e : ↥(Opens.comap i (U ⊓ V)) ≃ₜ ↥(U ⊓ V) :=
    { toFun x := ⟨x.val.val, x.property⟩
      invFun y := ⟨⟨y.val, (inf_le_left.trans le_sup_left : U ⊓ V ≤ U ⊔ V) y.property⟩,
        y.property⟩
      left_inv _ := rfl
      right_inv _ := rfl
      continuous_toFun := (continuous_subtypeVal.comp continuous_subtypeVal).subtype_mk _
      continuous_invFun := (continuous_subtypeVal.subtype_mk _).subtype_mk _ }
  have : IsIso (TopCat.ofHom (⟨e, e.continuous⟩ : C(_, _))) :=
    (TopCat.isIso_iff_isHomeomorph _).2 e.isHomeomorph
  have hiso := TopCat.isIso_compactSupportCohomologyExtend (R := ModuleCat.of ℤ (ULift.{0} ℤ))
    (k := ℤ) (M := L) (f := TopCat.ofHom (⟨e, e.continuous⟩ : C(_, _))) e.isOpenEmbedding (n + 1)
  refine (o.comap (U ⊔ V).isOpenEmbedding').bijective_dualityMap_of_sup_eq_top hn L h
    (U := Opens.comap i U) (V := Opens.comap i V) ?_
    (fun p q h ↦ (o.bijective_dualityMap_comap_comap_iff hn L h le_sup_left).2 (hDU p q h))
    (fun p q h ↦ (o.bijective_dualityMap_comap_comap_iff hn L h le_sup_right).2 (hDV p q h))
    (fun p q h ↦ ?_) ?_
  · rw [← map_sup, eq_top_iff]
    exact fun x _ ↦ x.property
  · rw [hinf]
    exact (o.bijective_dualityMap_comap_comap_iff hn L h (inf_le_left.trans le_sup_left)).2
      (hDUV p q h)
  · rw [hinf]
    -- The goal is stated on `(Opens.toTopCat _).obj _`, which is `TopCat.of` of the subtype only
    -- up to unfolding, so instance search does not find `hiso` and it is passed explicitly.
    exact hzero.of_iso (@asIso _ _ _ _ _ hiso)

end Union

end HomologicalOrientation

end TauCeti

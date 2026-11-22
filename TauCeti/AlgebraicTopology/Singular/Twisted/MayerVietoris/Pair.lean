/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Twisted.Small.MayerVietoris
public import TauCeti.AlgebraicTopology.Singular.Twisted.Small.QuasiIso
public import TauCeti.AlgebraicTopology.Singular.Twisted.Small.Relative
public import TauCeti.Algebra.Homology.HomologySequenceBiprod
import TauCeti.Algebra.Homology.ShortComplex.ShortExact
import TauCeti.CategoryTheory.Limits.Shapes.Biproduct

/-!
# The Mayer–Vietoris sequence of two pairs with local coefficients

Let `L` be a local coefficient system of `R`-modules on a topological space `X`, with arbitrary
module fibres over an arbitrary ring, and let `C ⊆ A` and `D ⊆ B` be subsets of `X`. Write
`Hₙ(A, C; L)` for the relative twisted homology of the pair `(A, C)` with `L` restricted to `A`.
When `A` and `B` are open in `A ∪ B` and `C` and `D` are open in `C ∪ D`, this file constructs the
Mayer–Vietoris long exact sequence of the two pairs,
```
⋯ ⟶ Hₙ(A ∩ B, C ∩ D; L) ⟶ Hₙ(A, C; L) ⊞ Hₙ(B, D; L) ⟶ Hₙ(A ∪ B, C ∪ D; L)
  ⟶ Hₙ₋₁(A ∩ B, C ∩ D; L) ⟶ ⋯,
```
whose first map is `(i_A, -i_B)` and whose second map is `j_A + j_B`, the `i` and `j` being induced
by the inclusions of pairs (`TauCeti.LocalCoefficientSystem.subsetPairTwistedChainComplexMap`).

For the restrictions `(E|_U, E₀|_U)` and `(E|_V, E₀|_V)` of a pair over two open sets of a base,
such as the Thom pair of a vector bundle over two trivializing open sets, this is the sequence that
assembles the relative homology with local coefficients over `U ∪ V` from its pieces. It is the
local-coefficient counterpart of `TopCat.pairMayerVietorisδ`.

The relative twisted chains of `(A, C)` are the quotient of the twisted chains of `X` supported in
`A` by those supported in `C`
(`TauCeti.LocalCoefficientSystem.isColimitSubsetPairTwistedChainComplexπ`). So the chain-level
sequence is the cokernel of the morphism from the absolute Mayer–Vietoris short exact sequence of
twisted chains supported in `C ∩ D`, `C` and `D`, and subordinate to `{C, D}`, to the one for `A`
and `B`
(`TauCeti.LocalCoefficientSystem.shortExact_smallTwistedMayerVietorisShortComplex`). Its last
component is a monomorphism, so the cokernel is short exact by the snake lemma
(`CategoryTheory.ShortComplex.ShortExact.of_isColimit_cokernelCofork`). Its last term, the chains
subordinate to `{A, B}` modulo those subordinate to `{C, D}`, is compared with the relative chains
of `(A ∪ B, C ∪ D)` by the small-chain theorem inside a subset
(`TauCeti.LocalCoefficientSystem.quasiIso_smallTwistedChainComplexInclusion`) and the five lemma.

## Main definitions and results

* `TauCeti.LocalCoefficientSystem.pairTwistedMayerVietorisToBiprod`,
  `TauCeti.LocalCoefficientSystem.pairTwistedMayerVietorisFromBiprod`: the maps
  `Hₙ(A ∩ B, C ∩ D; L) ⟶ Hₙ(A, C; L) ⊞ Hₙ(B, D; L)` and
  `Hₙ(A, C; L) ⊞ Hₙ(B, D; L) ⟶ Hₙ(A ∪ B, C ∪ D; L)`.
* `TauCeti.LocalCoefficientSystem.pairTwistedMayerVietorisδ`: the connecting morphism
  `Hₙ(A ∪ B, C ∪ D; L) ⟶ Hₘ(A ∩ B, C ∩ D; L)`, `m + 1 = n`.
* `TauCeti.LocalCoefficientSystem.pairTwistedMayerVietoris_exact₁`,
  `pairTwistedMayerVietoris_exact₂`, `pairTwistedMayerVietoris_exact₃`: exactness at
  `Hₘ(A ∩ B, C ∩ D; L)`, at `Hₙ(A, C; L) ⊞ Hₙ(B, D; L)` and at `Hₙ(A ∪ B, C ∪ D; L)`.
* `TauCeti.LocalCoefficientSystem.epi_pairTwistedMayerVietorisFromBiprod_zero` and
  `TauCeti.LocalCoefficientSystem.mono_pairTwistedMayerVietorisToBiprod`: surjectivity at the
  degree-zero end, and injectivity of the first map when `Hₖ₊₁(A ∪ B, C ∪ D; L)` vanishes.
* `TauCeti.LocalCoefficientSystem.isZero_twistedHomology_ofInclusion_union`: `Hₙ(A ∪ B, C ∪ D; L)`
  vanishes when `Hₙ(A, C; L)`, `Hₙ(B, D; L)` and `Hₙ₋₁(A ∩ B, C ∩ D; L)` do.

## References

* A. Hatcher, *Algebraic Topology*, Section 2.2 (the relative Mayer–Vietoris sequence of pairs
  `(A ∪ B, C ∪ D)` with `C ⊆ A` and `D ⊆ B`) and Section 3.H (local coefficients, p. 333).
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10, where the sequence of two pairs over open sets of a base is used for the
  Thom isomorphism.
-/

public section

noncomputable section

open CategoryTheory Limits

universe u v w

namespace TauCeti.LocalCoefficientSystem

variable {R : Type u} [Ring R] {X : TopCat.{v}}
  (L : LocalCoefficientSystem.{u, v, max v w} R X)

/-! ### The Mayer–Vietoris sequence of two pairs -/

section MayerVietoris

variable {A B C D : Set X} (hCA : C ⊆ A) (hDB : D ⊆ B)

/-- The first map `Hₙ(A ∩ B, C ∩ D; L) ⟶ Hₙ(A, C; L) ⊞ Hₙ(B, D; L)` of the Mayer–Vietoris sequence
of the pairs `(A, C)` and `(B, D)` with local coefficients, `(i_A, -i_B)`, where `i_A` and `i_B`
are induced by the inclusions of pairs. -/
def pairTwistedMayerVietorisToBiprod (n : ℕ) :
    (TopPair.ofInclusion (Set.inter_subset_inter hCA hDB)).twistedHomology
        ((pullback (X := TopCat.of ↥(A ∩ B)) (ContinuousMap.subtypeVal (A ∩ B))).obj L) n ⟶
      (TopPair.ofInclusion hCA).twistedHomology
          ((pullback (X := TopCat.of ↥A) (ContinuousMap.subtypeVal A)).obj L) n ⊞
        (TopPair.ofInclusion hDB).twistedHomology
          ((pullback (X := TopCat.of ↥B) (ContinuousMap.subtypeVal B)).obj L) n :=
  biprod.lift
    (HomologicalComplex.homologyMap (subsetPairTwistedChainComplexMap L _ hCA
      Set.inter_subset_left Set.inter_subset_left) n)
    (-HomologicalComplex.homologyMap (subsetPairTwistedChainComplexMap L _ hDB
      Set.inter_subset_right Set.inter_subset_right) n)

@[reassoc (attr := simp)]
lemma pairTwistedMayerVietorisToBiprod_fst (n : ℕ) :
    pairTwistedMayerVietorisToBiprod L hCA hDB n ≫ biprod.fst =
      HomologicalComplex.homologyMap (subsetPairTwistedChainComplexMap L _ hCA
        Set.inter_subset_left Set.inter_subset_left) n :=
  biprod.lift_fst _ _

@[reassoc (attr := simp)]
lemma pairTwistedMayerVietorisToBiprod_snd (n : ℕ) :
    pairTwistedMayerVietorisToBiprod L hCA hDB n ≫ biprod.snd =
      -HomologicalComplex.homologyMap (subsetPairTwistedChainComplexMap L _ hDB
        Set.inter_subset_right Set.inter_subset_right) n :=
  biprod.lift_snd _ _

/-- The second map `Hₙ(A, C; L) ⊞ Hₙ(B, D; L) ⟶ Hₙ(A ∪ B, C ∪ D; L)` of the Mayer–Vietoris
sequence of the pairs `(A, C)` and `(B, D)` with local coefficients, `j_A + j_B`, where `j_A` and
`j_B` are induced by the inclusions of pairs. -/
def pairTwistedMayerVietorisFromBiprod (n : ℕ) :
    (TopPair.ofInclusion hCA).twistedHomology
          ((pullback (X := TopCat.of ↥A) (ContinuousMap.subtypeVal A)).obj L) n ⊞
        (TopPair.ofInclusion hDB).twistedHomology
          ((pullback (X := TopCat.of ↥B) (ContinuousMap.subtypeVal B)).obj L) n ⟶
      (TopPair.ofInclusion (Set.union_subset_union hCA hDB)).twistedHomology
        ((pullback (X := TopCat.of ↥(A ∪ B)) (ContinuousMap.subtypeVal (A ∪ B))).obj L) n :=
  biprod.desc
    (HomologicalComplex.homologyMap (subsetPairTwistedChainComplexMap L hCA _
      Set.subset_union_left Set.subset_union_left) n)
    (HomologicalComplex.homologyMap (subsetPairTwistedChainComplexMap L hDB _
      Set.subset_union_right Set.subset_union_right) n)

@[reassoc (attr := simp)]
lemma inl_pairTwistedMayerVietorisFromBiprod (n : ℕ) :
    biprod.inl ≫ pairTwistedMayerVietorisFromBiprod L hCA hDB n =
      HomologicalComplex.homologyMap (subsetPairTwistedChainComplexMap L hCA _
        Set.subset_union_left Set.subset_union_left) n :=
  biprod.inl_desc _ _

@[reassoc (attr := simp)]
lemma inr_pairTwistedMayerVietorisFromBiprod (n : ℕ) :
    biprod.inr ≫ pairTwistedMayerVietorisFromBiprod L hCA hDB n =
      HomologicalComplex.homologyMap (subsetPairTwistedChainComplexMap L hDB _
        Set.subset_union_right Set.subset_union_right) n :=
  biprod.inr_desc _ _

/-- The composite of the first two maps of the Mayer–Vietoris sequence of two pairs vanishes. -/
@[reassoc (attr := simp)]
lemma pairTwistedMayerVietorisToBiprod_fromBiprod (n : ℕ) :
    pairTwistedMayerVietorisToBiprod L hCA hDB n ≫ pairTwistedMayerVietorisFromBiprod L hCA hDB n =
      0 := by
  simp [pairTwistedMayerVietorisToBiprod, pairTwistedMayerVietorisFromBiprod,
    ← HomologicalComplex.homologyMap_comp]

/-! #### The short exact sequence of relative chains -/

/-- The inclusion of the chains subordinate to `{C, D}` into those subordinate to `{A, B}`. -/
private abbrev boolIncl :
    smallTwistedChainComplex L (Bool.rec C D) ⟶ smallTwistedChainComplex L (Bool.rec A B) :=
  smallTwistedChainComplexInclusion fun n ↦
    smallTwistedChains_mono L _ _ id (fun b ↦ by cases b; exacts [hCA, hDB]) n

/-- The inclusion of the chains subordinate to `{U, V}` into those supported in `U ∪ V`. -/
private abbrev inclUnion (U V : Set X) :
    smallTwistedChainComplex L (Bool.rec U V) ⟶ smallTwistedChainComplex L (fun _ : Unit ↦ U ∪ V) :=
  smallTwistedChainComplexInclusion fun n ↦
    smallTwistedChains_mono L (Bool.rec U V) _ (fun _ ↦ ())
      (fun b ↦ by cases b; exacts [Set.subset_union_left, Set.subset_union_right]) n

/-- The map from the relative chains of `(A, C)` to the chains subordinate to `{A, B}` modulo
those subordinate to `{C, D}`. -/
private def relToCokernelLeft :
    (TopPair.ofInclusion hCA).twistedChainComplex
        ((pullback (X := TopCat.of ↥A) (ContinuousMap.subtypeVal A)).obj L) ⟶
      cokernel (boolIncl L hCA hDB) :=
  (isColimitSubsetPairTwistedChainComplexπ L hCA).desc (CokernelCofork.ofπ
    (biprod.inl ≫ smallTwistedMayerVietorisFromBiprod L A B ≫ cokernel.π (boolIncl L hCA hDB))
    (by
      rw [inl_smallTwistedMayerVietorisFromBiprod_assoc, ← Category.assoc,
        show smallTwistedChainComplexSubsetInclusion L hCA ≫ _ =
            (biprod.inl ≫ smallTwistedMayerVietorisFromBiprod L C D) ≫ boolIncl L hCA hDB by
          simp only [inl_smallTwistedMayerVietorisFromBiprod,
            smallTwistedChainComplexInclusion_comp],
        Category.assoc, cokernel.condition, comp_zero]))

/-- The map from the relative chains of `(B, D)` to the chains subordinate to `{A, B}` modulo
those subordinate to `{C, D}`. -/
private def relToCokernelRight :
    (TopPair.ofInclusion hDB).twistedChainComplex
        ((pullback (X := TopCat.of ↥B) (ContinuousMap.subtypeVal B)).obj L) ⟶
      cokernel (boolIncl L hCA hDB) :=
  (isColimitSubsetPairTwistedChainComplexπ L hDB).desc (CokernelCofork.ofπ
    (biprod.inr ≫ smallTwistedMayerVietorisFromBiprod L A B ≫ cokernel.π (boolIncl L hCA hDB))
    (by
      rw [inr_smallTwistedMayerVietorisFromBiprod_assoc, ← Category.assoc,
        show smallTwistedChainComplexSubsetInclusion L hDB ≫ _ =
            (biprod.inr ≫ smallTwistedMayerVietorisFromBiprod L C D) ≫ boolIncl L hCA hDB by
          simp only [inr_smallTwistedMayerVietorisFromBiprod,
            smallTwistedChainComplexInclusion_comp],
        Category.assoc, cokernel.condition, comp_zero]))

@[reassoc (attr := simp)]
private lemma subsetPairTwistedChainComplexπ_comp_relToCokernelLeft :
    subsetPairTwistedChainComplexπ L hCA ≫ relToCokernelLeft L hCA hDB =
      biprod.inl ≫ smallTwistedMayerVietorisFromBiprod L A B ≫ cokernel.π (boolIncl L hCA hDB) :=
  (isColimitSubsetPairTwistedChainComplexπ L hCA).fac _ WalkingParallelPair.one

@[reassoc (attr := simp)]
private lemma subsetPairTwistedChainComplexπ_comp_relToCokernelRight :
    subsetPairTwistedChainComplexπ L hDB ≫ relToCokernelRight L hCA hDB =
      biprod.inr ≫ smallTwistedMayerVietorisFromBiprod L A B ≫ cokernel.π (boolIncl L hCA hDB) :=
  (isColimitSubsetPairTwistedChainComplexπ L hDB).fac _ WalkingParallelPair.one

/-- The relative Mayer–Vietoris short complex of chains: the relative chains of `(A ∩ B, C ∩ D)`,
of `(A, C)` and `(B, D)`, and the chains subordinate to `{A, B}` modulo those subordinate to
`{C, D}`. -/
private abbrev relShortComplex : ShortComplex (ChainComplex (ModuleCat.{max v w} R) ℕ) :=
  ShortComplex.mk
    (biprod.lift (subsetPairTwistedChainComplexMap L _ hCA
        Set.inter_subset_left Set.inter_subset_left)
      (-subsetPairTwistedChainComplexMap L _ hDB Set.inter_subset_right Set.inter_subset_right))
    (biprod.desc (relToCokernelLeft L hCA hDB) (relToCokernelRight L hCA hDB)) (by
      refine (cancel_epi (subsetPairTwistedChainComplexπ L (Set.inter_subset_inter hCA hDB))).1 ?_
      simp only [biprod.lift_desc, Preadditive.neg_comp, Preadditive.comp_add,
        Preadditive.comp_neg,
        subsetPairTwistedChainComplexπ_comp_subsetPairTwistedChainComplexMap_assoc,
        subsetPairTwistedChainComplexπ_comp_relToCokernelLeft,
        subsetPairTwistedChainComplexπ_comp_relToCokernelRight,
        inl_smallTwistedMayerVietorisFromBiprod_assoc,
        inr_smallTwistedMayerVietorisFromBiprod_assoc, comp_zero]
      simp only [← Category.assoc, smallTwistedChainComplexInclusion_comp, add_neg_cancel])

/-- The inclusion of the absolute Mayer–Vietoris short exact sequence of the chains supported in
`C ∩ D`, `C`, `D` and subordinate to `{C, D}` into that for `A ∩ B`, `A`, `B` and `{A, B}`. -/
private def smallMayerVietorisInclusion :
    ShortComplex.mk _ _ (smallTwistedMayerVietorisToBiprod_fromBiprod L C D) ⟶
      ShortComplex.mk _ _ (smallTwistedMayerVietorisToBiprod_fromBiprod L A B) where
  τ₁ := smallTwistedChainComplexSubsetInclusion L (Set.inter_subset_inter hCA hDB)
  τ₂ := biprod.map (smallTwistedChainComplexSubsetInclusion L hCA)
    (smallTwistedChainComplexSubsetInclusion L hDB)
  τ₃ := boolIncl L hCA hDB
  comm₁₂ := by
    apply biprod.hom_ext
    · simp only [Category.assoc, biprod.map_fst, smallTwistedMayerVietorisToBiprod_comp_fst_assoc,
        smallTwistedMayerVietorisToBiprod_comp_fst, smallTwistedChainComplexInclusion_comp]
    · simp only [Category.assoc, biprod.map_snd, smallTwistedMayerVietorisToBiprod_comp_snd_assoc,
        smallTwistedMayerVietorisToBiprod_comp_snd, smallTwistedChainComplexInclusion_comp,
        Preadditive.neg_comp, Preadditive.comp_neg]
  comm₂₃ := by
    apply biprod.hom_ext'
    · simp only [biprod.inl_map_assoc, inl_smallTwistedMayerVietorisFromBiprod_assoc,
        inl_smallTwistedMayerVietorisFromBiprod, smallTwistedChainComplexInclusion_comp]
    · simp only [biprod.inr_map_assoc, inr_smallTwistedMayerVietorisFromBiprod_assoc,
        inr_smallTwistedMayerVietorisFromBiprod, smallTwistedChainComplexInclusion_comp]

/-- The quotient maps from the absolute Mayer–Vietoris short exact sequence of the chains supported
in `A ∩ B`, `A`, `B` and subordinate to `{A, B}` onto the relative short complex. -/
private def smallMayerVietorisToRel :
    ShortComplex.mk _ _ (smallTwistedMayerVietorisToBiprod_fromBiprod L A B) ⟶
      relShortComplex L hCA hDB where
  τ₁ := subsetPairTwistedChainComplexπ L (Set.inter_subset_inter hCA hDB)
  τ₂ := biprod.map (subsetPairTwistedChainComplexπ L hCA) (subsetPairTwistedChainComplexπ L hDB)
  τ₃ := cokernel.π (boolIncl L hCA hDB)
  comm₁₂ := by
    apply biprod.hom_ext
    · simp only [Category.assoc, biprod.map_fst, smallTwistedMayerVietorisToBiprod_comp_fst_assoc,
        biprod.lift_fst, subsetPairTwistedChainComplexπ_comp_subsetPairTwistedChainComplexMap]
    · simp only [Category.assoc, biprod.map_snd, smallTwistedMayerVietorisToBiprod_comp_snd_assoc,
        biprod.lift_snd, Preadditive.neg_comp, Preadditive.comp_neg,
        subsetPairTwistedChainComplexπ_comp_subsetPairTwistedChainComplexMap]
  comm₂₃ := by
    apply biprod.hom_ext'
    · simp only [biprod.inl_map_assoc, biprod.inl_desc,
        subsetPairTwistedChainComplexπ_comp_relToCokernelLeft]
    · simp only [biprod.inr_map_assoc, biprod.inr_desc,
        subsetPairTwistedChainComplexπ_comp_relToCokernelRight]

/-- **The relative Mayer–Vietoris short exact sequence of chains**, the cokernel of the inclusion
of the absolute Mayer–Vietoris short exact sequence for `C` and `D` into that for `A` and `B`. -/
private lemma shortExact_relShortComplex : (relShortComplex L hCA hDB).ShortExact := by
  have hL₁ := shortExact_mk_smallTwistedMayerVietoris L C D
  have hw : smallMayerVietorisInclusion L hCA hDB ≫ smallMayerVietorisToRel L hCA hDB = 0 := by
    refine ShortComplex.hom_ext _ _
      (smallTwistedChainComplexSubsetInclusion_comp_subsetPairTwistedChainComplexπ L _) ?_
      (cokernel.condition _)
    apply biprod.hom_ext' <;> simp [smallMayerVietorisInclusion, smallMayerVietorisToRel,
      smallTwistedChainComplexSubsetInclusion_comp_subsetPairTwistedChainComplexπ_assoc]
  have : Mono (smallMayerVietorisInclusion L hCA hDB).τ₃ :=
    mono_of_mono_fac (smallTwistedChainComplexInclusion_ι _)
  have := hL₁.epi_g
  refine (shortExact_mk_smallTwistedMayerVietoris L A B).of_isColimit_cokernelCofork hL₁.exact
    (smallMayerVietorisInclusion L hCA hDB) (smallMayerVietorisToRel L hCA hDB) hw ?_
  apply ShortComplex.isColimitOfIsColimitπ <;>
    apply (CokernelCofork.isColimitMapCoconeEquiv _ _).invFun
  · exact isColimitSubsetPairTwistedChainComplexπ L (Set.inter_subset_inter hCA hDB)
  · exact CokernelCofork.isColimitBiprod (isColimitSubsetPairTwistedChainComplexπ L hCA)
      (isColimitSubsetPairTwistedChainComplexπ L hDB)
  · exact cokernelIsCokernel _

/-! #### Comparison with the pair `(A ∪ B, C ∪ D)` -/

/-- The comparison of the chains subordinate to `{A, B}` modulo those subordinate to `{C, D}` with
the relative chains of `(A ∪ B, C ∪ D)`. -/
private def cokernelToUnion :
    cokernel (boolIncl L hCA hDB) ⟶
      (TopPair.ofInclusion (Set.union_subset_union hCA hDB)).twistedChainComplex
        ((pullback (X := TopCat.of ↥(A ∪ B)) (ContinuousMap.subtypeVal (A ∪ B))).obj L) :=
  cokernel.desc _
    (inclUnion L A B ≫ subsetPairTwistedChainComplexπ L (Set.union_subset_union hCA hDB)) (by
      rw [← Category.assoc, show boolIncl L hCA hDB ≫ inclUnion L A B = inclUnion L C D ≫
          smallTwistedChainComplexSubsetInclusion L (Set.union_subset_union hCA hDB) by
          simp only [smallTwistedChainComplexInclusion_comp],
        Category.assoc, smallTwistedChainComplexSubsetInclusion_comp_subsetPairTwistedChainComplexπ,
        comp_zero])

private lemma relToCokernelLeft_comp_cokernelToUnion :
    relToCokernelLeft L hCA hDB ≫ cokernelToUnion L hCA hDB =
      subsetPairTwistedChainComplexMap L hCA _ Set.subset_union_left Set.subset_union_left := by
  refine (cancel_epi (subsetPairTwistedChainComplexπ L hCA)).1 ?_
  rw [subsetPairTwistedChainComplexπ_comp_relToCokernelLeft_assoc, cokernelToUnion,
    cokernel.π_desc, inl_smallTwistedMayerVietorisFromBiprod_assoc,
    subsetPairTwistedChainComplexπ_comp_subsetPairTwistedChainComplexMap, ← Category.assoc,
    smallTwistedChainComplexInclusion_comp]

private lemma relToCokernelRight_comp_cokernelToUnion :
    relToCokernelRight L hCA hDB ≫ cokernelToUnion L hCA hDB =
      subsetPairTwistedChainComplexMap L hDB _ Set.subset_union_right Set.subset_union_right := by
  refine (cancel_epi (subsetPairTwistedChainComplexπ L hDB)).1 ?_
  rw [subsetPairTwistedChainComplexπ_comp_relToCokernelRight_assoc, cokernelToUnion,
    cokernel.π_desc, inr_smallTwistedMayerVietorisFromBiprod_assoc,
    subsetPairTwistedChainComplexπ_comp_subsetPairTwistedChainComplexMap, ← Category.assoc,
    smallTwistedChainComplexInclusion_comp]

/-- By the small-chain theorem inside `U ∪ V`, the inclusion of the chains subordinate to `{U, V}`
into those supported in `U ∪ V` is a quasi-isomorphism when `U` and `V` are open in `U ∪ V`. -/
private lemma quasiIso_inclUnion {U V : Set X} (hU : IsOpen ((↑) ⁻¹' U : Set ↥(U ∪ V)))
    (hV : IsOpen ((↑) ⁻¹' V : Set ↥(U ∪ V))) : QuasiIso (inclUnion L U V) :=
  quasiIso_smallTwistedChainComplexInclusion L (Bool.rec U V)
    (fun b ↦ by cases b; exacts [Set.subset_union_left, Set.subset_union_right])
    (fun x hx ↦ by
      rcases hx with hx | hx
      exacts [Set.mem_iUnion.2 ⟨false, hx⟩, Set.mem_iUnion.2 ⟨true, hx⟩])
    (fun b ↦ by cases b; exacts [hU, hV])

variable (hA : IsOpen ((↑) ⁻¹' A : Set ↥(A ∪ B)))
  (hB : IsOpen ((↑) ⁻¹' B : Set ↥(A ∪ B))) (hC : IsOpen ((↑) ⁻¹' C : Set ↥(C ∪ D)))
  (hD : IsOpen ((↑) ⁻¹' D : Set ↥(C ∪ D)))

include hA hB hC hD in
/-- By the small-chain theorem inside `A ∪ B` and inside `C ∪ D`, and the five lemma, the comparison
with the relative chains of `(A ∪ B, C ∪ D)` is a quasi-isomorphism. -/
private lemma quasiIso_cokernelToUnion : QuasiIso (cokernelToUnion L hCA hDB) := by
  have : Mono (boolIncl L hCA hDB) := mono_of_mono_fac (smallTwistedChainComplexInclusion_ι _)
  have hS₁ := cokernelSequence_shortExact (boolIncl L hCA hDB)
  have : Mono (smallTwistedChainComplexSubsetInclusion L (Set.union_subset_union hCA hDB)) :=
    mono_of_mono_fac (smallTwistedChainComplexInclusion_ι _)
  have hw := smallTwistedChainComplexSubsetInclusion_comp_subsetPairTwistedChainComplexπ L
    (Set.union_subset_union hCA hDB)
  have hS₂ : (ShortComplex.mk _ _ hw).ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_of_g_is_cokernel _
      (isColimitSubsetPairTwistedChainComplexπ L (Set.union_subset_union hCA hDB)))
      inferInstance inferInstance
  let φ : ShortComplex.cokernelSequence (boolIncl L hCA hDB) ⟶ ShortComplex.mk _ _ hw :=
    { τ₁ := inclUnion L C D
      τ₂ := inclUnion L A B
      τ₃ := cokernelToUnion L hCA hDB
      comm₁₂ := by
        dsimp only [ShortComplex.cokernelSequence]
        rw [smallTwistedChainComplexInclusion_comp, smallTwistedChainComplexInclusion_comp]
      comm₂₃ := (cokernel.π_desc _ _ _).symm }
  exact HomologicalComplex.HomologySequence.quasiIso_τ₃ φ hS₁ hS₂ (quasiIso_inclUnion L hC hD)
    (quasiIso_inclUnion L hA hB)

/-- The homology of the chains subordinate to `{A, B}` modulo those subordinate to `{C, D}` is
`Hₙ(A ∪ B, C ∪ D; L)`. -/
private def homologyIsoUnion (n : ℕ) :
    (cokernel (boolIncl L hCA hDB)).homology n ≅
      (TopPair.ofInclusion (Set.union_subset_union hCA hDB)).twistedHomology
        ((pullback (X := TopCat.of ↥(A ∪ B)) (ContinuousMap.subtypeVal (A ∪ B))).obj L) n :=
  have := quasiIso_cokernelToUnion L hCA hDB hA hB hC hD
  asIso (HomologicalComplex.homologyMap (cokernelToUnion L hCA hDB) n)

private lemma biprod_desc_homologyMap_comp_homologyIsoUnion_hom (n : ℕ) :
    biprod.desc (HomologicalComplex.homologyMap (relToCokernelLeft L hCA hDB) n)
        (HomologicalComplex.homologyMap (relToCokernelRight L hCA hDB) n) ≫
      (homologyIsoUnion L hCA hDB hA hB hC hD n).hom =
        pairTwistedMayerVietorisFromBiprod L hCA hDB n := by
  apply biprod.hom_ext' <;>
    simp [homologyIsoUnion, pairTwistedMayerVietorisFromBiprod,
      ← HomologicalComplex.homologyMap_comp, relToCokernelLeft_comp_cokernelToUnion,
      relToCokernelRight_comp_cokernelToUnion]

private lemma pairTwistedMayerVietorisToBiprod_eq (n : ℕ) :
    pairTwistedMayerVietorisToBiprod L hCA hDB n =
      biprod.lift (HomologicalComplex.homologyMap (subsetPairTwistedChainComplexMap L _ hCA
          Set.inter_subset_left Set.inter_subset_left) n)
        (HomologicalComplex.homologyMap (-subsetPairTwistedChainComplexMap L _ hDB
          Set.inter_subset_right Set.inter_subset_right) n) := by
  rw [pairTwistedMayerVietorisToBiprod, HomologicalComplex.homologyMap_neg]

/-! #### The long exact sequence -/

/-- The **Mayer–Vietoris connecting morphism** `Hₙ(A ∪ B, C ∪ D; L) ⟶ Hₘ(A ∩ B, C ∩ D; L)`,
`m + 1 = n`, of the pairs `(A, C)` and `(B, D)` with local coefficients, for `A` and `B` open in
`A ∪ B` and `C` and `D` open in `C ∪ D`: the connecting morphism of the short exact sequence of
relative chains of `(A ∩ B, C ∩ D)`, of `(A, C)` and `(B, D)`, and of chains subordinate to
`{A, B}` modulo those subordinate to `{C, D}`, the homology of the last being identified with
`Hₙ(A ∪ B, C ∪ D; L)`. -/
def pairTwistedMayerVietorisδ (n m : ℕ) (h : m + 1 = n := by lia) :
    (TopPair.ofInclusion (Set.union_subset_union hCA hDB)).twistedHomology
        ((pullback (X := TopCat.of ↥(A ∪ B)) (ContinuousMap.subtypeVal (A ∪ B))).obj L) n ⟶
      (TopPair.ofInclusion (Set.inter_subset_inter hCA hDB)).twistedHomology
        ((pullback (X := TopCat.of ↥(A ∩ B)) (ContinuousMap.subtypeVal (A ∩ B))).obj L) m :=
  (homologyIsoUnion L hCA hDB hA hB hC hD n).inv ≫
    (shortExact_relShortComplex L hCA hDB).δ n m (by simpa)

/-- The connecting morphism followed by the first map vanishes. -/
@[reassoc (attr := simp)]
lemma pairTwistedMayerVietorisδ_toBiprod (n m : ℕ) (h : m + 1 = n := by lia) :
    pairTwistedMayerVietorisδ L hCA hDB hA hB hC hD n m h ≫
      pairTwistedMayerVietorisToBiprod L hCA hDB m = 0 := by
  rw [pairTwistedMayerVietorisδ, pairTwistedMayerVietorisToBiprod_eq, Category.assoc,
    (shortExact_relShortComplex L hCA hDB).δ_comp_biprod_lift_homologyMap n m (by simpa),
    comp_zero]

/-- The second map followed by the connecting morphism vanishes. -/
@[reassoc (attr := simp)]
lemma pairTwistedMayerVietorisFromBiprod_δ (n m : ℕ) (h : m + 1 = n := by lia) :
    pairTwistedMayerVietorisFromBiprod L hCA hDB n ≫
      pairTwistedMayerVietorisδ L hCA hDB hA hB hC hD n m h = 0 := by
  rw [← biprod_desc_homologyMap_comp_homologyIsoUnion_hom L hCA hDB hA hB hC hD,
    pairTwistedMayerVietorisδ, Category.assoc, Iso.hom_inv_id_assoc]
  exact (shortExact_relShortComplex L hCA hDB).biprod_desc_homologyMap_comp_δ n m (by simpa)

/-- **Exactness of the Mayer–Vietoris sequence of two pairs with local coefficients at
`Hₘ(A ∩ B, C ∩ D; L)`.** -/
lemma pairTwistedMayerVietoris_exact₁ (n m : ℕ) (h : m + 1 = n := by lia) :
    (ShortComplex.mk _ _
      (pairTwistedMayerVietorisδ_toBiprod L hCA hDB hA hB hC hD n m h)).Exact := by
  refine (ShortComplex.exact_iff_of_iso ?_).1
    ((shortExact_relShortComplex L hCA hDB).biprod_homology_exact₁ n m (by simpa))
  refine ShortComplex.isoMk (homologyIsoUnion L hCA hDB hA hB hC hD n) (Iso.refl _) (Iso.refl _)
    ?_ ?_
  · simp [pairTwistedMayerVietorisδ]
  · simp [pairTwistedMayerVietorisToBiprod_eq]

include hA hB hC hD in
/-- **Exactness of the Mayer–Vietoris sequence of two pairs with local coefficients at
`Hₙ(A, C; L) ⊞ Hₙ(B, D; L)`.** -/
lemma pairTwistedMayerVietoris_exact₂ (n : ℕ) :
    (ShortComplex.mk _ _ (pairTwistedMayerVietorisToBiprod_fromBiprod L hCA hDB n)).Exact := by
  refine (ShortComplex.exact_iff_of_iso ?_).1
    ((shortExact_relShortComplex L hCA hDB).biprod_homology_exact₂ n)
  refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (homologyIsoUnion L hCA hDB hA hB hC hD n)
    ?_ ?_
  · simp [pairTwistedMayerVietorisToBiprod_eq]
  · simp [biprod_desc_homologyMap_comp_homologyIsoUnion_hom]

/-- **Exactness of the Mayer–Vietoris sequence of two pairs with local coefficients at
`Hₙ(A ∪ B, C ∪ D; L)`.** -/
lemma pairTwistedMayerVietoris_exact₃ (n m : ℕ) (h : m + 1 = n := by lia) :
    (ShortComplex.mk _ _
      (pairTwistedMayerVietorisFromBiprod_δ L hCA hDB hA hB hC hD n m h)).Exact := by
  refine (ShortComplex.exact_iff_of_iso ?_).1
    ((shortExact_relShortComplex L hCA hDB).biprod_homology_exact₃ n m (by simpa))
  refine ShortComplex.isoMk (Iso.refl _) (homologyIsoUnion L hCA hDB hA hB hC hD n) (Iso.refl _)
    ?_ ?_
  · simp [biprod_desc_homologyMap_comp_homologyIsoUnion_hom]
  · simp [pairTwistedMayerVietorisδ]

include hA hB hC hD in
/-- If `Hₖ₊₁(A ∪ B, C ∪ D; L)` vanishes, the first map
`Hₖ(A ∩ B, C ∩ D; L) ⟶ Hₖ(A, C; L) ⊞ Hₖ(B, D; L)` of the Mayer–Vietoris sequence of two pairs is a
monomorphism. -/
lemma mono_pairTwistedMayerVietorisToBiprod {k : ℕ}
    (h : IsZero ((TopPair.ofInclusion (Set.union_subset_union hCA hDB)).twistedHomology
      ((pullback (X := TopCat.of ↥(A ∪ B)) (ContinuousMap.subtypeVal (A ∪ B))).obj L) (k + 1))) :
    Mono (pairTwistedMayerVietorisToBiprod L hCA hDB k) :=
  (pairTwistedMayerVietoris_exact₁ L hCA hDB hA hB hC hD (k + 1) k).mono_g (h.eq_of_src _ _)

include hA hB hC hD in
/-- The map `H₀(A, C; L) ⊞ H₀(B, D; L) ⟶ H₀(A ∪ B, C ∪ D; L)` at the end of the Mayer–Vietoris
sequence of two pairs is an epimorphism. -/
lemma epi_pairTwistedMayerVietorisFromBiprod_zero :
    Epi (pairTwistedMayerVietorisFromBiprod L hCA hDB 0) := by
  have : Epi ((relShortComplex L hCA hDB).g.f 0) :=
    ((HomologicalComplex.shortExact_iff_degreewise_shortExact _).1
      (shortExact_relShortComplex L hCA hDB) 0).epi_g
  have : Epi (HomologicalComplex.homologyMap (relShortComplex L hCA hDB).g 0) :=
    HomologicalComplex.epi_homologyMap_of_epi_of_not_rel _ _ (by simp)
  have : Epi (biprod.desc (HomologicalComplex.homologyMap (relToCokernelLeft L hCA hDB) 0)
      (HomologicalComplex.homologyMap (relToCokernelRight L hCA hDB) 0)) :=
    (HomologicalComplex.epi_biprod_desc_homologyMap_iff 0).2 this
  rw [← biprod_desc_homologyMap_comp_homologyIsoUnion_hom L hCA hDB hA hB hC hD]
  infer_instance

include hA hB hC hD in
/-- **Vanishing propagates along the Mayer–Vietoris sequence of two pairs**: if `Hₙ(A, C; L)` and
`Hₙ(B, D; L)` vanish, and so does `Hₙ₋₁(A ∩ B, C ∩ D; L)` when `n` is positive, then
`Hₙ(A ∪ B, C ∪ D; L)` vanishes. -/
lemma isZero_twistedHomology_ofInclusion_union {n : ℕ}
    (hAC : IsZero ((TopPair.ofInclusion hCA).twistedHomology
      ((pullback (X := TopCat.of ↥A) (ContinuousMap.subtypeVal A)).obj L) n))
    (hBD : IsZero ((TopPair.ofInclusion hDB).twistedHomology
      ((pullback (X := TopCat.of ↥B) (ContinuousMap.subtypeVal B)).obj L) n))
    (hABCD : ∀ m, m + 1 = n →
      IsZero ((TopPair.ofInclusion (Set.inter_subset_inter hCA hDB)).twistedHomology
        ((pullback (X := TopCat.of ↥(A ∩ B)) (ContinuousMap.subtypeVal (A ∩ B))).obj L) m)) :
    IsZero ((TopPair.ofInclusion (Set.union_subset_union hCA hDB)).twistedHomology
      ((pullback (X := TopCat.of ↥(A ∪ B)) (ContinuousMap.subtypeVal (A ∪ B))).obj L) n) := by
  have hbiprod := (biprod_isZero_iff _ _).2 ⟨hAC, hBD⟩
  cases n with
  | zero =>
    have := epi_pairTwistedMayerVietorisFromBiprod_zero L hCA hDB hA hB hC hD
    exact IsZero.of_epi_eq_zero (pairTwistedMayerVietorisFromBiprod L hCA hDB 0)
      (hbiprod.eq_of_src _ _)
  | succ m =>
    exact (pairTwistedMayerVietoris_exact₃ L hCA hDB hA hB hC hD (m + 1) m).isZero_of_both_isZero
      hbiprod (hABCD m rfl)

end MayerVietoris

end TauCeti.LocalCoefficientSystem

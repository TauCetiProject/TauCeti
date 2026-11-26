/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Cubical.Kunneth.Pair
public import TauCeti.AlgebraicTopology.Singular.Cubical.Comparison.Relative.Homotopy
public import TauCeti.AlgebraicTopology.Singular.Excision

/-!
# The Künneth theorem for a product of open pairs in singular homology

For subsets `A ⊆ X` and `B ⊆ Y`, the relative cubical chains of the product of the pairs
`P = (X, A)` and `Q = (Y, B)` are the complex `N(P × Q) = N(X × Y) ⧸ (N(A × Y) + N(X × B))`
(`TopPair.cubicalChainComplexProd`), and the cubical cross product of pairs
`N(X, A) ⊗ N(Y, B) ⟶ N(P × Q)` is a quasi-isomorphism (`TauCeti.quasiIso_cubicalCrossProductPair`).
This file identifies the homology of `N(P × Q)` with the relative singular homology of
`(X × Y, A × Y ∪ X × B)` when `A` and `B` are open, where `A × Y` and `X × B` are the preimages of
`A` and `B` under the projections, and so obtains the Künneth theorem for a product of pairs in
relative singular homology.

The comparison `N(P × Q) ⟶ C(X × Y, A × Y ∪ X × B)` (`TauCeti.cubicalChainComplexProdToSingular`)
is the comparison of relative cubical with relative singular chains of `(X × Y, X × B)`, followed by
the quotient modulo the chains of `A × Y ∪ X × B`. It is a map from the short exact sequence

`0 ⟶ N(A × Y, A × B) ⟶ N(X × Y, X × B) ⟶ N(P × Q) ⟶ 0`

to the singular chain sequence of the triple `(X × Y, A × Y ∪ X × B, X × B)`

`0 ⟶ C(A × Y ∪ X × B, X × B) ⟶ C(X × Y, X × B) ⟶ C(X × Y, A × Y ∪ X × B) ⟶ 0`.

The middle component is a quasi-isomorphism by the cubical–singular comparison. The first is the
comparison followed by the excision map of pairs `(A × Y, A × B) ⟶ (A × Y ∪ X × B, X × B)`
(`TopPair.prodExcisionMap`), which induces isomorphisms on singular homology when `A` and `B` are
open (`TopPair.isIso_singularHomologyMap_prodExcisionMap_of_isOpen`): then `A × Y` and `X × B` are
open sets covering the union, the first the image of the inclusion and the second the subspace.
By the five lemma the comparison is a
quasi-isomorphism (`TauCeti.quasiIso_cubicalChainComplexProdToSingular`). This is the small-chain
theorem for the cover of `A × Y ∪ X × B` by `A × Y` and `X × B`, in the form needed for products of
pairs.

Composing the cubical Künneth map of a product of pairs with the comparison isomorphisms gives the
**Künneth map** in relative singular homology (`TauCeti.singularHomologyKunnethPair`)

`⨁_{p + q = n} Hₚ(X, A; k) ⊗ H_q(Y, B; k) ⟶ Hₙ(X × Y, A × Y ∪ X × B; k)`,

which is natural in both pairs. For open `A` and `B` it is an isomorphism over a commutative
semisimple ring such as a field, and over any commutative ring when the relative homology of
`(X, A)` is projective. For instance, for points `x` and `y` of T₁ spaces `X` and `Y`, the subsets
`X ∖ {x}` and `Y ∖ {y}` are open and `(X ∖ {x}) × Y ∪ X × (Y ∖ {y})` is the complement of
`(x, y)`, so the local homology of `X × Y` at `(x, y)` is computed from the local homology of the
factors.

## Main definitions

* `TauCeti.cubicalChainComplexProdToSingular k A B`: the comparison
  `N(P × Q) ⟶ C(X × Y, A × Y ∪ X × B)`.
* `TauCeti.cubicalChainComplexProdHomologyIso`: for open `A` and `B`, the isomorphism
  `Hₙ(N(P × Q)) ≅ Hₙ(X × Y, A × Y ∪ X × B)`.
* `TauCeti.singularHomologyKunnethPair k A B n`: the Künneth map of a product of pairs in relative
  singular homology.

## Main results

* `TauCeti.π_cubicalChainComplexProdToSingular`: the comparison is induced by the comparison of
  relative chains of `(X × Y, X × B)`.
* `TauCeti.quasiIso_cubicalChainComplexProdToSingular`: for open `A` and `B` the comparison is a
  quasi-isomorphism.
* `TauCeti.cubicalChainComplexProdToSingular_naturality`,
  `TauCeti.singularHomologyKunnethPair_naturality`: naturality in both pairs.
* `TauCeti.cubicalChainComplexProdComparison_comp_cubicalToSingularRel`: naturality in a map out
  of the product.
* `TauCeti.tensorHom_ι_cubicalHomologyKunnethPair_comp_cubicalChainComplexProdToSingular`: the
  cubical Künneth class of arbitrary pairs, read in the singular homology of the pairs it maps to.
* `TauCeti.ι_singularHomologyKunnethPair`: on each summand the Künneth map is the cubical cross
  product of pairs, read in singular homology.
* `TauCeti.isIso_singularHomologyKunnethPair_of_isSemisimpleRing`,
  `TauCeti.isIso_singularHomologyKunnethPair_of_projective`: the Künneth theorem for a product of
  open pairs.

## References

* A. Hatcher, *Algebraic Topology*, Section 3.B, the relative cross product
  `Hₚ(X, A) ⊗ H_q(Y, B) ⟶ Hₙ(X × Y, A × Y ∪ X × B)` for open `A` and `B` and the relative Künneth
  formula.
* E. H. Spanier, *Algebraic Topology*, Chapter 5, Section 3, excisive couples and the relative
  Künneth formula.
-/

public section

noncomputable section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory HomologicalComplex Limits Topology

universe u

namespace TauCeti

open TopPair

section Comparison

variable (k : Type u) [Ring k] {X Y : TopCat.{u}} (A : Set X) (B : Set Y)

/-- The pair `(X × Y, X × B)` of `TopPair.prodLeft` is the pair `(X × Y, X × B)` of the triple,
with `X × B` realized as the product and as the preimage of `B`. -/
private def prodLeftToTotalPair :
    (ofSubset B).prodLeft (ofSubset A).fst ⟶ TopTriple.totalPair.obj (prodUnionTripleSnd A B) :=
  TopPair.ofHom (𝟙 _) (TopCat.ofHom ⟨fun x ↦ ⟨(x.1, x.2.val), x.2.property⟩, by fun_prop⟩)
      (by ext; rfl)

private instance : IsIso (prodLeftToTotalPair A B) := by
  have : IsIso (Hom.fst (prodLeftToTotalPair A B)) := inferInstanceAs (IsIso (𝟙 _))
  exact isIso_of_isIso_fst_of_surjective_snd _ fun y ↦ ⟨(y.val.1, ⟨y.val.2, y.property⟩), rfl⟩

/-- The pair `(A × Y ∪ X × B, X × B)` of `TopPair.prodExcisionPair` is the inner pair of the
triple, with `A × Y ∪ X × B` and `X × B` realized as preimages of `A` and `B`. -/
private def prodExcisionPairToInnerPair :
    (ofSubset A).prodExcisionPair (ofSubset B) ⟶
      TopTriple.innerPair.obj (prodUnionTripleSnd A B) :=
  TopPair.ofHom (TopCat.isoOfHomeo (Homeomorph.setCongr (by
      -- The ambient space `(ofSubset A).fst ⊗ (ofSubset B).fst` of `prodSubspace` is `X ⊗ Y`.
      rw [prodSubspace, range_ofSubset_map, range_ofSubset_map]; rfl))).hom
    (TopCat.ofHom ⟨fun x ↦ ⟨(x.1, x.2.val), x.2.property⟩, by fun_prop⟩)
    (by ext x; exact Subtype.ext ((ofSubset A).coe_prodSubspaceInr_apply (ofSubset B) x).symm)

private instance : IsIso (prodExcisionPairToInnerPair A B) := by
  have : IsIso (Hom.fst (prodExcisionPairToInnerPair A B)) :=
    inferInstanceAs (IsIso (TopCat.isoOfHomeo _).hom)
  exact isIso_of_isIso_fst_of_surjective_snd _ fun y ↦ ⟨(y.val.1, ⟨y.val.2, y.property⟩), rfl⟩

/-- The comparison on the first terms: relative cubical chains of `(A × Y, A × B)` to relative
singular chains of `(A × Y ∪ X × B, X × B)`. -/
private def prodComparisonτ₁ :
    ((ofSubset B).prodLeft (ofSubset A).snd).cubicalChainComplex k ⟶
      (TopTriple.innerPair.obj (prodUnionTripleSnd A B)).singularChainComplex (ModuleCat.of k k) :=
  cubicalToSingularRel k _ ≫ TopPair.singularChainComplexMap
    ((ofSubset A).prodExcisionMap (ofSubset B) ≫ prodExcisionPairToInnerPair A B) _

/-- The comparison on the middle terms: relative cubical chains of `(X × Y, X × B)` to relative
singular chains of the same pair, written as the pair of the triple. -/
private def prodComparisonτ₂ :
    ((ofSubset B).prodLeft (ofSubset A).fst).cubicalChainComplex k ⟶
      (TopTriple.totalPair.obj (prodUnionTripleSnd A B)).singularChainComplex (ModuleCat.of k k) :=
  cubicalToSingularRel k _ ≫ TopPair.singularChainComplexMap (prodLeftToTotalPair A B) _

private theorem prodLeftMap_comp_prodLeftToTotalPair :
    prodLeftMap (𝟙 (ofSubset B)) (ofSubset A).map ≫ prodLeftToTotalPair A B =
      ((ofSubset A).prodExcisionMap (ofSubset B) ≫ prodExcisionPairToInnerPair A B) ≫
        TopTriple.innerToTotal.app (prodUnionTripleSnd A B) :=
  hom_ext_of_fst _ (by
    rw [Hom.fst_comp, Hom.fst_comp, Hom.fst_comp, prodExcisionMap_fst,
      TopTriple.innerToTotal_app_fst]
    ext x
    exact ((ofSubset A).coe_prodSubspaceInl_apply (ofSubset B) x).symm)

@[reassoc]
private theorem prodComparison_comm₁₂ :
    cubicalChainComplexMap k (prodLeftMap (𝟙 (ofSubset B)) (ofSubset A).map) ≫
        prodComparisonτ₂ k A B =
      prodComparisonτ₁ k A B ≫ TopPair.singularChainComplexMap
        (TopTriple.innerToTotal.app (prodUnionTripleSnd A B)) (ModuleCat.of k k) := by
  rw [prodComparisonτ₂, cubicalToSingularRel_naturality_assoc, prodComparisonτ₁, Category.assoc]
  rw [← TopPair.singularChainComplexMap_comp, ← TopPair.singularChainComplexMap_comp,
    prodLeftMap_comp_prodLeftToTotalPair]

private theorem prodComparison_condition :
    cubicalChainComplexMap k (prodLeftMap (𝟙 (ofSubset B)) (ofSubset A).map) ≫
        prodComparisonτ₂ k A B ≫ TopPair.singularChainComplexMap
          (TopTriple.totalToOuter.app (prodUnionTripleSnd A B)) (ModuleCat.of k k) = 0 := by
  rw [prodComparison_comm₁₂_assoc,
    TopTriple.singularChainComplexMap_innerToTotal_comp_totalToOuter, comp_zero]

private theorem prodLeftToTotalPair_comp_totalToOuter :
    prodLeftToTotalPair A B ≫ TopTriple.totalToOuter.app (prodUnionTripleSnd A B) =
      prodLeftToPreimageUnion A B :=
  hom_ext_of_fst _ (by rw [prodLeftToPreimageUnion_fst]; ext; rfl)

/-- **The comparison of the cubical chains of a product of pairs with singular chains.** For
subsets `A ⊆ X` and `B ⊆ Y`, the relative cubical chains
`N(P × Q) = N(X × Y) ⧸ (N(A × Y) + N(X × B))` of the product of the pairs `P = (X, A)` and
`Q = (Y, B)` map to the relative singular chains of `(X × Y, A × Y ∪ X × B)`: the comparison of
relative cubical with relative singular chains of `(X × Y, X × B)`, followed by the quotient modulo
the chains of `A × Y ∪ X × B`, vanishes on the chains of `A × Y`. It is a quasi-isomorphism when
`A` and `B` are open (`TauCeti.quasiIso_cubicalChainComplexProdToSingular`). -/
def cubicalChainComplexProdToSingular :
    (ofSubset A).cubicalChainComplexProd k (ofSubset B) ⟶
      (ofSubset (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B)).singularChainComplex (ModuleCat.of k k) :=
  cokernel.desc _ (prodComparisonτ₂ k A B ≫ TopPair.singularChainComplexMap
    (TopTriple.totalToOuter.app (prodUnionTripleSnd A B)) (ModuleCat.of k k))
    (prodComparison_condition k A B)

/-- The comparison of the cubical chains of a product of pairs with singular chains is induced by
the comparison of relative cubical and singular chains of `(X × Y, X × B)`. -/
@[reassoc (attr := simp)]
theorem π_cubicalChainComplexProdToSingular :
    cokernel.π _ ≫ cubicalChainComplexProdToSingular k A B =
      cubicalToSingularRel k ((ofSubset B).prodLeft (ofSubset A).fst) ≫
        TopPair.singularChainComplexMap (prodLeftToPreimageUnion A B) (ModuleCat.of k k) := by
  have h := congrArg (TopPair.singularChainComplexMap · (ModuleCat.of k k))
    (prodLeftToTotalPair_comp_totalToOuter A B)
  rw [TopPair.singularChainComplexMap_comp] at h
  -- The target of the comparison is the outer pair of the triple, which is the pair
  -- `(X × Y, A × Y ∪ X × B)` only up to unfolding, so the steps are composed with `trans`.
  exact (cokernel.π_desc _ _ (prodComparison_condition k A B)).trans
    ((Category.assoc _ _ _).trans (congrArg (cubicalToSingularRel k _ ≫ ·) h))

/-- The morphism of short exact sequences from the cubical sequence of a product of pairs to the
singular sequence of the triple `(X × Y, A × Y ∪ X × B, X × B)`. -/
private def prodComparisonShortComplexMap :
    (ofSubset A).cubicalChainComplexProdShortComplex k (ofSubset B) ⟶
      (prodUnionTripleSnd A B).singularChainComplexShortComplex (ModuleCat.of k k) where
  τ₁ := prodComparisonτ₁ k A B
  τ₂ := prodComparisonτ₂ k A B
  τ₃ := cubicalChainComplexProdToSingular k A B
  comm₁₂ := (prodComparison_comm₁₂ k A B).symm
  comm₂₃ := (cokernel.π_desc _ _ _).symm

variable {A B}

/-- **The small-chain theorem for a product of open pairs**: for open `A ⊆ X` and `B ⊆ Y`, the
comparison `N(P × Q) ⟶ C(X × Y, A × Y ∪ X × B)` of the relative cubical chains of the product of
the pairs `P = (X, A)` and `Q = (Y, B)` with relative singular chains is a quasi-isomorphism. -/
theorem quasiIso_cubicalChainComplexProdToSingular (hA : IsOpen A) (hB : IsOpen B) :
    QuasiIso (cubicalChainComplexProdToSingular k A B) := by
  have : QuasiIso (TopPair.singularChainComplexMap
      ((ofSubset A).prodExcisionMap (ofSubset B) ≫ prodExcisionPairToInnerPair A B)
      (ModuleCat.of k k)) :=
    (quasiIso_iff _).2 fun n ↦ (quasiIsoAt_iff_isIso_homologyMap _ n).2 (by
      have := isIso_singularHomologyMap_prodExcisionMap_of_isOpen (ModuleCat.of k k)
        (ofSubset A) (ofSubset B) (range_ofSubset_map ▸ hA) (range_ofSubset_map ▸ hB) n
      have := (singularHomologyMapIso (ModuleCat.of k k)
        (asIso (prodExcisionPairToInnerPair A B)) n).isIso_hom
      -- The homology map of a singular chain map is the induced map on singular homology.
      change IsIso (TopPair.singularHomologyMap _ (ModuleCat.of k k) n)
      rw [singularHomologyMap_comp]
      infer_instance)
  have : QuasiIso (prodComparisonτ₁ k A B) := by
    rw [prodComparisonτ₁]
    infer_instance
  have : QuasiIso (prodComparisonτ₂ k A B) := by
    rw [prodComparisonτ₂]
    infer_instance
  exact HomologySequence.quasiIso_τ₃ (prodComparisonShortComplexMap k A B)
    ((ofSubset A).shortExact_cubicalChainComplexProdShortComplex k (ofSubset B))
    ((prodUnionTripleSnd A B).shortExact_singularChainComplexShortComplex _) ‹_› ‹_›

/-- **The homology of the cubical chains of a product of open pairs** `P = (X, A)` and
`Q = (Y, B)` is the relative singular homology of `(X × Y, A × Y ∪ X × B)`. -/
def cubicalChainComplexProdHomologyIso (hA : IsOpen A) (hB : IsOpen B) (n : ℕ) :
    ((ofSubset A).cubicalChainComplexProd k (ofSubset B)).homology n ≅
      (ofSubset (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B)).singularHomology (ModuleCat.of k k) n :=
  have := quasiIso_cubicalChainComplexProdToSingular k hA hB
  asIso (homologyMap (cubicalChainComplexProdToSingular k A B) n)

/-- The isomorphism `Hₙ(N(P × Q)) ≅ Hₙ(X × Y, A × Y ∪ X × B)` is induced by the comparison. -/
@[simp]
theorem cubicalChainComplexProdHomologyIso_hom (hA : IsOpen A) (hB : IsOpen B) (n : ℕ) :
    (cubicalChainComplexProdHomologyIso k hA hB n).hom =
      homologyMap (cubicalChainComplexProdToSingular k A B) n :=
  (rfl)

end Comparison

section Naturality

variable (k : Type u) [Ring k] {X Y X' Y' : TopCat.{u}} {A : Set X} {B : Set Y} {A' : Set X'}
  {B' : Set Y'} (g : X ⟶ X') (h : Y ⟶ Y') (hg : Set.MapsTo g A A') (hh : Set.MapsTo h B B')

include hg hh

/-- **Naturality of the comparison** of the cubical chains of a product of pairs with singular
chains, in maps `g : X ⟶ X'` and `h : Y ⟶ Y'` carrying `A` into `A'` and `B` into `B'`. -/
@[reassoc]
theorem cubicalChainComplexProdToSingular_naturality :
    cubicalChainComplexProdMap k (ofSubset A) (ofSubset B) (ofSubsetMap g hg) (ofSubsetMap h hh) ≫
        cubicalChainComplexProdToSingular k A' B' =
      cubicalChainComplexProdToSingular k A B ≫ TopPair.singularChainComplexMap
        (ofSubsetMap (g ⊗ₘ h) (TopCat.mapsTo_tensorHom_preimage_union g h hg hh))
        (ModuleCat.of k k) := by
  have hpair : prodLeftMap (ofSubsetMap h hh) (Hom.fst (ofSubsetMap g hg)) ≫
      prodLeftToPreimageUnion A' B' = prodLeftToPreimageUnion A B ≫
        ofSubsetMap (g ⊗ₘ h) (TopCat.mapsTo_tensorHom_preimage_union g h hg hh) :=
    hom_ext_of_fst _ (by
      -- `prodLeftMap_fst` must fire before `ofSubsetMap_fst` rewrites its argument.
      simp only [Hom.fst_comp, prodLeftMap_fst, prodLeftToPreimageUnion_fst]
      simp only [ofSubsetMap_fst]
      ext; rfl)
  refine coequalizer.hom_ext ?_
  rw [π_cubicalChainComplexProdMap_assoc, π_cubicalChainComplexProdToSingular,
    π_cubicalChainComplexProdToSingular_assoc, cubicalToSingularRel_naturality_assoc,
    ← TopPair.singularChainComplexMap_comp, ← TopPair.singularChainComplexMap_comp, hpair]

omit hg hh in
/-- **Naturality of the comparison in a map out of the product.** For a continuous map
`f : X × Y → Z` carrying `A × Y ∪ X × B` into `C`, carrying the cubical chains of the product of the
pairs `(X, A)` and `(Y, B)` along `f` to the relative cubical chains of `(Z, C)` and then to
singular chains is the comparison of the product with singular chains followed by the singular
chain map of `f`. -/
@[reassoc]
theorem cubicalChainComplexProdComparison_comp_cubicalToSingularRel {Z : Type u}
    [TopologicalSpace Z] {C : Set Z} (f : C(↑(X ⊗ Y), Z))
    (hf : Set.MapsTo (TopCat.ofHom (X := ↑(X ⊗ Y)) f) (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B) C) :
    (ofSubset A).cubicalChainComplexProdComparison k (ofSubset B) ≫
        cubicalChainComplexMap k
          (ofSubsetMap (TopCat.ofHom (X := ↑((ofSubset A).fst ⊗ (ofSubset B).fst)) f)
            (hf.mono_left (Set.union_subset_union (Set.preimage_mono range_ofSubset_map.subset)
              (Set.preimage_mono range_ofSubset_map.subset)))) ≫
          cubicalToSingularRel k (ofSubset (X := TopCat.of Z) C) =
      cubicalChainComplexProdToSingular k A B ≫
        TopPair.singularChainComplexMap (ofSubsetMap (X := X ⊗ Y) _ hf) (ModuleCat.of k k) := by
  refine coequalizer.hom_ext ?_
  rw [π_cubicalChainComplexProdComparison_assoc, ← Category.assoc, ← cubicalChainComplexMap_comp,
    cubicalToSingularRel_naturality, π_cubicalChainComplexProdToSingular_assoc,
    ← TopPair.singularChainComplexMap_comp]
  refine congrArg (_ ≫ TopPair.singularChainComplexMap · _) (hom_ext_of_fst _ ?_)
  simp only [Hom.fst_comp, prodLeftToProdSubspace_fst, prodLeftToPreimageUnion_fst, ofSubsetMap_fst]
  -- Both sides are `𝟙 _ ≫ TopCat.ofHom f`, with the identity typed on the ambient space of the
  -- product subspace on the left and on `X ⊗ Y` on the right; these agree only up to unfolding,
  -- so neither `rw [Category.id_comp]` nor `simp only [ofSubsetMap_fst]` can see the left
  -- composite.
  exact (Category.id_comp _).trans ((ofSubsetMap_fst _ _).trans (Category.id_comp _).symm)

end Naturality

section Kunneth

variable (k : Type u) [CommRing k] {X Y : TopCat.{u}} (A : Set X) (B : Set Y)

/-- **The Künneth map of a product of pairs in singular homology**,
`⨁_{p + q = n} Hₚ(X, A; k) ⊗ H_q(Y, B; k) ⟶ Hₙ(X × Y, A × Y ∪ X × B; k)`: the cubical Künneth map
of the product of the pairs `(X, A)` and `(Y, B)`, read in singular homology through the
comparison isomorphisms of the factors and the comparison of the cubical chains of the product of
pairs with singular chains. It is an isomorphism for open `A` and `B` over a field
(`TauCeti.isIso_singularHomologyKunnethPair_of_isSemisimpleRing`), and over any commutative ring
when the relative homology of `(X, A)` is projective
(`TauCeti.isIso_singularHomologyKunnethPair_of_projective`). -/
def singularHomologyKunnethPair (n : ℕ) :
    GradedObject.Monoidal.tensorObj
        (fun p ↦ (ofSubset A).singularHomology (ModuleCat.of k k) p)
        (fun q ↦ (ofSubset B).singularHomology (ModuleCat.of k k) q) n ⟶
      (ofSubset (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B)).singularHomology (ModuleCat.of k k) n :=
  GradedObject.Monoidal.tensorHom (fun p ↦ (TopPair.singularCubicalHomologyIso k _ p).hom)
      (fun q ↦ (TopPair.singularCubicalHomologyIso k _ q).hom) n ≫
    cubicalHomologyKunnethPair k (ofSubset A) (ofSubset B) n ≫
      homologyMap (cubicalChainComplexProdToSingular k A B) n

/-- On the summand of `Hₚ(X, A; k) ⊗ H_q(Y, B; k)`, the Künneth map of a product of pairs is the
cross product of the relative cubical classes, followed by the comparison with singular homology. -/
@[reassoc (attr := simp)]
theorem ι_singularHomologyKunnethPair (p q n : ℕ) (hpq : p + q = n) :
    GradedObject.Monoidal.ιTensorObj
        (fun p ↦ (ofSubset A).singularHomology (ModuleCat.of k k) p)
        (fun q ↦ (ofSubset B).singularHomology (ModuleCat.of k k) q) p q n hpq ≫
      singularHomologyKunnethPair k A B n =
      ((TopPair.singularCubicalHomologyIso k _ p).hom ⊗ₘ
          (TopPair.singularCubicalHomologyIso k _ q).hom) ≫
        homologyCross ((ofSubset A).cubicalChainComplex k) ((ofSubset B).cubicalChainComplex k)
          p q n hpq ≫
          homologyMap (cubicalCrossProductPair k (ofSubset A) (ofSubset B)) n ≫
            homologyMap (cubicalChainComplexProdToSingular k A B) n := by
  rw [singularHomologyKunnethPair, GradedObject.Monoidal.ι_tensorHom_assoc,
    ι_cubicalHomologyKunnethPair_assoc]

variable {A B} in
/-- The cubical cross product of pairs followed by the comparison with singular chains is natural
in maps `g : X ⟶ X'` and `h : Y ⟶ Y'` carrying `A` into `A'` and `B` into `B'`. -/
@[reassoc]
private theorem cubicalCrossProductPair_comp_toSingular_naturality {X' Y' : TopCat.{u}}
    {A' : Set X'} {B' : Set Y'} (g : X ⟶ X') (h : Y ⟶ Y') (hg : Set.MapsTo g A A')
    (hh : Set.MapsTo h B B') :
    HomologicalComplex.tensorHom (cubicalChainComplexMap k (ofSubsetMap g hg))
        (cubicalChainComplexMap k (ofSubsetMap h hh)) ≫
      cubicalCrossProductPair k (ofSubset A') (ofSubset B') ≫
        cubicalChainComplexProdToSingular k A' B' =
      cubicalCrossProductPair k (ofSubset A) (ofSubset B) ≫
        cubicalChainComplexProdToSingular k A B ≫ TopPair.singularChainComplexMap
          (ofSubsetMap (g ⊗ₘ h) (TopCat.mapsTo_tensorHom_preimage_union g h hg hh))
          (ModuleCat.of k k) := by
  -- The monoidal product of chain maps is `HomologicalComplex.tensorHom`.
  have hcross : HomologicalComplex.tensorHom (cubicalChainComplexMap k (ofSubsetMap g hg))
        (cubicalChainComplexMap k (ofSubsetMap h hh)) ≫
        cubicalCrossProductPair k (ofSubset A') (ofSubset B') =
      cubicalCrossProductPair k (ofSubset A) (ofSubset B) ≫
        cubicalChainComplexProdMap k (ofSubset A) (ofSubset B) (ofSubsetMap g hg)
          (ofSubsetMap h hh) :=
    cubicalCrossProductPair_naturality k (ofSubset A) (ofSubset B) (ofSubsetMap g hg)
      (ofSubsetMap h hh)
  rw [reassoc_of% hcross, cubicalChainComplexProdToSingular_naturality]

/-- **Naturality of the Künneth map of a product of pairs** in maps `g : X ⟶ X'` and
`h : Y ⟶ Y'` carrying `A` into `A'` and `B` into `B'`. -/
@[reassoc]
theorem singularHomologyKunnethPair_naturality {X' Y' : TopCat.{u}} {A' : Set X'} {B' : Set Y'}
    (g : X ⟶ X') (h : Y ⟶ Y') (hg : Set.MapsTo g A A') (hh : Set.MapsTo h B B') (n : ℕ) :
    GradedObject.Monoidal.tensorHom
        (fun p ↦ TopPair.singularHomologyMap (ofSubsetMap g hg) (ModuleCat.of k k) p)
        (fun q ↦ TopPair.singularHomologyMap (ofSubsetMap h hh) (ModuleCat.of k k) q) n ≫
      singularHomologyKunnethPair k A' B' n =
      singularHomologyKunnethPair k A B n ≫ TopPair.singularHomologyMap
        (ofSubsetMap (g ⊗ₘ h) (TopCat.mapsTo_tensorHom_preimage_union g h hg hh))
        (ModuleCat.of k k) n := by
  refine GradedObject.Monoidal.tensorObj_ext _ _ fun p q hpq ↦ ?_
  have hnat := congrArg (homologyMap · n)
    (cubicalCrossProductPair_comp_toSingular_naturality k g h hg hh)
  simp only [homologyMap_comp] at hnat
  -- Move the maps of the factors past the comparison isomorphisms and the homology cross product.
  rw [GradedObject.Monoidal.ι_tensorHom_assoc, ι_singularHomologyKunnethPair,
    ι_singularHomologyKunnethPair_assoc, tensorHom_comp_tensorHom_assoc,
    ← TopPair.singularCubicalHomologyIso_hom_naturality,
    ← TopPair.singularCubicalHomologyIso_hom_naturality, ← tensorHom_comp_tensorHom_assoc,
    homologyCross_naturality_assoc, hnat]

variable {A B}

/-- **The singular Künneth class of the image of a product of pairs.** Let `g : X ⟶ X'` and
`h : Y ⟶ Y'` carry `A` into `A'` and `B` into `B'`. Read in the singular homology of
`(X' × Y', A' × Y' ∪ X' × B')`, the image of the cubical cross product of the classes of `a` and
`b` in `Hₙ(N((X, A) × (Y, B)))` is the singular Künneth class of `g_* a` and `h_* b`. The pairs
`(X, A)` and `(Y, B)` need not be open, so their own cross product is only a class of cubical
chains: this is how its images in the singular homology of open pairs, such as the local homology
at a point, are computed. -/
@[reassoc]
theorem tensorHom_ι_cubicalHomologyKunnethPair_comp_cubicalChainComplexProdToSingular
    {X' Y' : TopCat.{u}} {A' : Set X'} {B' : Set Y'} (g : X ⟶ X')
    (h : Y ⟶ Y') (hg : Set.MapsTo g A A') (hh : Set.MapsTo h B B') (p q n : ℕ)
    (hpq : p + q = n) :
    ((TopPair.singularCubicalHomologyIso k (ofSubset A) p).hom ⊗ₘ
        (TopPair.singularCubicalHomologyIso k (ofSubset B) q).hom) ≫
      GradedObject.Monoidal.ιTensorObj (fun p ↦ ((ofSubset A).cubicalChainComplex k).homology p)
        (fun q ↦ ((ofSubset B).cubicalChainComplex k).homology q) p q n hpq ≫
        cubicalHomologyKunnethPair k (ofSubset A) (ofSubset B) n ≫
          homologyMap (cubicalChainComplexProdMap k (ofSubset A) (ofSubset B)
            (ofSubsetMap g hg) (ofSubsetMap h hh)) n ≫
            homologyMap (cubicalChainComplexProdToSingular k A' B') n =
      (TopPair.singularHomologyMap (ofSubsetMap g hg) (ModuleCat.of k k) p ⊗ₘ
          TopPair.singularHomologyMap (ofSubsetMap h hh) (ModuleCat.of k k) q) ≫
        GradedObject.Monoidal.ιTensorObj
          (fun p ↦ (ofSubset A').singularHomology (ModuleCat.of k k) p)
          (fun q ↦ (ofSubset B').singularHomology (ModuleCat.of k k) q) p q n hpq ≫
          singularHomologyKunnethPair k A' B' n := by
  -- Move the maps of the factors in front of the cubical Künneth map, then past the comparison
  -- isomorphisms, and read both sides on the summand of `(p, q)`.
  rw [← cubicalHomologyKunnethPair_naturality_assoc, GradedObject.Monoidal.ι_tensorHom_assoc,
    tensorHom_comp_tensorHom_assoc, TopPair.singularCubicalHomologyIso_hom_naturality,
    TopPair.singularCubicalHomologyIso_hom_naturality, ← tensorHom_comp_tensorHom_assoc,
    ι_singularHomologyKunnethPair, ι_cubicalHomologyKunnethPair_assoc]

/-- **The Künneth theorem for a product of open pairs** in singular homology: for open `A ⊆ X`
and `B ⊆ Y`, the Künneth map
`⨁_{p + q = n} Hₚ(X, A; k) ⊗ H_q(Y, B; k) ⟶ Hₙ(X × Y, A × Y ∪ X × B; k)` is an isomorphism as
soon as the cubical Künneth map of the product of the pairs is. -/
theorem isIso_singularHomologyKunnethPair (hA : IsOpen A) (hB : IsOpen B) (n : ℕ)
    [IsIso (cubicalHomologyKunnethPair k (ofSubset A) (ofSubset B) n)] :
    IsIso (singularHomologyKunnethPair k A B n) := by
  have := quasiIso_cubicalChainComplexProdToSingular k hA hB
  -- The `n`-th component of the monoidal product of the isomorphisms of graded objects assembled
  -- from the comparison isomorphisms is by definition the monoidal product of their components.
  have : IsIso (GradedObject.Monoidal.tensorHom
      (fun p ↦ (TopPair.singularCubicalHomologyIso k (ofSubset A) p).hom)
      (fun q ↦ (TopPair.singularCubicalHomologyIso k (ofSubset B) q).hom) n) :=
    inferInstanceAs (IsIso (GradedObject.Monoidal.tensorIso
      (GradedObject.isoMk _ _ fun p ↦ TopPair.singularCubicalHomologyIso k (ofSubset A) p)
      (GradedObject.isoMk _ _ fun q ↦ TopPair.singularCubicalHomologyIso k (ofSubset B) q)
      |>.hom n))
  rw [singularHomologyKunnethPair]
  infer_instance

/-- **The Künneth theorem for a product of open pairs over a field**: for open `A ⊆ X` and
`B ⊆ Y` and a commutative semisimple ring `k`,
`⨁_{p + q = n} Hₚ(X, A; k) ⊗ H_q(Y, B; k) ≅ Hₙ(X × Y, A × Y ∪ X × B; k)`. -/
theorem isIso_singularHomologyKunnethPair_of_isSemisimpleRing [IsSemisimpleRing k]
    (hA : IsOpen A) (hB : IsOpen B) (n : ℕ) :
    IsIso (singularHomologyKunnethPair k A B n) :=
  isIso_singularHomologyKunnethPair k hA hB n

/-- **The Künneth theorem for a product of open pairs with projective homology**: for open
`A ⊆ X` and `B ⊆ Y`, if the relative singular homology modules `Hₚ(X, A; k)` are all projective,
then `⨁_{p + q = n} Hₚ(X, A; k) ⊗ H_q(Y, B; k) ≅ Hₙ(X × Y, A × Y ∪ X × B; k)`. No condition is
placed on the pair `(Y, B)`. This applies over `ℤ` to the local homology of manifolds, which is
free. -/
theorem isIso_singularHomologyKunnethPair_of_projective (hA : IsOpen A) (hB : IsOpen B)
    [hA' : ∀ p, Projective ((ofSubset A).singularHomology (ModuleCat.of k k) p)] (n : ℕ) :
    IsIso (singularHomologyKunnethPair k A B n) := by
  have (p : ℕ) : Projective (((ofSubset A).cubicalChainComplex k).homology p) :=
    Projective.of_iso (TopPair.singularCubicalHomologyIso k _ p) (hA' p)
  have := isIso_cubicalHomologyKunnethPair_of_projective k (ofSubset A) (ofSubset B) n
  exact isIso_singularHomologyKunnethPair k hA hB n

end Kunneth

end TauCeti

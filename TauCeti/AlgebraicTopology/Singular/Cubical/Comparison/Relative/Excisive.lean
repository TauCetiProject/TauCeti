/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Cubical.Comparison.Excision
public import TauCeti.AlgebraicTopology.Singular.Cubical.Comparison.Relative.Prod
public import TauCeti.CategoryTheory.Abelian.DiagramLemmas.CokernelComp

/-!
# Relative cubical chains of an excisive product of pairs

For topological pairs `P = (X, A)` and `Q = (Y, B)`, the relative cubical chains of the product
pair are the complex `N(P × Q) = N(X × Y) ⧸ (N(A × Y) + N(X × B))`
(`TopPair.cubicalChainComplexProd`), the target of the cross product of pairs
`N(X, A) ⊗ N(Y, B) ⟶ N(P × Q)`. This file compares it with the relative cubical chains of the
genuine pair `(X × Y, A × Y ∪ X × B)`, whose subspace is `TopPair.prodSubspace P Q`.

The chains supported in `A × Y` or in `X × B` are supported in their union, so the identity of
`X × Y` induces a comparison map (`TopPair.cubicalChainComplexProdComparison`)

`N(P × Q) ⟶ N(X × Y, A × Y ∪ X × B)`.

It is a quasi-isomorphism as soon as `A × Y` and `X × B` form an excisive couple, in the sense
that the excision map of pairs `(A × Y, A × B) ⟶ (A × Y ∪ X × B, X × B)`
(`TopPair.prodExcisionMap`) induces isomorphisms on relative singular homology
(`TopPair.quasiIso_cubicalChainComplexProdComparison_of_isIso`). The proof is the five lemma for
the morphism of short exact sequences

```
0 ⟶ N(A × Y, A × B)          ⟶ N(X × Y, X × B) ⟶ N(P × Q)                    ⟶ 0
          │ excision                  │ identity       │ comparison
0 ⟶ N(A × Y ∪ X × B, X × B) ⟶ N(X × Y, X × B) ⟶ N(X × Y, A × Y ∪ X × B) ⟶ 0
```

whose top row is `TopPair.shortExact_cubicalChainComplexProdShortComplex` and whose bottom row is
the sequence of the triple `X × B ⊆ A × Y ∪ X × B ⊆ X × Y`, short exact by the third isomorphism
theorem (`TauCeti.shortExact_of_isColimit_cokernelCofork`). Excision for open covers
(`TopPair.isIso_singularHomologyMap_of_open_cover`) supplies the hypothesis when the interiors of
`A × Y` and `X × B` in their union cover it
(`TopPair.quasiIso_cubicalChainComplexProdComparison`), in particular when `A` and `B` are open
(`TopPair.quasiIso_cubicalChainComplexProdComparison_of_isOpen`).

Together with the Eilenberg–Zilber theorem for a product of pairs
(`TauCeti.quasiIso_cubicalCrossProductPair`), this makes the cross product of relative chains a
quasi-isomorphism onto the relative chains of `(X × Y, A × Y ∪ X × B)` for excisive couples: for
instance for the local homology `H(M × N, M × N ∖ {(x, y)})` of a product of manifolds, with `A`
and `B` the open complements of points. For the pair `(M, ∂M) × (N, ∂N)` of two manifolds with
boundary the subspaces are closed, and the excision hypothesis is the one to verify, for
instance through collars.

## Main definitions

* `TopPair.cubicalChainComplexProdComparison k P Q`: the comparison map
  `N(P × Q) ⟶ N(X × Y, A × Y ∪ X × B)`.

## Main results

* `TopPair.quasiIso_cubicalChainComplexProdComparison_of_isIso`: the comparison map is a
  quasi-isomorphism when the excision map induces isomorphisms on relative singular homology.
* `TopPair.quasiIso_cubicalChainComplexProdComparison`: the same when the interiors of `A × Y` and
  `X × B` cover `A × Y ∪ X × B`.
* `TopPair.quasiIso_cubicalChainComplexProdComparison_of_isOpen`: the same when `A` and `B` are
  open.

## References

* W. S. Massey, *Singular Homology Theory*, GTM 70, Springer, 1980, Chapter VII.
* E. H. Spanier, *Algebraic Topology*, McGraw-Hill, 1966, Chapter 4, Section 6 (excisive couples)
  and Chapter 5, Section 3 (the relative Künneth formula).
* A. Hatcher, *Algebraic Topology*, Section 3.B.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory Topology

universe u

namespace TopPair

open TauCeti

variable (k : Type u) [Ring k] (P Q : TopPair.{u})

/-! ### The comparison map -/

/-- The **comparison map** `N(P × Q) ⟶ N(X × Y, A × Y ∪ X × B)` from the relative cubical chains
of the product of pairs `P = (X, A)` and `Q = (Y, B)` to those of the pair
`(X × Y, A × Y ∪ X × B)`, induced by the identity of `X × Y`: chains supported in `A × Y` or in
`X × B` are supported in their union. -/
def cubicalChainComplexProdComparison :
    P.cubicalChainComplexProd k Q ⟶ (ofSubset (P.prodSubspace Q)).cubicalChainComplex k :=
  cokernel.desc _ (cubicalChainComplexMap k (P.prodLeftToProdSubspace Q)) (by
    rw [← cubicalChainComplexMap_comp]
    -- The ambient map `A × Y ⟶ X × Y` factors through `A × Y ∪ X × B`.
    exact cubicalChainComplexMap_eq_zero_of_fac k _ (P.prodSubspaceInl Q) (by
      rw [Hom.fst_comp, prodLeftToProdSubspace_fst]
      exact P.prodSubspaceInl_comp_map Q))

/-- The comparison map is induced by the map of pairs `(X × Y, X × B) ⟶ (X × Y, A × Y ∪ X × B)`. -/
@[reassoc (attr := simp)]
theorem π_cubicalChainComplexProdComparison :
    cokernel.π _ ≫ P.cubicalChainComplexProdComparison k Q =
      cubicalChainComplexMap k (P.prodLeftToProdSubspace Q) :=
  cokernel.π_desc _ _ _

/-- The sequence `N(A × Y ∪ X × B, X × B) ⟶ N(X × Y, X × B) ⟶ N(X × Y, A × Y ∪ X × B)` of the
triple `X × B ⊆ A × Y ∪ X × B ⊆ X × Y`. -/
private abbrev prodSubspaceShortComplex : ShortComplex (ChainComplex (ModuleCat.{u} k) ℕ) :=
  ShortComplex.mk (cubicalChainComplexMap k (P.prodExcisionPairToProdLeft Q))
    (cubicalChainComplexMap k (P.prodLeftToProdSubspace Q)) (by
      rw [← cubicalChainComplexMap_comp]
      -- The ambient map is the inclusion of `A × Y ∪ X × B` into `X × Y`.
      exact cubicalChainComplexMap_eq_zero_of_fac k _ (𝟙 _) (by
        rw [Hom.fst_comp, prodExcisionPairToProdLeft_fst, prodLeftToProdSubspace_fst]
        exact (Category.id_comp _).trans (Category.comp_id _).symm))

/-- The sequence of the triple `X × B ⊆ A × Y ∪ X × B ⊆ X × Y` is short exact: each term is a
quotient of chains, and the relative chains of `(X × Y, A × Y ∪ X × B)` are the quotient of those
of `(X × Y, X × B)` by those of `(A × Y ∪ X × B, X × B)`. -/
private theorem shortExact_prodSubspaceShortComplex :
    (prodSubspaceShortComplex k P Q).ShortExact := by
  have hu := π_cubicalChainComplexMap k (P.prodExcisionPairToProdLeft Q)
  rw [prodExcisionPairToProdLeft_fst] at hu
  -- The map of pairs `(X × Y, X × B) ⟶ (X × Y, A × Y ∪ X × B)` is the identity of `X × Y`.
  have hv : cokernel.π _ ≫ cubicalChainComplexMap k (P.prodLeftToProdSubspace Q) =
      cokernel.π _ := by
    rw [π_cubicalChainComplexMap, prodLeftToProdSubspace_fst]
    exact (congrArg (· ≫ _) ((normalizedCubicalChainComplex k).map_id _)).trans
      (Category.id_comp _)
  -- `X × B ⊆ A × Y ∪ X × B ⊆ X × Y` composes to the inclusion `X × B ⊆ X × Y`.
  exact shortExact_of_isColimit_cokernelCofork
    (((normalizedCubicalChainComplex k).map_comp _ _).symm.trans
      (congrArg _ (P.prodSubspaceInr_comp_map Q)))
    (mono_normalizedCubicalChainComplex_map k _)
    (cokernelIsCokernel _) (cokernelIsCokernel _) (cokernelIsCokernel _) hu hv

/-- The morphism from the sequence of the product of pairs to the sequence of the triple
`X × B ⊆ A × Y ∪ X × B ⊆ X × Y`, given by the excision map, the identity and the comparison map. -/
private def prodSubspaceShortComplexMap :
    P.cubicalChainComplexProdShortComplex k Q ⟶ prodSubspaceShortComplex k P Q where
  τ₁ := cubicalChainComplexMap k (P.prodExcisionMap Q)
  τ₂ := 𝟙 _
  τ₃ := P.cubicalChainComplexProdComparison k Q
  comm₁₂ := by
    dsimp
    rw [← cubicalChainComplexMap_comp, prodExcisionMap_comp_prodExcisionPairToProdLeft,
      Category.comp_id]
  comm₂₃ := by
    dsimp
    rw [π_cubicalChainComplexProdComparison, Category.id_comp]

/-- **The relative cubical chains of an excisive product of pairs.** If the excision map
`(A × Y, A × B) ⟶ (A × Y ∪ X × B, X × B)` induces isomorphisms on relative singular homology, then
the comparison map `N(P × Q) ⟶ N(X × Y, A × Y ∪ X × B)` is a quasi-isomorphism, so the homology of
`N(P × Q)` is the relative homology of `(X × Y, A × Y ∪ X × B)`. -/
theorem quasiIso_cubicalChainComplexProdComparison_of_isIso
    (h : ∀ n, IsIso (TopPair.singularHomologyMap (P.prodExcisionMap Q) (ModuleCat.of k k) n)) :
    QuasiIso (P.cubicalChainComplexProdComparison k Q) := by
  have : QuasiIso (cubicalChainComplexMap k (P.prodExcisionMap Q)) := by
    rw [quasiIso_iff]
    intro n
    rw [quasiIsoAt_iff_isIso_homologyMap]
    have := h n
    exact isIso_homologyMap_cubicalChainComplexMap_of_isIso _ n
  exact HomologicalComplex.HomologySequence.quasiIso_τ₃ (prodSubspaceShortComplexMap k P Q)
    (P.shortExact_cubicalChainComplexProdShortComplex k Q)
    (shortExact_prodSubspaceShortComplex k P Q) this (inferInstanceAs (QuasiIso (𝟙 _)))

/-- **The relative cubical chains of a product of pairs with covering interiors.** If the
interiors of `A × Y` and `X × B` in `A × Y ∪ X × B` cover it, then the comparison map
`N(P × Q) ⟶ N(X × Y, A × Y ∪ X × B)` is a quasi-isomorphism. -/
theorem quasiIso_cubicalChainComplexProdComparison
    (h : interior ((↑) ⁻¹' (CartesianMonoidalCategory.fst P.fst Q.fst ⁻¹' Set.range P.map) :
        Set (P.prodSubspace Q)) ∪
      interior ((↑) ⁻¹' (CartesianMonoidalCategory.snd P.fst Q.fst ⁻¹' Set.range Q.map) :
        Set (P.prodSubspace Q)) = Set.univ) :
    QuasiIso (P.cubicalChainComplexProdComparison k Q) := by
  refine quasiIso_cubicalChainComplexProdComparison_of_isIso k P Q fun n ↦
    isIso_singularHomologyMap_of_open_cover _ (P.prodExcisionMap Q)
      (by rw [prodExcisionMap_fst]; exact P.isEmbedding_prodSubspaceInl Q) ?_ _ (fun b ↦ ?_)
      (Set.union_eq_iUnion.symm.trans h) (fun b ↦ ?_) n
  · -- A point `(a, y)` of `A × Y` lying in `X × B` lies in `A × B`.
    rintro ⟨a, y⟩ ⟨⟨x, b⟩, hxb⟩
    rw [prodExcisionMap_fst] at hxb
    -- In `X × Y`, `hxb` says `(x, Q.map b) = (P.map a, y)`; compare second coordinates.
    have hy : Q.map b = y := congrArg Prod.snd ((P.coe_prodSubspaceInr_apply Q _).symm.trans
      ((congrArg Subtype.val hxb).trans (P.coe_prodSubspaceInl_apply Q _)))
    exact ⟨(a, b), Prod.ext rfl hy⟩
  · cases b <;> exact isOpen_interior
  · cases b
    · -- Points with second coordinate in `B` lie in `X × B`.
      refine Or.inl fun x hx ↦ ?_
      obtain ⟨b, hb⟩ := interior_subset hx
      exact ⟨(x.val.1, b), Subtype.ext ((P.coe_prodSubspaceInr_apply Q _).trans (Prod.ext rfl hb))⟩
    · -- Points with first coordinate in `A` lie in `A × Y`.
      refine Or.inr fun x hx ↦ ?_
      obtain ⟨a, ha⟩ := interior_subset hx
      rw [prodExcisionMap_fst]
      exact ⟨(a, x.val.2), Subtype.ext ((P.coe_prodSubspaceInl_apply Q _).trans (Prod.ext ha rfl))⟩

/-- **The relative cubical chains of a product of pairs with open subspaces.** If `A` is open in
`X` and `B` is open in `Y`, then the comparison map `N(P × Q) ⟶ N(X × Y, A × Y ∪ X × B)` is a
quasi-isomorphism. -/
theorem quasiIso_cubicalChainComplexProdComparison_of_isOpen (hA : IsOpen (Set.range P.map))
    (hB : IsOpen (Set.range Q.map)) : QuasiIso (P.cubicalChainComplexProdComparison k Q) := by
  refine quasiIso_cubicalChainComplexProdComparison k P Q ?_
  rw [(TopCat.isOpen_subtypeVal_preimage_preimage_fst_union hA).interior_eq,
    (TopCat.isOpen_subtypeVal_preimage_preimage_snd_union hB).interior_eq]
  exact Set.eq_univ_of_forall fun x ↦ x.property

end TopPair

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Cubical.Comparison.Relative.Basic
public import TauCeti.AlgebraicTopology.Singular.Cubical.Relative

/-!
# Relative cubical chains of a product of pairs

For topological pairs `P = (X, A)` and `Q = (Y, B)`, the relative cubical chains of the product
pair `P × Q = (X × Y, A × Y ∪ X × B)` are the chains of `X × Y` modulo the chains supported in
`A × Y` or in `X × B`:

`N(P × Q) = N(X × Y) ⧸ (N(A × Y) + N(X × B))`.

We realize this complex (`TopPair.cubicalChainComplexProd`) as the cokernel of the map
`N(A × Y, A × B) ⟶ N(X × Y, X × B)` of relative chains induced by the inclusion of pairs. This map
is a monomorphism (`TopPair.mono_cubicalChainComplexMap_prodLeftMap`): a normalized chain of
`X × Y` supported both in `A × Y` and in `X × B` is supported in their intersection `A × B`
(`TauCeti.NormalizedCubicalChain.supportedIn_inter`). So the sequence

`0 ⟶ N(A × Y, A × B) ⟶ N(X × Y, X × B) ⟶ N(P × Q) ⟶ 0`

is short exact (`TopPair.shortExact_cubicalChainComplexProdShortComplex`). The complex is
functorial in both pairs (`TopPair.cubicalChainComplexProdMap`).

No hypothesis is placed on the subspaces. When the interiors of `A × Y` and `X × B` cover
`A × Y ∪ X × B`, for instance when `A` and `B` are open, the small-chain theorem identifies the
homology of `N(P × Q)` with the relative homology of `(X × Y, A × Y ∪ X × B)`; that comparison is
not made here.

## Main definitions

* `TopPair.cubicalChainComplexProd k P Q`: the relative cubical chains `N(P × Q)` of a product of
  pairs.
* `TopPair.cubicalChainComplexProdShortComplex k P Q`: the sequence
  `N(A × Y, A × B) ⟶ N(X × Y, X × B) ⟶ N(P × Q)`.
* `TopPair.cubicalChainComplexProdMap k P Q f g`: the map induced by maps of pairs `f` and `g`.

## Main results

* `TopPair.mono_cubicalChainComplexMap_prodLeftMap`: `N(A × Y, A × B) ⟶ N(X × Y, X × B)` is a
  monomorphism.
* `TopPair.shortExact_cubicalChainComplexProdShortComplex`: the sequence above is short exact.

## References

* W. S. Massey, *Singular Homology Theory*, GTM 70, Springer, 1980, Chapter VII.
* A. Hatcher, *Algebraic Topology*, Section 3.B.
-/

public section

noncomputable section

open CategoryTheory HomologicalComplex Limits

universe u

namespace TopPair

open TauCeti

variable (k : Type u) [Ring k] (P Q : TopPair.{u})

/-- A point of `X × Y` lies in the images of both `A × Y` and `X × B` exactly when it lies in
the image of `A × B`. -/
private theorem range_inter_range :
    Set.range (Hom.fst (prodLeftMap (𝟙 Q) P.map)) ∩ Set.range (Q.prodLeft P.fst).map =
      Set.range (Hom.fst (prodLeftMap (𝟙 Q) P.map) ∘ (Q.prodLeft P.snd).map) := by
  -- `prodLeft` and `prodLeftMap` are abbreviations for `TopPair.of (X ◁ P.map)` and
  -- `TopPair.ofHom (g ⊗ₘ Hom.fst f) _ _`, and on points `◁` and `⊗ₘ` in `TopCat` are `Prod.map`
  -- by definition (`TopCat.whiskerLeft_apply`, `TopCat.tensor_apply`). Mathlib has no evaluation
  -- lemmas for the maps of `TopPair.of` and `TopPair.ofHom`, which are built with
  -- `MorphismProperty.Arrow.mk` and `MorphismProperty.Arrow.homMk`, so `simp` cannot reach those
  -- lemmas, and we unfold the three maps to `Prod.map` directly.
  change Set.range (Prod.map P.map id) ∩ Set.range (Prod.map id Q.map) =
    Set.range (Prod.map P.map Q.map)
  simp only [Set.range_prodMap, Set.range_id, Set.prod_inter_prod, Set.inter_univ, Set.univ_inter]

/-- The inclusion of pairs `(A × Y, A × B) ⟶ (X × Y, X × B)` induces a monomorphism of relative
cubical chains: a chain of `A × Y` whose image in `X × Y` is supported in `X × B` is supported in
`A × B`. -/
instance mono_cubicalChainComplexMap_prodLeftMap :
    Mono (cubicalChainComplexMap k (prodLeftMap (𝟙 Q) P.map)) := by
  refine HomologicalComplex.mono_of_mono_f _ fun n ↦ (ModuleCat.mono_iff_injective _).2 ?_
  have h₁ := (HomologicalComplex.shortExact_iff_degreewise_shortExact _).1
    ((Q.prodLeft P.snd).shortExact_cubicalChainComplexShortComplex k) n
  have h₂ := (HomologicalComplex.shortExact_iff_degreewise_shortExact _).1
    ((Q.prodLeft P.fst).shortExact_cubicalChainComplexShortComplex k) n
  refine (injective_iff_map_eq_zero _).2 fun x hx ↦ ?_
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective _).1 h₁.epi_g x
  set f := Hom.fst (prodLeftMap (𝟙 Q) P.map)
  have hf : Topology.IsEmbedding f := P.isEmbedding_map.prodMap Topology.IsEmbedding.id
  have hz := ConcreteCategory.congr_hom
    (congrArg (fun φ ↦ φ.f n) (π_cubicalChainComplexMap k (prodLeftMap (𝟙 Q) P.map))) z
  rw [comp_f, comp_f, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hz
  -- The image of `z` in the chains of `X × Y` is supported in `X × B` and in `A × Y`.
  obtain ⟨w, hw⟩ := (ShortComplex.moduleCat_exact_iff _).1 h₂.exact _ (hz.symm.trans hx)
  have hz₁ : NormalizedCubicalChain.map k f.hom n z ∈
      NormalizedCubicalChain.supportedIn k (Set.range f) n := by
    rw [← NormalizedCubicalChain.range_map_eq_supportedIn_range k hf.isInducing n]
    exact LinearMap.mem_range_self _ z
  have hz₂ : NormalizedCubicalChain.map k f.hom n z ∈
      NormalizedCubicalChain.supportedIn k (Set.range (Q.prodLeft P.fst).map) n := by
    rw [← NormalizedCubicalChain.range_map_eq_supportedIn_range k
      (Q.prodLeft P.fst).isEmbedding_map.isInducing n]
    exact ⟨w, hw⟩
  have hz₃ := Submodule.mem_inf.2 ⟨hz₁, hz₂⟩
  rw [← NormalizedCubicalChain.supportedIn_inter, range_inter_range] at hz₃
  -- So it comes from `A × B`, and `z` itself comes from `A × B`.
  obtain ⟨u, hu⟩ := (NormalizedCubicalChain.range_map_eq_supportedIn_range k
    (f := f.hom.comp (Q.prodLeft P.snd).map.hom)
    (hf.isInducing.comp (Q.prodLeft P.snd).isEmbedding_map.isInducing) n).symm ▸ hz₃
  rw [NormalizedCubicalChain.map_comp, LinearMap.comp_apply] at hu
  obtain rfl := NormalizedCubicalChain.map_injective k _ hf.injective n hu
  exact ConcreteCategory.congr_hom (cubicalChainComplex_condition_f k (Q.prodLeft P.snd) n) u

/-- The **relative cubical chains of a product of pairs** `P × Q = (X × Y, A × Y ∪ X × B)`, for
`P = (X, A)` and `Q = (Y, B)`: the chains of `X × Y` modulo those supported in `A × Y` or in
`X × B`, realized as the cokernel of `N(A × Y, A × B) ⟶ N(X × Y, X × B)`. -/
abbrev cubicalChainComplexProd : ChainComplex (ModuleCat.{u} k) ℕ :=
  cokernel (cubicalChainComplexMap k (prodLeftMap (𝟙 Q) P.map))

/-- The sequence `N(A × Y, A × B) ⟶ N(X × Y, X × B) ⟶ N(P × Q)` of relative cubical chains. -/
abbrev cubicalChainComplexProdShortComplex : ShortComplex (ChainComplex (ModuleCat.{u} k) ℕ) :=
  ShortComplex.mk _ _ (cokernel.condition (cubicalChainComplexMap k (prodLeftMap (𝟙 Q) P.map)))

/-- The sequence `0 ⟶ N(A × Y, A × B) ⟶ N(X × Y, X × B) ⟶ N(P × Q) ⟶ 0` is short exact. -/
theorem shortExact_cubicalChainComplexProdShortComplex :
    (P.cubicalChainComplexProdShortComplex k Q).ShortExact :=
  ShortComplex.ShortExact.mk' (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _))
    (mono_cubicalChainComplexMap_prodLeftMap k P Q) (by dsimp; infer_instance)

/-- A map of pairs `(A × Y, A × B) ⟶ (X × Y, X × B)` followed by a product of maps of pairs is the
product of maps of pairs followed by the inclusion `(A' × Y', A' × B') ⟶ (X' × Y', X' × B')`. -/
private theorem cubicalChainComplexMap_prodLeftMap_comm {P' Q' : TopPair.{u}} (f : P ⟶ P')
    (g : Q ⟶ Q') :
    cubicalChainComplexMap k (prodLeftMap (𝟙 Q) P.map) ≫
        cubicalChainComplexMap k (prodLeftMap g (Hom.fst f)) =
      cubicalChainComplexMap k (prodLeftMap g (Hom.snd f)) ≫
        cubicalChainComplexMap k (prodLeftMap (𝟙 Q') P'.map) := by
  rw [← cubicalChainComplexMap_comp, ← cubicalChainComplexMap_comp, ← prodLeftMap_comp,
    ← prodLeftMap_comp, Category.id_comp, Category.comp_id, Hom.w]

/-- The map of relative cubical chains of products of pairs `N(P × Q) ⟶ N(P' × Q')` induced by
maps of pairs `f : P ⟶ P'` and `g : Q ⟶ Q'`. -/
def cubicalChainComplexProdMap {P' Q' : TopPair.{u}} (f : P ⟶ P') (g : Q ⟶ Q') :
    P.cubicalChainComplexProd k Q ⟶ P'.cubicalChainComplexProd k Q' :=
  cokernel.map _ _ (cubicalChainComplexMap k (prodLeftMap g (Hom.snd f)))
    (cubicalChainComplexMap k (prodLeftMap g (Hom.fst f)))
    (cubicalChainComplexMap_prodLeftMap_comm k P Q f g)

/-- The map of chains of products of pairs is induced by the map of relative chains
`N(X × Y, X × B) ⟶ N(X' × Y', X' × B')`. -/
@[reassoc (attr := simp)]
theorem π_cubicalChainComplexProdMap {P' Q' : TopPair.{u}} (f : P ⟶ P') (g : Q ⟶ Q') :
    cokernel.π _ ≫ cubicalChainComplexProdMap k P Q f g =
      cubicalChainComplexMap k (prodLeftMap g (Hom.fst f)) ≫ cokernel.π _ := by
  simp [cubicalChainComplexProdMap]

/-- The identity maps of pairs induce the identity. -/
@[simp]
theorem cubicalChainComplexProdMap_id :
    cubicalChainComplexProdMap k P Q (𝟙 P) (𝟙 Q) = 𝟙 (P.cubicalChainComplexProd k Q) :=
  coequalizer.hom_ext (by simp)

/-- The induced maps of chains of products of pairs are functorial. -/
@[simp]
theorem cubicalChainComplexProdMap_comp {P' Q' P'' Q'' : TopPair.{u}} (f : P ⟶ P') (g : Q ⟶ Q')
    (f' : P' ⟶ P'') (g' : Q' ⟶ Q'') :
    cubicalChainComplexProdMap k P Q (f ≫ f') (g ≫ g') =
      cubicalChainComplexProdMap k P Q f g ≫ cubicalChainComplexProdMap k P' Q' f' g' :=
  coequalizer.hom_ext (by simp)

end TopPair

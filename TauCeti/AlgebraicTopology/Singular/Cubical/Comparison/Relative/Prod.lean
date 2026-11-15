/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Cubical.Comparison.Excision
public import TauCeti.AlgebraicTopology.Singular.Cubical.Comparison.Relative.Triple
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

No hypothesis is placed on the subspaces in the construction. The identity of `X × Y` induces a
comparison map `N(P × Q) ⟶ N(X × Y, A × Y ∪ X × B)` to the relative chains of the pair
`(X × Y, A × Y ∪ X × B)` (`TopPair.cubicalChainComplexProdToOfSubset`), where `A × Y ∪ X × B` is the
union of the preimages of `A` and `B` under the two projections (`TopPair.prodSubspace`). When the
interiors of `A × Y` and `X × B` cover `A × Y ∪ X × B`, for instance when `A` and `B` are open,
this map is a quasi-isomorphism (`TopPair.quasiIso_cubicalChainComplexProdToOfSubset`), so the
homology of `N(P × Q)` is the relative homology of `(X × Y, A × Y ∪ X × B)`. The proof compares
the sequence above with the short exact sequence of the triple `(X × Y, A × Y ∪ X × B, X × B)`
(`TauCeti.TopTriple.shortExact_cubicalChainComplexShortComplex`): on the first terms the inclusion
`(A × Y, A × B) ⟶ (A × Y ∪ X × B, X × B)` is an excision, which induces isomorphisms on relative
homology under the hypothesis on the interiors, and on the second terms it is the identity of
`(X × Y, X × B)`, so the five lemma applies.

## Main definitions

* `TopPair.cubicalChainComplexProd k P Q`: the relative cubical chains `N(P × Q)` of a product of
  pairs.
* `TopPair.cubicalChainComplexProdShortComplex k P Q`: the sequence
  `N(A × Y, A × B) ⟶ N(X × Y, X × B) ⟶ N(P × Q)`.
* `TopPair.cubicalChainComplexProdMap k P Q f g`: the map induced by maps of pairs `f` and `g`.
* `TopPair.prodSubspace P Q`: the subspace `A × Y ∪ X × B` of `X × Y`.
* `TopPair.cubicalChainComplexProdToOfSubset k P Q`: the comparison map
  `N(P × Q) ⟶ N(X × Y, A × Y ∪ X × B)`.

## Main results

* `TopPair.mono_cubicalChainComplexMap_prodLeftMap`: `N(A × Y, A × B) ⟶ N(X × Y, X × B)` is a
  monomorphism.
* `TopPair.shortExact_cubicalChainComplexProdShortComplex`: the sequence above is short exact.
* `TopPair.quasiIso_cubicalChainComplexProdToOfSubset`,
  `TopPair.quasiIso_cubicalChainComplexProdToOfSubset_of_isOpen`: when the interiors of `A × Y`
  and `X × B` cover their union, for instance when `A` and `B` are open, the comparison map is a
  quasi-isomorphism.

## References

* W. S. Massey, *Singular Homology Theory*, GTM 70, Springer, 1980, Chapter VII.
* A. Hatcher, *Algebraic Topology*, Section 2.1 (excision) and Section 3.B.
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

/-! ### Comparison with the relative chains of `(X × Y, A × Y ∪ X × B)` -/

section Subspace

open MonoidalCategory

/-- The subspace `A × Y ∪ X × B` of `X × Y`, for pairs `P = (X, A)` and `Q = (Y, B)`: the union of
the preimages of `A` and of `B` under the two projections. -/
abbrev prodSubspace : Set (P.fst ⊗ Q.fst : TopCat.{u}) :=
  CartesianMonoidalCategory.fst P.fst Q.fst ⁻¹' Set.range P.map ∪
    CartesianMonoidalCategory.snd P.fst Q.fst ⁻¹' Set.range Q.map

/-- The map of pairs `(X × Y, X × B) ⟶ (X × Y, A × Y ∪ X × B)` induced by the identity of `X × Y`,
for pairs `P = (X, A)` and `Q = (Y, B)`. -/
def prodLeftToProdSubspace : Q.prodLeft P.fst ⟶ ofSubset (prodSubspace P Q) :=
  ofHom (𝟙 _) (TopCat.ofHom ⟨fun x ↦ ⟨(Q.prodLeft P.fst).map x, .inr ⟨x.2, rfl⟩⟩,
    (Q.prodLeft P.fst).map.hom.continuous.subtype_mk _⟩) (by ext x; rfl)

@[simp]
theorem prodLeftToProdSubspace_fst : Hom.fst (prodLeftToProdSubspace P Q) = 𝟙 _ :=
  (rfl)

/-- The triple `(X × Y, A × Y ∪ X × B, X × B)`. -/
private abbrev prodSubspaceTriple : TopTriple.{u} :=
  TopTriple.of (Hom.snd (prodLeftToProdSubspace P Q)) (ofSubset (prodSubspace P Q)).map
    (Topology.IsEmbedding.subtypeVal.of_comp_iff.1 (Q.prodLeft P.fst).isEmbedding_map)
    (ofSubset _).isEmbedding_map

/-- The inclusion of pairs `(A × Y, A × B) ⟶ (A × Y ∪ X × B, X × B)`. -/
private def prodLeftToInnerPair :
    Q.prodLeft P.snd ⟶ TopTriple.innerPair.obj (prodSubspaceTriple P Q) :=
  ofHom (TopCat.ofHom ⟨fun x ↦ ⟨Hom.fst (prodLeftMap (𝟙 Q) P.map) x, .inl ⟨x.1, rfl⟩⟩,
      (Hom.fst (prodLeftMap (𝟙 Q) P.map)).hom.continuous.subtype_mk _⟩)
    (Hom.snd (X := Q.prodLeft P.snd) (Y := Q.prodLeft P.fst) (prodLeftMap (𝟙 Q) P.map))
    (by ext x; exact Subtype.ext (Hom.w_apply (prodLeftMap (𝟙 Q) P.map) x))

/-- The identity of `(X × Y, X × B)`, onto the pair `(X × Y, X × B)` of the triple. -/
private def prodLeftToTotalPair :
    Q.prodLeft P.fst ⟶ TopTriple.totalPair.obj (prodSubspaceTriple P Q) :=
  ofHom (𝟙 _) (𝟙 _) (by ext x; rfl)

private instance : IsIso (prodLeftToTotalPair P Q) :=
  have : IsIso (Hom.fst (prodLeftToTotalPair P Q)) := inferInstanceAs (IsIso (𝟙 _))
  isIso_of_isIso_fst_of_surjective_snd _ fun x ↦ ⟨x, rfl⟩

/-- The relative chains of `(X × Y, A × Y ∪ X × B)` kill the chains of `A × Y`, since the map of
pairs `(A × Y, A × B) ⟶ (X × Y, A × Y ∪ X × B)` factors through the triple
`(X × Y, A × Y ∪ X × B, X × B)`. -/
private theorem prodLeftMap_comp_prodLeftToProdSubspace :
    prodLeftMap (𝟙 Q) P.map ≫ prodLeftToProdSubspace P Q =
      prodLeftToInnerPair P Q ≫ TopTriple.innerToTotal.app _ ≫ TopTriple.totalToOuter.app _ :=
  -- On ambient spaces both maps are `(a, y) ↦ (P.map a, y)`, by their definitions.
  hom_ext_of_fst _ (by ext x; rfl)

/-- The comparison map `N(P × Q) ⟶ N(X × Y, A × Y ∪ X × B)` from the relative cubical chains of the
product of pairs `P = (X, A)` and `Q = (Y, B)` to those of the pair `(X × Y, A × Y ∪ X × B)`,
induced by the identity of `X × Y`: the class of a chain modulo the chains supported in `A × Y` or
in `X × B` goes to its class modulo the chains supported in `A × Y ∪ X × B`. It is a
quasi-isomorphism when the interiors of `A × Y` and `X × B` cover their union
(`TopPair.quasiIso_cubicalChainComplexProdToOfSubset`). -/
def cubicalChainComplexProdToOfSubset :
    P.cubicalChainComplexProd k Q ⟶ (ofSubset (prodSubspace P Q)).cubicalChainComplex k :=
  cokernel.desc _ (cubicalChainComplexMap k (prodLeftToProdSubspace P Q)) (by
    rw [← cubicalChainComplexMap_comp, prodLeftMap_comp_prodLeftToProdSubspace,
      cubicalChainComplexMap_comp, cubicalChainComplexMap_comp,
      TopTriple.cubicalChainComplexMap_innerToTotal_comp_totalToOuter, Limits.comp_zero])

/-- The comparison map is induced by the map of pairs `(X × Y, X × B) ⟶ (X × Y, A × Y ∪ X × B)`. -/
@[reassoc (attr := simp)]
theorem π_cubicalChainComplexProdToOfSubset :
    cokernel.π _ ≫ P.cubicalChainComplexProdToOfSubset k Q =
      cubicalChainComplexMap k (prodLeftToProdSubspace P Q) :=
  cokernel.π_desc _ _ _

/-- The morphism from the sequence `N(A × Y, A × B) ⟶ N(X × Y, X × B) ⟶ N(P × Q)` to the sequence
of the triple `(X × Y, A × Y ∪ X × B, X × B)`, ending in the comparison map. -/
private def cubicalChainComplexProdShortComplexToTriple :
    P.cubicalChainComplexProdShortComplex k Q ⟶
      (prodSubspaceTriple P Q).cubicalChainComplexShortComplex k where
  τ₁ := cubicalChainComplexMap k (prodLeftToInnerPair P Q)
  τ₂ := cubicalChainComplexMap k (prodLeftToTotalPair P Q)
  τ₃ := P.cubicalChainComplexProdToOfSubset k Q
  -- In both squares the two maps of pairs agree on ambient spaces by their definitions.
  comm₁₂ := by
    rw [← cubicalChainComplexMap_comp, ← cubicalChainComplexMap_comp]
    exact congrArg _ (hom_ext_of_fst _ (by ext x; rfl))
  comm₂₃ := by
    dsimp only
    rw [π_cubicalChainComplexProdToOfSubset, ← cubicalChainComplexMap_comp]
    exact congrArg _ (hom_ext_of_fst _ (by ext x; rfl))

/-- When the interiors of `A × Y` and `X × B` cover their union, the inclusion of pairs
`(A × Y, A × B) ⟶ (A × Y ∪ X × B, X × B)` is an excision, so it induces isomorphisms on relative
cubical homology. -/
private theorem quasiIso_cubicalChainComplexMap_prodLeftToInnerPair
    (h : prodSubspace P Q ⊆
      interior (CartesianMonoidalCategory.fst P.fst Q.fst ⁻¹' Set.range P.map) ∪
        interior (CartesianMonoidalCategory.snd P.fst Q.fst ⁻¹' Set.range Q.map)) :
    QuasiIso (cubicalChainComplexMap k (prodLeftToInnerPair P Q)) := by
  refine ⟨fun n ↦ (quasiIsoAt_iff_isIso_homologyMap _ n).2 ?_⟩
  have := isIso_singularHomologyMap_of_open_cover (ModuleCat.of k k) (prodLeftToInnerPair P Q)
    (Topology.IsEmbedding.subtypeVal.of_comp_iff.1
      (P.isEmbedding_map.prodMap Topology.IsEmbedding.id))
    (by
      -- A point `(a, y)` of `A × Y` lying in `X × B` has `y` in `B`.
      rintro x ⟨z, hz⟩
      exact ⟨(x.1, z.2), Prod.ext rfl (congrArg (fun s ↦ s.1.2) hz)⟩)
    (fun b : Bool ↦ bif b
      then Subtype.val ⁻¹' interior (CartesianMonoidalCategory.fst P.fst Q.fst ⁻¹' Set.range P.map)
      else Subtype.val ⁻¹' interior (CartesianMonoidalCategory.snd P.fst Q.fst ⁻¹' Set.range Q.map))
    (fun b ↦ by cases b <;> exact isOpen_interior.preimage continuous_subtype_val)
    (Set.iUnion_eq_univ_iff.2 fun s ↦ (h s.2).elim (⟨true, ·⟩) (⟨false, ·⟩))
    (fun b ↦ by
      cases b
      · refine .inl fun s hs ↦ ?_
        obtain ⟨y, hy⟩ := interior_subset hs
        exact ⟨(s.1.1, y), Subtype.ext (Prod.ext rfl hy)⟩
      · refine .inr fun s hs ↦ ?_
        obtain ⟨a, ha⟩ := interior_subset hs
        exact ⟨(a, s.1.2), Subtype.ext (Prod.ext ha rfl)⟩)
    n
  exact isIso_homologyMap_cubicalChainComplexMap_of_isIso _ n

/-- **The relative chains of a product of pairs compute the relative homology of
`(X × Y, A × Y ∪ X × B)`.** If the interiors of `A × Y` and `X × B` in `X × Y` cover their union,
the comparison map `N(P × Q) ⟶ N(X × Y, A × Y ∪ X × B)` is a quasi-isomorphism. It is the map of
cokernels of a morphism from the sequence `N(A × Y, A × B) ⟶ N(X × Y, X × B) ⟶ N(P × Q)` to the
sequence of the triple `(X × Y, A × Y ∪ X × B, X × B)`, which is an excision on the first terms and
the identity on the second, so the five lemma applies. -/
theorem quasiIso_cubicalChainComplexProdToOfSubset
    (h : prodSubspace P Q ⊆
      interior (CartesianMonoidalCategory.fst P.fst Q.fst ⁻¹' Set.range P.map) ∪
        interior (CartesianMonoidalCategory.snd P.fst Q.fst ⁻¹' Set.range Q.map)) :
    QuasiIso (P.cubicalChainComplexProdToOfSubset k Q) :=
  -- The identity of `(X × Y, X × B)` onto the pair of the triple is an isomorphism of pairs.
  have : IsIso (cubicalChainComplexMap k (prodLeftToTotalPair P Q)) :=
    ⟨cubicalChainComplexMap k (inv (prodLeftToTotalPair P Q)),
      by rw [← cubicalChainComplexMap_comp, IsIso.hom_inv_id, cubicalChainComplexMap_id],
      by rw [← cubicalChainComplexMap_comp, IsIso.inv_hom_id, cubicalChainComplexMap_id]⟩
  HomologySequence.quasiIso_τ₃ (cubicalChainComplexProdShortComplexToTriple k P Q)
    (P.shortExact_cubicalChainComplexProdShortComplex k Q)
    ((prodSubspaceTriple P Q).shortExact_cubicalChainComplexShortComplex k)
    (quasiIso_cubicalChainComplexMap_prodLeftToInnerPair k P Q h)
    (inferInstanceAs (QuasiIso (cubicalChainComplexMap k (prodLeftToTotalPair P Q))))

/-- For open subspaces `A ⊆ X` and `B ⊆ Y`, the preimages `A × Y` and `X × B` are open, so their
interiors cover their union. -/
theorem prodSubspace_subset_interior_union_interior (hA : IsOpen (Set.range P.map))
    (hB : IsOpen (Set.range Q.map)) :
    prodSubspace P Q ⊆
      interior (CartesianMonoidalCategory.fst P.fst Q.fst ⁻¹' Set.range P.map) ∪
        interior (CartesianMonoidalCategory.snd P.fst Q.fst ⁻¹' Set.range Q.map) := by
  rw [(hA.preimage (CartesianMonoidalCategory.fst P.fst Q.fst).hom.continuous).interior_eq,
    (hB.preimage (CartesianMonoidalCategory.snd P.fst Q.fst).hom.continuous).interior_eq]

/-- For open subspaces `A ⊆ X` and `B ⊆ Y`, the comparison map
`N(P × Q) ⟶ N(X × Y, A × Y ∪ X × B)` is a quasi-isomorphism. -/
theorem quasiIso_cubicalChainComplexProdToOfSubset_of_isOpen (hA : IsOpen (Set.range P.map))
    (hB : IsOpen (Set.range Q.map)) : QuasiIso (P.cubicalChainComplexProdToOfSubset k Q) :=
  quasiIso_cubicalChainComplexProdToOfSubset k P Q
    (prodSubspace_subset_interior_union_interior P Q hA hB)

end Subspace

end TopPair

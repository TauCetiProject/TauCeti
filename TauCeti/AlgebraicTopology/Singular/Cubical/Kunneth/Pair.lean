/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Cubical.Kunneth.Relative
public import TauCeti.AlgebraicTopology.Singular.Cubical.Relative

/-!
# The cubical Eilenberg–Zilber theorem for a product of pairs

For topological pairs `P = (X, A)` and `Q = (Y, B)`, the relative cubical chains of the product
pair `P × Q = (X × Y, A × Y ∪ X × B)` are the chains of `X × Y` modulo the chains supported in
`A × Y` or in `X × B`:

`N(P × Q) = N(X × Y) ⧸ (N(A × Y) + N(X × B))`.

We realize this complex (`TopPair.cubicalChainComplexProd`) as the cokernel of the map
`N(A × Y, A × B) ⟶ N(X × Y, X × B)` of relative chains induced by the inclusion of pairs. This map
is a monomorphism (`TopPair.mono_cubicalChainComplexMap_prodLeftMap`): a normalized chain of
`X × Y` supported both in `A × Y` and in `X × B` is supported in their intersection `A × B`
(`TauCeti.NormalizedCubicalChain.supportedIn_inf`). So the sequence

`0 ⟶ N(A × Y, A × B) ⟶ N(X × Y, X × B) ⟶ N(P × Q) ⟶ 0`

is short exact (`TopPair.shortExact_cubicalChainComplexProdShortComplex`).

The cubical cross product descends to the **cross product of pairs**
(`TauCeti.cubicalCrossProductPair`)

`N(X, A) ⊗ N(Y, B) ⟶ N(P × Q)`, `[a] ⊗ [b] ↦ [a × b]`.

It is the map on cokernels of a morphism from the short exact sequence obtained by tensoring
`N(A) ⟶ N(X) ⟶ N(X, A)` on the right with `N(Y, B)` to the sequence above, whose first two
components are the relative cross products of `A` and of `X` with `Q`. These are
quasi-isomorphisms by the relative Eilenberg–Zilber theorem for a space and a pair
(`TauCeti.quasiIso_cubicalCrossProductRel`), so by the five lemma the cross product of pairs is a
quasi-isomorphism (`TauCeti.quasiIso_cubicalCrossProductPair`): the **Eilenberg–Zilber theorem for
a product of pairs**. Consequently the Künneth map
`⨁_{p + q = n} Hₚ(X, A; k) ⊗ H_q(Y, B; k) ⟶ Hₙ(N(P × Q))` is an isomorphism over a field
(`TauCeti.isIso_cubicalHomologyKunnethPair_of_isSemisimpleRing`). Everything is natural in both
pairs.

No hypothesis is placed on the subspaces. When the interiors of `A × Y` and `X × B` cover
`A × Y ∪ X × B`, for instance when `A` and `B` are open, the small-chain theorem identifies the
homology of `N(P × Q)` with the relative homology of `(X × Y, A × Y ∪ X × B)`; that comparison is
not made here. For compact manifolds `M` and `N` with boundary, `(M, ∂M) × (N, ∂N)` is the pair
`(M × N, ∂M × N ∪ M × ∂N)`, and `N(P × Q)` is the complex in which cross products of fundamental
chains rel boundary are relative cycles.

## Main definitions

* `TopPair.cubicalChainComplexProd k P Q`: the relative cubical chains `N(P × Q)` of a product of
  pairs, with the short exact sequence `TopPair.cubicalChainComplexProdShortComplex k P Q` and the
  maps `TopPair.cubicalChainComplexProdMap k P Q f g` induced by maps of pairs.
* `TauCeti.cubicalCrossProductPair k P Q`: the cross product `N(X, A) ⊗ N(Y, B) ⟶ N(P × Q)`.
* `TauCeti.cubicalCrossProductPairShortComplexMap k P Q`: the morphism of short exact sequences
  given by the relative cross products and the cross product of pairs.
* `TauCeti.cubicalHomologyKunnethPair k P Q n`: the Künneth map of a product of pairs.

## Main results

* `TauCeti.NormalizedCubicalChain.supportedIn_inf` (in
  `TauCeti.AlgebraicTopology.Singular.Cubical.Relative`): chains supported in `A` and in `B` are
  supported in `A ∩ B`.
* `TopPair.mono_cubicalChainComplexMap_prodLeftMap`: `N(A × Y, A × B) ⟶ N(X × Y, X × B)` is a
  monomorphism.
* `TauCeti.cubicalCrossProductPair_f_ιTensorObj_tmul`: the cross product of pairs sends
  `[a] ⊗ [b]` to `[a × b]`.
* `TauCeti.quasiIso_cubicalCrossProductPair`: the Eilenberg–Zilber theorem for a product of pairs.
* `TauCeti.cubicalCrossProductPair_naturality`, `TauCeti.cubicalHomologyKunnethPair_naturality`:
  naturality in both pairs.
* `TauCeti.isIso_cubicalHomologyKunnethPair`,
  `TauCeti.isIso_cubicalHomologyKunnethPair_of_isSemisimpleRing`: the Künneth theorem for a
  product of pairs.

## References

* W. S. Massey, *Singular Homology Theory*, GTM 70, Springer, 1980, Chapter VII.
* A. Hatcher, *Algebraic Topology*, Section 3.B, the relative cross product
  `Hₚ(X, A) ⊗ H_q(Y, B) ⟶ Hₙ(X × Y, A × Y ∪ X × B)`.
* E. H. Spanier, *Algebraic Topology*, Chapter 5, Section 3.
-/

public section

noncomputable section

open CategoryTheory MonoidalCategory HomologicalComplex Limits

universe u

namespace TopPair

open TauCeti

variable (k : Type u) [CommRing k] (P Q : TopPair.{u})

/-- A point of `X × Y` lies in the images of both `A × Y` and `X × B` exactly when it lies in
the image of `A × B`. -/
private theorem range_inter_range :
    Set.range (Hom.fst (prodLeftMap (𝟙 Q) P.map)) ∩ Set.range (Q.prodLeft P.fst).map =
      Set.range (Hom.fst (prodLeftMap (𝟙 Q) P.map) ∘ (Q.prodLeft P.snd).map) := by
  -- The maps of pairs act componentwise on points of the products. The `TopCat` lemmas
  -- `TopCat.tensor_apply` and `TopCat.whiskerLeft_apply` state this for `f.hom`, a coercion form
  -- that does not match the one produced by `Set.range`, so the componentwise form is reached by
  -- `change`.
  ext ⟨x, y⟩
  constructor
  · rintro ⟨⟨⟨a, y'⟩, ha⟩, ⟨⟨x', b⟩, hb⟩⟩
    change (P.map a, y') = (x, y) at ha
    change (x', Q.map b) = (x, y) at hb
    simp only [Prod.mk.injEq] at ha hb
    obtain ⟨rfl, rfl⟩ := ha
    obtain ⟨rfl, rfl⟩ := hb
    exact ⟨⟨a, b⟩, rfl⟩
  · rintro ⟨⟨a, b⟩, h⟩
    change (P.map a, Q.map b) = (x, y) at h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨⟨⟨a, Q.map b⟩, rfl⟩, ⟨⟨P.map a, b⟩, rfl⟩⟩

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
  rw [NormalizedCubicalChain.supportedIn_inf, range_inter_range] at hz₃
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

namespace TauCeti

variable (k : Type u) [CommRing k] (P Q : TopPair.{u})

/-- Tensoring on the right with `N(Y, B)` preserves the short exact sequence
`N(A) ⟶ N(X) ⟶ N(X, A)` of normalized cubical chains of a pair `(X, A)`, which splits in each
degree. -/
theorem shortExact_tensorRightShortComplex_cubicalChainComplexShortComplex :
    (tensorRightShortComplex (Q.cubicalChainComplex k)
      (P.cubicalChainComplexShortComplex k)).ShortExact := by
  have (n : ℕ) : IsSplitMono (((normalizedCubicalChainComplex k).map P.map).f n) := by
    obtain ⟨r, hr⟩ := NormalizedCubicalChain.exists_comp_map_eq_id k P.isEmbedding_map.injective n
    exact .mk' ⟨ModuleCat.ofHom r, ModuleCat.hom_ext hr⟩
  exact shortExact_tensorRightShortComplex _ _ (P.shortExact_cubicalChainComplexShortComplex k)

/-- The relative cross product of `X` with `Q` carries `N(A) ⊗ N(Y, B)` into the chains of
`X × Y` supported in `A × Y`, which vanish in the chains of the product pair. -/
private theorem cubicalCrossProductRel_cokernel_condition :
    (normalizedCubicalChainComplex k).map P.map ▷ Q.cubicalChainComplex k ≫
        cubicalCrossProductRel k P.fst Q ≫
          cokernel.π (TopPair.cubicalChainComplexMap k (TopPair.prodLeftMap (𝟙 Q) P.map)) =
      0 := by
  have h := cubicalCrossProductRel_naturality k P.snd Q P.map (𝟙 Q)
  rw [TopPair.cubicalChainComplexMap_id, tensorHom_id] at h
  rw [reassoc_of% h, cokernel.condition, Limits.comp_zero]

/-- **The cubical cross product of pairs** `N(X, A) ⊗ N(Y, B) ⟶ N(P × Q)` of `P = (X, A)` and
`Q = (Y, B)`, induced by the relative cross product `N(X) ⊗ N(Y, B) ⟶ N(X × Y, X × B)` on the
cokernels; it is characterized by `TauCeti.whiskerRight_π_cubicalCrossProductPair`. -/
def cubicalCrossProductPair :
    P.cubicalChainComplex k ⊗ Q.cubicalChainComplex k ⟶ P.cubicalChainComplexProd k Q :=
  have hS := shortExact_tensorRightShortComplex_cubicalChainComplexShortComplex k P Q
  have := hS.epi_g
  hS.exact.gIsCokernel.desc
    (CokernelCofork.ofπ _ (cubicalCrossProductRel_cokernel_condition k P Q))

/-- The cross product of pairs is induced by the relative cross product: on `N(X) ⊗ N(Y, B)` it is
the relative cross product followed by the projection to the chains of the product pair. -/
@[reassoc (attr := simp)]
theorem whiskerRight_π_cubicalCrossProductPair :
    cokernel.π ((normalizedCubicalChainComplex k).map P.map) ▷ Q.cubicalChainComplex k ≫
        cubicalCrossProductPair k P Q =
      cubicalCrossProductRel k P.fst Q ≫
        cokernel.π (TopPair.cubicalChainComplexMap k (TopPair.prodLeftMap (𝟙 Q) P.map)) :=
  have hS := shortExact_tensorRightShortComplex_cubicalChainComplexShortComplex k P Q
  have := hS.epi_g
  hS.exact.gIsCokernel.fac _ WalkingParallelPair.one

/-- The cross product of pairs sends `[a] ⊗ [b]` to `[a × b]`, reindexed along `p + q = n`, for
normalized chains `a` of `X` and `b` of `Y`. -/
theorem cubicalCrossProductPair_f_ιTensorObj_tmul {p q n : ℕ} (h : p + q = n)
    (a : NormalizedCubicalChain P.fst k p) (b : NormalizedCubicalChain Q.fst k q) :
    (cubicalCrossProductPair k P Q).f n
        (ιTensorObj (P.cubicalChainComplex k) (Q.cubicalChainComplex k) p q n h
          ((cokernel.π ((normalizedCubicalChainComplex k).map P.map)).f p a ⊗ₜ
            (cokernel.π ((normalizedCubicalChainComplex k).map Q.map)).f q b)) =
      (cokernel.π (TopPair.cubicalChainComplexMap k (TopPair.prodLeftMap (𝟙 Q) P.map))).f n
        ((cokernel.π ((normalizedCubicalChainComplex k).map (Q.prodLeft P.fst).map)).f n
          (NormalizedCubicalChain.cast k h
            (NormalizedCubicalChain.crossProduct P.fst Q.fst k p q a b))) := by
  have hι : (cokernel.π ((normalizedCubicalChainComplex k).map P.map) ▷
      Q.cubicalChainComplex k).f n
        (ιTensorObj ((normalizedCubicalChainComplex k).obj P.fst) (Q.cubicalChainComplex k) p q n h
          (a ⊗ₜ (cokernel.π ((normalizedCubicalChainComplex k).map Q.map)).f q b)) =
      ιTensorObj (P.cubicalChainComplex k) (Q.cubicalChainComplex k) p q n h
        ((cokernel.π ((normalizedCubicalChainComplex k).map P.map)).f p a ⊗ₜ
          (cokernel.π ((normalizedCubicalChainComplex k).map Q.map)).f q b) :=
    ConcreteCategory.congr_hom
      (ι_whiskerRight (cokernel.π ((normalizedCubicalChainComplex k).map P.map))
        (Q.cubicalChainComplex k) p q n h)
      (a ⊗ₜ (cokernel.π ((normalizedCubicalChainComplex k).map Q.map)).f q b)
  have hw := ConcreteCategory.congr_hom
    (congrArg (fun φ ↦ φ.f n) (whiskerRight_π_cubicalCrossProductPair k P Q))
    (ιTensorObj ((normalizedCubicalChainComplex k).obj P.fst) (Q.cubicalChainComplex k) p q n h
      (a ⊗ₜ (cokernel.π ((normalizedCubicalChainComplex k).map Q.map)).f q b))
  rw [comp_f, comp_f, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
    cubicalCrossProductRel_f_ιTensorObj_tmul, hι] at hw
  exact hw

/-- The morphism of short exact sequences from `(N(A) ⟶ N(X) ⟶ N(X, A)) ⊗ N(Y, B)` to
`N(A × Y, A × B) ⟶ N(X × Y, X × B) ⟶ N(P × Q)` given by the relative cross products of `A` and of
`X` with `Q` and the cross product of pairs. -/
def cubicalCrossProductPairShortComplexMap :
    tensorRightShortComplex (Q.cubicalChainComplex k) (P.cubicalChainComplexShortComplex k) ⟶
      P.cubicalChainComplexProdShortComplex k Q where
  τ₁ := cubicalCrossProductRel k P.snd Q
  τ₂ := cubicalCrossProductRel k P.fst Q
  τ₃ := cubicalCrossProductPair k P Q
  comm₁₂ := by
    have h := cubicalCrossProductRel_naturality k P.snd Q P.map (𝟙 Q)
    rw [TopPair.cubicalChainComplexMap_id] at h
    exact h.symm
  comm₂₃ := (whiskerRight_π_cubicalCrossProductPair k P Q).symm

@[simp]
theorem cubicalCrossProductPairShortComplexMap_τ₁ :
    (cubicalCrossProductPairShortComplexMap k P Q).τ₁ = cubicalCrossProductRel k P.snd Q :=
  (rfl)

@[simp]
theorem cubicalCrossProductPairShortComplexMap_τ₂ :
    (cubicalCrossProductPairShortComplexMap k P Q).τ₂ = cubicalCrossProductRel k P.fst Q :=
  (rfl)

@[simp]
theorem cubicalCrossProductPairShortComplexMap_τ₃ :
    (cubicalCrossProductPairShortComplexMap k P Q).τ₃ = cubicalCrossProductPair k P Q :=
  (rfl)

/-- **The cubical Eilenberg–Zilber theorem for a product of pairs**: the cross product
`N(X, A) ⊗ N(Y, B) ⟶ N(P × Q)` is a quasi-isomorphism. By the five lemma, this follows from the
relative Eilenberg–Zilber theorem for `A` and for `X` with the pair `Q`. -/
instance quasiIso_cubicalCrossProductPair : QuasiIso (cubicalCrossProductPair k P Q) :=
  HomologySequence.quasiIso_τ₃ (cubicalCrossProductPairShortComplexMap k P Q)
    (shortExact_tensorRightShortComplex_cubicalChainComplexShortComplex k P Q)
    (P.shortExact_cubicalChainComplexProdShortComplex k Q)
    (inferInstanceAs (QuasiIso (cubicalCrossProductRel k P.snd Q)))
    (inferInstanceAs (QuasiIso (cubicalCrossProductRel k P.fst Q)))

/-- **Naturality of the cross product of pairs** in both pairs. -/
@[reassoc]
theorem cubicalCrossProductPair_naturality {P' Q' : TopPair.{u}} (f : P ⟶ P') (g : Q ⟶ Q') :
    (TopPair.cubicalChainComplexMap k f ⊗ₘ TopPair.cubicalChainComplexMap k g) ≫
        cubicalCrossProductPair k P' Q' =
      cubicalCrossProductPair k P Q ≫ TopPair.cubicalChainComplexProdMap k P Q f g := by
  have hS := shortExact_tensorRightShortComplex_cubicalChainComplexShortComplex k P Q
  have : Epi (cokernel.π ((normalizedCubicalChainComplex k).map P.map) ▷
      Q.cubicalChainComplex k) := hS.epi_g
  refine (cancel_epi (cokernel.π ((normalizedCubicalChainComplex k).map P.map) ▷
      Q.cubicalChainComplex k)).1 ?_
  have h₁ : cokernel.π ((normalizedCubicalChainComplex k).map P.map) ▷ Q.cubicalChainComplex k ≫
        (TopPair.cubicalChainComplexMap k f ⊗ₘ TopPair.cubicalChainComplexMap k g) =
      ((normalizedCubicalChainComplex k).map (TopPair.Hom.fst f) ⊗ₘ
        TopPair.cubicalChainComplexMap k g) ≫
          cokernel.π ((normalizedCubicalChainComplex k).map P'.map) ▷
            Q'.cubicalChainComplex k := by
    simp [whiskerRight_comp_tensorHom, tensorHom_comp_whiskerRight]
  calc _ = ((normalizedCubicalChainComplex k).map (TopPair.Hom.fst f) ⊗ₘ
        TopPair.cubicalChainComplexMap k g) ≫ cubicalCrossProductRel k P'.fst Q' ≫
          cokernel.π (TopPair.cubicalChainComplexMap k (TopPair.prodLeftMap (𝟙 Q') P'.map)) := by
        rw [reassoc_of% h₁, whiskerRight_π_cubicalCrossProductPair]
    _ = cubicalCrossProductRel k P.fst Q ≫
          TopPair.cubicalChainComplexMap k (TopPair.prodLeftMap g (TopPair.Hom.fst f)) ≫
            cokernel.π (TopPair.cubicalChainComplexMap k (TopPair.prodLeftMap (𝟙 Q') P'.map)) :=
        cubicalCrossProductRel_naturality_assoc _ _ _ _ _ _
    _ = cubicalCrossProductRel k P.fst Q ≫
          cokernel.π (TopPair.cubicalChainComplexMap k (TopPair.prodLeftMap (𝟙 Q) P.map)) ≫
            TopPair.cubicalChainComplexProdMap k P Q f g :=
        congrArg (cubicalCrossProductRel k P.fst Q ≫ ·)
          (TopPair.π_cubicalChainComplexProdMap k P Q f g).symm
    _ = _ := (whiskerRight_π_cubicalCrossProductPair_assoc k P Q _).symm

/-- **The Künneth map of a product of pairs**,
`⨁_{p + q = n} Hₚ(X, A; k) ⊗ H_q(Y, B; k) ⟶ Hₙ(N(P × Q))`: the algebraic Künneth map of the
chain complexes `N(X, A)` and `N(Y, B)` followed by the map induced by the cross product of
pairs. -/
def cubicalHomologyKunnethPair (n : ℕ) :
    GradedObject.Monoidal.tensorObj (fun p ↦ (P.cubicalChainComplex k).homology p)
        (fun q ↦ (Q.cubicalChainComplex k).homology q) n ⟶
      (P.cubicalChainComplexProd k Q).homology n :=
  homologyKunneth (P.cubicalChainComplex k) (Q.cubicalChainComplex k) n ≫
    homologyMap (cubicalCrossProductPair k P Q) n

/-- The Künneth map of a product of pairs is the algebraic Künneth map followed by the map induced
by the cross product of pairs. -/
theorem cubicalHomologyKunnethPair_def (n : ℕ) :
    cubicalHomologyKunnethPair k P Q n =
      homologyKunneth (P.cubicalChainComplex k) (Q.cubicalChainComplex k) n ≫
        homologyMap (cubicalCrossProductPair k P Q) n :=
  (rfl)

/-- The Künneth map of a product of pairs restricts to the homology cross product followed by the
map induced by the cross product of pairs on each summand. -/
@[reassoc (attr := simp)]
theorem ι_cubicalHomologyKunnethPair (p q n : ℕ) (h : p + q = n) :
    GradedObject.Monoidal.ιTensorObj (fun p ↦ (P.cubicalChainComplex k).homology p)
        (fun q ↦ (Q.cubicalChainComplex k).homology q) p q n h ≫
      cubicalHomologyKunnethPair k P Q n =
      homologyCross (P.cubicalChainComplex k) (Q.cubicalChainComplex k) p q n h ≫
        homologyMap (cubicalCrossProductPair k P Q) n := by
  rw [cubicalHomologyKunnethPair_def, ← Category.assoc, ι_homologyKunneth]

/-- **Naturality of the Künneth map of a product of pairs** in both pairs. -/
@[reassoc]
theorem cubicalHomologyKunnethPair_naturality {P' Q' : TopPair.{u}} (f : P ⟶ P') (g : Q ⟶ Q')
    (n : ℕ) :
    GradedObject.Monoidal.tensorHom
        (fun p ↦ homologyMap (TopPair.cubicalChainComplexMap k f) p)
        (fun q ↦ homologyMap (TopPair.cubicalChainComplexMap k g) q) n ≫
      cubicalHomologyKunnethPair k P' Q' n =
      cubicalHomologyKunnethPair k P Q n ≫
        homologyMap (TopPair.cubicalChainComplexProdMap k P Q f g) n := by
  have h := congrArg (homologyMap · n) (cubicalCrossProductPair_naturality k P Q f g)
  simp only [homologyMap_comp] at h
  simp only [cubicalHomologyKunnethPair_def, homologyKunneth_naturality_assoc, Category.assoc]
  exact congrArg (homologyKunneth _ _ n ≫ ·) h

/-- **The Künneth theorem for a product of pairs**: if the cycles of `N(X, A)` and `N(Y, B)` split
off their terms and their homology splits off the cycles, the Künneth map
`⨁_{p + q = n} Hₚ(X, A; k) ⊗ H_q(Y, B; k) ⟶ Hₙ(N(P × Q))` is an isomorphism. -/
theorem isIso_cubicalHomologyKunnethPair
    [∀ p, IsSplitMono ((P.cubicalChainComplex k).iCycles p)]
    [∀ p, IsSplitEpi ((P.cubicalChainComplex k).homologyπ p)]
    [∀ q, IsSplitMono ((Q.cubicalChainComplex k).iCycles q)]
    [∀ q, IsSplitEpi ((Q.cubicalChainComplex k).homologyπ q)] (n : ℕ) :
    IsIso (cubicalHomologyKunnethPair k P Q n) := by
  rw [cubicalHomologyKunnethPair_def]
  infer_instance

/-- **The Künneth theorem for a product of pairs over a semisimple ring**, for instance a field:
`⨁_{p + q = n} Hₚ(X, A; k) ⊗ H_q(Y, B; k) ≅ Hₙ(N(P × Q))`. -/
instance isIso_cubicalHomologyKunnethPair_of_isSemisimpleRing [IsSemisimpleRing k] (n : ℕ) :
    IsIso (cubicalHomologyKunnethPair k P Q n) :=
  isIso_cubicalHomologyKunnethPair k P Q n

end TauCeti

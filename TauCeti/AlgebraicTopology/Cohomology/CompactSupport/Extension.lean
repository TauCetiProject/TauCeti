/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.CompactSupport.Basic
public import TauCeti.AlgebraicTopology.Cohomology.Excision

/-!
# Extension of compactly supported classes along open embeddings

Singular cohomology with compact supports is covariant along open embeddings. Let `f : U ⟶ X` be
an open embedding into a Hausdorff space and `K ⊆ U` compact. Then `f(K)` is compact, hence
closed, so `X` is covered by the open sets `X ∖ f(K)` and `f(U)`, and excision
(`TopPair.isIso_singularCohomologyMap_of_open_cover`) shows that the map of pairs
`(U, U ∖ K) ⟶ (X, X ∖ f(K))` induces an isomorphism `Hⁿ(X, X ∖ f(K)) ≅ Hⁿ(U, U ∖ K)`
(`TopCat.singularCohomologyComplCompactsMapIso`). Its inverse extends a class supported in `K` by
zero, and these inverses are compatible with enlarging `K`, so they pass to the colimits over the
compact subsets, giving the extension `f_! : Hⁿ_c(U) ⟶ Hⁿ_c(X)`
(`TopCat.compactSupportCohomologyExtend`). Extension is functorial: `id_! = id` and
`(g ∘ f)_! = g_! ∘ f_!`.

These maps are the ones in the Mayer–Vietoris sequence of cohomology with compact supports, and the
ones along which the duality maps `Hⁿ_c(U) ⟶ H_{m-n}(U)` of the open subsets of a manifold are
compared in the proof of Poincaré duality.

## Main definitions and results

* `TopCat.isIso_singularCohomologyMap_ofSubsetMap_compl_compacts_map` and
  `TopCat.singularCohomologyComplCompactsMapIso`: excision `Hⁿ(X, X ∖ f(K)) ≅ Hⁿ(U, U ∖ K)`.
* `TopCat.compactSupportCohomologyExtend`: the extension `f_! : Hⁿ_c(U) ⟶ Hⁿ_c(X)`, characterized
  by `TopCat.compactSupportCohomologyι_comp_extend` and
  `TopCat.singularCohomologyMap_comp_compactSupportCohomologyι_comp_extend`.
* `TopCat.compactSupportCohomologyExtend_id` and `TopCat.compactSupportCohomologyExtend_comp`:
  functoriality.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3, the maps `Hⁿ_c(U) ⟶ Hⁿ_c(V)` induced by inclusions of open sets `U ⊆ V`, used
  in Lemma 3.36 and the proof of Theorem 3.35.
-/

public section

noncomputable section

open CategoryTheory Limits TopologicalSpace Topology

universe v u

namespace TopCat

/-- An injective map `f : U ⟶ X` carries the complement of a compact set `K ⊆ U` into the
complement of its image `f(K)`. -/
lemma mapsTo_compl_compacts_map {U X : TopCat.{v}} {f : U ⟶ X} (hf : Function.Injective f)
    (K : Compacts U) :
    Set.MapsTo f (K : Set U)ᶜ (K.map f f.hom.continuous : Set X)ᶜ :=
  fun _ hx hK ↦ hx (by simpa [hf.mem_set_image] using hK)

variable {C : Type u} [Category.{v} C] [HasCoproducts.{v} C] [Abelian C] {R : C}
  {k : Type v} [Ring k] [Linear k C] {M : C} {U X Y : TopCat.{v}}

/-- **Excision for compact sets along an open embedding.** For an open embedding `f : U ⟶ X` into
a Hausdorff space and a compact `K ⊆ U`, the map of pairs `(U, U ∖ K) ⟶ (X, X ∖ f(K))` induced by
`f` is an isomorphism `Hⁿ(X, X ∖ f(K)) ≅ Hⁿ(U, U ∖ K)` on relative singular cohomology. -/
theorem isIso_singularCohomologyMap_ofSubsetMap_compl_compacts_map [T2Space X] {f : U ⟶ X}
    (hf : IsOpenEmbedding f) (K : Compacts U) (n : ℕ) :
    IsIso (TopPair.singularCohomologyMap (R := R) (k := k) (M := M)
      (TopPair.ofSubsetMap f (mapsTo_compl_compacts_map hf.injective K)) n) := by
  refine TopPair.isIso_singularCohomologyMap_of_open_cover _
    (by rw [TopPair.ofSubsetMap_fst]; exact hf.isEmbedding) ?_
    ![(K.map f f.hom.continuous : Set X)ᶜ, Set.range f] ?_ ?_ ?_ n
  · intro x hx
    simp only [TopPair.ofSubsetMap_fst_apply, TopPair.range_ofSubset_map] at hx ⊢
    exact fun hK ↦ hx ⟨x, hK, rfl⟩
  · intro i
    fin_cases i
    exacts [(K.map f f.hom.continuous).isCompact.isClosed.isOpen_compl, hf.isOpen_range]
  · refine Set.eq_univ_of_forall fun x ↦ ?_
    by_cases hx : x ∈ (K.map f f.hom.continuous : Set X)
    · obtain ⟨y, -, rfl⟩ := hx
      exact Set.mem_iUnion.2 ⟨1, Set.mem_range_self y⟩
    · exact Set.mem_iUnion.2 ⟨0, hx⟩
  -- the ambient space of `(X, X ∖ f(K))` is `X` only after unfolding, so the two members of the
  -- cover are compared with the subspace and the image by `exact` rather than by rewriting
  · intro i
    fin_cases i
    · exact Or.inl fun x hx ↦ ⟨⟨x, hx⟩, rfl⟩
    · refine Or.inr fun x hx ↦ ?_
      rw [TopPair.ofSubsetMap_fst]
      exact hx

/-- For compact sets `K ⊆ L` of `U`, restricting along the identity commutes with the
excision maps of an injective `f : U ⟶ X`. -/
private lemma ofSubsetMap_id_comp_ofSubsetMap_compl_compacts_map {f : U ⟶ X}
    (hf : Function.Injective f) {K L : Compacts U} (h : K ≤ L) :
    TopPair.ofSubsetMap (𝟙 U) (mapsTo_id_compl_compacts h) ≫
        TopPair.ofSubsetMap f (mapsTo_compl_compacts_map hf K) =
      TopPair.ofSubsetMap f (mapsTo_compl_compacts_map hf L) ≫
        TopPair.ofSubsetMap (𝟙 X)
          (mapsTo_id_compl_compacts (Compacts.map_mono f f.hom.continuous h)) :=
  TopPair.ofSubsetMap_comp_ofSubsetMap_eq _ _ _ _ (by simp)

variable [T2Space X]

variable (R k M) in
/-- The excision isomorphism `Hⁿ(X, X ∖ f(K)) ≅ Hⁿ(U, U ∖ K)` for an open embedding
`f : U ⟶ X` into a Hausdorff space and a compact `K ⊆ U`, the map induced by `f`. -/
def singularCohomologyComplCompactsMapIso {f : U ⟶ X} (hf : IsOpenEmbedding f)
    (K : Compacts U) (n : ℕ) :
    (TopPair.ofSubset (K.map f f.hom.continuous : Set X)ᶜ).singularCohomology R k M n ≅
      (TopPair.ofSubset (K : Set U)ᶜ).singularCohomology R k M n :=
  @asIso _ _ _ _ _ (isIso_singularCohomologyMap_ofSubsetMap_compl_compacts_map hf K n)

@[simp]
lemma singularCohomologyComplCompactsMapIso_hom {f : U ⟶ X} (hf : IsOpenEmbedding f)
    (K : Compacts U) (n : ℕ) :
    (singularCohomologyComplCompactsMapIso R k M hf K n).hom =
      TopPair.singularCohomologyMap
        (TopPair.ofSubsetMap f (mapsTo_compl_compacts_map hf.injective K)) n :=
  (rfl)

/-- The excision isomorphisms are natural in the compact set: for `K ⊆ L` they commute with the
restrictions `Hⁿ(X, X ∖ f(K)) ⟶ Hⁿ(X, X ∖ f(L))` and `Hⁿ(U, U ∖ K) ⟶ Hⁿ(U, U ∖ L)`. -/
@[reassoc]
lemma singularCohomologyComplCompactsMapIso_hom_naturality {f : U ⟶ X} (hf : IsOpenEmbedding f)
    {K L : Compacts U} (h : K ≤ L) (n : ℕ) :
    TopPair.singularCohomologyMap (TopPair.ofSubsetMap (𝟙 X)
        (mapsTo_id_compl_compacts (Compacts.map_mono f f.hom.continuous h))) n ≫
      (singularCohomologyComplCompactsMapIso R k M hf L n).hom =
    (singularCohomologyComplCompactsMapIso R k M hf K n).hom ≫
      TopPair.singularCohomologyMap (TopPair.ofSubsetMap (𝟙 U) (mapsTo_id_compl_compacts h)) n := by
  simp only [singularCohomologyComplCompactsMapIso_hom, ← TopPair.singularCohomologyMap_comp]
  rw [ofSubsetMap_id_comp_ofSubsetMap_compl_compacts_map hf.injective h]

/-- The inverse excision isomorphisms are natural in the compact set. -/
@[reassoc]
lemma singularCohomologyComplCompactsMapIso_inv_naturality {f : U ⟶ X} (hf : IsOpenEmbedding f)
    {K L : Compacts U} (h : K ≤ L) (n : ℕ) :
    TopPair.singularCohomologyMap (TopPair.ofSubsetMap (𝟙 U) (mapsTo_id_compl_compacts h)) n ≫
      (singularCohomologyComplCompactsMapIso R k M hf L n).inv =
    (singularCohomologyComplCompactsMapIso R k M hf K n).inv ≫
      TopPair.singularCohomologyMap (TopPair.ofSubsetMap (𝟙 X)
        (mapsTo_id_compl_compacts (Compacts.map_mono f f.hom.continuous h))) n := by
  rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp,
    singularCohomologyComplCompactsMapIso_hom_naturality hf h n]

/-- The excision isomorphism of a composite of open embeddings `f : U ⟶ Y` and `g : Y ⟶ X` is the
composite of the excision isomorphisms of `g` along `f(K)` and of `f` along `K`, after the
restriction from `g(f(K))` to the equal compact set `(g ∘ f)(K)`. -/
@[reassoc]
lemma singularCohomologyComplCompactsMapIso_hom_comp [T2Space Y] {f : U ⟶ Y} {g : Y ⟶ X}
    (hf : IsOpenEmbedding f) (hg : IsOpenEmbedding g) (hfg : IsOpenEmbedding (f ≫ g))
    (K : Compacts U) (hle : K.map (f ≫ g) (f ≫ g).hom.continuous ≤
      (K.map f f.hom.continuous).map g g.hom.continuous) (n : ℕ) :
    TopPair.singularCohomologyMap (TopPair.ofSubsetMap (𝟙 X) (mapsTo_id_compl_compacts hle)) n ≫
        (singularCohomologyComplCompactsMapIso R k M hg (K.map f f.hom.continuous) n).hom ≫
          (singularCohomologyComplCompactsMapIso R k M hf K n).hom =
      (singularCohomologyComplCompactsMapIso R k M hfg K n).hom := by
  simp only [singularCohomologyComplCompactsMapIso_hom, ← TopPair.singularCohomologyMap_comp]
  rw [← TopPair.ofSubsetMap_comp, TopPair.ofSubsetMap_comp_ofSubsetMap_of_comp_eq _ _
    (mapsTo_compl_compacts_map hfg.injective K) (Category.comp_id _)]
  exact fun x hx ↦
    mapsTo_compl_compacts_map hg.injective _ (mapsTo_compl_compacts_map hf.injective K hx)

/-- The **extension** `f_! : Hⁿ_c(U) ⟶ Hⁿ_c(X)` of compactly supported classes along an open
embedding `f : U ⟶ X` into a Hausdorff space. A class of `Hⁿ(U, U ∖ K)` is carried to
`Hⁿ(X, X ∖ f(K))` by the inverse of the excision isomorphism
`TopCat.singularCohomologyComplCompactsMapIso`: on cohomology classes, this is the extension by
zero of a class supported in `K`. -/
def compactSupportCohomologyExtend {f : U ⟶ X} (hf : IsOpenEmbedding f) (n : ℕ) :
    U.compactSupportCohomology R k M n ⟶ X.compactSupportCohomology R k M n :=
  compactSupportCohomologyDesc
    (fun K ↦ (singularCohomologyComplCompactsMapIso R k M hf K n).inv ≫
      compactSupportCohomologyι n (K.map f f.hom.continuous))
    (fun K L h ↦ by
      rw [singularCohomologyComplCompactsMapIso_inv_naturality_assoc hf h n,
        singularCohomologyMap_comp_compactSupportCohomologyι n
          (Compacts.map_mono f f.hom.continuous h)])

/-- On `Hⁿ(U, U ∖ K)`, the extension along an open embedding `f` is the inverse of excision
followed by the map into `Hⁿ_c(X)` from `Hⁿ(X, X ∖ f(K))`. -/
@[reassoc (attr := simp)]
lemma compactSupportCohomologyι_comp_extend {f : U ⟶ X} (hf : IsOpenEmbedding f) (n : ℕ)
    (K : Compacts U) :
    compactSupportCohomologyι n K ≫
        compactSupportCohomologyExtend (R := R) (k := k) (M := M) hf n =
      (singularCohomologyComplCompactsMapIso R k M hf K n).inv ≫
        compactSupportCohomologyι n (K.map f f.hom.continuous) :=
  compactSupportCohomologyι_desc _ _ K

/-- The characteristic property of the extension along an open embedding `f : U ⟶ X`: a class of
`Hⁿ(X, X ∖ f(K))`, restricted to `Hⁿ(U, U ∖ K)` and extended back, is the original class with
compact support. -/
@[reassoc]
lemma singularCohomologyMap_comp_compactSupportCohomologyι_comp_extend {f : U ⟶ X}
    (hf : IsOpenEmbedding f) (n : ℕ) (K : Compacts U) :
    TopPair.singularCohomologyMap
        (TopPair.ofSubsetMap f (mapsTo_compl_compacts_map hf.injective K)) n ≫
      compactSupportCohomologyι n K ≫
        compactSupportCohomologyExtend (R := R) (k := k) (M := M) hf n =
      compactSupportCohomologyι n (K.map f f.hom.continuous) := by
  rw [compactSupportCohomologyι_comp_extend,
    ← singularCohomologyComplCompactsMapIso_hom (R := R) (k := k) (M := M) hf K n,
    Iso.hom_inv_id_assoc]

/-- Extension along the identity is the identity. -/
@[simp]
lemma compactSupportCohomologyExtend_id (n : ℕ)
    (h : IsOpenEmbedding (𝟙 X) := by simpa using IsOpenEmbedding.id) :
    compactSupportCohomologyExtend (R := R) (k := k) (M := M) h n = 𝟙 _ := by
  refine compactSupportCohomology_hom_ext fun K ↦ ?_
  rw [compactSupportCohomologyι_comp_extend, Category.comp_id, Iso.inv_comp_eq,
    singularCohomologyComplCompactsMapIso_hom]
  exact (singularCohomologyMap_comp_compactSupportCohomologyι n
    fun x hx ↦ SetLike.mem_coe.1 (by simpa using hx)).symm

/-- Extension along open embeddings is functorial: `(g ∘ f)_! = g_! ∘ f_!`. -/
@[reassoc]
lemma compactSupportCohomologyExtend_comp [T2Space Y] {f : U ⟶ Y} {g : Y ⟶ X}
    (hf : IsOpenEmbedding f) (hg : IsOpenEmbedding g) (n : ℕ)
    (hfg : IsOpenEmbedding (f ≫ g) := by simpa using hg.comp hf) :
    compactSupportCohomologyExtend (R := R) (k := k) (M := M) hfg n =
      compactSupportCohomologyExtend hf n ≫ compactSupportCohomologyExtend hg n := by
  refine compactSupportCohomology_hom_ext fun K ↦ ?_
  have hle : K.map (f ≫ g) (f ≫ g).hom.continuous ≤
      (K.map f f.hom.continuous).map g g.hom.continuous := fun x hx ↦ by
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨f y, ⟨y, hy, rfl⟩, rfl⟩
  have hcomp := singularCohomologyComplCompactsMapIso_hom_comp (R := R) (k := k) (M := M)
    hf hg hfg K hle n
  simp only [compactSupportCohomologyι_comp_extend, compactSupportCohomologyι_comp_extend_assoc,
    ← singularCohomologyMap_comp_compactSupportCohomologyι n hle, ← hcomp, Iso.inv_comp_eq,
    Category.assoc, Iso.hom_inv_id_assoc]

end TopCat

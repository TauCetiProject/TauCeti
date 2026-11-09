/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.CompactSupport.Extension
public import TauCeti.AlgebraicTopology.Cohomology.MayerVietoris.Pair

/-!
# The Mayer–Vietoris sequence of cohomology with compact supports

Let `X` be a Hausdorff space covered by two open sets `U` and `V`, and write `Hⁿ_c(-)` for
singular cohomology with compact supports. Extension by zero along the inclusions of open sets
(`TopCat.compactSupportCohomologyExtend`) gives the maps
`Hⁿ_c(U ∩ V) ⟶ Hⁿ_c(U) ⊞ Hⁿ_c(V) ⟶ Hⁿ_c(X)` of the Mayer–Vietoris sequence of cohomology with
compact supports, the first with components the extension to `U` and minus the extension to `V`,
the second the sum of the extensions to `X`. This file constructs these two maps and proves that
the sequence is exact at `Hⁿ_c(U) ⊞ Hⁿ_c(V)`.

The proof follows Hatcher's proof of Lemma 3.36. For compact sets `K ⊆ U` and `L ⊆ V`, the
Mayer–Vietoris sequence of the pairs `(X, X ∖ K)` and `(X, X ∖ L)`
(`TopCat.singularCohomologyPairMayerVietoris_exact₂`) reads
`Hⁿ(X, X ∖ (K ∩ L)) ⟶ Hⁿ(X, X ∖ K) ⊞ Hⁿ(X, X ∖ L) ⟶ Hⁿ(X, X ∖ (K ∪ L))`, and excision identifies
its first two terms with `Hⁿ(U ∩ V, U ∩ V ∖ (K ∩ L))` and `Hⁿ(U, U ∖ K) ⊞ Hⁿ(V, V ∖ L)`. Passing to
the colimits over the compact sets, every compact subset of `X = U ∪ V` is of the form `K ∪ L`
(`IsCompact.binary_compact_cover`), so the third terms give `Hⁿ_c(X)`. Exactness survives the
filtered colimits; here this is checked on elements, using the description of the elements of
`Hⁿ_c` in `TopCat.exists_compactSupportCohomologyι_eq` and
`TopCat.compactSupportCohomologyι_eq_zero_iff`.

## Main definitions and results

* `TopCat.compactSupportCohomologyMayerVietorisToBiprod`: the map
  `Hⁿ_c(U ∩ V) ⟶ Hⁿ_c(U) ⊞ Hⁿ_c(V)`, with components the extension to `U` and minus the
  extension to `V`.
* `TopCat.compactSupportCohomologyMayerVietorisFromBiprod`: the map
  `Hⁿ_c(U) ⊞ Hⁿ_c(V) ⟶ Hⁿ_c(X)`, the sum of the extensions to `X`.
* `TopCat.compactSupportCohomologyMayerVietorisToBiprod_fromBiprod`: the two maps compose to zero.
* `TopCat.compactSupportCohomologyMayerVietoris_exact₂`: exactness at `Hⁿ_c(U) ⊞ Hⁿ_c(V)` when
  `U ∪ V = X`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3, the Mayer–Vietoris sequence `Hⁿ_c(U ∩ V) ⟶ Hⁿ_c(U) ⊕ Hⁿ_c(V) ⟶ Hⁿ_c(X) ⟶ ⋯` in the
  proof of Lemma 3.36.
-/

public section

noncomputable section

open CategoryTheory Limits TopologicalSpace Topology

universe v u

namespace TopCat

variable {C : Type u} [Category.{v} C] [HasCoproducts.{v} C] [Abelian C] {R : C}
  {k : Type v} [Ring k] [Linear k C] {M : C} {X : TopCat.{v}}

/-! ### Restriction between the complements of two sets -/

/-- For `S ⊆ T`, the identity of `X` carries `X ∖ T` into `X ∖ S`. -/
private lemma mapsTo_id_compl {S T : Set X} (h : S ⊆ T) : Set.MapsTo (𝟙 X) Tᶜ Sᶜ :=
  fun _ hx hS ↦ hx (h hS)

/-- The restriction `Hⁿ(X, X ∖ S) ⟶ Hⁿ(X, X ∖ T)` for `S ⊆ T`. -/
private abbrev complRestrict {S T : Set X} (h : S ⊆ T) (n : ℕ) :
    (TopPair.ofSubset Sᶜ).singularCohomology R k M n ⟶
      (TopPair.ofSubset Tᶜ).singularCohomology R k M n :=
  TopPair.singularCohomologyMap (TopPair.ofSubsetMap (𝟙 X) (mapsTo_id_compl h)) n

private lemma complRestrict_apply_complRestrict {S T Q : Set X} (h : S ⊆ T) (h' : T ⊆ Q)
    (n : ℕ) (a : (TopPair.ofSubset Sᶜ).singularCohomology R k M n) :
    complRestrict h' n (complRestrict h n a) = complRestrict (h.trans h') n a := by
  rw [← TopPair.singularCohomologyMap_comp_apply,
    TopPair.ofSubsetMap_comp_ofSubsetMap_of_comp_eq _ _ (mapsTo_id_compl (h.trans h'))
      (Category.id_comp _)]

/-! ### Mayer–Vietoris for the complements of two closed sets -/

/-- For a set `t` containing every point of `X` and `s ⊆ t`, the pair `(t, s)` is the pair
`(X, s')` for any `s'` with the same points as `s`. -/
private def ofInclusionIsoOfSubset {t s : Set X} (ht : ∀ x, x ∈ t) (hst : s ⊆ t) {s' : Set X}
    (hs : ∀ x, x ∈ s ↔ x ∈ s') : TopPair.ofInclusion hst ≅ TopPair.ofSubset s' where
  hom := TopPair.ofHom (ofHom ⟨Subtype.val, continuous_subtype_val⟩)
    (ofHom ⟨fun x ↦ ⟨x.1, (hs _).1 x.2⟩, by fun_prop⟩)
  inv := TopPair.ofHom (ofHom ⟨fun x ↦ ⟨x, ht x⟩, by fun_prop⟩)
    (ofHom ⟨fun x ↦ ⟨x.1, (hs _).2 x.2⟩, by fun_prop⟩)
  hom_inv_id := by ext : 2 <;> rfl
  inv_hom_id := by ext : 2 <;> rfl

/-- A map of pairs which is an isomorphism induces an injective map on cohomology. -/
private lemma singularCohomologyMap_hom_injective {P Q : TopPair.{v}} (e : P ≅ Q) (n : ℕ) :
    Function.Injective (TopPair.singularCohomologyMap (R := R) (k := k) (M := M) e.hom n) := by
  intro y y' h
  have hy : ∀ y : Q.singularCohomology R k M n,
      TopPair.singularCohomologyMap e.inv n (TopPair.singularCohomologyMap e.hom n y) = y := by
    intro y
    rw [← TopPair.singularCohomologyMap_comp_apply, e.inv_hom_id, TopPair.singularCohomologyMap_id,
      ModuleCat.id_apply]
  rw [← hy y, h, hy]

/-- **Mayer–Vietoris for the complements of two closed sets**, exactness at the middle term: if
`a ∈ Hⁿ(X, X ∖ S)` and `b ∈ Hⁿ(X, X ∖ T)` restrict to classes of `Hⁿ(X, X ∖ (S ∪ T))` with sum
zero, then `a` and `-b` are the restrictions of one class of `Hⁿ(X, X ∖ (S ∩ T))`. This is the
Mayer–Vietoris sequence of the pairs `(X, X ∖ S)` and `(X, X ∖ T)`. -/
private lemma exists_complRestrict_eq_of_add_eq_zero {S T : Set X} (hS : IsClosed S)
    (hT : IsClosed T) {n : ℕ} (a : (TopPair.ofSubset Sᶜ).singularCohomology R k M n)
    (b : (TopPair.ofSubset Tᶜ).singularCohomology R k M n)
    (h : complRestrict Set.subset_union_left n a + complRestrict Set.subset_union_right n b = 0) :
    ∃ z : (TopPair.ofSubset (S ∩ T)ᶜ).singularCohomology R k M n,
      complRestrict Set.inter_subset_left n z = a ∧
        complRestrict Set.inter_subset_right n z = -b := by
  have hCA : Sᶜ ⊆ (Set.univ : Set X) := Set.subset_univ _
  have hDB : Tᶜ ⊆ (Set.univ : Set X) := Set.subset_univ _
  let eC := ofInclusionIsoOfSubset (Set.mem_univ) hCA (s' := Sᶜ) fun _ ↦ Iff.rfl
  let eD := ofInclusionIsoOfSubset (Set.mem_univ) hDB (s' := Tᶜ) fun _ ↦ Iff.rfl
  let eU := ofInclusionIsoOfSubset (fun _ ↦ Or.inl (Set.mem_univ _))
    (Set.union_subset_union hCA hDB)
    (s' := (S ∩ T)ᶜ) fun _ ↦ by rw [Set.compl_inter]
  let eI := ofInclusionIsoOfSubset (t := Set.univ ∩ Set.univ)
    (fun _ ↦ ⟨Set.mem_univ _, Set.mem_univ _⟩) (Set.inter_subset_inter hCA hDB)
    (s' := (S ∪ T)ᶜ) fun _ ↦ by rw [Set.compl_union]
  have hA : IsOpen ((↑) ⁻¹' (Set.univ : Set X) : Set ↥((Set.univ : Set X) ∪ Set.univ)) := by
    simp
  have hC : IsOpen ((↑) ⁻¹' Sᶜ : Set ↥(Sᶜ ∪ Tᶜ)) :=
    hS.isOpen_compl.preimage continuous_subtype_val
  have hD : IsOpen ((↑) ⁻¹' Tᶜ : Set ↥(Sᶜ ∪ Tᶜ)) :=
    hT.isOpen_compl.preimage continuous_subtype_val
  have hex := (ShortComplex.moduleCat_exact_iff _).1
    (singularCohomologyPairMayerVietoris_exact₂ R k M hCA hDB hA hA hC hD n)
  have hiA : TopPair.ofInclusionMap (Set.inter_subset_inter hCA hDB) hCA
      (ContinuousMap.inclusion Set.inter_subset_left) (fun _ hx ↦ Set.inter_subset_left hx) ≫
        eC.hom = eI.hom ≫ TopPair.ofSubsetMap (𝟙 X) (mapsTo_id_compl Set.subset_union_left) :=
    TopPair.hom_ext_of_fst _ (by
      ext x
      simp only [TopPair.Hom.fst_comp, ConcreteCategory.comp_apply,
        TopPair.ofSubsetMap_fst_apply]
      exact congrArg Subtype.val (TopPair.ofInclusionMap_fst_apply _ _ x))
  have hiB : TopPair.ofInclusionMap (Set.inter_subset_inter hCA hDB) hDB
      (ContinuousMap.inclusion Set.inter_subset_right) (fun _ hx ↦ Set.inter_subset_right hx) ≫
        eD.hom = eI.hom ≫ TopPair.ofSubsetMap (𝟙 X) (mapsTo_id_compl Set.subset_union_right) :=
    TopPair.hom_ext_of_fst _ (by
      ext x
      simp only [TopPair.Hom.fst_comp, ConcreteCategory.comp_apply,
        TopPair.ofSubsetMap_fst_apply]
      exact congrArg Subtype.val (TopPair.ofInclusionMap_fst_apply _ _ x))
  have hjA : TopPair.ofInclusionMap hCA (Set.union_subset_union hCA hDB)
      (ContinuousMap.inclusion Set.subset_union_left) (fun _ hx ↦ Set.subset_union_left hx) ≫
        eU.hom = eC.hom ≫ TopPair.ofSubsetMap (𝟙 X) (mapsTo_id_compl Set.inter_subset_left) :=
    TopPair.hom_ext_of_fst _ (by
      ext x
      simp only [TopPair.Hom.fst_comp, ConcreteCategory.comp_apply,
        TopPair.ofSubsetMap_fst_apply]
      exact congrArg Subtype.val (TopPair.ofInclusionMap_fst_apply _ _ x))
  have hjB : TopPair.ofInclusionMap hDB (Set.union_subset_union hCA hDB)
      (ContinuousMap.inclusion Set.subset_union_right) (fun _ hx ↦ Set.subset_union_right hx) ≫
        eU.hom = eD.hom ≫ TopPair.ofSubsetMap (𝟙 X) (mapsTo_id_compl Set.inter_subset_right) :=
    TopPair.hom_ext_of_fst _ (by
      ext x
      simp only [TopPair.Hom.fst_comp, ConcreteCategory.comp_apply,
        TopPair.ofSubsetMap_fst_apply]
      exact congrArg Subtype.val (TopPair.ofInclusionMap_fst_apply _ _ x))
  let HC := (TopPair.ofInclusion hCA).singularCohomology R k M n
  let HD := (TopPair.ofInclusion hDB).singularCohomology R k M n
  have hinl (y : HC) := ConcreteCategory.congr_hom
    (inl_singularCohomologyPairMayerVietorisFromBiprod R k M hCA hDB n) y
  have hinr (y : HD) := ConcreteCategory.congr_hom
    (inr_singularCohomologyPairMayerVietorisFromBiprod R k M hCA hDB n) y
  have hfst := ConcreteCategory.congr_hom
    (singularCohomologyPairMayerVietorisToBiprod_fst R k M hCA hDB n)
  have hsnd := ConcreteCategory.congr_hom
    (singularCohomologyPairMayerVietorisToBiprod_snd R k M hCA hDB n)
  simp only [ConcreteCategory.comp_apply] at hinl hinr hfst hsnd
  obtain ⟨q, hq⟩ := hex ((biprod.inl : HC ⟶ HC ⊞ HD) (TopPair.singularCohomologyMap eC.hom n a) +
    (biprod.inr : HD ⟶ HC ⊞ HD) (-TopPair.singularCohomologyMap eD.hom n b)) (by
      dsimp only
      rw [map_add, hinl, hinr]
      simp only [map_neg, ModuleCat.hom_neg, LinearMap.neg_apply, neg_neg]
      rw [← TopPair.singularCohomologyMap_comp_apply, ← TopPair.singularCohomologyMap_comp_apply,
        hiA,
        hiB, TopPair.singularCohomologyMap_comp_apply, TopPair.singularCohomologyMap_comp_apply,
        ← map_add, h, map_zero])
  let z := TopPair.singularCohomologyMap eU.inv n q
  have hz : TopPair.singularCohomologyMap eU.hom n z = q := by
    rw [← TopPair.singularCohomologyMap_comp_apply, eU.hom_inv_id,
      TopPair.singularCohomologyMap_id, ModuleCat.id_apply]
  refine ⟨z, singularCohomologyMap_hom_injective eC n ?_,
    singularCohomologyMap_hom_injective eD n ?_⟩
  · rw [← TopPair.singularCohomologyMap_comp_apply, ← hjA, TopPair.singularCohomologyMap_comp_apply,
      hz, ← hfst, hq]
    have h1 (y : HC) : (biprod.fst : HC ⊞ HD ⟶ HC) ((biprod.inl : HC ⟶ HC ⊞ HD) y) = y := by
      rw [← ConcreteCategory.comp_apply, biprod.inl_fst, ModuleCat.id_apply]
    have h2 (y : HD) : (biprod.fst : HC ⊞ HD ⟶ HC) ((biprod.inr : HD ⟶ HC ⊞ HD) y) = 0 := by
      rw [← ConcreteCategory.comp_apply, biprod.inr_fst]
      rfl
    rw [map_add, h1, h2, add_zero]
  · rw [← TopPair.singularCohomologyMap_comp_apply, ← hjB, TopPair.singularCohomologyMap_comp_apply,
      hz, ← hsnd, hq]
    have h1 (y : HC) : (biprod.snd : HC ⊞ HD ⟶ HD) ((biprod.inl : HC ⟶ HC ⊞ HD) y) = 0 := by
      rw [← ConcreteCategory.comp_apply, biprod.inl_snd]
      rfl
    have h2 (y : HD) : (biprod.snd : HC ⊞ HD ⟶ HD) ((biprod.inr : HD ⟶ HC ⊞ HD) y) = y := by
      rw [← ConcreteCategory.comp_apply, biprod.inr_snd, ModuleCat.id_apply]
    rw [map_add, h1, h2, zero_add, map_neg]

/-! ### Classes restricted to an open subset and extended back -/

section Extend

variable {P W : TopCat.{v}}

/-- The restriction `Hⁿ(X, X ∖ f(K)) ⟶ Hⁿ(P, P ∖ K)` along an injective map `f : P ⟶ X`. -/
private abbrev compactsRestrict {f : P ⟶ X} (hf : Function.Injective f) (K : Compacts P)
    (n : ℕ) :
    (TopPair.ofSubset (K.map f f.hom.continuous : Set X)ᶜ).singularCohomology R k M n ⟶
      (TopPair.ofSubset (K : Set P)ᶜ).singularCohomology R k M n :=
  TopPair.singularCohomologyMap (TopPair.ofSubsetMap f (mapsTo_compl_compacts_map hf K)) n

/-- Restricting along `f` commutes with enlarging the compact set. -/
private lemma compactSupportCohomologyι_compactsRestrict_complRestrict {f : P ⟶ X}
    (hf : Function.Injective f) {K L : Compacts P} (hKL : K ≤ L) {n : ℕ}
    (a : (TopPair.ofSubset (K.map f f.hom.continuous : Set X)ᶜ).singularCohomology R k M n) :
    compactSupportCohomologyι n L (compactsRestrict hf L n
        (complRestrict (Compacts.map_mono f f.hom.continuous hKL) n a)) =
      compactSupportCohomologyι n K (compactsRestrict hf K n a) := by
  have hpair : TopPair.ofSubsetMap (𝟙 P) (mapsTo_id_compl_compacts hKL) ≫
        TopPair.ofSubsetMap f (mapsTo_compl_compacts_map hf K) =
      TopPair.ofSubsetMap f (mapsTo_compl_compacts_map hf L) ≫
        TopPair.ofSubsetMap (𝟙 X) (mapsTo_id_compl (Compacts.map_mono f f.hom.continuous hKL)) :=
    TopPair.ofSubsetMap_comp_ofSubsetMap_eq _ _ _ _ (by simp)
  rw [← singularCohomologyMap_comp_compactSupportCohomologyι_apply n hKL]
  simp only [← TopPair.singularCohomologyMap_comp_apply, hpair]

/-- A class of `Hⁿ(X, X ∖ i(M))`, restricted to `Hⁿ(W, W ∖ M)` along an open embedding
`i = g ≫ f` and extended to `P` along `g`, is the class restricted along `f` from the larger
compact set `f(K) ⊇ i(M)`. -/
private lemma compactSupportCohomologyExtend_compactSupportCohomologyι_compactsRestrict
    [T2Space P] {f : P ⟶ X} {g : W ⟶ P} {i : W ⟶ X} (hf : IsOpenEmbedding f)
    (hg : IsOpenEmbedding g) (hi : IsOpenEmbedding i) (hgf : g ≫ f = i) {M' : Compacts W}
    {K : Compacts P} (hMK : (M'.map i i.hom.continuous : Set X) ⊆ K.map f f.hom.continuous)
    {n : ℕ}
    (z : (TopPair.ofSubset (M'.map i i.hom.continuous : Set X)ᶜ).singularCohomology R k M n) :
    compactSupportCohomologyExtend hg n
        (compactSupportCohomologyι n M' (compactsRestrict hi.injective M' n z)) =
      compactSupportCohomologyι n K
        (compactsRestrict hf.injective K n (complRestrict hMK n z)) := by
  have hset : ((M'.map g g.hom.continuous).map f f.hom.continuous : Set X) =
      M'.map i i.hom.continuous := by
    simp only [Compacts.coe_map, ← Set.image_comp, ← hgf]
    rfl
  have hle : M'.map g g.hom.continuous ≤ K := fun x hx ↦ by
    have hx' : f x ∈ ((M'.map g g.hom.continuous).map f f.hom.continuous : Set X) :=
      Set.mem_image_of_mem f hx
    rw [hset] at hx'
    simpa [hf.injective.mem_set_image] using hMK hx'
  have hz : compactsRestrict hi.injective M' n z =
      TopPair.singularCohomologyMap (TopPair.ofSubsetMap g
        (mapsTo_compl_compacts_map hg.injective M')) n
        (compactsRestrict hf.injective _ n (complRestrict hset.ge n z)) := by
    have hpair : (TopPair.ofSubsetMap g (mapsTo_compl_compacts_map hg.injective M') ≫
          TopPair.ofSubsetMap f (mapsTo_compl_compacts_map hf.injective _)) ≫
          TopPair.ofSubsetMap (𝟙 X) (mapsTo_id_compl hset.ge) =
        TopPair.ofSubsetMap i (mapsTo_compl_compacts_map hi.injective M') := by
      rw [TopPair.ofSubsetMap_comp_ofSubsetMap_of_comp_eq (g'' := g ≫ f) _ _
          (fun _ hx ↦ mapsTo_compl_compacts_map hf.injective _
            (mapsTo_compl_compacts_map hg.injective M' hx)) rfl]
      exact TopPair.ofSubsetMap_comp_ofSubsetMap_of_comp_eq _ _ _ (by rw [Category.comp_id, hgf])
    rw [← TopPair.singularCohomologyMap_comp_apply, ← TopPair.singularCohomologyMap_comp_apply,
      hpair]
  rw [hz, ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
    singularCohomologyMap_comp_compactSupportCohomologyι_comp_extend,
    ← compactSupportCohomologyι_compactsRestrict_complRestrict hf.injective hle,
    complRestrict_apply_complRestrict hset.ge (Compacts.map_mono f f.hom.continuous hle)]

end Extend

/-! ### The first two maps -/

variable {U V : Set X} (hU : IsOpen U) (hV : IsOpen V)

/-- The inclusion of an open subset, as a morphism of `TopCat`, is an open embedding. -/
lemma isOpenEmbedding_ofHom_subtypeVal {s : Set X} (hs : IsOpen s) :
    IsOpenEmbedding (ofHom (ContinuousMap.subtypeVal s) : of s ⟶ X) :=
  hs.isOpenEmbedding_subtypeVal

/-- The inclusion of an open subset `s` into a subset `t ⊇ s`, as a morphism of `TopCat`, is an
open embedding. -/
lemma isOpenEmbedding_ofHom_inclusion {s t : Set X} (h : s ⊆ t) (hs : IsOpen s) :
    IsOpenEmbedding (ofHom (ContinuousMap.inclusion h) : of s ⟶ of t) :=
  IsOpenEmbedding.inclusion h (hs.preimage continuous_subtype_val)

variable [T2Space X] (R k M)

/-- The first map `Hⁿ_c(U ∩ V) ⟶ Hⁿ_c(U) ⊞ Hⁿ_c(V)` of the Mayer–Vietoris sequence of cohomology
with compact supports, with components the extension by zero to `U` and minus the extension by
zero to `V`. -/
def compactSupportCohomologyMayerVietorisToBiprod (n : ℕ) :
    (of ↥(U ∩ V)).compactSupportCohomology R k M n ⟶
      (of U).compactSupportCohomology R k M n ⊞ (of V).compactSupportCohomology R k M n :=
  biprod.lift
    (compactSupportCohomologyExtend
      (isOpenEmbedding_ofHom_inclusion Set.inter_subset_left (hU.inter hV)) n)
    (-compactSupportCohomologyExtend
      (isOpenEmbedding_ofHom_inclusion Set.inter_subset_right (hU.inter hV)) n)

/-- The second map `Hⁿ_c(U) ⊞ Hⁿ_c(V) ⟶ Hⁿ_c(X)` of the Mayer–Vietoris sequence of cohomology
with compact supports, the sum of the extensions by zero to `X`. -/
def compactSupportCohomologyMayerVietorisFromBiprod (n : ℕ) :
    (of U).compactSupportCohomology R k M n ⊞ (of V).compactSupportCohomology R k M n ⟶
      X.compactSupportCohomology R k M n :=
  biprod.desc (compactSupportCohomologyExtend (isOpenEmbedding_ofHom_subtypeVal hU) n)
    (compactSupportCohomologyExtend (isOpenEmbedding_ofHom_subtypeVal hV) n)

@[reassoc (attr := simp)]
lemma compactSupportCohomologyMayerVietorisToBiprod_fst (n : ℕ) :
    compactSupportCohomologyMayerVietorisToBiprod R k M hU hV n ≫ biprod.fst =
      compactSupportCohomologyExtend
        (isOpenEmbedding_ofHom_inclusion Set.inter_subset_left (hU.inter hV)) n :=
  biprod.lift_fst _ _

@[reassoc (attr := simp)]
lemma compactSupportCohomologyMayerVietorisToBiprod_snd (n : ℕ) :
    compactSupportCohomologyMayerVietorisToBiprod R k M hU hV n ≫ biprod.snd =
      -compactSupportCohomologyExtend
        (isOpenEmbedding_ofHom_inclusion Set.inter_subset_right (hU.inter hV)) n :=
  biprod.lift_snd _ _

@[reassoc (attr := simp)]
lemma inl_compactSupportCohomologyMayerVietorisFromBiprod (n : ℕ) :
    biprod.inl ≫ compactSupportCohomologyMayerVietorisFromBiprod R k M hU hV n =
      compactSupportCohomologyExtend (isOpenEmbedding_ofHom_subtypeVal hU) n :=
  biprod.inl_desc _ _

@[reassoc (attr := simp)]
lemma inr_compactSupportCohomologyMayerVietorisFromBiprod (n : ℕ) :
    biprod.inr ≫ compactSupportCohomologyMayerVietorisFromBiprod R k M hU hV n =
      compactSupportCohomologyExtend (isOpenEmbedding_ofHom_subtypeVal hV) n :=
  biprod.inr_desc _ _

/-- The first two maps of the Mayer–Vietoris sequence of cohomology with compact supports compose
to zero: both composites `Hⁿ_c(U ∩ V) ⟶ Hⁿ_c(X)` are the extension by zero. -/
@[reassoc (attr := simp)]
lemma compactSupportCohomologyMayerVietorisToBiprod_fromBiprod (n : ℕ) :
    compactSupportCohomologyMayerVietorisToBiprod R k M hU hV n ≫
      compactSupportCohomologyMayerVietorisFromBiprod R k M hU hV n = 0 := by
  rw [compactSupportCohomologyMayerVietorisToBiprod,
    compactSupportCohomologyMayerVietorisFromBiprod,
    biprod.lift_desc, Preadditive.neg_comp,
    ← compactSupportCohomologyExtend_comp _ _ n ((isOpenEmbedding_ofHom_subtypeVal hU).comp
      (isOpenEmbedding_ofHom_inclusion Set.inter_subset_left (hU.inter hV))),
    ← compactSupportCohomologyExtend_comp _ _ n ((isOpenEmbedding_ofHom_subtypeVal hV).comp
      (isOpenEmbedding_ofHom_inclusion Set.inter_subset_right (hU.inter hV)))]
  -- both composites are the inclusion of `U ∩ V` into `X`
  exact add_neg_eq_zero.2 rfl

/-! ### Exactness at `Hⁿ_c(U) ⊞ Hⁿ_c(V)` -/

variable {R k M}

omit [T2Space X] in
/-- A compact subset of `X` lying in an open set `U` is the image of a compact subset of `U`. -/
private lemma exists_compacts_map_subtypeVal_eq {K : Compacts X} (hK : (K : Set X) ⊆ U) :
    ∃ K' : Compacts (of U),
      (K'.map (ofHom (ContinuousMap.subtypeVal U) : of U ⟶ X) (map_continuous _) : Set X) = K := by
  obtain ⟨K', hK'⟩ := (Compacts.range_map IsInducing.subtypeVal).ge
    (show (K : Set X) ⊆ Set.range ((↑) : U → X) by rwa [Subtype.range_coe])
  exact ⟨K', congrArg SetLike.coe hK'⟩

/-- The heart of exactness of the Mayer–Vietoris sequence of cohomology with compact supports at
`Hⁿ_c(U) ⊞ Hⁿ_c(V)`: if the extensions of `x ∈ Hⁿ_c(U)` and `y ∈ Hⁿ_c(V)` to `X = U ∪ V` cancel,
then `x` and `-y` are the extensions of one class of `Hⁿ_c(U ∩ V)`. Represent `x` and `y` on
compact sets `K ⊆ U` and `L ⊆ V`; the sum of their extensions vanishes on some compact `C ⊇ K ∪ L`
of `X`, which splits as `K₂ ∪ L₂` with `K ⊆ K₂ ⊆ U` and `L ⊆ L₂ ⊆ V` compact; Mayer–Vietoris for
`(X, X ∖ K₂)` and `(X, X ∖ L₂)` gives a class supported in `K₂ ∩ L₂ ⊆ U ∩ V`. -/
private lemma exists_compactSupportCohomologyExtend_eq (hUV : U ∪ V = Set.univ) {n : ℕ}
    (x : (of U).compactSupportCohomology R k M n) (y : (of V).compactSupportCohomology R k M n)
    (h : compactSupportCohomologyExtend (isOpenEmbedding_ofHom_subtypeVal hU) n x +
      compactSupportCohomologyExtend (isOpenEmbedding_ofHom_subtypeVal hV) n y = 0) :
    ∃ w : (of ↥(U ∩ V)).compactSupportCohomology R k M n,
      compactSupportCohomologyExtend
          (isOpenEmbedding_ofHom_inclusion Set.inter_subset_left (hU.inter hV)) n w = x ∧
        compactSupportCohomologyExtend
          (isOpenEmbedding_ofHom_inclusion Set.inter_subset_right (hU.inter hV)) n w = -y := by
  have hiU := isOpenEmbedding_ofHom_subtypeVal hU
  have hiV := isOpenEmbedding_ofHom_subtypeVal hV
  have hiW := isOpenEmbedding_ofHom_subtypeVal (hU.inter hV)
  obtain ⟨K, -, x', rfl⟩ := exists_compactSupportCohomologyι_eq x ⊥
  obtain ⟨L, -, y', rfl⟩ := exists_compactSupportCohomologyι_eq y ⊥
  obtain ⟨a, rfl⟩ : ∃ a, compactsRestrict hiU.injective K n a = x' := by
    refine ⟨(singularCohomologyComplCompactsMapIso R k M hiU K n).inv x', ?_⟩
    have := (singularCohomologyComplCompactsMapIso R k M hiU K n).inv_hom_id_apply x'
    rwa [singularCohomologyComplCompactsMapIso_hom] at this
  obtain ⟨b, rfl⟩ : ∃ b, compactsRestrict hiV.injective L n b = y' := by
    refine ⟨(singularCohomologyComplCompactsMapIso R k M hiV L n).inv y', ?_⟩
    have := (singularCohomologyComplCompactsMapIso R k M hiV L n).inv_hom_id_apply y'
    rwa [singularCohomologyComplCompactsMapIso_hom] at this
  have hxa := ConcreteCategory.congr_hom
    (singularCohomologyMap_comp_compactSupportCohomologyι_comp_extend hiU n K) a
  have hyb := ConcreteCategory.congr_hom
    (singularCohomologyMap_comp_compactSupportCohomologyι_comp_extend hiV n L) b
  simp only [ConcreteCategory.comp_apply] at hxa hyb
  rw [hxa, hyb] at h
  -- the sum of the extensions vanishes on some compact set `C` containing `K ∪ L`
  let KX := K.map _ (ofHom (ContinuousMap.subtypeVal U) : of U ⟶ X).hom.continuous
  let LX := L.map _ (ofHom (ContinuousMap.subtypeVal V) : of V ⟶ X).hom.continuous
  rw [← singularCohomologyMap_comp_compactSupportCohomologyι_apply n (le_sup_left : KX ≤ KX ⊔ LX),
    ← singularCohomologyMap_comp_compactSupportCohomologyι_apply n (le_sup_right : LX ≤ KX ⊔ LX),
    ← map_add, compactSupportCohomologyι_eq_zero_iff] at h
  obtain ⟨C', hC', hzero⟩ := h
  rw [map_add, complRestrict_apply_complRestrict (le_sup_left : KX ≤ KX ⊔ LX) hC',
    complRestrict_apply_complRestrict (le_sup_right : LX ≤ KX ⊔ LX) hC'] at hzero
  -- split `C` as `K₁ ∪ L₁` with `K₁ ⊆ U` and `L₁ ⊆ V`, and enlarge `K` and `L` accordingly
  obtain ⟨K₁, L₁, hK₁, hL₁, hK₁U, hL₁V, hC'eq⟩ :=
    C'.isCompact.binary_compact_cover hU hV (hUV.symm ▸ Set.subset_univ _)
  obtain ⟨K₂, hK₂⟩ := exists_compacts_map_subtypeVal_eq (K := KX ⊔ ⟨K₁, hK₁⟩)
    (Set.union_subset (by rintro _ ⟨x, -, rfl⟩; exact x.2) hK₁U)
  obtain ⟨L₂, hL₂⟩ := exists_compacts_map_subtypeVal_eq (K := LX ⊔ ⟨L₁, hL₁⟩)
    (Set.union_subset (by rintro _ ⟨x, -, rfl⟩; exact x.2) hL₁V)
  let S := (K₂.map _ (ofHom (ContinuousMap.subtypeVal U) : of U ⟶ X).hom.continuous : Set X)
  let T := (L₂.map _ (ofHom (ContinuousMap.subtypeVal V) : of V ⟶ X).hom.continuous : Set X)
  have hSeq : S = (KX : Set X) ∪ K₁ := hK₂
  have hTeq : T = (LX : Set X) ∪ L₁ := hL₂
  have hKS : (KX : Set X) ⊆ S := hSeq ▸ Set.subset_union_left
  have hLT : (LX : Set X) ⊆ T := hTeq ▸ Set.subset_union_left
  have hCST : (C' : Set X) ⊆ S ∪ T := by
    rw [hC'eq, hSeq, hTeq]
    exact Set.union_subset_union Set.subset_union_right Set.subset_union_right
  have hKK₂ : K ≤ K₂ := fun x hx ↦ by
    have : (x : X) ∈ S := hKS ⟨x, hx, rfl⟩
    simpa [S, Subtype.val_injective.mem_set_image] using this
  have hLL₂ : L ≤ L₂ := fun x hx ↦ by
    have : (x : X) ∈ T := hLT ⟨x, hx, rfl⟩
    simpa [T, Subtype.val_injective.mem_set_image] using this
  -- Mayer–Vietoris for `(X, X ∖ S)` and `(X, X ∖ T)`
  have hsum : complRestrict Set.subset_union_left n (complRestrict hKS n a) +
      complRestrict Set.subset_union_right n (complRestrict hLT n b) = 0 := by
    have := congrArg (complRestrict hCST n) hzero
    rw [map_add, map_zero, complRestrict_apply_complRestrict, complRestrict_apply_complRestrict]
      at this
    rw [complRestrict_apply_complRestrict, complRestrict_apply_complRestrict]
    exact this
  obtain ⟨z, hzS, hzT⟩ := exists_complRestrict_eq_of_add_eq_zero
    (K₂.map _ (map_continuous _)).isCompact.isClosed
    (L₂.map _ (map_continuous _)).isCompact.isClosed _ _ hsum
  -- the class `z` is supported in the compact set `S ∩ T ⊆ U ∩ V`
  obtain ⟨M', hM'⟩ := exists_compacts_map_subtypeVal_eq (U := U ∩ V)
    (K := ⟨S ∩ T, (K₂.map _ (map_continuous _)).isCompact.inter_right
      (L₂.map _ (map_continuous _)).isCompact.isClosed⟩)
    (Set.inter_subset_inter (by rintro _ ⟨x, -, rfl⟩; exact x.2)
      (by rintro _ ⟨x, -, rfl⟩; exact x.2))
  refine ⟨compactSupportCohomologyι n M' (compactsRestrict hiW.injective M' n
    (complRestrict hM'.ge n z)), ?_, ?_⟩
  · rw [compactSupportCohomologyExtend_compactSupportCohomologyι_compactsRestrict hiU
      (isOpenEmbedding_ofHom_inclusion Set.inter_subset_left (hU.inter hV)) hiW rfl
      (K := K₂) (hM'.trans_subset Set.inter_subset_left), complRestrict_apply_complRestrict, hzS,
      compactSupportCohomologyι_compactsRestrict_complRestrict hiU.injective hKK₂]
  · rw [compactSupportCohomologyExtend_compactSupportCohomologyι_compactsRestrict hiV
      (isOpenEmbedding_ofHom_inclusion Set.inter_subset_right (hU.inter hV)) hiW rfl
      (K := L₂) (hM'.trans_subset Set.inter_subset_right), complRestrict_apply_complRestrict, hzT,
      map_neg, map_neg, compactSupportCohomologyι_compactsRestrict_complRestrict hiV.injective hLL₂]

omit [T2Space X] in
/-- An element of a biproduct of modules is the sum of the inclusions of its two components. -/
private lemma moduleCat_biprod_eq_inl_add_inr {A B : ModuleCat.{v} k} (q : ↑(A ⊞ B)) :
    q = (biprod.inl : A ⟶ A ⊞ B) ((biprod.fst : A ⊞ B ⟶ A) q) +
      (biprod.inr : B ⟶ A ⊞ B) ((biprod.snd : A ⊞ B ⟶ B) q) := by
  have := ConcreteCategory.congr_hom (biprod.total (X := A) (Y := B)) q
  simp only [ModuleCat.hom_add, LinearMap.add_apply, ConcreteCategory.comp_apply,
    ModuleCat.id_apply] at this
  exact this.symm

variable (R k M) in
/-- **Exactness of the Mayer–Vietoris sequence of cohomology with compact supports at
`Hⁿ_c(U) ⊞ Hⁿ_c(V)`**, for an open cover `X = U ∪ V` of a Hausdorff space. -/
lemma compactSupportCohomologyMayerVietoris_exact₂ (hUV : U ∪ V = Set.univ) (n : ℕ) :
    (ShortComplex.mk _ _
      (compactSupportCohomologyMayerVietorisToBiprod_fromBiprod R k M hU hV n)).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  intro p hp
  let HU := (of U).compactSupportCohomology R k M n
  let HV := (of V).compactSupportCohomology R k M n
  have h₁ := ConcreteCategory.congr_hom
    (inl_compactSupportCohomologyMayerVietorisFromBiprod R k M hU hV n)
    ((biprod.fst : HU ⊞ HV ⟶ HU) p)
  have h₂ := ConcreteCategory.congr_hom
    (inr_compactSupportCohomologyMayerVietorisFromBiprod R k M hU hV n)
    ((biprod.snd : HU ⊞ HV ⟶ HV) p)
  rw [ConcreteCategory.comp_apply] at h₁ h₂
  rw [moduleCat_biprod_eq_inl_add_inr p] at hp ⊢
  dsimp only at hp ⊢
  rw [map_add, h₁, h₂] at hp
  obtain ⟨w, hwU, hwV⟩ := exists_compactSupportCohomologyExtend_eq hU hV hUV _ _ hp
  refine ⟨w, ?_⟩
  have h₃ := ConcreteCategory.congr_hom
    (compactSupportCohomologyMayerVietorisToBiprod_fst R k M hU hV n) w
  have h₄ := ConcreteCategory.congr_hom
    (compactSupportCohomologyMayerVietorisToBiprod_snd R k M hU hV n) w
  rw [ConcreteCategory.comp_apply] at h₃ h₄
  rw [moduleCat_biprod_eq_inl_add_inr
      (compactSupportCohomologyMayerVietorisToBiprod R k M hU hV n w),
    h₃, h₄, hwU]
  simp only [ModuleCat.hom_neg, LinearMap.neg_apply, hwV, neg_neg]
  rfl

end TopCat

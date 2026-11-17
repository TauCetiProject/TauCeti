/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Excision
public import TauCeti.AlgebraicTopology.Singular.Homotopy.Invariance
public import TauCeti.Topology.Homotopy.Attach
public import TauCeti.Topology.Maps.IsClosedEmbedding

/-!
# Relative homology of an attachment

Let `P = (A, S)` be a topological pair and let `Z` be obtained from a closed subset `X` by attaching
`A` along `S` through a map of pairs `f : (A, S) ⟶ (Z, X)`: the map `φ : A → Z` underlying `f` is a
closed embedding, it sends a point into `X` only if the point lies in `S`, and `X` together with the
image of `φ` is all of `Z`. Suppose that `S` has an open neighbourhood `O` in `A` and that there is
a deformation `H` of `A`, starting at the identity, which fixes `S` pointwise, keeps `O` inside
`O` and pushes `O` into `S` at time one. Then `f` induces isomorphisms `Hₙ(A, S) ≅ Hₙ(Z, X)` on
relative singular homology, with coefficients in any abelian category with coproducts, in every
degree (`TopPair.isIso_singularHomologyMap_of_attach`).

This is the homology of a relative homeomorphism out of a good pair. Typical instances are the
attachment of a closed disc along its boundary sphere, where `O` is the outer half of the disc and
`H` the radial push onto the sphere, and of the disc bundle of a vector bundle along its sphere
bundle, where the same push runs in every fibre.

The proof thickens `X` to the open set `N = X ∪ φ(O)`
(`Topology.IsClosedEmbedding.isOpen_union_image`). The deformation `H` shows that
`(A, S) ⟶ (A, O)` induces isomorphisms, and its extension by the identity of `X`
(`Topology.IsClosedEmbedding.attachDeformation`) that `(Z, X) ⟶ (Z, N)` does
(`ContinuousMap.exists_homotopy_id_of_deformation`,
`Topology.IsClosedEmbedding.exists_homotopy_id_attach` and
`TopPair.isIso_singularHomologyMap_ofSubsetMap_id_of_homotopy`). Finally the complement of `X`
lies in the image of `φ`, so excision for the open cover of `Z` by `N` and the complement of `X`
(`TopPair.isIso_singularHomologyMap_of_open_cover`) makes `(A, O) ⟶ (Z, N)` an isomorphism.

## Main results

* `TopPair.isOpen_cond_union_image_compl`, `TopPair.iUnion_cond_union_image_compl` and
  `TopPair.cond_union_image_compl_subset_range_or_subset_range_fst`: the open cover of `Z` by
  `X ∪ φ(O)` and the complement of `X` to which excision is applied, in homology and in
  cohomology.
* `TopPair.comp_ofSubsetMap_id_eq`: the comparison square of maps of pairs relating `f` to the map
  of the enlarged pairs, in homology and in cohomology.
* `TopPair.isIso_singularHomologyMap_ofSubsetMap_union_image`: excision of the complement of the
  attached space from the thickened pair `(Z, X ∪ φ(O))`.
* `TopPair.isIso_singularHomologyMap_of_attach`: attaching along a subspace with a deformation
  neighbourhood induces isomorphisms on relative singular homology.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 2.1,
  Proposition 2.22 and its proof (good pairs and excision).
-/

public section

noncomputable section

open CategoryTheory Limits Set Topology TauCeti
open scoped unitInterval

universe w v u

namespace TopPair

section Cover

variable {A Z : TopCat.{w}} {O : Set A} {X : Set Z} (φ : A ⟶ Z)

/-- If an injective map `φ : A → Z` sends a point into `X` only if it lies in `O`, the subspace `O`
of `(A, O)` is the full preimage of the subspace of `(Z, X ∪ φ(O))`. -/
lemma mem_range_map_of_fst_ofSubsetMap_union_image_mem (hφ : Function.Injective φ)
    (hφX : ∀ a, φ a ∈ X → a ∈ O) (hφO : MapsTo φ O (X ∪ φ '' O)) (a : (ofSubset O).fst)
    (ha : Hom.fst (ofSubsetMap φ hφO) a ∈ range (ofSubset (X ∪ φ '' O)).map) :
    a ∈ range (ofSubset O).map := by
  rw [range_ofSubset_map, ofSubsetMap_fst] at ha
  rw [range_ofSubset_map]
  obtain hX' | ⟨b, hb, hba⟩ := ha
  exacts [hφX a hX', hφ hba ▸ hb]

/-- Under the hypotheses of `Topology.IsClosedEmbedding.isOpen_union_image`, with `X` closed, the
thickening `X ∪ φ(O)` and the complement of `X` are open. -/
lemma isOpen_cond_union_image_compl (hX : IsClosed X) (hφ : IsClosedEmbedding φ) (hO : IsOpen O)
    (hφX : ∀ a, φ a ∈ X → a ∈ O) (hcover : X ∪ range φ = univ) (b : Bool) :
    IsOpen (bif b then X ∪ φ '' O else Xᶜ) := by
  cases b
  exacts [hX.isOpen_compl, hφ.isOpen_union_image hO hφX hcover]

/-- The thickening `X ∪ φ(O)` and the complement of `X` cover `Z`. -/
lemma iUnion_cond_union_image_compl :
    ⋃ b : Bool, (bif b then X ∪ φ '' O else Xᶜ) = univ :=
  union_eq_iUnion.symm.trans (eq_univ_of_forall fun z ↦ (em (z ∈ X)).imp Or.inl id)

/-- If `X` together with the image of `φ` is all of `Z`, the thickening `X ∪ φ(O)` is the subspace
of `(Z, X ∪ φ(O))` and the complement of `X` lies in the image of `φ`: this is the cover to which
the excision theorems for maps of pairs are applied. -/
lemma cond_union_image_compl_subset_range_or_subset_range_fst (hcover : X ∪ range φ = univ)
    (hφO : MapsTo φ O (X ∪ φ '' O)) (b : Bool) :
    (bif b then X ∪ φ '' O else Xᶜ) ⊆ range (ofSubset (X ∪ φ '' O)).map ∨
      (bif b then X ∪ φ '' O else Xᶜ) ⊆ range (Hom.fst (ofSubsetMap φ hφO)) := by
  cases b
  · rw [ofSubsetMap_fst]
    exact Or.inr fun z hz ↦ (hcover.symm ▸ mem_univ z : z ∈ X ∪ _).resolve_left hz
  · exact Or.inl (range_ofSubset_map (X := Z) (B := X ∪ φ '' O)).ge

end Cover

variable {P : TopPair.{w}} {Z : TopCat.{w}} {X : Set Z} {O : Set P.fst}

/-- **The comparison square of an attachment.** A map of pairs `f : (A, S) ⟶ (Z, X)` followed by an
enlargement `(Z, X) ⟶ (Z, N)` is the isomorphism of `(A, S)` with the pair of `A` and the range of
the embedding of `S`, followed by an enlargement `(A, S) ⟶ (A, O)` and the map `(A, O) ⟶ (Z, N)`
induced by the map `φ` underlying `f`: on the ambient spaces both composites are `φ`. -/
lemma comp_ofSubsetMap_id_eq {N : Set Z} (f : P ⟶ ofSubset X) (hXN : MapsTo (𝟙 Z) X N)
    (hSO : MapsTo (𝟙 P.fst) (range P.map) O) (hφO : MapsTo (Hom.fst f) O N) :
    f ≫ ofSubsetMap (𝟙 Z) hXN =
      (isoOfSubsetRange P).hom ≫ ofSubsetMap (𝟙 P.fst) hSO ≫
        ofSubsetMap (Y := Z) (Hom.fst f) hφO :=
  (congrArg (· ≫ ofSubsetMap (𝟙 Z) hXN) (isoOfSubsetRange_hom_comp_ofSubsetMap f)).symm.trans <|
    (Category.assoc _ _ _).trans <| congrArg ((isoOfSubsetRange P).hom ≫ ·) <|
      ofSubsetMap_comp_ofSubsetMap_eq _ _ _ _ ((Category.comp_id _).trans (Category.id_comp _).symm)

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C) (n : ℕ)

/-- **Excision for the thickening of an attachment.** Let `φ : A → Z` be a closed embedding with `X`
closed in `Z` and `X` together with the image of `φ` all of `Z`, and let `O` be an open subset of
`A` containing every point which `φ` sends into `X`. Then the map of pairs
`(A, O) ⟶ (Z, X ∪ φ(O))` induced by `φ` induces isomorphisms on relative singular homology: the
open sets `X ∪ φ(O)` and `Z ∖ X` cover `Z`, and the second lies in the image of `φ`. -/
theorem isIso_singularHomologyMap_ofSubsetMap_union_image {A : TopCat.{w}} {O : Set A}
    (φ : A ⟶ Z) (hX : IsClosed X) (hφ : IsClosedEmbedding φ) (hO : IsOpen O)
    (hφX : ∀ a, φ a ∈ X → a ∈ O) (hcover : X ∪ range φ = univ)
    (hφO : MapsTo φ O (X ∪ φ '' O)) :
    IsIso (TopPair.singularHomologyMap (ofSubsetMap φ hφO) R n) :=
  isIso_singularHomologyMap_of_open_cover R (ofSubsetMap φ hφO)
    (by rw [ofSubsetMap_fst]; exact hφ.isEmbedding)
    (mem_range_map_of_fst_ofSubsetMap_union_image_mem φ hφ.injective hφX hφO) _
    (isOpen_cond_union_image_compl φ hX hφ hO hφX hcover) (iUnion_cond_union_image_compl φ)
    (cond_union_image_compl_subset_range_or_subset_range_fst φ hcover hφO) n

/-- **Attaching along a subspace with a deformation neighbourhood induces isomorphisms on relative
homology.** Let `f : (A, S) ⟶ (Z, X)` be a map of pairs with `X` closed in `Z`, whose map
`φ : A → Z` is a closed embedding sending a point into `X` only if it lies in `S`, and such that
`X` together with the image of `φ` is all of `Z`. Let `O` be an open neighbourhood of `S` in `A`,
and `H : I × A → A` a deformation starting at the identity, fixing `S` pointwise, keeping `O`
inside `O`, and pushing `O` into `S` at time one. Then `f` induces isomorphisms
`Hₙ(A, S) ≅ Hₙ(Z, X)` on relative singular homology, with coefficients in any abelian category with
coproducts, in every degree. -/
theorem isIso_singularHomologyMap_of_attach (f : P ⟶ ofSubset X) (hX : IsClosed X)
    (hf : IsClosedEmbedding (Hom.fst f)) (hfX : ∀ a, Hom.fst f a ∈ X → a ∈ range P.map)
    (hcover : X ∪ range (Hom.fst f) = univ) (hO : IsOpen O) (hSO : range P.map ⊆ O)
    (H : C(I × P.fst, P.fst)) (hH₀ : ∀ a, H (0, a) = a)
    (hHS : ∀ t, ∀ a ∈ range P.map, H (t, a) = a) (hHO : ∀ t, ∀ a ∈ O, H (t, a) ∈ O)
    (hH₁ : ∀ a ∈ O, H (1, a) ∈ range P.map) :
    IsIso (TopPair.singularHomologyMap f R n) := by
  -- The map `φ` with its codomain read as `Z` rather than as the ambient space of `(Z, X)`.
  let g : P.fst ⟶ Z := Hom.fst f
  -- Both subspaces are enlarged: `S` to `O`, and `X` to the open thickening `X ∪ φ(O)`.
  have hSO' : MapsTo (𝟙 P.fst) (range P.map) O :=
    ConcreteCategory.coe_id (X := P.fst) ▸ (mapsTo_id _).mono_right hSO
  have hXN : MapsTo (𝟙 Z) X (X ∪ g '' O) := fun _ hz ↦ Or.inl hz
  have hφO : MapsTo g O (X ∪ g '' O) := fun a ha ↦ Or.inr ⟨a, ha, rfl⟩
  -- The deformation `H` and its extension to `Z` make both enlargements isomorphisms, and excision
  -- for the open cover of `Z` by the thickening and the complement of `X` makes the map of the
  -- enlarged pairs one.
  obtain ⟨ρA, HA, hA₁, hA₂, hA₃⟩ := ContinuousMap.exists_homotopy_id_of_deformation H hH₀
    (fun t a ha ↦ (hHS t a ha).symm ▸ ha) hHO hH₁
  obtain ⟨ρZ, HZ, hZ₁, hZ₂, hZ₃⟩ := hf.exists_homotopy_id_attach hX hfX hcover H hHS
    (mapsTo_range_map_of_hom f) hH₀ hHO hH₁
  -- The homotopies are read as homotopies of morphisms of `TopCat`: the identity morphism has
  -- underlying map `ContinuousMap.id`, and `TopCat.ofHom ρ` has underlying map `ρ`, definitionally.
  have := isIso_singularHomologyMap_ofSubsetMap_id_of_homotopy (ρ := TopCat.ofHom ρA) hSO' HA
    hA₁ hA₂ hA₃ R n
  have := isIso_singularHomologyMap_ofSubsetMap_id_of_homotopy (ρ := TopCat.ofHom ρZ) hXN HZ
    hZ₁ hZ₂ hZ₃ R n
  have := isIso_singularHomologyMap_ofSubsetMap_union_image R n g hX hf hO
    (fun a ha ↦ hSO (hfX a ha)) hcover hφO
  have : IsIso (TopPair.singularHomologyMap (isoOfSubsetRange P).hom R n) := by
    rw [← singularHomologyMapIso_hom]
    infer_instance
  have : IsIso (TopPair.singularHomologyMap f R n ≫
      TopPair.singularHomologyMap (ofSubsetMap (𝟙 Z) hXN) R n) := by
    rw [← singularHomologyMap_comp, comp_ofSubsetMap_id_eq f hXN hSO' hφO,
      singularHomologyMap_comp, singularHomologyMap_comp]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (TopPair.singularHomologyMap (ofSubsetMap (𝟙 Z) hXN) R n)

end TopPair

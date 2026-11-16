/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Excision
public import TauCeti.AlgebraicTopology.Singular.Homotopy.Invariance
public import TauCeti.Topology.Homotopy.Attach

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
(`TauCeti.isOpen_union_image_of_isClosedEmbedding`). The deformation `H` shows that
`(A, S) ⟶ (A, O)` induces isomorphisms, and its extension by the identity of `X`
(`TauCeti.attachHomotopy`) that `(Z, X) ⟶ (Z, N)` does
(`TopPair.isIso_singularHomologyMap_ofSubsetMap_id_of_homotopy`). Finally the complement of `X`
lies in the image of `φ`, so excision for the open cover of `Z` by `N` and the complement of `X`
(`TopPair.isIso_singularHomologyMap_of_open_cover`) makes `(A, O) ⟶ (Z, N)` an isomorphism.

## Main results

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

variable {P : TopPair.{w}} {Z : TopCat.{w}} {X : Set Z} {O : Set P.fst}

/-- The subspace of a pair is the range of its embedding, so a map of pairs `f : P ⟶ (Z, X)` sends
it into `X`. -/
theorem mapsTo_range_map_of_hom (f : P ⟶ ofSubset X) :
    MapsTo (Hom.fst f) (range P.map) X := by
  rintro _ ⟨s, rfl⟩
  rw [← Hom.w_apply f s]
  exact (Hom.snd f s).2

/-- A pair is isomorphic to the pair of its ambient space and the range of its embedding, by the
identity of the ambient space. -/
theorem isIso_ofHom_id_rangeFactorization (P : TopPair.{w}) :
    IsIso (TopPair.ofHom (Y := ofSubset (range P.map)) (𝟙 P.fst)
      (TopCat.ofHom ⟨rangeFactorization P.map, P.map.hom.continuous.rangeFactorization⟩)) :=
  have : IsIso (Hom.fst (TopPair.ofHom (Y := ofSubset (range P.map)) (𝟙 P.fst)
      (TopCat.ofHom ⟨rangeFactorization P.map, P.map.hom.continuous.rangeFactorization⟩))) :=
    inferInstanceAs (IsIso (𝟙 P.fst))
  isIso_of_isIso_fst_of_surjective_snd _ rangeFactorization_surjective

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
    IsIso (TopPair.singularHomologyMap (ofSubsetMap φ hφO) R n) := by
  refine isIso_singularHomologyMap_of_open_cover R (ofSubsetMap φ hφO)
    (by rw [ofSubsetMap_fst]; exact hφ.isEmbedding) ?_
    (fun b : Bool ↦ bif b then X ∪ φ '' O else Xᶜ) ?_ ?_ ?_ n
  · intro a ha
    rw [range_ofSubset_map, ofSubsetMap_fst] at ha
    rw [range_ofSubset_map]
    obtain hX' | ⟨b, hb, hba⟩ := ha
    exacts [hφX a hX', hφ.injective hba ▸ hb]
  · rintro (_ | _)
    exacts [hX.isOpen_compl, isOpen_union_image_of_isClosedEmbedding hφ hO hφX hcover]
  · exact eq_univ_of_forall fun z ↦ mem_iUnion.2 <| by
      by_cases hz : z ∈ X
      · exact ⟨true, Or.inl hz⟩
      · exact ⟨false, hz⟩
  · rintro (_ | _)
    · rw [ofSubsetMap_fst]
      exact Or.inr fun z hz ↦ (hcover.symm ▸ mem_univ z : z ∈ X ∪ _).resolve_left hz
    · exact Or.inl (range_ofSubset_map (X := Z) (B := X ∪ φ '' O)).ge

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
  have hφS : MapsTo g (range P.map) X := mapsTo_range_map_of_hom f
  -- First replace `P` by the pair of `A` and the range of its embedding.
  set e := TopPair.ofHom (Y := ofSubset (range P.map)) (𝟙 P.fst)
    (TopCat.ofHom ⟨rangeFactorization P.map, P.map.hom.continuous.rangeFactorization⟩)
  have : IsIso e := isIso_ofHom_id_rangeFactorization P
  have hfe : f = e ≫ ofSubsetMap g hφS :=
    hom_ext_of_fst _ (by rw [Hom.fst_comp, ofSubsetMap_fst]; exact (Category.id_comp g).symm)
  -- The deformation of `A` and its extension to `Z` enlarge both subspaces.
  have hSO' : MapsTo (𝟙 P.fst) (range P.map) O := hSO
  have hXN : MapsTo (𝟙 Z) X (X ∪ g '' O) := fun _ hz ↦ Or.inl hz
  let G := attachHomotopy hf hX hfX hcover H hHS
  have hA : IsIso (TopPair.singularHomologyMap (ofSubsetMap (𝟙 P.fst) hSO') R n) :=
    isIso_singularHomologyMap_ofSubsetMap_id_of_homotopy hSO'
      (ρ := TopCat.ofHom (H.curry 1))
      { toContinuousMap := H, map_zero_left := hH₀, map_one_left _ := rfl }
      (fun t a ha ↦ (hHS t a ha).symm ▸ ha) hHO (fun a ha ↦ hH₁ a ha) R n
  have hZ : IsIso (TopPair.singularHomologyMap (ofSubsetMap (𝟙 Z) hXN) R n) :=
    isIso_singularHomologyMap_ofSubsetMap_id_of_homotopy hXN (ρ := TopCat.ofHom (G.curry 1))
      { toContinuousMap := G
        map_zero_left := attachHomotopy_zero hf hX hfX hcover H hHS hH₀
        map_one_left _ := rfl }
      (fun t _ hz ↦ (attachHomotopy_apply_of_mem hf hX hfX hcover H hHS t hz).symm ▸ hz)
      (fun t _ hz ↦ attachHomotopy_mem_union_image hf hX hfX hcover H hHS hHO t hz)
      (fun _ hz ↦ attachHomotopy_one_mem hf hX hfX hcover H hHS hφS hH₁ hz) R n
  -- Excision for the open cover of `Z` by the thickening and the complement of `X`.
  have hφO : MapsTo g O (X ∪ g '' O) := fun a ha ↦ Or.inr ⟨a, ha, rfl⟩
  have hexc := isIso_singularHomologyMap_ofSubsetMap_union_image R n g hX hf hO
    (fun a ha ↦ hSO (hfX a ha)) hcover hφO
  -- The comparison square: both composites are `φ` on the ambient spaces.
  have hsq : ofSubsetMap g hφS ≫ ofSubsetMap (𝟙 Z) hXN =
      ofSubsetMap (𝟙 P.fst) hSO' ≫ ofSubsetMap g hφO :=
    hom_ext_of_fst _ (by
      rw [Hom.fst_comp, Hom.fst_comp, ofSubsetMap_fst, ofSubsetMap_fst, ofSubsetMap_fst,
        ofSubsetMap_fst]
      exact (Category.comp_id g).trans (Category.id_comp g).symm)
  have : IsIso (TopPair.singularHomologyMap (ofSubsetMap g hφS) R n ≫
      TopPair.singularHomologyMap (ofSubsetMap (𝟙 Z) hXN) R n) := by
    rw [← singularHomologyMap_comp, hsq, singularHomologyMap_comp]
    infer_instance
  have := IsIso.of_isIso_comp_right (TopPair.singularHomologyMap (ofSubsetMap g hφS) R n)
    (TopPair.singularHomologyMap (ofSubsetMap (𝟙 Z) hXN) R n)
  rw [hfe, singularHomologyMap_comp]
  have : IsIso (TopPair.singularHomologyMap e R n) :=
    inferInstanceAs (IsIso (TopPair.singularHomologyMapIso R (asIso e) n).hom)
  infer_instance

end TopPair

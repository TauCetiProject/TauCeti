/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Excision
public import TauCeti.AlgebraicTopology.Cohomology.HomotopyInvariance
public import TauCeti.AlgebraicTopology.Singular.Attach

/-!
# Relative cohomology of an attachment

Let `Z` be obtained from a closed subset `X` by attaching `A` along `S` through a map of pairs
`f : (A, S) ⟶ (Z, X)`, where `S` has an open neighbourhood `O` in `A` which a deformation of `A`
fixing `S` pushes into `S`. Then `f` induces isomorphisms `Hⁿ(Z, X) ≅ Hⁿ(A, S)` on relative
singular cohomology, with arbitrary coefficients, in every degree
(`TopPair.isIso_singularCohomologyMap_of_attach`). This is the cohomology form of
`TopPair.isIso_singularHomologyMap_of_attach`, proved in the same way: the subspaces are thickened
to the open neighbourhoods `O` of `S` and `X ∪ φ(O)` of `X`, which the deformation and its
extension (`TauCeti.attachHomotopy`) push back into the subspaces, and excision compares the
thickened pairs.

## Main results

* `TopPair.isIso_singularCohomologyMap_ofSubsetMap_union_image`: excision of the complement of the
  attached space from the thickened pair `(Z, X ∪ φ(O))`.
* `TopPair.isIso_singularCohomologyMap_of_attach`: attaching along a subspace with a deformation
  neighbourhood induces isomorphisms on relative singular cohomology.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 2.1,
  Proposition 2.22 and its proof (good pairs and excision).
-/

public section

noncomputable section

open CategoryTheory Limits Set Topology TauCeti
open ContinuousMap.Homotopy (ofApplyZero)
open scoped unitInterval

universe w v u

namespace TopPair

variable {P : TopPair.{w}} {Z : TopCat.{w}} {X : Set Z} {O : Set P.fst}
  {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C)
  (k : Type*) [Ring k] [Linear k C] (M : C) (n : ℕ)

/-- **Excision for the thickening of an attachment, in cohomology.** Under the hypotheses of
`TopPair.isIso_singularHomologyMap_ofSubsetMap_union_image`, the map of pairs
`(A, O) ⟶ (Z, X ∪ φ(O))` induced by `φ` induces isomorphisms on relative singular cohomology. -/
theorem isIso_singularCohomologyMap_ofSubsetMap_union_image {A : TopCat.{w}} {O : Set A}
    (φ : A ⟶ Z) (hX : IsClosed X) (hφ : IsClosedEmbedding φ) (hO : IsOpen O)
    (hφX : ∀ a, φ a ∈ X → a ∈ O) (hcover : X ∪ range φ = univ)
    (hφO : MapsTo φ O (X ∪ φ '' O)) :
    IsIso (TopPair.singularCohomologyMap (R := R) (k := k) (M := M) (ofSubsetMap φ hφO) n) :=
  isIso_singularCohomologyMap_of_open_cover (ofSubsetMap φ hφO)
    (by rw [ofSubsetMap_fst]; exact hφ.isEmbedding)
    (mem_range_map_of_fst_ofSubsetMap_union_image_mem φ hφ.injective hφX hφO) _
    (isOpen_cond_union_image_compl φ hX hφ hO hφX hcover) (iUnion_cond_union_image_compl φ)
    (cond_union_image_compl_subset_range_or_subset_range_fst φ hcover hφO) n

/-- **Attaching along a subspace with a deformation neighbourhood induces isomorphisms on relative
cohomology.** Under the hypotheses of `TopPair.isIso_singularHomologyMap_of_attach`, the map of
pairs `f : (A, S) ⟶ (Z, X)` induces isomorphisms `Hⁿ(Z, X) ≅ Hⁿ(A, S)` on relative singular
cohomology, with arbitrary coefficients, in every degree. -/
theorem isIso_singularCohomologyMap_of_attach (f : P ⟶ ofSubset X) (hX : IsClosed X)
    (hf : IsClosedEmbedding (Hom.fst f)) (hfX : ∀ a, Hom.fst f a ∈ X → a ∈ range P.map)
    (hcover : X ∪ range (Hom.fst f) = univ) (hO : IsOpen O) (hSO : range P.map ⊆ O)
    (H : C(I × P.fst, P.fst)) (hH₀ : ∀ a, H (0, a) = a)
    (hHS : ∀ t, ∀ a ∈ range P.map, H (t, a) = a) (hHO : ∀ t, ∀ a ∈ O, H (t, a) ∈ O)
    (hH₁ : ∀ a ∈ O, H (1, a) ∈ range P.map) :
    IsIso (TopPair.singularCohomologyMap (R := R) (k := k) (M := M) f n) := by
  -- The map `φ` with its codomain read as `Z` rather than as the ambient space of `(Z, X)`.
  let g : P.fst ⟶ Z := Hom.fst f
  have hφS : MapsTo g (range P.map) X := mapsTo_range_map_of_hom f
  -- The deformation of `A` and its extension to `Z` enlarge both subspaces.
  have hSO' : MapsTo (𝟙 P.fst) (range P.map) O :=
    ConcreteCategory.coe_id (X := P.fst) ▸ (mapsTo_id _).mono_right hSO
  have hXN : MapsTo (𝟙 Z) X (X ∪ g '' O) := fun _ hz ↦ Or.inl hz
  let G := attachHomotopy hf hX hfX hcover H hHS
  have hA : IsIso (TopPair.singularCohomologyMap (R := R) (k := k) (M := M)
      (ofSubsetMap (𝟙 P.fst) hSO') n) :=
    isIso_singularCohomologyMap_ofSubsetMap_id_of_homotopy hSO'
      (ρ := TopCat.ofHom (H.curry 1))
      (ofApplyZero H hH₀)
      (fun t a ha ↦ (hHS t a ha).symm ▸ ha) hHO (fun a ha ↦ hH₁ a ha) R k M n
  have hZ : IsIso (TopPair.singularCohomologyMap (R := R) (k := k) (M := M)
      (ofSubsetMap (𝟙 Z) hXN) n) :=
    isIso_singularCohomologyMap_ofSubsetMap_id_of_homotopy hXN (ρ := TopCat.ofHom (G.curry 1))
      (ofApplyZero G (attachHomotopy_zero hf hX hfX hcover H hHS hH₀))
      (fun t _ hz ↦ (attachHomotopy_apply_of_mem hf hX hfX hcover H hHS t hz).symm ▸ hz)
      (fun t _ hz ↦ attachHomotopy_mem_union_image hf hX hfX hcover H hHS hHO t hz)
      (fun _ hz ↦ attachHomotopy_one_mem hf hX hfX hcover H hHS hφS hH₁ hz) R k M n
  -- Excision for the open cover of `Z` by the thickening and the complement of `X`.
  have hφO : MapsTo g O (X ∪ g '' O) := fun a ha ↦ Or.inr ⟨a, ha, rfl⟩
  have hexc := isIso_singularCohomologyMap_ofSubsetMap_union_image R k M n g hX hf hO
    (fun a ha ↦ hSO (hfX a ha)) hcover hφO
  -- The comparison square: both composites are `φ` on the ambient spaces.
  have hsq : ofSubsetMap g hφS ≫ ofSubsetMap (𝟙 Z) hXN =
      ofSubsetMap (𝟙 P.fst) hSO' ≫ ofSubsetMap g hφO :=
    ofSubsetMap_comp_ofSubsetMap_eq _ _ _ _ ((Category.comp_id g).trans (Category.id_comp g).symm)
  have : IsIso (TopPair.singularCohomologyMap (R := R) (k := k) (M := M)
      (ofSubsetMap (𝟙 Z) hXN) n ≫ TopPair.singularCohomologyMap (ofSubsetMap g hφS) n) := by
    rw [← singularCohomologyMap_comp, hsq, singularCohomologyMap_comp]
    infer_instance
  have := IsIso.of_isIso_comp_left
    (TopPair.singularCohomologyMap (R := R) (k := k) (M := M) (ofSubsetMap (𝟙 Z) hXN) n)
    (TopPair.singularCohomologyMap (ofSubsetMap g hφS) n)
  -- Finally `f` factors through the isomorphism of `P` with the pair of `A` and the range of its
  -- embedding.
  have hfe : f = (isoOfSubsetRange P).hom ≫ ofSubsetMap g hφS :=
    (isoOfSubsetRange_hom_comp_ofSubsetMap f).symm
  rw [hfe, singularCohomologyMap_comp]
  have : IsIso (TopPair.singularCohomologyMap (R := R) (k := k) (M := M)
      (isoOfSubsetRange P).hom n) := by
    rw [← Quiver.Hom.unop_op (isoOfSubsetRange P).hom, ← singularCohomologyFunctor_map]
    exact (singularCohomologyFunctor R k M n).map_isIso _
  infer_instance

end TopPair

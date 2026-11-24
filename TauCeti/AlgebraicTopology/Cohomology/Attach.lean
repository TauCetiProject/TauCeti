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
extension (`Topology.IsClosedEmbedding.attachDeformation`) push back into the subspaces, and
excision compares the thickened pairs.

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
  have := isIso_singularCohomologyMap_ofSubsetMap_id_of_homotopy (ρ := TopCat.ofHom ρA) hSO' HA
    hA₁ hA₂ hA₃ R k M n
  have := isIso_singularCohomologyMap_ofSubsetMap_id_of_homotopy (ρ := TopCat.ofHom ρZ) hXN HZ
    hZ₁ hZ₂ hZ₃ R k M n
  have := isIso_singularCohomologyMap_ofSubsetMap_union_image R k M n g hX hf hO
    (fun a ha ↦ hSO (hfX a ha)) hcover hφO
  have : IsIso (TopPair.singularCohomologyMap (R := R) (k := k) (M := M)
      (isoOfSubsetRange P).hom n) := by
    rw [← Quiver.Hom.unop_op (isoOfSubsetRange P).hom, ← singularCohomologyFunctor_map]
    exact (singularCohomologyFunctor R k M n).map_isIso _
  have : IsIso (TopPair.singularCohomologyMap (R := R) (k := k) (M := M)
      (ofSubsetMap (𝟙 Z) hXN) n ≫ TopPair.singularCohomologyMap f n) := by
    rw [← singularCohomologyMap_comp, comp_ofSubsetMap_id_eq f hXN hSO' hφO,
      singularCohomologyMap_comp, singularCohomologyMap_comp]
    infer_instance
  exact IsIso.of_isIso_comp_left
    (TopPair.singularCohomologyMap (R := R) (k := k) (M := M) (ofSubsetMap (𝟙 Z) hXN) n) _

end TopPair

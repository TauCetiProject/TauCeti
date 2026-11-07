/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.MayerVietoris.Basic
public import TauCeti.AlgebraicTopology.Cohomology.Relative
public import TauCeti.AlgebraicTopology.Singular.Excision

/-!
# Excision for relative singular cohomology

Let `(X, B)` be a topological pair and `A ⊆ X` a subset such that the interiors of `A` and `B`
cover `X`.  The inclusion of pairs `(A, A ∩ B) ⟶ (X, B)` induces an isomorphism
`Hⁿ(X, B; R, M) ⟶ Hⁿ(A, A ∩ B; R, M)` on relative singular cohomology in every degree, for
coefficients `R` and `M` in any linear abelian category with coproducts
(`TopPair.isIso_singularCohomologyMap_excisionMap`).  Equivalently, excising a set `Z` whose
closure lies in the interior of `B` does not change relative cohomology
(`TopPair.isIso_singularCohomologyMap_excisionMap_compl`).  In particular, for a closed set `K`
and an open neighbourhood `U` of `K`, restriction `Hⁿ(X, X ∖ K) ⟶ Hⁿ(U, U ∖ K)` is an
isomorphism (`TopPair.isIso_singularCohomologyMap_excisionMap_of_isClosed_subset`); this is the
form in which cohomology with supports in a compact subset of a Hausdorff space, and hence
Poincaré duality, is localised.

All of these follow from the general statement
`TopPair.quasiIso_singularCochainComplexMap_of_open_cover`: a map of topological pairs
`f : P ⟶ P'` which is an embedding on ambient spaces, whose subspace is the full preimage of the
subspace of `P'`, and such that the ambient space of `P'` has an open cover each of whose members
lies in the subspace of `P'` or in the image of `f`, induces a quasi-isomorphism of relative
singular cochain complexes.

The proof dualizes the one for homology in `TauCeti.AlgebraicTopology.Singular.Excision`, but
works with chain homotopy equivalences rather than quasi-isomorphisms, since `Hom(-, M)` need not
preserve quasi-isomorphisms.  The inclusion of the chains subordinate to an open cover is a chain
homotopy equivalence (`TauCeti.smallSingularChainHomotopyEquiv`), so restricting cochains to them
is a quasi-isomorphism (`TauCeti.quasiIso_cochainComplexMap_smallSingularSubcomplex_ι`), and this
passes to restricted pairs
(`TopPair.quasiIso_cochainComplexMap_restrictι_smallSingularSubcomplex`) by the five lemma for the
long exact sequences of the pairs.  On the restricted pairs the map induced by `f` bijects the
complementary simplices (`TopPair.relativeSimplex_restrictMap_bijective`), so it is an
isomorphism of relative chain complexes, and hence of relative cochain complexes
(`SSetPair.isIso_cochainComplexMap_of_relativeSimplex_equiv`).

Naturality of the excision isomorphisms in the excision data follows by applying
`TopPair.singularCohomologyMap` to `TopPair.interPairMap_comp_excisionMap`, and compatibility with
the connecting morphism of the pair is `TopPair.singularCohomologyδ_naturality` applied to the
excision map.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.1, excision in cohomology, and Section 2.1, Theorem 2.20 and Proposition 2.21.
* S. Eilenberg and N. Steenrod, *Foundations of Algebraic Topology*, Chapter VII.
-/

public section

noncomputable section

open CategoryTheory Limits Topology

universe w v u

namespace TopPair

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] {R : C}
  {k : Type*} [Ring k] [Linear k C] {M : C}

section Excision

variable {ι : Type*}

/-- **The relative small-chain theorem for cochains.** Restricting relative singular cochains of
a topological pair to the simplices subordinate to an open cover of the ambient space is a
quasi-isomorphism. -/
theorem quasiIso_cochainComplexMap_restrictι_smallSingularSubcomplex (P : TopPair.{w})
    (U : ι → Set P.fst) (hU : ∀ i, IsOpen (U i)) (hcov : ⋃ i, U i = Set.univ) :
    QuasiIso (SSetPair.cochainComplexMap (R := R) (k := k) (M := M)
      ((toSSetPair.obj P).restrictι (P.smallSingularSubcomplex U))) := by
  refine SSetPair.quasiIso_cochainComplexMap_restrictι _ ?_ ?_
  · rw [P.smallSingularSubcomplex_preimage_hom U]
    exact TauCeti.quasiIso_cochainComplexMap_smallSingularSubcomplex_ι R k M
      (fun i ↦ P.map ⁻¹' U i) (fun i ↦ (hU i).preimage P.map.hom.continuous)
      (by rw [← Set.preimage_iUnion, hcov, Set.preimage_univ])
  · rw [P.smallSingularSubcomplex_eq U]
    exact TauCeti.quasiIso_cochainComplexMap_smallSingularSubcomplex_ι R k M U hU hcov

variable {P P' : TopPair.{w}} (f : P ⟶ P') (hf : IsEmbedding (Hom.fst f))
  (hsnd : ∀ x, Hom.fst f x ∈ Set.range P'.map → x ∈ Set.range P.map)
  (U : ι → Set P'.fst) (hU : ∀ i, IsOpen (U i)) (hcov : ⋃ i, U i = Set.univ)
  (hUf : ∀ i, U i ⊆ Set.range P'.map ∨ U i ⊆ Set.range (Hom.fst f))

include hf hsnd hU hcov hUf in
/-- **Excision for relative singular cochains.** Let `f : P ⟶ P'` be a map of topological pairs
which is an embedding on ambient spaces and whose subspace is the full preimage of the subspace of
`P'`.  If the ambient space of `P'` has an open cover each of whose members lies in the subspace of
`P'` or in the image of `f`, then `f` induces a quasi-isomorphism of relative singular cochain
complexes. -/
theorem quasiIso_singularCochainComplexMap_of_open_cover :
    QuasiIso (singularCochainComplexMap (R := R) (k := k) (M := M) f) := by
  have h₁ := P'.quasiIso_cochainComplexMap_restrictι_smallSingularSubcomplex
    (R := R) (k := k) (M := M) U hU hcov
  have h₂ := P.quasiIso_cochainComplexMap_restrictι_smallSingularSubcomplex
    (R := R) (k := k) (M := M) (fun i ↦ Hom.fst f ⁻¹' U i)
    (fun i ↦ (hU i).preimage (Hom.fst f).hom.continuous)
    (by rw [← Set.preimage_iUnion, hcov, Set.preimage_univ])
  have := SSetPair.isIso_cochainComplexMap_of_relativeSimplex_equiv (R := R) (k := k) (M := M)
    (SSetPair.restrictMap (toSSetPair.map f) (smallSingularSubcomplex_le_preimage f U))
    (fun m ↦ Equiv.ofBijective _ (relativeSimplex_restrictMap_bijective f hf hsnd U hUf m))
    (fun _ _ ↦ rfl)
  -- Restricting along `f` and then to small simplices is restricting to small simplices and
  -- then along the restriction of `f`, and the last three of these maps are quasi-isomorphisms.
  have hsq := congrArg (SSetPair.cochainComplexMap (R := R) (k := k) (M := M))
    (SSetPair.restrictMap_comp_restrictι (toSSetPair.map f)
      (smallSingularSubcomplex_le_preimage f U))
  rw [SSetPair.cochainComplexMap_comp, SSetPair.cochainComplexMap_comp] at hsq
  have : QuasiIso (singularCochainComplexMap (R := R) (k := k) (M := M) f ≫
      SSetPair.cochainComplexMap ((toSSetPair.obj P).restrictι
        (P.smallSingularSubcomplex (fun i ↦ Hom.fst f ⁻¹' U i)))) := by
    rw [singularCochainComplexMap_eq, ← hsq]
    infer_instance
  exact quasiIso_of_comp_right _ (SSetPair.cochainComplexMap ((toSSetPair.obj P).restrictι
    (P.smallSingularSubcomplex (fun i ↦ Hom.fst f ⁻¹' U i))))

include hf hsnd hU hcov hUf in
/-- **Excision for relative singular cohomology.** Under the hypotheses of
`TopPair.quasiIso_singularCochainComplexMap_of_open_cover`, the map of pairs `f` induces
isomorphisms on relative singular cohomology. -/
theorem isIso_singularCohomologyMap_of_open_cover (n : ℕ) :
    IsIso (TopPair.singularCohomologyMap (R := R) (k := k) (M := M) f n) := by
  have := quasiIso_singularCochainComplexMap_of_open_cover (R := R) (k := k) (M := M) f hf hsnd U
    hU hcov hUf
  infer_instance

end Excision

section Subsets

variable {X : TopCat.{w}} (A B : Set X)

variable (R k M) in
/-- **Excision.** If the interiors of `A` and `B` cover `X`, the inclusion of pairs
`(A, A ∩ B) ⟶ (X, B)` induces isomorphisms `Hⁿ(X, B) ⟶ Hⁿ(A, A ∩ B)` on relative singular
cohomology. -/
theorem isIso_singularCohomologyMap_excisionMap (h : interior A ∪ interior B = Set.univ)
    (n : ℕ) :
    IsIso (TopPair.singularCohomologyMap (R := R) (k := k) (M := M) (excisionMap A B) n) := by
  refine isIso_singularCohomologyMap_of_open_cover (excisionMap A B)
    (isEmbedding_fst_excisionMap A B) (mem_range_map_of_fst_excisionMap_mem A B)
    (fun b : Bool ↦ bif b then interior A else interior B)
    (fun b ↦ by cases b <;> exact isOpen_interior) ?_
    (interior_subset_range_or_subset_range_fst_excisionMap A B) n
  rw [← Set.union_eq_iUnion]
  exact h

variable (R k M) in
/-- **Excision of a set with closure in the interior of the subspace.** If
`closure Z ⊆ interior B`, the inclusion of pairs `(X ∖ Z, B ∖ Z) ⟶ (X, B)` induces isomorphisms
`Hⁿ(X, B) ⟶ Hⁿ(X ∖ Z, B ∖ Z)` on relative singular cohomology. -/
theorem isIso_singularCohomologyMap_excisionMap_compl (Z : Set X) (h : closure Z ⊆ interior B)
    (n : ℕ) :
    IsIso (TopPair.singularCohomologyMap (R := R) (k := k) (M := M) (excisionMap Zᶜ B) n) := by
  refine isIso_singularCohomologyMap_excisionMap R k M Zᶜ B ?_ n
  rw [interior_compl, Set.eq_univ_iff_forall]
  intro x
  by_cases hx : x ∈ closure Z
  · exact Or.inr (h hx)
  · exact Or.inl hx

variable (R k M) in
/-- **Excision onto a neighbourhood.** If `U` is open and contains the closed set `K`, the
inclusion of pairs `(U, U ∖ K) ⟶ (X, X ∖ K)` induces isomorphisms
`Hⁿ(X, X ∖ K) ⟶ Hⁿ(U, U ∖ K)` on relative singular cohomology. -/
theorem isIso_singularCohomologyMap_excisionMap_of_isClosed_subset {U K : Set X} (hU : IsOpen U)
    (hK : IsClosed K) (hKU : K ⊆ U) (n : ℕ) :
    IsIso (TopPair.singularCohomologyMap (R := R) (k := k) (M := M) (excisionMap U Kᶜ) n) := by
  refine isIso_singularCohomologyMap_excisionMap R k M U Kᶜ ?_ n
  rw [hU.interior_eq, hK.isOpen_compl.interior_eq]
  exact Set.eq_univ_of_subset (Set.union_subset_union_left _ hKU) (Set.union_compl_self K)

variable (R k M) in
/-- **Excision is compatible with shrinking the excised set.** Let `U` be open and let
`L₂ ⊆ L₁ ⊆ U` be closed. The restriction `Hⁿ(U, U ∖ L₂) ⟶ Hⁿ(U, U ∖ L₁)` is an isomorphism
exactly when `Hⁿ(X, X ∖ L₂) ⟶ Hⁿ(X, X ∖ L₁)` is, since both pairs in `U` are identified with the
corresponding pairs in `X` by excision. -/
theorem isIso_singularCohomologyMap_ofSubsetMap_compl_iff {U L₁ L₂ : Set X} (hU : IsOpen U)
    (hL₁ : IsClosed L₁) (hL₂ : IsClosed L₂) (hL₁U : L₁ ⊆ U) (h : L₂ ⊆ L₁) (n : ℕ) :
    IsIso (TopPair.singularCohomologyMap (R := R) (k := k) (M := M)
        (ofSubsetMap (𝟙 (TopCat.of U)) (B := Subtype.val ⁻¹' L₁ᶜ) (B' := Subtype.val ⁻¹' L₂ᶜ)
          fun _ hz ↦ Set.compl_subset_compl.2 h hz) n) ↔
      IsIso (TopPair.singularCohomologyMap (R := R) (k := k) (M := M)
        (ofSubsetMap (𝟙 X) (Set.compl_subset_compl.2 h)) n) := by
  have := isIso_singularCohomologyMap_excisionMap_of_isClosed_subset R k M hU hL₁ hL₁U n
  have := isIso_singularCohomologyMap_excisionMap_of_isClosed_subset R k M hU hL₂
    (h.trans hL₁U) n
  have hw := congrArg (TopPair.singularCohomologyMap (R := R) (k := k) (M := M) · n)
    (interPairMap_comp_excisionMap (𝟙 X) (Set.mapsTo_id U) (Set.compl_subset_compl.2 h))
  simp only [TopPair.singularCohomologyMap_comp] at hw
  rw [ofSubsetMap_id_eq_interPairMap]
  exact ⟨fun _ ↦ IsIso.of_isIso_fac_right hw.symm, fun _ ↦ IsIso.of_isIso_fac_left hw⟩

end Subsets

end TopPair

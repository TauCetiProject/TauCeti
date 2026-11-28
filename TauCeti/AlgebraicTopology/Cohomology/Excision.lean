/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.MayerVietoris.Basic
public import TauCeti.AlgebraicTopology.Cohomology.Relative
public import TauCeti.AlgebraicTopology.Singular.Excision
import TauCeti.Topology.Closure

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
Poincaré duality, is localised. For a continuous real function `f` and `a' ≤ b` with `a < a'` or
`a' = b`, excising `{f < a}` gives isomorphisms for the collar inclusion
`TauCeti.bandCollarPairInclusion f a ha'b : (f⁻¹[a, b], f⁻¹[a, a']) ⟶ ({f ≤ b}, {f ≤ a'})`
(`TopPair.isIso_singularCohomologyMap_bandCollarPairInclusion`).

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
  exact isIso_singularCohomologyMap_of_open_cover (excisionMap A B)
    (isEmbedding_fst_excisionMap A B) (mem_range_map_of_fst_excisionMap_mem A B)
    (fun b : Bool ↦ bif b then interior A else interior B)
    (fun b ↦ by cases b <;> exact isOpen_interior) (Set.union_eq_iUnion.symm.trans h)
    (interior_subset_range_or_subset_range_fst_excisionMap A B) n

variable (R k M) in
/-- **Excision of a set with closure in the interior of the subspace.** If
`closure Z ⊆ interior B`, the inclusion of pairs `(X ∖ Z, B ∖ Z) ⟶ (X, B)` induces isomorphisms
`Hⁿ(X, B) ⟶ Hⁿ(X ∖ Z, B ∖ Z)` on relative singular cohomology. -/
theorem isIso_singularCohomologyMap_excisionMap_compl (Z : Set X) (h : closure Z ⊆ interior B)
    (n : ℕ) :
    IsIso (TopPair.singularCohomologyMap (R := R) (k := k) (M := M) (excisionMap Zᶜ B) n) := by
  exact isIso_singularCohomologyMap_excisionMap R k M Zᶜ B
    (TauCeti.interior_compl_union_interior_eq_univ_iff.2 h) n

variable (R k M) in
/-- **Excision onto a neighbourhood.** If `U` is open and contains the closed set `K`, the
inclusion of pairs `(U, U ∖ K) ⟶ (X, X ∖ K)` induces isomorphisms
`Hⁿ(X, X ∖ K) ⟶ Hⁿ(U, U ∖ K)` on relative singular cohomology. -/
theorem isIso_singularCohomologyMap_excisionMap_of_isClosed_subset {U K : Set X} (hU : IsOpen U)
    (hK : IsClosed K) (hKU : K ⊆ U) (n : ℕ) :
    IsIso (TopPair.singularCohomologyMap (R := R) (k := k) (M := M) (excisionMap U Kᶜ) n) := by
  exact isIso_singularCohomologyMap_excisionMap R k M U Kᶜ
    (TauCeti.interior_union_interior_compl_eq_univ hU hK hKU) n

/-- **Excision onto a neighbourhood is injective.** If `U` is open and contains the closed set
`K`, a class of `Hⁿ(X, X ∖ K)` is determined by its restriction to `(U, U ∖ K)`. -/
theorem injective_singularCohomologyMap_excisionMap_of_isClosed_subset {U K : Set X}
    (hU : IsOpen U) (hK : IsClosed K) (hKU : K ⊆ U) (n : ℕ) :
    Function.Injective
      (TopPair.singularCohomologyMap (R := R) (k := k) (M := M) (excisionMap U Kᶜ) n) := by
  have := isIso_singularCohomologyMap_excisionMap_of_isClosed_subset R k M hU hK hKU n
  exact ConcreteCategory.injective_of_mono_of_preservesPullback _

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

section BandCollar

variable (R k M) in
/-- **Collar excision for continuous real functions, in cohomology.** For a continuous function
`f : X → ℝ` and `a' ≤ b` with `a < a'` or `a' = b`, excising `{f < a}` from `({f ≤ b}, {f ≤ a'})`
shows that
`TauCeti.bandCollarPairInclusion f a ha'b : (f⁻¹[a, b], f⁻¹[a, a']) ⟶ ({f ≤ b}, {f ≤ a'})`
induces isomorphisms on relative singular cohomology in every degree. -/
theorem isIso_singularCohomologyMap_bandCollarPairInclusion {X : Type w} [TopologicalSpace X]
    {f : X → ℝ} (hf : Continuous f) {a a' b : ℝ} (ha'b : a' ≤ b) (hlt : a < a' ∨ a' = b)
    (n : ℕ) :
    IsIso (TopPair.singularCohomologyMap (R := R) (k := k) (M := M)
      (TauCeti.bandCollarPairInclusion f a ha'b) n) := by
  obtain ⟨h₁, h₂, U, h₃, h₄, h₅⟩ :=
    TauCeti.exists_open_cover_bandCollarPairInclusion hf ha'b hlt
  exact isIso_singularCohomologyMap_of_open_cover (R := R) (k := k) (M := M) _ h₁ h₂ U h₃ h₄ h₅ n

end BandCollar

/-- If `A ⊆ B''`, the inclusion `(A, A ∩ B) ⟶ (X, B')` followed by the restriction
`(X, B') ⟶ (X, B'')` factors through the subspace `B''`, so it induces zero on relative
cohomology. -/
lemma singularCohomologyMap_interPairMapOfSubset_comp_eq_zero {X : TopCat.{w}}
    {A B B' B'' : Set X} (h : A ∩ B ⊆ B') (hB : Set.MapsTo (𝟙 X) B' B'') (hA : A ⊆ B'') (n : ℕ) :
    TopPair.singularCohomologyMap (R := R) (k := k) (M := M)
      (interPairMapOfSubset h ≫ ofSubsetMap (𝟙 X) hB) n = 0 :=
  singularCohomologyMap_eq_zero_of_fac R k M _
    (TopCat.ofHom ⟨fun x : A ↦ (⟨x.val, Set.mem_of_subset_of_mem hA x.property⟩ : B''),
      by fun_prop⟩)
    -- Both sides are `Subtype.val : A → X`; the `rfl` unfolds the composite of `TopCat.ofHom`s.
    (by rw [interPairMapOfSubset_comp_ofSubsetMap_id, interPairMapOfSubset_fst, ofSubset_map]; rfl)
    n

end TopPair

namespace TopCat

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] {R : C}
  {k : Type*} [Ring k] [Linear k C] {M : C} {X : TopCat.{w}} {S T : Set X}

/-- Restricting a class of `Hⁿ(X, X ∖ S)` to `Hⁿ(X, X ∖ T)`, `S ⊆ T`, and then to a pair
`(A, A ∩ B)` with `A ∩ B ⊆ X ∖ T` is restricting it to `(A, A ∩ B)` directly. -/
@[simp]
lemma singularCohomologyMap_interPairMapOfSubset_singularCohomologyComplRestrict (hST : S ⊆ T)
    {A B : Set X} (h : A ∩ B ⊆ Tᶜ) {n : ℕ}
    (x : (TopPair.ofSubset Sᶜ).singularCohomology R k M n) :
    TopPair.singularCohomologyMap (TopPair.interPairMapOfSubset h) n
        (singularCohomologyComplRestrict R k M hST n x) =
      TopPair.singularCohomologyMap (TopPair.interPairMapOfSubset
        (h.trans (Set.compl_subset_compl.2 hST))) n x := by
  dsimp only [singularCohomologyComplRestrict]
  rw [← TopPair.singularCohomologyMap_comp_apply, TopPair.interPairMapOfSubset_comp_ofSubsetMap_id]

/-- Restricting a class of `Hⁿ(X, X ∖ S)` to `Hⁿ(X, X ∖ T)`, `S ⊆ T`, and then along the excision
map `(A, A ∖ T) ⟶ (X, X ∖ T)` is restricting it to `(A, A ∖ T)` directly. This is the form of
`TopCat.singularCohomologyMap_interPairMapOfSubset_singularCohomologyComplRestrict` reached after
`TopPair.interPairMapOfSubset_eq_excisionMap` rewrites the inclusion. -/
@[simp]
lemma singularCohomologyMap_excisionMap_singularCohomologyComplRestrict (hST : S ⊆ T)
    {A : Set X} {n : ℕ} (x : (TopPair.ofSubset Sᶜ).singularCohomology R k M n) :
    TopPair.singularCohomologyMap (TopPair.excisionMap A Tᶜ) n
        (singularCohomologyComplRestrict R k M hST n x) =
      TopPair.singularCohomologyMap (TopPair.interPairMapOfSubset
        (Set.inter_subset_right.trans (Set.compl_subset_compl.2 hST))) n x := by
  dsimp only [singularCohomologyComplRestrict]
  rw [← TopPair.singularCohomologyMap_comp_apply, TopPair.excisionMap_comp_ofSubsetMap_id]

/-- If moreover `A ⊆ X ∖ S`, that restriction vanishes: the inclusion of `(A, A ∩ B)` into
`(X, X ∖ S)` factors through the subspace `X ∖ S`. -/
lemma singularCohomologyMap_interPairMapOfSubset_singularCohomologyComplRestrict_eq_zero
    (hST : S ⊆ T) {A B : Set X} (h : A ∩ B ⊆ Tᶜ) (hA : A ⊆ Sᶜ) {n : ℕ}
    (x : (TopPair.ofSubset Sᶜ).singularCohomology R k M n) :
    TopPair.singularCohomologyMap (TopPair.interPairMapOfSubset h) n
        (singularCohomologyComplRestrict R k M hST n x) = 0 := by
  dsimp only [singularCohomologyComplRestrict]
  rw [← TopPair.singularCohomologyMap_comp_apply,
    TopPair.singularCohomologyMap_interPairMapOfSubset_comp_eq_zero h _ hA]
  simp only [ModuleCat.hom_zero, LinearMap.zero_apply]

end TopCat

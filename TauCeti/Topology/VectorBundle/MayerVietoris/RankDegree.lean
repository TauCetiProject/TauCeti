/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.FiniteUnionInduction
public import TauCeti.Topology.VectorBundle.MayerVietoris.DirectedUnion

/-!
# Isomorphisms onto the bottom homology of Thom pairs, glued over the base

Let `E → B` be a real vector bundle of rank `r` with Thom pair `(E, E₀)`. A computation of the
first nonvanishing homology group `Hᵣ(E, E₀)` in terms of the base, such as `H₀(B)` with
coefficients in a ring whose only unit is `1`, or `H₀(B)` with coefficients twisted by the
orientations of the fibres, has the same shape: a functor `A` on the subsets `W` of the base,
the group computed over `W`, and maps `ψ W : A(W) ⟶ Hᵣ(E|_W, E₀|_W)` commuting with the
restrictions. This file proves, once and for all, that such maps are isomorphisms over the whole
base as soon as they are over the subsets of the base sets of the chosen trivializations
`trivializationAt F E b`, following the argument of Milnor and Stasheff for the Thom isomorphism.

* **Finite unions** (`TauCeti.isIso_thomPairOver_biUnion_of_isIso`), by the Mayer–Vietoris
  induction `TauCeti.isIso_biUnion_of_subsetMayerVietoris`, below the rank: the homology over
  trivializing sets vanishes one degree lower, so the Mayer–Vietoris sequence of the Thom pairs
  over two open sets, one of them trivializing, ends in this degree.
* **The whole base** (`TauCeti.isIso_of_isColimit_biUnion_baseSet`). Singular homology has
  compact supports, so the homology of the Thom pair is the filtered colimit of the homology over
  the finite unions of the base sets of the chosen trivializations `trivializationAt F E b`. If
  `A(B)`, or any object, is the colimit of `A` over the same unions, the induced map is an
  isomorphism.

The base is arbitrary: neither compactness nor paracompactness is used.

## Main results

* `TauCeti.isIso_thomPairOver_biUnion_of_isIso`: finite unions of trivializing open sets.
* `TauCeti.isIso_of_isColimit_biUnion_baseSet`: the passage to the whole base.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10, Lemma 10.3 and the proof of Theorem 10.4.
* A. Hatcher, *Algebraic Topology*, Section 4.D, Theorem 4D.10 and its proof.
-/

public section

noncomputable section

open Bundle CategoryTheory Limits Set Module

universe w v u

namespace TauCeti

section Gluing

variable {B : Type w} [TopologicalSpace B] {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {E : B → Type w} [TopologicalSpace (TotalSpace F E)]
  [∀ b, AddCommMonoid (E b)] [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)]
  [FiberBundle F E] {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] {R : C}
  {A : Set B ⥤ C} {r : ℕ} {ψ : ∀ W, A.obj W ⟶ (thomPairOver F E W).singularHomology R r}

/-- **Finite unions of trivializing open sets.** Let `ψ W : A(W) ⟶ Hᵣ(E|_W, E₀|_W)`, with `r` at
most the rank, be maps commuting with the restrictions, for a functor `A` on the subsets of the
base such that `A(U) ⊞ A(V) ⟶ A(U ∪ V)` is an epimorphism for open `U` and `V` and `A(∅) = 0`. If
`ψ W` is an isomorphism whenever `W` lies in the base set of the chosen trivialization
`trivializationAt F E b` at some point `b`, it is one over every finite union of open sets each
lying in such a base set. -/
theorem isIso_thomPairOver_biUnion_of_isIso [VectorBundle ℝ F E] (hr : r ≤ finrank ℝ F)
    (hψ : ∀ {W W' : Set B} (h : W ⊆ W'), A.map (homOfLE h) ≫ ψ W' =
      ψ W ≫ TopPair.singularHomologyMap (thomPairOverMap F E h) R r)
    (hA : ∀ {U V : Set B}, IsOpen U → IsOpen V →
      Epi (biprod.desc (A.map (homOfLE (subset_union_left : U ⊆ U ∪ V)))
        (A.map (homOfLE (subset_union_right : V ⊆ U ∪ V)))))
    (hempty : IsZero (A.obj ∅))
    (htriv : ∀ (b : B) {W : Set B}, W ⊆ (trivializationAt F E b).baseSet → IsIso (ψ W))
    {ι : Type*} (s : Finset ι) {W : ι → Set B} (hWo : ∀ i ∈ s, IsOpen (W i))
    (hWe : ∀ i ∈ s, ∃ b, W i ⊆ (trivializationAt F E b).baseSet) :
    IsIso (ψ (⋃ i ∈ s, W i)) :=
  isIso_biUnion_of_subsetMayerVietoris
    (fun h ↦ TopPair.singularHomologyMap (thomPairOverMap F E h) R r)
    (fun h h' ↦ by rw [← TopPair.singularHomologyMap_comp, thomPairOverMap_comp_thomPairOverMap])
    hψ (P := fun W ↦ ∃ b, W ⊆ (trivializationAt F E b).baseSet) (fun h ⟨b, hb⟩ ↦ ⟨b, h.trans hb⟩)
    (fun _ ⟨b, hb⟩ ↦ htriv b hb)
    (isIso_of_source_target_iso_zero _ hempty.isoZero
      (isZero_singularHomology_thomPairOver_empty _ _).isoZero) hA
    (fun hU hV ⟨b, hb⟩ ↦ ⟨singularHomology_thomPairOver_mayerVietoris_exact R hU hV r,
      epi_singularHomology_thomPairOver_union R hU hV fun _ hm ↦
        (trivializationAt F E b).isZero_singularHomology_thomPairOver
          (inter_subset_left.trans hb) _ (by omega)⟩)
    s hWo hWe

/-- **The passage to the whole base.** Under the hypotheses of
`TauCeti.isIso_thomPairOver_biUnion_of_isIso`, let `c` be a colimit cocone over the values of `A`
on the finite unions of the base sets of the chosen trivializations `trivializationAt F E b`, and
`φ : c.pt ⟶ Hᵣ(E, E₀)` a map which, on the value over each finite union, is `ψ` followed by the
inclusion into the whole Thom pair. Then `φ` is an isomorphism. -/
theorem isIso_of_isColimit_biUnion_baseSet [VectorBundle ℝ F E]
    [HasFilteredColimitsOfSize.{w, w} C] [AB5OfSize.{w, w} C] (hr : r ≤ finrank ℝ F)
    (hψ : ∀ {W W' : Set B} (h : W ⊆ W'), A.map (homOfLE h) ≫ ψ W' =
      ψ W ≫ TopPair.singularHomologyMap (thomPairOverMap F E h) R r)
    (hA : ∀ {U V : Set B}, IsOpen U → IsOpen V →
      Epi (biprod.desc (A.map (homOfLE (subset_union_left : U ⊆ U ∪ V)))
        (A.map (homOfLE (subset_union_right : V ⊆ U ∪ V)))))
    (hempty : IsZero (A.obj ∅))
    (htriv : ∀ (b : B) {W : Set B}, W ⊆ (trivializationAt F E b).baseSet → IsIso (ψ W))
    {c : Cocone ((monotone_biUnion_baseSet_trivializationAt F E).functor ⋙ A)} (hc : IsColimit c)
    (φ : c.pt ⟶ (thomPair F E).singularHomology R r)
    (hφ : ∀ s, c.ι.app s ≫ φ = ψ (⋃ b ∈ s, (trivializationAt F E b).baseSet) ≫
      TopPair.singularHomologyMap (thomPairOverMap F E (subset_univ _) ≫
        (thomPairOverUnivIso F E).hom) R r) :
    IsIso φ := by
  have hfin (s : Finset B) : IsIso (ψ (⋃ b ∈ s, (trivializationAt F E b).baseSet)) :=
    isIso_thomPairOver_biUnion_of_isIso hr hψ hA hempty htriv s
      (fun b _ ↦ (trivializationAt F E b).open_baseSet)
      fun b _ ↦ ⟨b, subset_rfl⟩
  have hobj (s : Finset B) :
      (thomPairOver F E (⋃ b ∈ s, (trivializationAt F E b).baseSet)).singularHomology R
          r =
        (TopPair.singularHomologyFunctor R r).obj
          ((thomPairFiniteTrivializingUnionDiagram (F := F) (E := E)).obj s) := by
    rw [thomPairFiniteTrivializingUnionDiagram_obj, TopPair.singularHomologyFunctor_obj]
  have hpt : (thomPair F E).singularHomology R r =
      (TopPair.singularHomologyFunctor R r).obj
        (thomPairFiniteTrivializingUnionCocone (F := F) (E := E)).pt := by
    rw [thomPairFiniteTrivializingUnionCocone_pt, TopPair.singularHomologyFunctor_obj]
  -- The maps over the finite unions form a natural isomorphism of the two diagrams.
  let α : (monotone_biUnion_baseSet_trivializationAt F E).functor ⋙ A ≅
      thomPairFiniteTrivializingUnionDiagram (F := F) (E := E) ⋙
        TopPair.singularHomologyFunctor R r :=
    NatIso.ofComponents (fun s ↦ @asIso _ _ _ _ (ψ _) (hfin s) ≪≫ eqToIso (hobj s))
      fun {s t} f ↦ by
        have hf : (monotone_biUnion_baseSet_trivializationAt F E).functor.map f =
            homOfLE (biUnion_subset_biUnion_left f.le) := rfl
        simp only [Functor.comp_map, hf, thomPairFiniteTrivializingUnionDiagram_map,
          TopPair.singularHomologyFunctor_map, Iso.trans_hom, asIso_hom, eqToIso.hom,
          TopPair.singularHomologyMap_comp, TopPair.singularHomologyMap_eqToHom, Category.assoc,
          eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, reassoc_of% hψ, eqToHom_trans]
  let P := isColimitMapCoconeSingularHomologyThomPairFiniteTrivializingUnion (F := F) (E := E)
    R r
  have h : φ ≫ eqToHom hpt = (hc.coconePointsIsoOfNatIso P α).hom :=
    hc.hom_ext fun s ↦ by
      rw [hc.comp_coconePointsIsoOfNatIso_hom P α s, reassoc_of% (hφ s)]
      simp [α, TopPair.singularHomologyMap_comp, TopPair.singularHomologyMap_eqToHom]
  have : IsIso (φ ≫ eqToHom hpt) := by
    rw [h]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (eqToHom hpt)

end Gluing

end TauCeti

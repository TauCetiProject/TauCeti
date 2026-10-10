/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Collapse.Basic
import Mathlib.Data.Set.Card
import Mathlib.Order.Preorder.Finite

/-!
# Removing a dominated vertex by simplicial collapse

If adjoining `w` to every face containing `v` still gives a face, and `w ≠ v`, then a finite
complex collapses onto the deletion of `v`. Every face avoiding `v` is retained. This is the
relative collapse needed when simplifying a triangulated cylinder onto an endpoint copy:
vertices in the other endpoint can be removed in order, dominated by their partners.

The statement uses precomplexes, so removing a vertex really removes it from the face set.
Finiteness is required only of the faces containing `v`, allowing an infinite retained complex.
The maximal-face pairing adapts the cone-collapse argument in
`TauCeti.AlgebraicTopology.SimplicialComplex.Collapse.Cone` to the faces incident to `v`.

## References

* C. P. Rourke and B. J. Sanderson, *Introduction to Piecewise-Linear Topology* (1972),
  Chapter 3 (elementary simplicial collapse).
-/

public section

namespace PreAbstractSimplicialComplex

variable {ι : Type*} [DecidableEq ι]

/-- A finite collection of faces containing `v` and missing `w` can be removed by free-pair
collapses, pairing each such face with the face obtained by adjoining `w`. -/
private theorem collapsesTo_deletion_vertex_aux (v w : ι) (hwv : w ≠ v) :
    ∀ (n : ℕ) (K : PreAbstractSimplicialComplex ι),
      {σ : Finset ι | σ ∈ K ∧ v ∈ σ}.Finite →
      {σ : Finset ι | σ ∈ K ∧ v ∈ σ}.ncard ≤ n →
      (∀ σ ∈ K, v ∈ σ → insert w σ ∈ K) →
      CollapsesTo K (deletion K {v}) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro K hfin hcard hdom
    by_cases hempty : ∀ σ ∈ K, v ∉ σ
    · have heq : deletion K {v} = K := by
        apply SetLike.ext
        intro σ
        simp only [mem_deletion, Finset.singleton_subset_iff]
        exact ⟨And.left, fun hσ => ⟨hσ, hempty σ hσ⟩⟩
      rw [heq]
    -- Choose a maximal incident face missing the dominating vertex.
    push Not at hempty
    obtain ⟨ρ, hρ, hvρ⟩ := hempty
    have hρerase : ρ.erase w ∈ K :=
      (K.isRelLowerSet_faces hρ).2 (Finset.erase_subset _ _)
        ⟨v, Finset.mem_erase.mpr ⟨hwv.symm, hvρ⟩⟩
    let S : Set (Finset ι) := {σ | σ ∈ K ∧ v ∈ σ ∧ w ∉ σ}
    have hS : S.Finite := hfin.subset (fun _ h => ⟨h.1, h.2.1⟩)
    obtain ⟨σ, _, hmax⟩ := hS.exists_le_maximal
      (show ρ.erase w ∈ S from
        ⟨hρerase, Finset.mem_erase.mpr ⟨hwv.symm, hvρ⟩, Finset.notMem_erase _ _⟩)
    have hσ : σ ∈ K := hmax.prop.1
    have hvσ : v ∈ σ := hmax.prop.2.1
    have hwσ : w ∉ σ := hmax.prop.2.2
    -- Maximality leaves exactly two cofaces, giving an elementary collapse.
    have hfree : IsFreePair K σ (insert w σ) := by
      refine ⟨hσ, hdom σ hσ hvσ, Finset.ssubset_insert hwσ, ?_⟩
      intro τ hτ hστ
      by_cases hwτ : w ∈ τ
      · have hsub : σ ⊆ τ.erase w := Finset.subset_erase.mpr ⟨hστ, hwσ⟩
        have hmem : τ.erase w ∈ K :=
          (K.isRelLowerSet_faces hτ).2 (Finset.erase_subset _ _)
            ⟨v, hsub hvσ⟩
        have heq := hmax.eq_of_ge
          (show τ.erase w ∈ S from ⟨hmem, hsub hvσ, Finset.notMem_erase _ _⟩) hsub
        exact Or.inr (by rw [← heq, Finset.insert_erase hwτ])
      · exact Or.inl (hmax.eq_of_ge ⟨hτ, hστ hvσ, hwτ⟩ hστ)
    have hstep : ElementaryCollapsesTo K (deletion K σ) :=
      ElementaryCollapsesTo.of_isFreePair hfree rfl
    -- Deleting this pair reduces the finite set of incident faces.
    let T : Set (Finset ι) := {τ | τ ∈ deletion K σ ∧ v ∈ τ}
    have hT : T.Finite := hfin.subset (fun _ h => ⟨deletion_le h.1, h.2⟩)
    have hTlt : T.ncard < n := by
      have hstrict : T ⊂ {τ : Finset ι | τ ∈ K ∧ v ∈ τ} := by
        refine Set.ssubset_iff_subset_ne.mpr ⟨fun _ h => ⟨deletion_le h.1, h.2⟩, ?_⟩
        intro heq
        have hσT : σ ∈ T := heq.symm ▸ (show σ ∈ {τ | τ ∈ K ∧ v ∈ τ} from ⟨hσ, hvσ⟩)
        exact (mem_deletion.mp hσT.1).2 Finset.Subset.rfl
      exact (Set.ncard_lt_ncard hstrict hfin).trans_le hcard
    -- Domination survives deletion, and the terminal vertex-deletion complex is unchanged.
    have hdom' : ∀ τ ∈ deletion K σ, v ∈ τ → insert w τ ∈ deletion K σ := by
      intro τ hτ hvτ
      obtain ⟨hτK, hστ⟩ := mem_deletion.mp hτ
      refine mem_deletion.mpr ⟨hdom τ hτK hvτ, ?_⟩
      intro hsub
      apply hστ
      intro a ha
      exact (Finset.mem_insert.mp (hsub ha)).resolve_left
        (fun haw => hwσ (haw ▸ ha))
    have hend : deletion (deletion K σ) {v} = deletion K {v} := by
      apply SetLike.ext
      intro τ
      simp only [mem_deletion, Finset.singleton_subset_iff]
      constructor
      · exact fun h => ⟨h.1.1, h.2⟩
      · rintro ⟨hτ, hvτ⟩
        exact ⟨⟨hτ, fun hστ => hvτ (hστ hvσ)⟩, hvτ⟩
    rw [← hend]
    exact CollapsesTo.head hstep (ih T.ncard hTlt (deletion K σ) hT le_rfl hdom')

/-- A vertex dominated by a different vertex can be removed by a finite sequence of elementary
collapses, retaining every face that avoids the removed vertex. Only the faces incident to the
removed vertex need be finite; the rest of the complex may be infinite. -/
theorem collapsesTo_deletion_vertex_of_dominated {K : PreAbstractSimplicialComplex ι}
    {v w : ι} (hwv : w ≠ v)
    (hfin : {σ : Finset ι | σ ∈ K ∧ v ∈ σ}.Finite)
    (hdom : ∀ σ ∈ K, v ∈ σ → insert w σ ∈ K) :
    CollapsesTo K (deletion K {v}) :=
  collapsesTo_deletion_vertex_aux v w hwv _ K hfin le_rfl hdom

end PreAbstractSimplicialComplex

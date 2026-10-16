/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Join.Basic
public import TauCeti.AlgebraicTopology.SimplicialComplex.Subdivision.Stellar.Equivalence

/-!
# Stellar equivalence and joins

Starring a face in either factor of a join stars the corresponding face of the join. Thus joins
preserve stellar equivalence, including intrinsic stellar equivalence up to relabeling. This
allows the factors of a link of the form `∂σ ∗ link K σ` to be replaced by standard models when
checking the sphere-or-ball condition for a combinatorial manifold.

The void complex is allowed in either factor. Only the starred face must be nonempty; starring
the empty set gives the void complex, whereas joining a void factor retains the other factor.

## Main results

* `PreAbstractSimplicialComplex.stellarSubdivision_join_inl` and
  `PreAbstractSimplicialComplex.stellarSubdivision_join_inr`: starring a nonempty face
  commutes with joining in either factor.
* `PreAbstractSimplicialComplex.IsStellarMove.join_left` and
  `PreAbstractSimplicialComplex.IsStellarMove.join_right`: a stellar move in either factor
  induces one in the join.
* `PreAbstractSimplicialComplex.StellarEquivalent.join`: stellar equivalences in both factors
  induce an equivalence of joins.
* `PreAbstractSimplicialComplex.StellarEquivalentUpToRelabeling.join`: the same transport for
  intrinsic stellar equivalence.

## References

* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Chapters 2–3.
* W. B. R. Lickorish, *Simplicial moves on complexes and manifolds*, Geom. Topol. Monogr. 2
  (1999), 299–320.
-/

public section

open Finset

namespace PreAbstractSimplicialComplex

variable {α β : Type*} [DecidableEq α] [DecidableEq β]
  {K K' : PreAbstractSimplicialComplex α} {L L' : PreAbstractSimplicialComplex β}

/-- Starring a nonempty left face commutes with joining another complex. -/
@[simp]
theorem stellarSubdivision_join_inl {σ : Finset α} (hσ : σ.Nonempty) (v : α) :
    stellarSubdivision (join K L) (σ.map Function.Embedding.inl) (Sum.inl v) =
      join (stellarSubdivision K σ v) L := by
  refine SetLike.ext fun τ => ?_
  have he : ¬ σ ⊆ ∅ := fun h => hσ.ne_empty (Finset.subset_empty.mp h)
  have hsub : ∀ ρ : Finset (α ⊕ β), σ.map Function.Embedding.inl ⊆ ρ ↔ σ ⊆ ρ.toLeft :=
    fun _ => Finset.map_inl_subset_iff_subset_toLeft
  simp only [mem_stellarSubdivision_iff, hsub, mem_join_iff,
    ← Finset.mem_toLeft, Finset.toLeft_erase_inl, Finset.toRight_erase_inl,
    Finset.toLeft_union, Finset.toRight_union]
  have hleft : (σ.map (Function.Embedding.inl : α ↪ α ⊕ β)).toLeft = σ := by
    rw [← Finset.disjSum_empty, Finset.toLeft_disjSum]
  have hright : (σ.map (Function.Embedding.inl : α ↪ α ⊕ β)).toRight = ∅ := by
    rw [← Finset.disjSum_empty, Finset.toRight_disjSum]
  simp only [hleft, hright, Finset.union_empty]
  have hne : ∀ s : Finset α, s ∈ K → s.Nonempty := fun _ h => (K.isRelLowerSet_faces h).1
  have hσunion : ∀ s : Finset α, s ∪ σ ≠ ∅ := fun s => (hσ.mono subset_union_right).ne_empty
  have hvne : v ∈ τ.toLeft → τ.Nonempty := fun h => ⟨Sum.inl v, mem_toLeft.mp h⟩
  have : τ.toLeft ∈ K → τ.Nonempty := fun h => by
    obtain ⟨a, ha⟩ := hne _ h
    exact ⟨Sum.inl a, mem_toLeft.mp ha⟩
  have herase : v ∈ τ.toLeft → τ.toLeft ≠ ∅ := fun h => Finset.nonempty_iff_ne_empty.mp ⟨v, h⟩
  have hnew : v ∈ τ.toLeft →
      (τ.erase (Sum.inl v) ∪ σ.map Function.Embedding.inl).Nonempty :=
    fun _ => hσ.map.mono subset_union_right
  grind

/-- A stellar move in the left factor induces a stellar move in the join. -/
theorem IsStellarMove.join_left (h : IsStellarMove K K') (L : PreAbstractSimplicialComplex β) :
    IsStellarMove (join K L) (join K' L) := by
  obtain ⟨σ, v, hσ, hv, rfl⟩ := isStellarMove_iff.mp h
  refine isStellarMove_iff.mpr
    ⟨σ.map Function.Embedding.inl, Sum.inl v, map_inl_mem_join hσ, ?_, ?_⟩
  · have hsingleton : ({Sum.inl v} : Finset (α ⊕ β)) = ({v} : Finset α).disjSum ∅ := by
      simp
    rw [hsingleton, disjSum_mem_join_iff]
    simpa using hv
  · exact (stellarSubdivision_join_inl (K.isRelLowerSet_faces hσ).1 v).symm

/-- A stellar equivalence in the left factor induces one of the joins. -/
theorem StellarEquivalent.join_left (h : StellarEquivalent K K')
    (L : PreAbstractSimplicialComplex β) : StellarEquivalent (join K L) (join K' L) := by
  apply h.induction_on
  · intro A B h
    exact (h.join_left L).stellarEquivalent
  · intro A
    exact .refl _
  · intro A B h
    exact h.symm
  · intro A B C h h'
    exact h.trans h'

/-- Starring a nonempty right face commutes with joining another complex. -/
@[simp]
theorem stellarSubdivision_join_inr {σ : Finset β} (hσ : σ.Nonempty) (v : β) :
    stellarSubdivision (join K L) (σ.map Function.Embedding.inr) (Sum.inr v) =
      join K (stellarSubdivision L σ v) := by
  have h := congrArg (fun C => C.map Sum.swap)
    (stellarSubdivision_join_inl (K := L) (L := K) hσ v)
  have hface : (σ.map (Function.Embedding.inl : β ↪ β ⊕ α)).image Sum.swap =
      σ.map (Function.Embedding.inr : β ↪ α ⊕ β) := by
    simp only [Finset.map_eq_image, Finset.image_image]
    apply Finset.image_congr
    intro x _
    simp only [Function.comp_apply, Function.Embedding.inl_apply, Sum.swap_inl,
      Function.Embedding.inr_apply]
  simpa only [map_stellarSubdivision Sum.swap (Equiv.sumComm β α).injective,
    map_join_swap, hface, Sum.swap_inl] using h

/-- A stellar move in the right factor induces a stellar move in the join. -/
theorem IsStellarMove.join_right (h : IsStellarMove L L') (K : PreAbstractSimplicialComplex α) :
    IsStellarMove (join K L) (join K L') := by
  have h' := (h.join_left K).map Sum.swap (Equiv.sumComm β α).injective
  simpa only [map_join_swap] using h'

/-- A stellar equivalence in the right factor induces one of the joins. -/
theorem StellarEquivalent.join_right (h : StellarEquivalent L L')
    (K : PreAbstractSimplicialComplex α) : StellarEquivalent (join K L) (join K L') := by
  have h' := (h.join_left K).map Sum.swap (Equiv.sumComm β α).injective
  simpa only [map_join_swap] using h'

/-- Stellar equivalences in both factors induce a stellar equivalence of joins. -/
theorem StellarEquivalent.join (hK : StellarEquivalent K K') (hL : StellarEquivalent L L') :
    StellarEquivalent (join K L) (join K' L') :=
  (hK.join_left L).trans (hL.join_right K')

/-- An intrinsic stellar equivalence in the left factor induces one of the joins, even when
the two complexes use different vertex names in their common enlarged vertex type. -/
theorem StellarEquivalentUpToRelabeling.join_left
    (h : StellarEquivalentUpToRelabeling K K') (L : PreAbstractSimplicialComplex β) :
    StellarEquivalentUpToRelabeling (join K L) (join K' L) := by
  apply h.induction_on
  · intro A B f g he
    -- Move the reserved fresh vertices past the unchanged right factor.
    let e : (α ⊕ ℕ) ⊕ β ≃ (α ⊕ β) ⊕ ℕ :=
      (Equiv.sumAssoc α ℕ β).trans
        ((Equiv.sumCongr (Equiv.refl α) (Equiv.sumComm ℕ β)).trans
          (Equiv.sumAssoc α β ℕ).symm)
    let f' : α ⊕ β ↪ (α ⊕ β) ⊕ ℕ :=
      (f.sumMap (Function.Embedding.refl β)).trans e.toEmbedding
    let g' : α ⊕ β ↪ (α ⊕ β) ⊕ ℕ :=
      (g.sumMap (Function.Embedding.refl β)).trans e.toEmbedding
    apply of_common_relabeling f' g'
    have hfcoe : (f' : α ⊕ β → (α ⊕ β) ⊕ ℕ) = e ∘ Sum.map f id := by
      simp only [f', Function.Embedding.coe_trans, Equiv.coe_toEmbedding,
        Function.Embedding.coe_sumMap, Function.Embedding.coe_refl]
    have hgcoe : (g' : α ⊕ β → (α ⊕ β) ⊕ ℕ) = e ∘ Sum.map g id := by
      simp only [g', Function.Embedding.coe_trans, Equiv.coe_toEmbedding,
        Function.Embedding.coe_sumMap, Function.Embedding.coe_refl]
    have hf : (join A L).map f' = (join (A.map f) L).map e := by
      rw [hfcoe, ← map_map, map_join, map_id]
    have hg : (join B L).map g' = (join (B.map g) L).map e := by
      rw [hgcoe, ← map_map, map_join, map_id]
    rw [hf, hg]
    exact (he.join_left L).map e e.injective
  · intro A
    exact .refl _
  · intro A B h
    exact h.symm
  · intro A B C h h'
    exact h.trans h'

/-- An intrinsic stellar equivalence in the right factor induces one of the joins. -/
theorem StellarEquivalentUpToRelabeling.join_right
    (h : StellarEquivalentUpToRelabeling L L') (K : PreAbstractSimplicialComplex α) :
    StellarEquivalentUpToRelabeling (join K L) (join K L') := by
  have h' := (h.join_left K).map (Equiv.sumComm β α) (Equiv.sumComm β α).injective
  simpa only [Equiv.sumComm_apply, map_join_swap] using h'

/-- Intrinsic stellar equivalences in both factors induce an intrinsic stellar equivalence of
their joins. -/
theorem StellarEquivalentUpToRelabeling.join (hK : StellarEquivalentUpToRelabeling K K')
    (hL : StellarEquivalentUpToRelabeling L L') :
    StellarEquivalentUpToRelabeling (join K L) (join K' L') :=
  (hK.join_left L).trans (hL.join_right K')

end PreAbstractSimplicialComplex

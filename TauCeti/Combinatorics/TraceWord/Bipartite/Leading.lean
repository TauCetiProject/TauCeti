/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.TraceWord.Bipartite.Basic
public import TauCeti.Combinatorics.NoncrossingPartition.FormPerm
import TauCeti.Combinatorics.NoncrossingPartition.Geodesic
import TauCeti.Combinatorics.TreeWalk.Leading
import TauCeti.Data.Fin.Sum
import TauCeti.Data.Finset.Sum
import TauCeti.GroupTheory.Perm.OrbitCount.FinRotate
import Mathlib.Data.Set.Card

/-!
# Leading bipartite trace words

A word of half-length `k` is leading if no edge occurs just once and the word visits
`k + 1` vertices. Each edge then occurs once in each direction. Matching the two occurrences
gives a permutation of the `k` positions. Its cycles are the column classes, and the cycles
of the rotation composed with its inverse are the row classes. The sum of the two cycle
counts is maximal, so the column partition is noncrossing. Directed-edge uniqueness uses
`TreeWalk.prodMk_finRotate_injective_of_no_singleton_edge_of_card_image_eq`. The classification
uses `NoncrossingPartition.orbitCount_add_orbitCount_inv_mul_finRotate_eq_iff` to recover the
partition and `NoncrossingPartition.orbitCount_formPerm_add_orbitCount_inv_mul_finRotate` to
verify the vertex count for a word built from a partition.

## References

* Z. D. Bai, *Methodologies in spectral analysis of large dimensional random matrices, a
  review*, Statistica Sinica 9 (1999), §2.1.2, (2.15).
-/

public section

open Equiv Equiv.Perm Finset Function

namespace TauCeti

variable {α β : Type*} {k : ℕ} [DecidableEq α] [DecidableEq β]

/-- A leading bipartite trace word has no singleton edge and visits the maximal number
`k + 1` of row and column vertices. -/
def IsLeadingBipartiteWord (u : Fin k → α) (v : Fin k → β) : Prop :=
  (∀ a, ∃ b ≠ a, bipartiteEdge u v b = bipartiteEdge u v a) ∧
    #(univ.image u) + #(univ.image v) = k + 1

/-- A bipartite word is leading exactly when it has no singleton edge and attains the
vertex-count bound. -/
theorem isLeadingBipartiteWord_iff {u : Fin k → α} {v : Fin k → β} :
    IsLeadingBipartiteWord u v ↔
      (∀ a, ∃ b ≠ a, bipartiteEdge u v b = bipartiteEdge u v a) ∧
        #(univ.image u) + #(univ.image v) = k + 1 := Iff.rfl

/-- On each orientation of a leading bipartite word, the visited edges are distinct. -/
theorem IsLeadingBipartiteWord.injective_bipartiteEdge_orientations {u : Fin k → α} {v : Fin k → β}
    (h : IsLeadingBipartiteWord u v) :
    Injective (bipartiteEdge u v ∘ Sum.inl) ∧ Injective (bipartiteEdge u v ∘ Sum.inr) := by
  let e := interleaveIndexEquiv k
  have hleft (t : Fin k) : finRotate (2 * k) (e (.inl t)) = e (.inr t) :=
    finRotate_interleaveIndexEquiv_inl t
  have hright (t : Fin k) : finRotate (2 * k) (e (.inr t)) = e (.inl (finRotate k t)) :=
    finRotate_interleaveIndexEquiv_inr t
  let w : Fin (2 * k) → α ⊕ β := Sum.map u v ∘ e.symm
  have hw (a : Fin k ⊕ Fin k) : w (e a) = Sum.map u v a :=
    congrArg (Sum.map u v) (e.symm_apply_apply a)
  have hv : univ.image w = (univ.image u).disjSum (univ.image v) := by
    rw [show w = Sum.map u v ∘ e.symm from rfl, ← image_image, image_univ_equiv,
      ← univ_disjSum_univ, image_sumMap_disjSum]
  have hedge (a : Fin k ⊕ Fin k) :
      s(w (e a), w (finRotate (2 * k) (e a))) =
        s(Sum.inl (bipartiteEdge u v a).1, Sum.inr (bipartiteEdge u v a).2) := by
    cases a with
    | inl t => simp only [hleft, hw, Sum.map_inl, Sum.map_inr, bipartiteEdge_inl]
    | inr t => simp only [hright, hw, Sum.map_inr, Sum.map_inl, bipartiteEdge_inr]
               exact Sym2.eq_swap
  have hword (i : Fin (2 * k)) :
      ∃ j ≠ i, s(w j, w (finRotate (2 * k) j)) = s(w i, w (finRotate (2 * k) i)) := by
    obtain ⟨a, rfl⟩ := e.surjective i
    obtain ⟨b, hba, hb⟩ := (isLeadingBipartiteWord_iff.mp h).1 a
    exact ⟨e b, e.injective.ne hba, by rw [hedge, hedge, hb]⟩
  have hd := TreeWalk.prodMk_finRotate_injective_of_no_singleton_edge_of_card_image_eq hword
    (by rw [hv, card_disjSum]; exact (isLeadingBipartiteWord_iff.mp h).2)
  constructor
  · intro i j hij
    apply Sum.inl_injective (β := Fin k) (e.injective (hd ?_))
    simpa only [hleft, hw, Sum.map_inl, Sum.map_inr, comp_apply,
      bipartiteEdge_inl, Prod.mk.injEq, Sum.inl.injEq, Sum.inr.injEq] using hij
  · intro i j hij
    apply Sum.inr_injective (α := Fin k) (e.injective (hd ?_))
    simpa only [hright, hw, Sum.map_inr, Sum.map_inl, comp_apply,
      bipartiteEdge_inr, Prod.mk.injEq, Sum.inr.injEq, Sum.inl.injEq, and_comm] using hij

/-- For a leading word, there is a unique permutation matching each column-to-row step
to the row-to-column step on the same edge. -/
theorem IsLeadingBipartiteWord.existsUnique_perm_matching_bipartiteEdges
    {u : Fin k → α} {v : Fin k → β}
    (h : IsLeadingBipartiteWord u v) :
    ∃! π : Perm (Fin k), ∀ t, bipartiteEdge u v (.inl (π t)) = bipartiteEdge u v (.inr t) := by
  obtain ⟨hl, hr⟩ := h.injective_bipartiteEdge_orientations
  have hmatch (t : Fin k) :
      ∃ j, bipartiteEdge u v (.inl j) = bipartiteEdge u v (.inr t) := by
    obtain ⟨i, hne, hi⟩ := (isLeadingBipartiteWord_iff.mp h).1 (.inr t)
    cases i with
    | inl i => exact ⟨i, hi⟩
    | inr i => exact (hne (congrArg Sum.inr (hr hi))).elim
  choose f hf using hmatch
  have hfinj : Injective f := fun i j hij ↦ hr ((hf i).symm.trans (hij ▸ hf j))
  let π := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hfinj)
  have hπ : (π : Fin k → Fin k) = f := Equiv.coe_ofBijective _ _
  refine ⟨π, ?_, fun τ hτ ↦ Equiv.ext fun t ↦ hl ?_⟩
  · simpa only [hπ] using hf
  · simpa only [hπ, comp_apply] using (hτ t).trans (hf t).symm

private theorem card_image_cycleColouring_le_and_eq_iff {ι γ : Type*} [Fintype ι] [DecidableEq γ]
    (π : Perm ι) (f : Quotient (SameCycle.setoid π) → γ) :
    #(univ.image (invariantColouringEquiv π f).val) ≤ orbitCount π ∧
      (#(univ.image (invariantColouringEquiv π f).val) = orbitCount π ↔ Injective f) := by
  rw [card_image_invariantColouringEquiv, orbitCount_def]
  refine ⟨Nat.card_le_card_of_surjective _ Set.rangeFactorization_surjective, ?_⟩
  refine ⟨fun h x y hxy ↦ ?_, Nat.card_range_of_injective⟩
  exact (Set.rangeFactorization_surjective.bijective_of_nat_card_le
    (f := Set.rangeFactorization f) h.ge).injective (Subtype.ext hxy)

private theorem exists_noncrossing_cycleColourings {u : Fin k → α} {v : Fin k → β}
    (hk : k ≠ 0) (h : IsLeadingBipartiteWord u v) :
    ∃ π : NoncrossingPartition (univ : Finset (Fin k)),
      ∃ (f : Quotient (SameCycle.setoid (finRotate k * π.val.formPerm⁻¹)) ↪ α)
        (g : Quotient (SameCycle.setoid π.val.formPerm) ↪ β),
        (invariantColouringEquiv _ f).val = u ∧ (invariantColouringEquiv _ g).val = v := by
  obtain ⟨σ, hσ, _⟩ := h.existsUnique_perm_matching_bipartiteEdges
  simp only [bipartiteEdge_inl, bipartiteEdge_inr, Prod.mk.injEq] at hσ
  let ρ := finRotate k * σ⁻¹
  have hu : u ∘ ρ = u := funext fun i ↦ by
    have hi := (hσ (σ.symm i)).1.symm
    simpa only [ρ, comp_apply, Perm.mul_apply, Perm.inv_def, apply_symm_apply] using hi
  let f := (invariantColouringEquiv ρ).symm ⟨u, hu⟩
  let g := (invariantColouringEquiv σ).symm ⟨v, funext fun i ↦ (hσ i).2⟩
  have hf : (invariantColouringEquiv ρ f).val = u :=
    congrArg Subtype.val ((invariantColouringEquiv ρ).apply_symm_apply _)
  have hg : (invariantColouringEquiv σ g).val = v :=
    congrArg Subtype.val ((invariantColouringEquiv σ).apply_symm_apply _)
  obtain ⟨hboundf, heqf⟩ := card_image_cycleColouring_le_and_eq_iff ρ f
  obtain ⟨hboundg, heqg⟩ := card_image_cycleColouring_le_and_eq_iff σ g
  rw [hf] at hboundf heqf
  rw [hg] at hboundg heqg
  have hle : orbitCount ρ + orbitCount σ ≤ k + 1 := by
    simpa only [ρ, orbitCount_finRotate, Nat.card_fin, orbitCount_inv, ite_eq_right hk,
      Nat.add_comm] using (finRotate k).orbitCount_mul_add_orbitCount_le_orbitCount_add_card σ⁻¹
  have hv := (isLeadingBipartiteWord_iff.mp h).2
  have hEq : orbitCount σ + orbitCount ρ = k + 1 := by omega
  have hfinj := heqf.mp (by omega)
  have hginj := heqg.mp (by omega)
  dsimp only [ρ] at hEq
  rw [orbitCount_mul_comm (finRotate k)] at hEq
  obtain ⟨π, hπ⟩ :=
    (NoncrossingPartition.orbitCount_add_orbitCount_inv_mul_finRotate_eq_iff hk).mp hEq
  refine ⟨π, ?_⟩
  rw [hπ]
  exact ⟨⟨f, hfinj⟩, ⟨g, hginj⟩, hf, hg⟩

omit [DecidableEq α] [DecidableEq β] in
private theorem bipartiteEdge_cycleColouring (π : Perm (Fin k))
    (f : Quotient (SameCycle.setoid (finRotate k * π⁻¹)) → α)
    (g : Quotient (SameCycle.setoid π) → β) (t : Fin k) :
    bipartiteEdge (invariantColouringEquiv _ f).val
      (invariantColouringEquiv _ g).val (.inl (π t)) =
      bipartiteEdge (invariantColouringEquiv _ f).val
        (invariantColouringEquiv _ g).val (.inr t) := by
  have hu := congrFun (invariantColouringEquiv (finRotate k * π⁻¹) f).property (π t)
  have hv := congrFun (invariantColouringEquiv π g).property t
  simp only [comp_apply, Perm.mul_apply, Perm.inv_def, symm_apply_apply] at hu hv
  simpa only [bipartiteEdge_inl, bipartiteEdge_inr, Prod.mk.injEq] using ⟨hu.symm, hv⟩

private theorem isLeadingBipartiteWord_cycleColouring (hk : k ≠ 0)
    (π : NoncrossingPartition (univ : Finset (Fin k)))
    (f : Quotient (SameCycle.setoid (finRotate k * π.val.formPerm⁻¹)) ↪ α)
    (g : Quotient (SameCycle.setoid π.val.formPerm) ↪ β) :
    IsLeadingBipartiteWord (invariantColouringEquiv _ f).val
      (invariantColouringEquiv _ g).val := by
  let σ := (π : Finpartition (univ : Finset (Fin k))).formPerm
  refine isLeadingBipartiteWord_iff.mpr ⟨?_, ?_⟩
  · intro s
    cases s with
    | inl t =>
      obtain ⟨j, rfl⟩ := σ.surjective t
      exact ⟨.inr j, Sum.inr_ne_inl, (bipartiteEdge_cycleColouring σ f g j).symm⟩
    | inr t => exact ⟨.inl (σ t), Sum.inl_ne_inr, bipartiteEdge_cycleColouring σ f g t⟩
  · rw [card_image_invariantColouringEquiv, card_image_invariantColouringEquiv,
      Nat.card_range_of_injective f.injective, Nat.card_range_of_injective g.injective,
      ← orbitCount_def, ← orbitCount_def, orbitCount_mul_comm (finRotate k), Nat.add_comm]
    exact NoncrossingPartition.orbitCount_formPerm_add_orbitCount_inv_mul_finRotate hk π

/-- A leading bipartite trace word is specified by a noncrossing column partition and two
injective labellings. Column labels are attached to the cycles of its permutation, and row
labels to the cycles of the rotation composed with the inverse permutation. -/
noncomputable def leadingBipartiteWordEquiv (hk : k ≠ 0) :
    (Σ π : NoncrossingPartition (univ : Finset (Fin k)),
      (Quotient (SameCycle.setoid (finRotate k * π.val.formPerm⁻¹)) ↪ α) ×
      (Quotient (SameCycle.setoid π.val.formPerm) ↪ β)) ≃
      {w : (Fin k → α) × (Fin k → β) // IsLeadingBipartiteWord w.1 w.2} := by
  let label (q : Σ π : NoncrossingPartition (univ : Finset (Fin k)),
      (Quotient (SameCycle.setoid (finRotate k * π.val.formPerm⁻¹)) ↪ α) ×
      (Quotient (SameCycle.setoid π.val.formPerm) ↪ β)) :
      {w : (Fin k → α) × (Fin k → β) // IsLeadingBipartiteWord w.1 w.2} :=
    ⟨((invariantColouringEquiv _ q.2.1).val, (invariantColouringEquiv _ q.2.2).val),
      isLeadingBipartiteWord_cycleColouring hk q.1 q.2.1 q.2.2⟩
  refine Equiv.ofBijective label ⟨?_, ?_⟩
  · rintro ⟨π, f, g⟩ ⟨τ, f', g'⟩ he
    have hw := isLeadingBipartiteWord_cycleColouring hk π f g
    obtain ⟨σ, _, hu⟩ := hw.existsUnique_perm_matching_bipartiteEdges
    have hfirst := hu _ (bipartiteEdge_cycleColouring _ f g)
    have hlab := congrArg Subtype.val he
    dsimp only [label] at hlab
    obtain ⟨hrow, hcol⟩ := Prod.mk.inj hlab
    have hsecond := hu τ.val.formPerm (by
      rw [hrow, hcol]
      exact bipartiteEdge_cycleColouring τ.val.formPerm f' g')
    have hπτ : π = τ := Subtype.ext (Finpartition.formPerm_injective (hfirst.trans hsecond.symm))
    subst τ
    congr 1
    apply Prod.ext
    · ext q
      induction q using Quotient.inductionOn with
      | _ i => simpa only [label, invariantColouringEquiv_apply_coe] using congrFun hrow i
    · ext q
      induction q using Quotient.inductionOn with
      | _ i => simpa only [label, invariantColouringEquiv_apply_coe] using congrFun hcol i
  · rintro ⟨⟨u, v⟩, hw⟩
    obtain ⟨π, f, g, hf, hg⟩ := exists_noncrossing_cycleColourings hk hw
    exact ⟨⟨π, f, g⟩, Subtype.ext (Prod.ext hf hg)⟩

/-- The forward equivalence evaluates the labels on the cycles containing each position. -/
@[simp] theorem leadingBipartiteWordEquiv_apply (hk : k ≠ 0)
    (π : NoncrossingPartition (univ : Finset (Fin k)))
    (f : Quotient (SameCycle.setoid (finRotate k * π.val.formPerm⁻¹)) ↪ α)
    (g : Quotient (SameCycle.setoid π.val.formPerm) ↪ β) :
    (leadingBipartiteWordEquiv hk ⟨π, f, g⟩).val =
      (fun i ↦ f (Quotient.mk _ i), fun i ↦ g (Quotient.mk _ i)) := by
  unfold leadingBipartiteWordEquiv
  dsimp only
  erw [Equiv.coe_ofBijective]
  exact Prod.ext (funext fun i ↦ invariantColouringEquiv_apply_coe _ f i)
    (funext fun i ↦ invariantColouringEquiv_apply_coe _ g i)

/-- The inverse recovers the row and column labels on the cycles represented by each position. -/
theorem leadingBipartiteWordEquiv_symm_apply_labels (hk : k ≠ 0)
    (w : {w : (Fin k → α) × (Fin k → β) // IsLeadingBipartiteWord w.1 w.2}) (i : Fin k) :
    let q := (leadingBipartiteWordEquiv hk).symm w
    q.2.1 (Quotient.mk _ i) = w.val.1 i ∧ q.2.2 (Quotient.mk _ i) = w.val.2 i := by
  have h := congrArg Subtype.val ((leadingBipartiteWordEquiv hk).apply_symm_apply w)
  generalize (leadingBipartiteWordEquiv hk).symm w = q at h ⊢
  obtain ⟨π, f, g⟩ := q
  rw [leadingBipartiteWordEquiv_apply] at h
  exact ⟨congrFun (congrArg Prod.fst h) i, congrFun (congrArg Prod.snd h) i⟩

/-- The partition recovered by the inverse has the permutation that matches the two orientations
of each edge in the original word. -/
theorem leadingBipartiteWordEquiv_symm_apply_formPerm (hk : k ≠ 0)
    (w : {w : (Fin k → α) × (Fin k → β) // IsLeadingBipartiteWord w.1 w.2}) (i : Fin k) :
    let σ := ((leadingBipartiteWordEquiv hk).symm w).1.val.formPerm
    bipartiteEdge w.val.1 w.val.2 (.inl (σ i)) = bipartiteEdge w.val.1 w.val.2 (.inr i) := by
  have h := congrArg Subtype.val ((leadingBipartiteWordEquiv hk).apply_symm_apply w)
  generalize (leadingBipartiteWordEquiv hk).symm w = q at h ⊢
  obtain ⟨π, f, g⟩ := q
  rw [← h]
  simpa only [leadingBipartiteWordEquiv_apply, bipartiteEdge_inl, bipartiteEdge_inr,
    invariantColouringEquiv_apply_coe] using
    bipartiteEdge_cycleColouring π.val.formPerm f g i

open Classical in
/-- The contribution to the leading-word count from a noncrossing partition with `c` blocks
is the number of ways to assign `c` distinct column labels and `k + 1 - c` distinct row labels. -/
theorem card_leadingBipartiteWord [Finite α] [Finite β] (hk : k ≠ 0) :
    Nat.card {w : (Fin k → α) × (Fin k → β) // IsLeadingBipartiteWord w.1 w.2} =
      ∑ π : NoncrossingPartition (univ : Finset (Fin k)),
        (Nat.card α).descFactorial (k + 1 - #π.val.parts) *
          (Nat.card β).descFactorial #π.val.parts := by
  let := Fintype.ofFinite α
  let := Fintype.ofFinite β
  rw [← Nat.card_congr (leadingBipartiteWordEquiv (α := α) (β := β) hk),
    Nat.card_eq_fintype_card, Fintype.card_sigma]
  apply sum_congr rfl
  intro π _
  have hc := NoncrossingPartition.orbitCount_formPerm_add_orbitCount_inv_mul_finRotate hk π
  rw [Finpartition.orbitCount_formPerm, ← orbitCount_mul_comm (finRotate k)] at hc
  have hr : orbitCount (finRotate k * π.val.formPerm⁻¹) =
      k + 1 - #π.val.parts := by omega
  rw [Fintype.card_prod, Fintype.card_embedding_eq, Fintype.card_embedding_eq]
  simp only [← Nat.card_eq_fintype_card, ← orbitCount_def, Finpartition.orbitCount_formPerm, hr]

end TauCeti

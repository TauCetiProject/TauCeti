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
import TauCeti.Data.Finset.Sum
import TauCeti.GroupTheory.Perm.OrbitCount.FinRotate

/-!
# Leading bipartite trace words

A word of half-length `k` is leading if no edge occurs just once and the word visits
`k + 1` vertices. The empty word visits no vertices, so it is not leading. Each edge of a
leading word occurs once in each direction. Matching the two occurrences gives a permutation
of the `k` positions. Its cycles form a noncrossing column partition, and the cycles of the
rotation composed with its inverse give the row classes.

At positive half-length, every noncrossing column partition and pair of injective row and
column labellings of these classes determines a unique leading word. With `c` column blocks,
its contribution to the count is the product of the numbers of ways to assign `c` distinct
column labels and `k + 1 - c` distinct row labels.

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
    unfold w
    rw [← image_image, image_univ_equiv,
      ← univ_disjSum_univ, image_sumMap_disjSum]
  have hword (i : Fin (2 * k)) :
      ∃ j ≠ i, s(w j, w (finRotate (2 * k) j)) = s(w i, w (finRotate (2 * k) i)) := by
    obtain ⟨a, rfl⟩ := e.surjective i
    obtain ⟨b, hba, hb⟩ := (isLeadingBipartiteWord_iff.mp h).1 a
    exact ⟨e b, e.injective.ne hba, by rw [interleaveIndexEquiv_edge_eq_bipartiteEdge u v b,
      interleaveIndexEquiv_edge_eq_bipartiteEdge u v a, hb]⟩
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
  obtain ⟨hboundf, heqf⟩ := ρ.card_image_invariantColouringEquiv_le_and_eq_iff f
  obtain ⟨hboundg, heqg⟩ := σ.card_image_invariantColouringEquiv_le_and_eq_iff g
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

private def labelBipartiteWord (hk : k ≠ 0)
    (q : Σ π : NoncrossingPartition (univ : Finset (Fin k)),
      (Quotient (SameCycle.setoid (finRotate k * π.val.formPerm⁻¹)) ↪ α) ×
      (Quotient (SameCycle.setoid π.val.formPerm) ↪ β)) :
    {w : (Fin k → α) × (Fin k → β) // IsLeadingBipartiteWord w.1 w.2} :=
  ⟨((invariantColouringEquiv _ q.2.1).val, (invariantColouringEquiv _ q.2.2).val),
    isLeadingBipartiteWord_cycleColouring hk q.1 q.2.1 q.2.2⟩

/-- At half-length `k > 0`, a leading bipartite trace word is specified by a noncrossing column
partition and two injective labellings. Column labels are attached to the cycles of its
permutation, and row labels to the cycles of the rotation composed with the inverse permutation. -/
noncomputable def leadingBipartiteWordEquiv (hk : k ≠ 0) :
    (Σ π : NoncrossingPartition (univ : Finset (Fin k)),
      (Quotient (SameCycle.setoid (finRotate k * π.val.formPerm⁻¹)) ↪ α) ×
      (Quotient (SameCycle.setoid π.val.formPerm) ↪ β)) ≃
      {w : (Fin k → α) × (Fin k → β) // IsLeadingBipartiteWord w.1 w.2} := by
  refine Equiv.ofBijective (labelBipartiteWord hk) ⟨?_, ?_⟩
  · rintro ⟨π, f, g⟩ ⟨τ, f', g'⟩ he
    have hw := isLeadingBipartiteWord_cycleColouring hk π f g
    obtain ⟨σ, _, hu⟩ := hw.existsUnique_perm_matching_bipartiteEdges
    have hfirst := hu _ (bipartiteEdge_cycleColouring _ f g)
    have hlab := congrArg Subtype.val he
    dsimp only [labelBipartiteWord] at hlab
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
      | _ i =>
        simpa only [invariantColouringEquiv_apply_coe] using congrFun hrow i
    · ext q
      induction q using Quotient.inductionOn with
      | _ i =>
        simpa only [invariantColouringEquiv_apply_coe] using congrFun hcol i
  · rintro ⟨⟨u, v⟩, hw⟩
    obtain ⟨π, f, g, hf, hg⟩ := exists_noncrossing_cycleColourings hk hw
    exact ⟨⟨π, f, g⟩, Subtype.ext (Prod.ext hf hg)⟩

private theorem coe_leadingBipartiteWordEquiv (hk : k ≠ 0) :
    ⇑(leadingBipartiteWordEquiv (α := α) (β := β) hk) = labelBipartiteWord hk :=
  Equiv.coe_ofBijective _ _

/-- The forward equivalence evaluates the labels on the cycles containing each position. -/
@[simp] theorem leadingBipartiteWordEquiv_apply (hk : k ≠ 0)
    (π : NoncrossingPartition (univ : Finset (Fin k)))
    (f : Quotient (SameCycle.setoid (finRotate k * π.val.formPerm⁻¹)) ↪ α)
    (g : Quotient (SameCycle.setoid π.val.formPerm) ↪ β) :
    (leadingBipartiteWordEquiv hk ⟨π, f, g⟩).val =
      (fun i ↦ f (Quotient.mk _ i), fun i ↦ g (Quotient.mk _ i)) := by
  rw [coe_leadingBipartiteWordEquiv]
  exact Prod.ext (funext fun i ↦ invariantColouringEquiv_apply_coe _ f i)
    (funext fun i ↦ invariantColouringEquiv_apply_coe _ g i)

/-- The inverse recovers the row and column labels on the cycles represented by each position. -/
private theorem leadingBipartiteWordEquiv_symm_apply_labels (hk : k ≠ 0)
    (w : {w : (Fin k → α) × (Fin k → β) // IsLeadingBipartiteWord w.1 w.2}) (i : Fin k) :
    let q := (leadingBipartiteWordEquiv hk).symm w
    q.2.1 (Quotient.mk _ i) = w.val.1 i ∧ q.2.2 (Quotient.mk _ i) = w.val.2 i := by
  have h := congrArg Subtype.val ((leadingBipartiteWordEquiv hk).apply_symm_apply w)
  generalize (leadingBipartiteWordEquiv hk).symm w = q at h ⊢
  obtain ⟨π, f, g⟩ := q
  rw [leadingBipartiteWordEquiv_apply] at h
  exact ⟨congrFun (congrArg Prod.fst h) i, congrFun (congrArg Prod.snd h) i⟩

/-- The recovered row label at the cycle of a position is the word's row at that position. -/
@[simp] theorem leadingBipartiteWordEquiv_symm_apply_row (hk : k ≠ 0)
    (w : {w : (Fin k → α) × (Fin k → β) // IsLeadingBipartiteWord w.1 w.2}) (i : Fin k) :
    ((leadingBipartiteWordEquiv hk).symm w).2.1 (Quotient.mk _ i) = w.val.1 i :=
  (leadingBipartiteWordEquiv_symm_apply_labels hk w i).1

/-- The recovered column label at the cycle of a position is the word's column at that position. -/
@[simp] theorem leadingBipartiteWordEquiv_symm_apply_col (hk : k ≠ 0)
    (w : {w : (Fin k → α) × (Fin k → β) // IsLeadingBipartiteWord w.1 w.2}) (i : Fin k) :
    ((leadingBipartiteWordEquiv hk).symm w).2.2 (Quotient.mk _ i) = w.val.2 i :=
  (leadingBipartiteWordEquiv_symm_apply_labels hk w i).2

/-- The partition recovered by the inverse has the permutation that matches the two orientations
of each edge in the original word. -/
theorem bipartiteEdge_inl_formPerm_leadingBipartiteWordEquiv_symm (hk : k ≠ 0)
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
/-- At half-length `k > 0`, the leading-word count sums over noncrossing column partitions.
A partition with `c` blocks contributes the number of ways to assign `c` distinct column labels
and `k + 1 - c` distinct row labels. -/
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

/-- A leading word of half-length one is specified by one row and one column. -/
theorem card_leadingBipartiteWord_one :
    Nat.card {w : (Fin 1 → α) × (Fin 1 → β) // IsLeadingBipartiteWord w.1 w.2} =
      Nat.card α * Nat.card β := by
  have h (w : (Fin 1 → α) × (Fin 1 → β)) : IsLeadingBipartiteWord w.1 w.2 := by
    refine ⟨?_, ?_⟩
    · rintro (i | i)
      · exact ⟨.inr i, Sum.inr_ne_inl, by simp⟩
      · exact ⟨.inl i, Sum.inl_ne_inr, by simp⟩
    · simp [univ_unique]
  exact Nat.card_congr ((Equiv.subtypeUnivEquiv h).trans
    (Equiv.prodCongr (Equiv.funUnique (Fin 1) α) (Equiv.funUnique (Fin 1) β))) |>.trans
      (Nat.card_prod α β)

end TauCeti

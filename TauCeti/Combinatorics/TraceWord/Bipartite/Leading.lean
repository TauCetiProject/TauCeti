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
import TauCeti.GroupTheory.Perm.Basic
import TauCeti.Combinatorics.ChordDiagram
import Mathlib.Data.Set.Card

/-!
# Leading bipartite trace words

A word of half-length `k` is leading if no edge occurs just once and the word visits
`k + 1` vertices. Each edge then occurs once in each direction. Matching the two occurrences
gives a permutation of the `k` positions. Its cycles are the column classes, and the cycles
of the rotation composed with its inverse are the row classes. The sum of the two cycle
counts is maximal, so the column partition is noncrossing.

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

private def stepIndex : Fin k ⊕ Fin k ≃ Fin (2 * k) :=
  (Equiv.sumCongr (Equiv.prodUnique (Fin k) (Fin 1)).symm
    (Equiv.prodUnique (Fin k) (Fin 1)).symm).trans
    ((Equiv.prodSumDistrib (Fin k) (Fin 1) (Fin 1)).symm.trans
    ((Equiv.prodCongr (Equiv.refl _) finSumFinEquiv).trans
      (finProdFinEquiv.trans (finCongr (Nat.mul_comm k 2)))))

private theorem stepIndex_inl_val (t : Fin k) : (stepIndex (.inl t) : ℕ) = 2 * t.val := by
  have h : finSumFinEquiv (m := 1) (n := 1) (.inl 0) = (0 : Fin 2) := rfl
  simp [stepIndex, finProdFinEquiv_apply_val, h]

private theorem stepIndex_inr_val (t : Fin k) : (stepIndex (.inr t) : ℕ) = 2 * t.val + 1 := by
  have h : finSumFinEquiv (m := 1) (n := 1) (.inr 0) = (1 : Fin 2) := rfl
  simp [stepIndex, finProdFinEquiv_apply_val, h, Nat.add_comm]

private theorem finRotate_stepIndex_inl (t : Fin k) :
    finRotate (2 * k) (stepIndex (.inl t)) = stepIndex (.inr t) := by
  have : NeZero (2 * k) := ⟨by have := t.isLt; omega⟩
  apply Fin.ext
  rw [finRotate_apply, Fin.val_add, Fin.val_one', Nat.add_mod_mod,
    stepIndex_inl_val, stepIndex_inr_val, Nat.mod_eq_of_lt]
  omega

private theorem finRotate_stepIndex_inr (t : Fin k) :
    finRotate (2 * k) (stepIndex (.inr t)) = stepIndex (.inl (finRotate k t)) := by
  have : NeZero k := t.neZero
  have : NeZero (2 * k) := ⟨by have := t.isLt; omega⟩
  apply Fin.ext
  rw [stepIndex_inl_val, finRotate_apply, finRotate_apply, Fin.val_add, Fin.val_add,
    Fin.val_one', Fin.val_one', Nat.add_mod_mod, Nat.add_mod_mod, stepIndex_inr_val]
  by_cases ht : t.val + 1 < k
  · rw [Nat.mod_eq_of_lt ht, Nat.mod_eq_of_lt (by omega)]
    omega
  · have he : t.val + 1 = k := by omega
    rw [he, Nat.mod_self, Nat.mul_zero]
    have hstep : 2 * t.val + 1 + 1 = 2 * k := by omega
    rw [hstep, Nat.mod_self]

/-- On each orientation of a leading bipartite word, the visited edges are distinct. -/
theorem IsLeadingBipartiteWord.injective_bipartiteEdge {u : Fin k → α} {v : Fin k → β}
    (h : IsLeadingBipartiteWord u v) :
    Injective (bipartiteEdge u v ∘ Sum.inl) ∧ Injective (bipartiteEdge u v ∘ Sum.inr) := by
  let w : Fin (2 * k) → α ⊕ β := Sum.map u v ∘ stepIndex.symm
  have hw (a : Fin k ⊕ Fin k) : w (stepIndex a) = Sum.map u v a :=
    congrArg (Sum.map u v) (stepIndex.symm_apply_apply a)
  have hv : univ.image w = (univ.image u).disjSum (univ.image v) := by
    ext (x | x)
    all_goals
      simp only [mem_image, mem_univ, true_and, inl_mem_disjSum, inr_mem_disjSum]
      constructor
      · rintro ⟨i, hi⟩
        obtain ⟨a, rfl⟩ := stepIndex.surjective i
        rw [hw a] at hi
        cases a <;> simp_all only [Sum.map_inl, Sum.map_inr, Sum.inl.injEq,
          Sum.inr.injEq, Sum.inl_ne_inr, Sum.inr_ne_inl]
        exact ⟨_, hi⟩
      · rintro ⟨i, rfl⟩
        first | exact ⟨stepIndex (.inl i), hw (.inl i)⟩
              | exact ⟨stepIndex (.inr i), hw (.inr i)⟩
  have hedge (a : Fin k ⊕ Fin k) :
      s(w (stepIndex a), w (finRotate (2 * k) (stepIndex a))) =
        s(Sum.inl (bipartiteEdge u v a).1, Sum.inr (bipartiteEdge u v a).2) := by
    cases a with
    | inl t => simp only [finRotate_stepIndex_inl, hw, Sum.map_inl, Sum.map_inr, bipartiteEdge_inl]
    | inr t => simp only [finRotate_stepIndex_inr, hw, Sum.map_inr, Sum.map_inl, bipartiteEdge_inr]
               exact Sym2.eq_swap
  have hword (i : Fin (2 * k)) :
      ∃ j ≠ i, s(w j, w (finRotate (2 * k) j)) = s(w i, w (finRotate (2 * k) i)) := by
    obtain ⟨a, rfl⟩ := stepIndex.surjective i
    obtain ⟨b, hba, hb⟩ := (isLeadingBipartiteWord_iff.mp h).1 a
    exact ⟨stepIndex b, stepIndex.injective.ne hba, by rw [hedge, hedge, hb]⟩
  have hd := TreeWalk.prodMk_finRotate_injective_of_no_singleton_edge_of_card_image_eq hword
    (by rw [hv, card_disjSum]; exact (isLeadingBipartiteWord_iff.mp h).2)
  constructor
  · intro i j hij
    apply Sum.inl_injective (β := Fin k) (stepIndex.injective (hd ?_))
    simpa only [finRotate_stepIndex_inl, hw, Sum.map_inl, Sum.map_inr, comp_apply,
      bipartiteEdge_inl, Prod.mk.injEq, Sum.inl.injEq, Sum.inr.injEq] using hij
  · intro i j hij
    apply Sum.inr_injective (α := Fin k) (stepIndex.injective (hd ?_))
    simpa only [finRotate_stepIndex_inr, hw, Sum.map_inr, Sum.map_inl, comp_apply,
      bipartiteEdge_inr, Prod.mk.injEq, Sum.inr.injEq, Sum.inl.injEq, and_comm] using hij

/-- For a leading word, there is a unique permutation matching each column-to-row step
to the row-to-column step on the same edge. -/
theorem IsLeadingBipartiteWord.existsUnique_perm {u : Fin k → α} {v : Fin k → β}
    (h : IsLeadingBipartiteWord u v) :
    ∃! π : Perm (Fin k), ∀ t, bipartiteEdge u v (.inl (π t)) = bipartiteEdge u v (.inr t) := by
  obtain ⟨hl, hr⟩ := h.injective_bipartiteEdge
  have hmatch (t : Fin k) :
      ∃ j, bipartiteEdge u v (.inl j) = bipartiteEdge u v (.inr t) := by
    obtain ⟨i, hne, hi⟩ := (isLeadingBipartiteWord_iff.mp h).1 (.inr t)
    cases i with
    | inl i => exact ⟨i, hi⟩
    | inr i => exact (hne (congrArg Sum.inr (hr hi))).elim
  choose f hf using hmatch
  have hfinj : Injective f := fun i j hij ↦ hr ((hf i).symm.trans (hij ▸ hf j))
  let π := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hfinj)
  exact ⟨π, hf, fun τ hτ ↦ Equiv.ext fun t ↦ hl ((hτ t).trans (hf t).symm)⟩

private theorem card_image_cycleColouring (π : Perm (Fin k))
    (f : Quotient (SameCycle.setoid π) → α) :
    #(univ.image ((invariantColouringEquiv π f).val)) = Nat.card (Set.range f) := by
  rw [Nat.card_coe_set_eq, ← Set.image_univ, ← Quotient.mk_surjective.range_eq,
    ← Set.range_comp, ← Set.image_univ, ← coe_univ, ← coe_image, Set.ncard_coe_finset]
  refine congrArg (fun h : Fin k → α ↦ #(univ.image h)) (funext fun i ↦ ?_)
  exact invariantColouringEquiv_apply_coe π f i

private theorem exists_noncrossing_cycleColourings {u : Fin k → α} {v : Fin k → β}
    (hk : k ≠ 0) (h : IsLeadingBipartiteWord u v) :
    ∃ π : NoncrossingPartition (univ : Finset (Fin k)),
      ∃ (f : Quotient (SameCycle.setoid (finRotate k * π.val.formPerm⁻¹)) ↪ α)
        (g : Quotient (SameCycle.setoid π.val.formPerm) ↪ β),
        (invariantColouringEquiv _ f).val = u ∧ (invariantColouringEquiv _ g).val = v := by
  obtain ⟨σ, hσ, _⟩ := h.existsUnique_perm
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
  have hcf := card_image_cycleColouring ρ f
  have hcg := card_image_cycleColouring σ g
  rw [hf] at hcf
  rw [hg] at hcg
  have hle : orbitCount ρ + orbitCount σ ≤ k + 1 := by
    simpa only [ρ, orbitCount_finRotate, Nat.card_fin, orbitCount_inv, ite_eq_right hk,
      Nat.add_comm] using (finRotate k).orbitCount_mul_add_orbitCount_le_orbitCount_add_card σ⁻¹
  have hboundf : #(univ.image u) ≤ orbitCount ρ := by
    rw [hcf, orbitCount_def]
    exact Nat.card_le_card_of_surjective _ Set.rangeFactorization_surjective
  have hboundg : #(univ.image v) ≤ orbitCount σ := by
    rw [hcg, orbitCount_def]
    exact Nat.card_le_card_of_surjective _ Set.rangeFactorization_surjective
  have hv := (isLeadingBipartiteWord_iff.mp h).2
  have hEq : orbitCount σ + orbitCount ρ = k + 1 := by
    omega
  have hfinj : Injective f := fun x y hxy ↦
    (Set.rangeFactorization_surjective.bijective_of_nat_card_le (f := Set.rangeFactorization f)
      (by rw [← hcf, ← orbitCount_def]; omega)).injective (Subtype.ext hxy)
  have hginj : Injective g := fun x y hxy ↦
    (Set.rangeFactorization_surjective.bijective_of_nat_card_le (f := Set.rangeFactorization g)
      (by rw [← hcg, ← orbitCount_def]; omega)).injective (Subtype.ext hxy)
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
  · rw [card_image_cycleColouring, card_image_cycleColouring,
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
    obtain ⟨σ, _, hu⟩ := hw.existsUnique_perm
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
  exact Prod.ext (funext fun i ↦ invariantColouringEquiv_apply_coe _ f i)
    (funext fun i ↦ invariantColouringEquiv_apply_coe _ g i)

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

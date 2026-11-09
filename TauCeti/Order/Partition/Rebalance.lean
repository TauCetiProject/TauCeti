/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Regularity.Equitabilise
public import TauCeti.Order.Partition.Equiv
public import TauCeti.Data.Fintype.Matching

/-!
# Rebalancing a finite partition

A partition can be made equitable without changing its number of cells. The cells are
matched by a bijection, and the number of vertices leaving their matched cell is bounded
by the total surplus above the floor of the mean cell size.

If every original cell has size at most `m`, the number moved is at most
`t * m - n + t`, where `t` is the number of cells and `n` the host size. In particular,
restricting an equal-cell partition on `t * m` vertices to `n` vertices, with every cell
remaining nonempty, requires moving at most the number of deleted vertices plus `t`.
This is the quantitative rebalancing step in padding-and-restriction arguments for
hypergraph regularity.

The construction uses Mathlib's `Finpartition.exists_equipartition_card_eq` and a permutation
matching of cell labels. Regularity is not asserted to survive moving the vertices;
the bound supplies the exceptional set for the corresponding stability estimates.
-/

public section

open Finset Function

namespace Finpartition

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Rebalance a partition with a bijection between old and new cells. The total number of
vertices leaving their matched cell is bounded by the surplus above the floor mean size. -/
theorem exists_equipartition_sum_card_sdiff_le (P : Finpartition (univ : Finset V)) :
    ∃ (Q : Finpartition (univ : Finset V)) (e : P.parts ≃ Q.parts),
      Q.IsEquipartition ∧
      ∑ A : P.parts, #(A.1 \ (e A).1) ≤
        ∑ A : P.parts, (#A.1 - Fintype.card V / #P.parts) := by
  classical
  by_cases hV : IsEmpty V
  · have := hV
    refine ⟨P, Equiv.refl _, ?_, by simp⟩
    intro A B hA hB
    simp only [Subsingleton.elim A ∅, Subsingleton.elim B ∅, card_empty]
    omega
  have : Nonempty V := not_isEmpty_iff.mp hV
  obtain ⟨Q₀, hQ₀, hcard⟩ := exists_equipartition_card_eq (univ : Finset V)
    (card_ne_zero.mpr (P.parts_nonempty (univ_nonempty.ne_empty)))
    (P.card_parts_le_card.trans_eq (card_univ))
  let e₀ : P.parts ≃ Q₀.parts := Fintype.equivOfCardEq (by simpa using hcard.symm)
  let f (x : V) : P.parts := ⟨P.part x, P.part_mem.2 (mem_univ x)⟩
  let g (x : V) : P.parts := e₀.symm ⟨Q₀.part x, Q₀.part_mem.2 (mem_univ x)⟩
  obtain ⟨σ, hσ⟩ := exists_perm_card_filter_ne_le f g
  let Q := (Q₀.copy (image_univ_equiv σ).symm).comap σ
  let e := e₀.trans (Q₀.partsComapEquiv σ)
  refine ⟨Q, e, (isEquipartition_comap_equiv_iff Q₀ σ).2 hQ₀, ?_⟩
  have hf (A : P.parts) : occCount f A = #A.1 := by
    rw [occCount_eq_card_filter]
    congr 1
    ext x
    simp [f, Subtype.ext_iff, P.part_eq_iff_mem A.2]
  have hg (A : P.parts) : Fintype.card V / #P.parts ≤ occCount g A := by
    have hcount : occCount g A = #(e₀ A).1 := by
      rw [occCount_eq_card_filter]
      congr 1
      ext x
      simp [g, e₀.symm_apply_eq, Subtype.ext_iff, Q₀.part_eq_iff_mem (e₀ A).2]
    rw [hcount, ← hcard, ← card_univ]
    exact hQ₀.average_le_card_part (e₀ A).2
  have hcost : ∑ A : P.parts, #(A.1 \ (e A).1) = #{x | f x ≠ g (σ x)} := by
    rw [card_eq_sum_card_fiberwise (f := f) (t := univ) (fun _ _ ↦ mem_univ _)]
    refine sum_congr rfl fun A _ ↦ ?_
    congr 1
    ext x
    simp only [mem_sdiff, e, Equiv.trans_apply, partsComapEquiv_apply_coe,
      mem_map_equiv, Equiv.symm_symm, mem_filter, mem_univ, true_and]
    have hfx : f x = A ↔ x ∈ A.1 := by
      simp [f, Subtype.ext_iff, P.part_eq_iff_mem A.2]
    have hgx : g (σ x) = A ↔ σ x ∈ (e₀ A).1 := by
      simp [g, e₀.symm_apply_eq, Subtype.ext_iff, Q₀.part_eq_iff_mem (e₀ A).2]
    grind
  rw [hcost]
  exact hσ.trans (sum_le_sum fun A _ ↦ by rw [hf]; exact Nat.sub_le_sub_left (hg A) _)

/-- If cells have size at most `m`, rebalancing moves at most the missing mass from `t`
equal cells of size `m`, plus the remainder of the host size modulo `t`. The bijection `e`
preserves the number of cells, including for the empty host. -/
theorem exists_equipartition_sum_card_sdiff_le_of_card_le
    (P : Finpartition (univ : Finset V)) {m : ℕ} (hm : ∀ A ∈ P.parts, #A ≤ m) :
    ∃ (Q : Finpartition (univ : Finset V)) (e : P.parts ≃ Q.parts),
      Q.IsEquipartition ∧
      ∑ A : P.parts, #(A.1 \ (e A).1) ≤
        #P.parts * m - Fintype.card V + Fintype.card V % #P.parts := by
  obtain ⟨Q, e, hQ, hcost⟩ := P.exists_equipartition_sum_card_sdiff_le
  refine ⟨Q, e, hQ, hcost.trans ?_⟩
  have htotal : Fintype.card V ≤ #P.parts * m := by
    rw [← card_univ, ← P.sum_card_parts]
    exact (sum_le_sum hm).trans_eq (by simp)
  calc ∑ A : P.parts, (#A.1 - Fintype.card V / #P.parts)
      ≤ ∑ _A : P.parts, (m - Fintype.card V / #P.parts) :=
        sum_le_sum fun A _ ↦ Nat.sub_le_sub_right (hm A.1 A.2) _
    _ = #P.parts * m - Fintype.card V + Fintype.card V % #P.parts := by
      simp only [sum_const, nsmul_eq_mul, card_univ, Fintype.card_coe, Nat.cast_id, Nat.mul_sub]
      have hdiv := Nat.mod_add_div (Fintype.card V) #P.parts
      omega

end Finpartition

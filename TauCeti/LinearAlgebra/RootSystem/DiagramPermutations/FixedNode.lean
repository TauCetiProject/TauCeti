/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.DiagramPermutations.Basic
public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Diagram
import TauCeti.GroupTheory.Perm.Fin
import TauCeti.LinearAlgebra.RootSystem.DiagramPermutations.NonSimplyLaced

/-!
# Fixed nodes of the numbered diagram symmetries

Every symmetry of a Bourbaki-numbered Dynkin diagram of a valid type fixes a node, with one
exception: the reversal of the chain `A₂ₙ`, whose middle edge it inverts. This file proves this
node by node.

* The symmetries of `Aₙ` are the identity and the reversal `TauCeti.graphPermA n`; the reversal
  fixes the middle node of a chain with an odd number of nodes.
* A symmetry of `Dₙ` (`n ≥ 4`), `E₆`, `E₇` or `E₈` fixes the branch node, the only node with three
  neighbours.
* The nonsimply-laced diagrams have no nontrivial symmetry
  (`TauCeti.DynkinType.diagramSymmetry_eq_bot_of_not_isSimplyLaced`).

A fixed node is what makes the orbits of a diagram symmetry on a tree consist of pairwise
nonadjacent nodes, since such a symmetry preserves the distance to the fixed node; this is the
orthogonality condition on simple orbits in Stembridge's construction of folded root systems.

## Main results

* `TauCeti.DynkinType.mem_diagramSymmetry_A_iff`: the diagram symmetries of `Aₙ` are the identity
  and the reversal.
* `TauCeti.graphPermA_apply_middle`: the reversal of `A₂ₙ₊₁` fixes the middle node, whereas
  the reversal of `A₂ₙ` fixes no node (`TauCeti.graphPermA_apply_ne_self`) and inverts the middle
  edge and no other (`TauCeti.diagramGraph_A_adj_graphPermA_iff`).
* `TauCeti.DynkinType.apply_eq_self_of_mem_diagramSymmetry_D`,
  `TauCeti.DynkinType.apply_eq_self_of_cartanMatrix_E`: a diagram symmetry of `Dₙ` or of `Eₙ`
  fixes the branch node.
* `TauCeti.DynkinType.exists_apply_eq_self_of_mem_diagramSymmetry`: every diagram symmetry of a
  valid type other than `A₂ₙ` fixes a node.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4–6*, plates I–IX.
* J. R. Stembridge, *Folding by automorphisms*, note of 20 August 2008, condition (1).
-/

public section

namespace TauCeti

/-- A permutation preserving the entries of an integer matrix fixes a node of its diagram which is
the only node with three distinct neighbours. -/
private theorem apply_eq_self_of_three_neighbours {B : Type*} {A : Matrix B B ℤ}
    {ρ : Equiv.Perm B} (hρ : ∀ i j, A (ρ i) (ρ j) = A i j) {v a b c : B} (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) (ha : (diagramGraph A).Adj v a) (hb : (diagramGraph A).Adj v b)
    (hc : (diagramGraph A).Adj v c)
    (huniq : ∀ w a b c, a ≠ b → a ≠ c → b ≠ c → (diagramGraph A).Adj w a →
      (diagramGraph A).Adj w b → (diagramGraph A).Adj w c → w = v) :
    ρ v = v :=
  huniq _ (ρ a) (ρ b) (ρ c) (ρ.injective.ne hab) (ρ.injective.ne hac) (ρ.injective.ne hbc)
    ((diagramGraph_adj_apply_iff hρ).mpr ha) ((diagramGraph_adj_apply_iff hρ).mpr hb)
    ((diagramGraph_adj_apply_iff hρ).mpr hc)

/-- **The reversal of a chain with an odd number of nodes fixes its middle node.** -/
@[simp]
theorem graphPermA_apply_middle (m : ℕ) :
    graphPermA (2 * m + 1) ⟨m, by omega⟩ = ⟨m, by omega⟩ := by
  ext
  simp only [graphPermA_apply, Fin.val_rev]
  omega

/-- The reversal of a chain with an even number of nodes fixes no node. -/
theorem graphPermA_apply_ne_self (m : ℕ) (i : Fin (2 * m)) : graphPermA (2 * m) i ≠ i := by
  rw [graphPermA_apply, Ne, Fin.ext_iff, Fin.val_rev]
  omega

/-- **The reversal of `A₂ₘ` inverts the middle edge and no other.** A node of the chain is joined
to its mirror image exactly when it is one of the two middle nodes `m - 1` and `m`. -/
theorem diagramGraph_A_adj_graphPermA_iff (m : ℕ) (i : Fin (2 * m)) :
    (diagramGraph (CartanMatrix.A (2 * m))).Adj i (graphPermA (2 * m) i) ↔
      (i : ℕ) + 1 = m ∨ (i : ℕ) = m := by
  rw [DynkinType.diagramGraph_cartanMatrix_A, SimpleGraph.pathGraph_adj, graphPermA_apply,
    Fin.val_rev]
  omega

namespace DynkinType

variable {n : ℕ}

/-- **The diagram symmetries of `Aₙ` are the identity and the reversal of the chain.** -/
theorem mem_diagramSymmetry_A_iff {ρ : Equiv.Perm (Fin n)} :
    ρ ∈ (A n).diagramSymmetry ↔ ρ = 1 ∨ ρ = graphPermA n := by
  refine ⟨fun hρ ↦ ?_, ?_⟩
  · have hadj (i j : Fin n) : ((ρ i : ℕ) + 1 = ρ j ∨ (ρ j : ℕ) + 1 = ρ i) ↔
        ((i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i) := by
      rw [← diagramGraph_A_adj, ← diagramGraph_A_adj]
      exact diagramGraph_adj_apply_iff (mem_diagramSymmetry_iff.mp hρ)
    obtain _ | m := n
    · exact Or.inl (Subsingleton.elim _ _)
    -- The last node has at most one neighbour, so its image is an end of the chain.
    have hend : (ρ (Fin.last m) : ℕ) = m ∨ (ρ (Fin.last m) : ℕ) = 0 := by
      by_contra! hx
      obtain ⟨hx₁, hx₂⟩ := hx
      set x := ρ (Fin.last m)
      have hlt : (x : ℕ) < m := by have := x.2; omega
      have hp := (hadj (Fin.last m) (ρ.symm ⟨x - 1, by omega⟩)).mp (by simp; omega)
      have hq := (hadj (Fin.last m) (ρ.symm ⟨x + 1, by omega⟩)).mp (by simp; omega)
      have hpq : ρ.symm ⟨x - 1, by omega⟩ = ρ.symm ⟨x + 1, by omega⟩ := by
        ext
        simp only [Fin.val_last] at hp hq
        omega
      have := congrArg Fin.val (ρ.symm.injective hpq)
      simp only at this
      omega
    rcases hend with hlast | hzero
    · left
      exact Equiv.Perm.eq_one_of_adjacent_of_apply_last_eq_self
        (fun i j hij ↦ (hadj i j).mpr (Or.inl hij)) (Fin.ext hlast)
    · right
      -- Composing with the reversal gives a symmetry fixing the last node.
      have hone : graphPermA (m + 1) * ρ = 1 := by
        refine Equiv.Perm.eq_one_of_adjacent_of_apply_last_eq_self (fun i j hij ↦ ?_) ?_
        · have := (hadj i j).mpr (Or.inl hij)
          simp only [Equiv.Perm.coe_mul, Function.comp_apply, graphPermA_apply, Fin.val_rev]
          have := (ρ i).2
          have := (ρ j).2
          omega
        · ext
          simp only [Equiv.Perm.coe_mul, Function.comp_apply, graphPermA_apply, Fin.val_rev,
            hzero, Fin.val_last]
          omega
      rw [eq_inv_of_mul_eq_one_right hone, Equiv.Perm.inv_def, graphPermA_symm]
  · rintro (rfl | rfl)
    · exact (A n).diagramSymmetry.one_mem
    · exact mem_diagramSymmetry_iff.mpr (cartanMatrix_A_graphPermA n)

/-- From rank four on, the branch node `n - 3` of the `Dₙ` diagram is the only node with three
distinct neighbours, so every diagram symmetry of `Dₙ` fixes it. -/
theorem apply_eq_self_of_mem_diagramSymmetry_D (hn : 4 ≤ n) {ρ : Equiv.Perm (Fin n)}
    (hρ : ρ ∈ (D n).diagramSymmetry) : ρ ⟨n - 3, by omega⟩ = ⟨n - 3, by omega⟩ := by
  have hadj := diagramGraph_D_adj (n := n) (by omega)
  refine apply_eq_self_of_three_neighbours (B := Fin n) (mem_diagramSymmetry_iff.mp hρ)
    (a := ⟨n - 4, by omega⟩) (b := ⟨n - 2, by omega⟩) (c := ⟨n - 1, by omega⟩)
    (by simp [Fin.ext_iff]; omega) (by simp [Fin.ext_iff]; omega) (by simp [Fin.ext_iff]; omega)
    ((hadj _ _).mpr (by simp; omega)) ((hadj _ _).mpr (by simp; omega))
    ((hadj _ _).mpr (by simp; omega)) fun w a b c hab hac hbc ha hb hc ↦ ?_
  rw [hadj] at ha hb hc
  simp only [ne_eq, Fin.ext_iff] at hab hac hbc ⊢
  omega

/-- From rank five on, the branch node `3` of the `Eₙ` diagram is the only node with three
distinct neighbours, so every permutation preserving the `Eₙ` Cartan matrix fixes it. -/
theorem apply_eq_self_of_cartanMatrix_E (hn : 5 ≤ n) {ρ : Equiv.Perm (Fin n)}
    (hρ : ∀ i j, CartanMatrix.E n (ρ i) (ρ j) = CartanMatrix.E n i j) :
    ρ ⟨3, by omega⟩ = ⟨3, by omega⟩ := by
  refine apply_eq_self_of_three_neighbours hρ
    (a := ⟨1, by omega⟩) (b := ⟨2, by omega⟩) (c := ⟨4, by omega⟩)
    (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff])
    ((diagramGraph_E_adj _ _).mpr (by simp)) ((diagramGraph_E_adj _ _).mpr (by simp))
    ((diagramGraph_E_adj _ _).mpr (by simp)) fun w a b c hab hac hbc ha hb hc ↦ ?_
  rw [diagramGraph_E_adj] at ha hb hc
  simp only [ne_eq, Fin.ext_iff] at hab hac hbc ⊢
  omega

/-- **Every diagram symmetry of a valid Dynkin type other than `A₂ₙ` fixes a node**: the middle
node or every node for `A₂ₙ₊₁`, the branch node for `Dₙ`, `E₆`, `E₇` and `E₈`, and every node for
the nonsimply-laced types, which have no nontrivial symmetry. -/
theorem exists_apply_eq_self_of_mem_diagramSymmetry {t : DynkinType} (ht : t.Valid)
    (hA : ∀ n, t ≠ A (2 * n)) {ρ : Equiv.Perm (Fin t.rank)} (hρ : ρ ∈ t.diagramSymmetry) :
    ∃ x, ρ x = x := by
  by_cases hsl : t.IsSimplyLaced
  · have hρ' := mem_diagramSymmetry_iff.mp hρ
    cases t with
    | A n =>
      obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
      · exact absurd rfl (hA m)
      rcases mem_diagramSymmetry_A_iff.mp hρ with rfl | rfl
      · exact ⟨⟨0, by simp⟩, rfl⟩
      · exact ⟨_, graphPermA_apply_middle m⟩
    | D n => exact ⟨_, apply_eq_self_of_mem_diagramSymmetry_D (valid_D.mp ht) hρ⟩
    | E6 => exact ⟨_, apply_eq_self_of_cartanMatrix_E (by norm_num) (by simpa using hρ')⟩
    | E7 => exact ⟨_, apply_eq_self_of_cartanMatrix_E (by norm_num) (by simpa using hρ')⟩
    | E8 => exact ⟨_, apply_eq_self_of_cartanMatrix_E (by norm_num) (by simpa using hρ')⟩
    | B _ | C _ | F4 | G2 => simp at hsl
  · rw [diagramSymmetry_eq_bot_of_not_isSimplyLaced hsl, Subgroup.mem_bot] at hρ
    exact ⟨⟨0, rank_pos ht⟩, by simp [hρ]⟩

end DynkinType

end TauCeti

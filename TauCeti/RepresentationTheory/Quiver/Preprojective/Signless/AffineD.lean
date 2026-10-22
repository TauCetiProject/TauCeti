/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.SimpleGraph.Copy
public import TauCeti.LinearAlgebra.RootSystem.AffineDynkinType.Basic
public import TauCeti.RepresentationTheory.Quiver.Preprojective.Signless.MatrixRepresentation

/-!
# Nonzero cyclic classes from affine `Dₙ` subgraphs

Let `G` be a finite simple graph containing a copy of the affine diagram `Dₙ` (`n ≥ 4`), not
necessarily induced. This file shows that the cyclic quotient `Π⁺(G) / [Π⁺(G), Π⁺(G)]` of the
signless preprojective algebra of `G`, its zeroth Hochschild homology, is nonzero in path degree
four, over every nontrivial commutative ring. For a bipartite graph, such as a tree, `Π⁺(G)` is
isomorphic to the additive preprojective algebra of any orientation of `G` by a rescaling of the
arrows by signs (`SimpleGraph.IsBipartite.signlessPreprojectiveAlgebraEquiv`).

For a quiver `Q` whose underlying graph is a tree (bipartite, so `Π⁺` is the additive `Π(Q)`),
Liu and Wang identify the degree-`(q + 2)` piece of this cyclic quotient with the second
Hochschild cohomology `HH^{2,q}` of the two-dimensional Ginzburg algebra `Π₂(Q)`, which controls
the `A∞` deformations of the zigzag algebra of the tree. For the preprojective algebra of a Dynkin
quiver over a field of characteristic zero, the cyclic quotient is concentrated in degree zero
(Etingof--Eu). The present computation exhibits a positive-degree class for every graph
containing an affine `Dₙ`, for instance for every tree with a vertex of degree at least four or
with two vertices of degree at least three.

## The representation

Label `Dₙ` as in `TauCeti.AffineDynkinType.graph`: the path `0 - 1 - ⋯ - (n - 2)`, with a leaf
`n - 1` at node `1` and a leaf `n` at node `n - 3`. Put `k²` at every node and assign the
following matrices to the arrows, writing `Eᵢⱼ` for the matrix units,
`J = E₂₁ - E₁₂` and `D = E₁₁ - E₂₂`:

```text
0 → 1 : E₁₁      1 → 0 : E₁₂          (n-1) → 1 : E₂₂     1 → (n-1) : E₂₁
i → i+1 : J      i+1 → i : D          for 1 ≤ i < n - 3
(n-2) → (n-3) : -E₁₁   (n-3) → (n-2) : E₁₂    n → (n-3) : -E₂₂   (n-3) → n : E₂₁
```

At node `1` the two leaves contribute the backtracks `E₁₂` and `E₂₁`, whose sum is the swap
matrix `N = E₁₂ + E₂₁`. Along each path edge the backtracks are `D J = -N` at its lower end and
`J D = N` at its upper end, so the relations hold along the path, and at node `n - 3` the two
remaining leaves contribute `-E₁₂ - E₂₁ = -N`. Every backtrack at a leaf is zero. The resulting
representation of `Π⁺(Dₙ)` extends by zero to `Π⁺(G)` along the copy.

The walk `1 → 0 → 1 → (n - 1) → 1` at the branch node, the product of the backtrack through the
leaf `n - 1` and the backtrack through the leaf `0`, acts at node `1` by `E₂₁ E₁₂ = E₂₂`, of
trace one. Since the trace of a representation vanishes on commutators, the class of this walk in
the cyclic quotient is nonzero.

## Main results

* `TauCeti.exists_mem_signlessPreprojectiveGrade_four_notMem_commutatorSubmodule`: if `G`
  contains a copy of the affine diagram `Dₙ`, some element of path degree four of `Π⁺(G)` does not
  lie in `[Π⁺(G), Π⁺(G)]`.

## References

* Y. Liu and Z. Wang, *A-infinity deformations of zigzag algebras via Ginzburg dg algebras*,
  https://arxiv.org/abs/2301.06757, for the role of the cyclic quotient of the preprojective
  algebra.
* P. Etingof and C.-H. Eu, *Hochschild and cyclic homology of preprojective algebras of ADE
  quivers*, Mosc. Math. J. 7 (2007), https://arxiv.org/abs/math/0609006, for the cyclic quotient
  of the preprojective algebra of a Dynkin quiver.
-/

public section

namespace TauCeti

open _root_.Quiver PathAlgebra DoubledQuiver _root_.Matrix
open scoped Kronecker

universe u w

variable (k : Type w) [CommRing k]

/-- The matrix assigned to the arrow `i → j` of the doubled affine diagram `Dₙ` by the
representation of this file, with nodes given as natural numbers in the labelling of
`TauCeti.AffineDynkinType.graph`; it is zero unless `i` and `j` are adjacent. -/
private noncomputable def affineDMatrix (n i j : ℕ) : Matrix (Fin 2) (Fin 2) k :=
  if i = 0 ∧ j = 1 then !![1, 0; 0, 0]
  else if i = 1 ∧ j = 0 then !![0, 1; 0, 0]
  else if i = n - 1 ∧ j = 1 then !![0, 0; 0, 1]
  else if i = 1 ∧ j = n - 1 then !![0, 0; 1, 0]
  else if i = n - 2 ∧ j = n - 3 then !![-1, 0; 0, 0]
  else if i = n - 3 ∧ j = n - 2 then !![0, 1; 0, 0]
  else if i = n ∧ j = n - 3 then !![0, 0; 0, -1]
  else if i = n - 3 ∧ j = n then !![0, 0; 1, 0]
  else if 1 ≤ i ∧ i + 1 = j ∧ j ≤ n - 3 then !![0, -1; 1, 0]
  else if 1 ≤ j ∧ j + 1 = i ∧ i ≤ n - 3 then !![1, 0; 0, -1]
  else 0

/-! ### Evaluating the matrices -/

section Evaluation

variable {k} {n i j : ℕ} (hn : 4 ≤ n)

include hn

private theorem affineDMatrix_zero_one (hi : i = 0) (hj : j = 1) :
    affineDMatrix k n i j = !![1, 0; 0, 0] := by
  unfold affineDMatrix; split_ifs <;> first | rfl | omega

private theorem affineDMatrix_one_zero (hi : i = 1) (hj : j = 0) :
    affineDMatrix k n i j = !![0, 1; 0, 0] := by
  unfold affineDMatrix; split_ifs <;> first | rfl | omega

private theorem affineDMatrix_last_one (hi : i = n - 1) (hj : j = 1) :
    affineDMatrix k n i j = !![0, 0; 0, 1] := by
  unfold affineDMatrix; split_ifs <;> first | rfl | omega

private theorem affineDMatrix_one_last (hi : i = 1) (hj : j = n - 1) :
    affineDMatrix k n i j = !![0, 0; 1, 0] := by
  unfold affineDMatrix; split_ifs <;> first | rfl | omega

private theorem affineDMatrix_sub_two_sub_three (hi : i = n - 2) (hj : j = n - 3) :
    affineDMatrix k n i j = !![-1, 0; 0, 0] := by
  unfold affineDMatrix; split_ifs <;> first | rfl | omega

private theorem affineDMatrix_sub_three_sub_two (hi : i = n - 3) (hj : j = n - 2) :
    affineDMatrix k n i j = !![0, 1; 0, 0] := by
  unfold affineDMatrix; split_ifs <;> first | rfl | omega

private theorem affineDMatrix_self_sub_three (hi : i = n) (hj : j = n - 3) :
    affineDMatrix k n i j = !![0, 0; 0, -1] := by
  unfold affineDMatrix; split_ifs <;> first | rfl | omega

private theorem affineDMatrix_sub_three_self (hi : i = n - 3) (hj : j = n) :
    affineDMatrix k n i j = !![0, 0; 1, 0] := by
  unfold affineDMatrix; split_ifs <;> first | rfl | omega

private theorem affineDMatrix_succ (hi : 1 ≤ i) (hj : i + 1 = j) (hjn : j ≤ n - 3) :
    affineDMatrix k n i j = !![0, -1; 1, 0] := by
  unfold affineDMatrix; split_ifs <;> first | rfl | omega

private theorem affineDMatrix_pred (hj : 1 ≤ j) (hi : j + 1 = i) (hin : i ≤ n - 3) :
    affineDMatrix k n i j = !![1, 0; 0, -1] := by
  unfold affineDMatrix; split_ifs <;> first | rfl | omega

end Evaluation

/-- **The affine `Dₙ` matrices satisfy the signless relations**: at every node `v` of `Dₙ`, the
backtracks `β w v * β v w` over the neighbours `w` of `v` sum to zero. -/
private theorem sum_affineDMatrix_mul_affineDMatrix {n : ℕ} (hn : 4 ≤ n)
    (v : Fin (AffineDynkinType.D n).nodes) :
    ∑ w ∈ (AffineDynkinType.D n).graph.neighborFinset v,
      affineDMatrix k n w v * affineDMatrix k n v w = 0 := by
  have hv : (v : ℕ) < n + 1 := v.isLt.trans_eq (AffineDynkinType.nodes_D n)
  -- Each node supplies its list of neighbours. The list is `Nodup` and lists exactly the
  -- neighbours, both checked by the default arguments, leaving the sum of backtracks along it.
  have of_list (l : List (Fin (AffineDynkinType.D n).nodes))
      (h0 : (l.map fun w : Fin (AffineDynkinType.D n).nodes =>
        affineDMatrix k n w v * affineDMatrix k n v w).sum = 0)
      (hl : l.Nodup := by
        simp only [List.nodup_cons, List.nodup_nil, List.mem_cons, List.not_mem_nil, or_false,
          not_false_eq_true, and_true, Fin.ext_iff] <;> omega)
      (hs : ∀ w : Fin (AffineDynkinType.D n).nodes,
        (((v : ℕ) + 1 = (w : ℕ) ∧ (w : ℕ) ≤ n - 2) ∨ ((w : ℕ) + 1 = (v : ℕ) ∧ (v : ℕ) ≤ n - 2) ∨
          ((v : ℕ) = 1 ∧ (w : ℕ) = n - 1) ∨ ((w : ℕ) = 1 ∧ (v : ℕ) = n - 1) ∨
          ((v : ℕ) = n - 3 ∧ (w : ℕ) = n) ∨ ((w : ℕ) = n - 3 ∧ (v : ℕ) = n)) ↔ w ∈ l := by
        intro w
        simp only [List.mem_cons, List.not_mem_nil, or_false, Fin.ext_iff]
        omega) :
      ∑ w ∈ (AffineDynkinType.D n).graph.neighborFinset v,
        affineDMatrix k n w v * affineDMatrix k n v w = 0 := by
    rw [show (AffineDynkinType.D n).graph.neighborFinset v = l.toFinset from
      Finset.ext fun w => by
        rw [SimpleGraph.mem_neighborFinset, List.mem_toFinset]
        exact (AffineDynkinType.graph_D_adj hn (i := v) (j := w)).trans (hs w),
      List.sum_toFinset _ hl]
    exact h0
  -- The node roles: the leaf `0`, the branch node `1` of the star `D₄`, the branch node `1` for
  -- `n ≥ 5`, an interior path node, the branch node `n - 3` for `n ≥ 5`, and the leaves `n - 2`,
  -- `n - 1` and `n`.
  have hnodes := AffineDynkinType.nodes_D n
  rcases (by omega : (v : ℕ) = 0 ∨ ((v : ℕ) = 1 ∧ n = 4) ∨ ((v : ℕ) = 1 ∧ 5 ≤ n) ∨
      (2 ≤ (v : ℕ) ∧ (v : ℕ) ≤ n - 4) ∨ ((v : ℕ) = n - 3 ∧ 5 ≤ n) ∨ (v : ℕ) = n - 2 ∨
      (v : ℕ) = n - 1 ∨ (v : ℕ) = n) with
    h | h | h | h | h | h | h | h <;>
  [refine of_list [⟨1, by omega⟩] ?_;
    refine of_list [⟨0, by omega⟩, ⟨2, by omega⟩, ⟨3, by omega⟩, ⟨4, by omega⟩] ?_;
    refine of_list [⟨0, by omega⟩, ⟨2, by omega⟩, ⟨n - 1, by omega⟩] ?_;
    refine of_list [⟨(v : ℕ) - 1, by omega⟩, ⟨(v : ℕ) + 1, by omega⟩] ?_;
    refine of_list [⟨n - 4, by omega⟩, ⟨n - 2, by omega⟩, ⟨n, by omega⟩] ?_;
    refine of_list [⟨n - 3, by omega⟩] ?_;
    refine of_list [⟨1, by omega⟩] ?_;
    refine of_list [⟨n - 3, by omega⟩] ?_]
  -- Evaluate the matrices along the list and compare entries.
  all_goals
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    simp (disch := omega) only [affineDMatrix_zero_one hn, affineDMatrix_one_zero hn,
      affineDMatrix_last_one hn, affineDMatrix_one_last hn, affineDMatrix_sub_two_sub_three hn,
      affineDMatrix_sub_three_sub_two hn, affineDMatrix_self_sub_three hn,
      affineDMatrix_sub_three_self hn, affineDMatrix_succ hn, affineDMatrix_pred hn]
    simp only [mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp

variable {k} {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- **Graphs containing an affine `Dₙ` have nonzero cyclic classes in degree four.** If `G`
contains a copy of the affine diagram `Dₙ`, not necessarily induced, then over every nontrivial
commutative ring some element of path degree four of the signless preprojective algebra `Π⁺(G)`
does not lie in the commutator submodule `[Π⁺(G), Π⁺(G)]`: its class in the cyclic quotient is
nonzero.

The element is the closed walk `1 → 0 → 1 → (n - 1) → 1` at the image of the branch node `1`;
its image under the representation of this file has trace one. -/
theorem exists_mem_signlessPreprojectiveGrade_four_notMem_commutatorSubmodule [Nontrivial k]
    {n : ℕ} (hn : 4 ≤ n) (hG : (AffineDynkinType.D n).graph.IsContained G) :
    ∃ x ∈ signlessPreprojectiveGrade k (DoubledQuiver G) 4,
      x ∉ commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G)) := by
  classical
  obtain ⟨f⟩ := hG
  have hnodes := AffineDynkinType.nodes_D n
  let c : Fin (AffineDynkinType.D n).nodes := ⟨1, by omega⟩
  let l₁ : Fin (AffineDynkinType.D n).nodes := ⟨0, by omega⟩
  let l₂ : Fin (AffineDynkinType.D n).nodes := ⟨n - 1, by omega⟩
  have h₁ : (AffineDynkinType.D n).graph.Adj c l₁ :=
    (AffineDynkinType.graph_D_adj hn (i := c) (j := l₁)).2
      (Or.inr (Or.inl ⟨rfl, show 1 ≤ n - 2 by omega⟩))
  have h₂ : (AffineDynkinType.D n).graph.Adj c l₂ :=
    (AffineDynkinType.graph_D_adj hn (i := c) (j := l₂)).2 (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
  let β : Fin (AffineDynkinType.D n).nodes → Fin (AffineDynkinType.D n).nodes →
      Matrix (Fin 2) (Fin 2) k :=
    fun i j => affineDMatrix k n i j
  have hβ := f.sum_extendByZero_mul_extendByZero β
    (sum_affineDMatrix_mul_affineDMatrix k hn)
  refine ⟨signlessPreprojectiveMk k _
    (backtrackElem G k (f.toHom.map_adj h₂) * backtrackElem G k (f.toHom.map_adj h₁)), ?_,
    fun hx => ?_⟩
  · have harrow {i j : DoubledQuiver G} (e : i ⟶ j) :=
      signlessPreprojectiveMk_mem_grade k (DoubledQuiver G) (ofArrow_mem_grade_one (k := k) e)
    simp only [← ofArrow_symm_mul_ofArrow, map_mul]
    exact mul_mem_signlessPreprojectiveGrade k _ (m := 2) (n := 2)
      (mul_mem_signlessPreprojectiveGrade k _ (harrow _) (harrow _))
      (mul_mem_signlessPreprojectiveGrade k _ (harrow _) (harrow _))
  · have htrace := trace_map_eq_zero_of_mem_commutatorSubmodule
      (signlessMatrixRepresentation k (f.extendByZero β) hβ) hx
    rw [trace_signlessMatrixRepresentation_backtrackElem_mul_backtrackElem] at htrace
    simp only [SimpleGraph.Copy.toHom_apply, SimpleGraph.Copy.extendByZero_apply_apply_of_adj,
      h₁, h₂, h₁.symm, h₂.symm, β, c, l₁, l₂] at htrace
    simp (disch := omega) only [affineDMatrix_zero_one hn, affineDMatrix_one_zero hn,
      affineDMatrix_last_one hn, affineDMatrix_one_last hn] at htrace
    simp [Matrix.trace_fin_two] at htrace

end TauCeti

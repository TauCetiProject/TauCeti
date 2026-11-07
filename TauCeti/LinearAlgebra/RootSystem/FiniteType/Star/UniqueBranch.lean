/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.FiniteType.AffineD
public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Diagram
import TauCeti.Combinatorics.SimpleGraph.Degree

/-!
# A simply-laced finite-type diagram has at most one branch vertex

The simply-laced lane of the finite-type Cartan-matrix classification reduces connected diagrams
to paths and three-armed stars. Two branch vertices in a tree determine a double-fork subtree: the
path between them, together with the two unused edges at either end, has affine type `D`, whose
Cartan matrix is incompatible with finite type.

This file makes that reduction at the matrix level. Given two distinct degree-three vertices in
the same component, `TauCeti.IsFiniteType.exists_doubleFork_submatrix` extracts the corresponding
principal submatrix and identifies it with `TauCeti.doubleForkCartanMatrix`. The latter is not of
finite type, contradicting inheritance of finite type by principal submatrices. Consequently a
connected simply-laced finite-type diagram has a unique branch vertex whenever one exists.

The simple-lacedness hypothesis is essential at this stage: it identifies every edge on the path
with the entry `-1`. The componentwise results impose it only on the vertices reachable from the
first branch vertex, which is where the whole extracted submatrix lives. The separate
multiple-edge elimination in the classification removes this hypothesis before the final assembly
theorem.

## Main results

* `TauCeti.IsFiniteType.exists_doubleFork_submatrix`: two distinct branch vertices in one
  simply-laced component contain an affine `D` principal submatrix.
* `TauCeti.IsFiniteType.eq_of_reachable_of_degree_eq_three`: two reachable degree-three vertices
  coincide.
* `TauCeti.IsFiniteType.eq_of_degree_eq_three`: the connected specialization.

## References

This is the affine-`D` elimination in the “classification of finite-type Cartan matrices” target,
Layer 5 of `TauCetiRoadmap/RepresentationTheory/RootSystems/README.md`. See J. E. Humphreys,
*Introduction to Lie Algebras and Representation Theory*, §11.4, and Bourbaki, *Lie Groups and Lie
Algebras, Chapters 4--6*, Ch. VI, §4.
-/

public section

namespace TauCeti

namespace IsFiniteType

variable {B : Type*} [DecidableEq B] {A : Matrix B B ℤ}

omit [DecidableEq B] in
private lemma matrix_apply_eq_neg_one_iff_adj (h : IsFiniteType A) {i j : B} (hij : i ≠ j)
    (hsl : A i j = 0 ∨ A i j = -1) :
    A i j = -1 ↔ (diagramGraph A).Adj i j := by
  rw [h.diagramGraph_adj_iff]
  constructor
  · exact fun hij' ↦ ⟨hij, by omega⟩
  · rintro ⟨-, hij'⟩
    rcases hsl with hij0 | hij1
    · exact (hij' hij0).elim
    · exact hij1

private lemma adj_getVert_iff_succ {V : Type*} {G : SimpleGraph V} {u v : V}
    {p : G.Walk u v} (hG : G.IsAcyclic) (hp : p.IsPath) {i j : ℕ}
    (hi : i ≤ p.length) (hj : j ≤ p.length) (hij : i ≠ j) :
    G.Adj (p.getVert i) (p.getVert j) ↔ i + 1 = j ∨ j + 1 = i := by
  constructor
  · intro hadj
    rcases lt_or_gt_of_ne hij with hij' | hji'
    · have : ¬i + 1 < j := fun hlt ↦ hG.not_adj_getVert_of_add_one_lt hp hlt hj hadj
      exact Or.inl (by omega)
    · have : ¬j + 1 < i := fun hlt ↦ hG.not_adj_getVert_of_add_one_lt hp hlt hi hadj.symm
      exact Or.inr (by omega)
  · rintro (rfl | rfl)
    · exact p.adj_getVert_succ (by omega)
    · exact (p.adj_getVert_succ (by omega)).symm

/-- Embed the two left leaves, the path, and the two right leaves in their corresponding
summands. -/
private def doubleForkEmbedding {V : Type*} {G : SimpleGraph V} {u v : V} {n : ℕ}
    (q : G.Walk u v) (left right : Fin 2 → V) : DoubleForkIndex n → V
  | .inl i => left i
  | .inr (.inl i) => q.getVert i
  | .inr (.inr i) => right i

/-- The double-fork embedding is injective once the two leaf pairs lie off the path and are
disjoint from each other. -/
private lemma doubleForkEmbedding_injective {V : Type*} {G : SimpleGraph V} {u v : V}
    {q : G.Walk u v} (hq : q.IsPath) {n : ℕ} (hn : q.length = n + 1)
    (left right : Fin 2 → V) (hleft_inj : Function.Injective left)
    (hright_inj : Function.Injective right) (hleft_not_mem : ∀ i, left i ∉ q.support)
    (hright_not_mem : ∀ i, right i ∉ q.support)
    (hleft_right_ne : ∀ i j, left i ≠ right j) :
    Function.Injective (doubleForkEmbedding (n := n) q left right) := by
  intro i j hij
  rcases i with i | i | i <;> rcases j with j | j | j <;>
    simp only [doubleForkEmbedding] at hij
  · exact congrArg Sum.inl (hleft_inj hij)
  · exact (hleft_not_mem i (hij ▸ q.getVert_mem_support j)).elim
  · exact (hleft_right_ne i j hij).elim
  · exact (hleft_not_mem j (hij.symm ▸ q.getVert_mem_support i)).elim
  · apply congrArg (Sum.inr ∘ Sum.inl)
    apply Fin.ext
    exact hq.getVert_injOn (by simp only [Set.mem_ofPred_eq, hn]; omega)
      (by simp only [Set.mem_ofPred_eq, hn]; omega) hij
  · exact (hright_not_mem j (hij.symm ▸ q.getVert_mem_support i)).elim
  · exact (hleft_right_ne j i hij.symm).elim
  · exact (hright_not_mem i (hij ▸ q.getVert_mem_support j)).elim
  · exact congrArg (Sum.inr ∘ Sum.inr) (hright_inj hij)

omit [DecidableEq B] in
/-- The matrix on a double-fork embedding is the affine-`D` Cartan matrix when the entries along
the embedding are simply laced and the leaves have exactly the endpoint adjacencies and no
cross-edge. -/
private lemma submatrix_doubleForkEmbedding_eq (h : IsFiniteType A)
    {u v : B} {q : (diagramGraph A).Walk u v} (hq : q.IsPath) {n : ℕ}
    (hn : q.length = n + 1) (left right : Fin 2 → B)
    (he : Function.Injective (doubleForkEmbedding (n := n) q left right))
    (hsl : ∀ i j : DoubleForkIndex n, i ≠ j →
      A (doubleForkEmbedding q left right i) (doubleForkEmbedding q left right j) = 0 ∨
        A (doubleForkEmbedding q left right i) (doubleForkEmbedding q left right j) = -1)
    (hleft_inj : Function.Injective left) (hright_inj : Function.Injective right)
    (hleft_adj : ∀ i, (diagramGraph A).Adj u (left i))
    (hleft_ne_snd : ∀ i, left i ≠ q.snd)
    (hright_adj : ∀ i, (diagramGraph A).Adj v (right i))
    (hright_ne_penultimate : ∀ i, right i ≠ q.penultimate)
    (hleft_right_not_adj : ∀ i j, ¬(diagramGraph A).Adj (left i) (right j)) :
    A.submatrix (doubleForkEmbedding (n := n) q left right)
      (doubleForkEmbedding (n := n) q left right) =
      doubleForkCartanMatrix n := by
  classical
  set e : DoubleForkIndex n → B := doubleForkEmbedding (n := n) q left right with he_def
  have hA : ∀ i j, i ≠ j → A (e i) (e j) = if (diagramGraph A).Adj (e i) (e j) then -1 else 0 := by
    intro i j hij
    have hentry := matrix_apply_eq_neg_one_iff_adj h (fun heq ↦ hij (he heq)) (hsl i j hij)
    split_ifs with hadj
    · exact hentry.mpr hadj
    · exact (hsl i j hij).resolve_right (hadj ∘ hentry.mp)
  have hlen : ∀ k : Fin (n + 2), (k : ℕ) ≤ q.length := fun k ↦ by omega
  have hlast : q.getVert (n + 1) = v := by simpa only [← hn] using q.getVert_length
  apply Matrix.ext
  intro i j
  rcases eq_or_ne i j with rfl | hij
  · simp only [Matrix.submatrix_apply, h.apply_self, doubleForkCartanMatrix_diag]
  rw [Matrix.submatrix_apply, hA _ _ hij]
  -- The nine cases are the row-major left/path/right blocks of the double-fork matrix.
  -- Endpoint blocks use the supplied leaf adjacencies; the middle block uses path chordlessness.
  rcases i with i | i | i <;> rcases j with j | j | j <;>
    simp only [he_def, doubleForkEmbedding, doubleForkCartanMatrix_inl_inl,
      doubleForkCartanMatrix_inl_inr_inl, doubleForkCartanMatrix_inl_inr_inr,
      doubleForkCartanMatrix_inr_inl_inl, doubleForkCartanMatrix_inr_inl_inr_inl,
      doubleForkCartanMatrix_inr_inl_inr_inr, doubleForkCartanMatrix_inr_inr_inl,
      doubleForkCartanMatrix_inr_inr_inr_inl, doubleForkCartanMatrix_inr_inr_inr_inr]
  · have hij' : i ≠ j := fun h' ↦ hij (congrArg Sum.inl h')
    simp only [hij', not_adj_of_adj_of_adj h (hleft_adj i) (hleft_adj j)
      fun heq ↦ hij' (hleft_inj heq), ↓reduceIte]
  · exact if_congr (h.isAcyclic_diagramGraph.adj_getVert_iff_eq_zero hq (hleft_adj i)
      (hleft_ne_snd i) (hlen j)) rfl rfl
  · simp only [hleft_right_not_adj i j, ↓reduceIte]
  · exact if_congr ((SimpleGraph.adj_comm _ _ _).trans
      (h.isAcyclic_diagramGraph.adj_getVert_iff_eq_zero hq (hleft_adj j)
        (hleft_ne_snd j) (hlen i))) rfl rfl
  · have hij' : i ≠ j := fun h' ↦ hij (congrArg (Sum.inr ∘ Sum.inl) h')
    simp only [hij', ↓reduceIte]
    exact if_congr (adj_getVert_iff_succ h.isAcyclic_diagramGraph hq (hlen i) (hlen j)
      fun h' ↦ hij' (Fin.ext h')) rfl rfl
  · refine if_congr ((SimpleGraph.adj_comm _ _ _).trans
      ((h.isAcyclic_diagramGraph.adj_getVert_iff_eq_length hq (hright_adj j)
        (hright_ne_penultimate j) (hlen i)).trans ?_)) rfl rfl
    omega
  · simp only [mt SimpleGraph.Adj.symm (hleft_right_not_adj j i), ↓reduceIte]
  · refine if_congr ((h.isAcyclic_diagramGraph.adj_getVert_iff_eq_length hq (hright_adj i)
      (hright_ne_penultimate i) (hlen j)).trans ?_) rfl rfl
    omega
  · have hij' : i ≠ j := fun h' ↦ hij (congrArg (Sum.inr ∘ Sum.inr) h')
    simp only [hij', not_adj_of_adj_of_adj h (hright_adj i) (hright_adj j)
      fun heq ↦ hij' (hright_inj heq), ↓reduceIte]

/-- **Two distinct branch vertices in one simply-laced finite-type component contain an affine
`D` principal submatrix.** The middle `Fin (n + 2)` is the path between the branch vertices, and
the two outer copies of `Fin 2` enumerate the unused neighbours at either end.

Only the component of `u` is constrained: `hsl` asks for simple-lacedness on the vertices
reachable from `u`, which is where every selected vertex lives, so components carrying a multiple
edge do not obstruct the conclusion.

The returned map is injective, so `TauCeti.IsFiniteType.submatrix` applies directly. Its matrix
identity is oriented to match `TauCeti.doubleForkCartanMatrix`, the obstruction proved in
`TauCeti.LinearAlgebra.RootSystem.FiniteType.AffineD`. -/
theorem exists_doubleFork_submatrix [Fintype B] (h : IsFiniteType A) {u v : B}
    (huv : (diagramGraph A).Reachable u v)
    (hsl : {w | (diagramGraph A).Reachable u w}.Pairwise fun i j ↦ A i j = 0 ∨ A i j = -1)
    (huv_ne : u ≠ v)
    (hu : (diagramGraph A).degree u = 3) (hv : (diagramGraph A).degree v = 3) :
    ∃ (n : ℕ) (e : DoubleForkIndex n → B), Function.Injective e ∧
      A.submatrix e e = doubleForkCartanMatrix n := by
  classical
  let G := diagramGraph A
  let p : G.Path u v := huv.some.toPath
  let q : G.Walk u v := p
  have hq : q.IsPath := p.isPath
  have hqnil : ¬q.Nil := SimpleGraph.Walk.not_nil_of_ne huv_ne
  obtain ⟨n, hn⟩ : ∃ n, q.length = n + 1 := by
    exact Nat.exists_eq_succ_of_ne_zero (SimpleGraph.Walk.length_eq_zero_iff.not.mpr hqnil)
  obtain ⟨leftVertex, hleft_inj, hleft_adj, hleft_ne_snd⟩ :=
    (diagramGraph A).exists_injective_adj_ne_of_three_le_degree hu.ge q.snd
  obtain ⟨rightVertex, hright_inj, hright_adj, hright_ne_penultimate⟩ :=
    (diagramGraph A).exists_injective_adj_ne_of_three_le_degree hv.ge q.penultimate
  have hleft_not_mem (i : Fin 2) : leftVertex i ∉ q.support := fun hi ↦
    hleft_ne_snd i (h.isAcyclic_diagramGraph.eq_snd_of_adj_start hq (hleft_adj i) hi)
  have hright_not_mem (i : Fin 2) : rightVertex i ∉ q.support := fun hi ↦
    hright_ne_penultimate i
      (h.isAcyclic_diagramGraph.eq_penultimate_of_adj_end hq (hright_adj i) hi)
  have hleft_right_ne (i j : Fin 2) : leftVertex i ≠ rightVertex j :=
    h.isAcyclic_diagramGraph.ne_of_adj_start_of_adj_end huv_ne hq
      (hleft_adj i) (hleft_not_mem i) (hright_adj j)
  have hleft_right_not_adj (i j : Fin 2) : ¬G.Adj (leftVertex i) (rightVertex j) :=
    h.isAcyclic_diagramGraph.not_adj_of_adj_start_of_adj_end hq
      (hleft_adj i) (hleft_not_mem i) (hright_adj j) (hright_not_mem j)
  have he' := doubleForkEmbedding_injective hq hn leftVertex rightVertex hleft_inj hright_inj
    hleft_not_mem hright_not_mem hleft_right_ne
  -- Every vertex of the double fork lies in the component of `u`, so `hsl` applies to it.
  have hreach : ∀ i : DoubleForkIndex n,
      G.Reachable u (doubleForkEmbedding q leftVertex rightVertex i) := by
    rintro (i | i | i) <;> simp only [doubleForkEmbedding]
    · exact (hleft_adj i).reachable
    · exact (q.take i).reachable
    · exact huv.trans (hright_adj i).reachable
  have hslE (i j : DoubleForkIndex n) (hij : i ≠ j) :
      A (doubleForkEmbedding q leftVertex rightVertex i)
          (doubleForkEmbedding q leftVertex rightVertex j) = 0 ∨
        A (doubleForkEmbedding q leftVertex rightVertex i)
          (doubleForkEmbedding q leftVertex rightVertex j) = -1 :=
    hsl (hreach i) (hreach j) fun heq ↦ hij (he' heq)
  have hmatrix' := submatrix_doubleForkEmbedding_eq h hq hn leftVertex rightVertex he' hslE
    hleft_inj hright_inj hleft_adj hleft_ne_snd hright_adj hright_ne_penultimate
    hleft_right_not_adj
  let e : DoubleForkIndex n → B := doubleForkEmbedding q leftVertex rightVertex
  have he : Function.Injective e := by simpa only [e] using he'
  have hmatrix : A.submatrix e e = doubleForkCartanMatrix n := by
    simpa only [e] using hmatrix'
  exact ⟨n, e, he, hmatrix⟩

/-- **Reachable degree-three vertices of a simply-laced finite-type diagram coincide.** As in
`TauCeti.IsFiniteType.exists_doubleFork_submatrix`, simple-lacedness is needed only on the
component of `u`. Otherwise that theorem produces an affine `D` principal submatrix,
contradicting `TauCeti.not_isFiniteType_doubleForkCartanMatrix`. -/
theorem eq_of_reachable_of_degree_eq_three [Fintype B] (h : IsFiniteType A) {u v : B}
    (huv : (diagramGraph A).Reachable u v)
    (hsl : {w | (diagramGraph A).Reachable u w}.Pairwise fun i j ↦ A i j = 0 ∨ A i j = -1)
    (hu : (diagramGraph A).degree u = 3) (hv : (diagramGraph A).degree v = 3) :
    u = v := by
  by_contra huv_ne
  obtain ⟨n, e, he, hmatrix⟩ := h.exists_doubleFork_submatrix huv hsl huv_ne hu hv
  have hfinite := h.submatrix he
  rw [hmatrix] at hfinite
  exact not_isFiniteType_doubleForkCartanMatrix n hfinite

/-- **A connected simply-laced finite-type diagram has at most one branch vertex.** This is the
connected form used when extracting the `D` and `E` Dynkin diagrams from a finite-type matrix. -/
theorem eq_of_degree_eq_three [Fintype B] (h : IsFiniteType A) (hsl : A.IsSimplyLaced)
    (hconn : (diagramGraph A).Connected) {u v : B}
    (hu : (diagramGraph A).degree u = 3) (hv : (diagramGraph A).degree v = 3) :
    u = v :=
  h.eq_of_reachable_of_degree_eq_three (hconn u v) (fun _ _ _ _ hij ↦ hsl hij) hu hv

end IsFiniteType

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.SimpleGraph.CycleGraph
public import TauCeti.GroupTheory.Coxeter.Bipartite
public import TauCeti.LinearAlgebra.RootSystem.AffineDynkinType.Basic

/-!
# Two-colourings of the affine simply-laced Dynkin diagrams

A finite Dynkin diagram is a forest, so it always has a two-colouring, and the bipartite Coxeter
element (`CoxeterSystem.bipartiteCoxeterElement`) is the product of the simple reflections of one
colour followed by those of the other. This file answers the corresponding questions for the
affine simply-laced diagrams `TauCeti.AffineDynkinType`.

First, which of them have a two-colouring at all. The diagrams `Dₙ`, `E₆`, `E₇` and `E₈` are trees
and are bipartite (`TauCeti.AffineDynkinType.isBipartite_graph_D` and its exceptional analogues),
while `Aₙ` is the cycle on `n + 1` nodes, which is bipartite exactly when `n` is odd. So the
nonbipartite affine diagrams are the odd cycles `A₂, A₄, …`; for them the symmetry question is a
question about graph automorphisms only, with no colour classes to compare.

Second, for a bipartite diagram, how its graph automorphisms act on the colour classes. A
connected graph has only the two colourings exchanged by `not`, so an automorphism either keeps the
colour of every node or exchanges the two colour classes
(`SimpleGraph.Coloring.forall_apply_eq_or_forall_apply_eq_not`). An exchanging automorphism is a
bijection between the two classes, so they have the same size; this rules it out for `Dₙ` with
`n` even, `E₆` and `E₈`, which have an odd number of nodes, and for `E₇`, whose classes have three
and five nodes. Conversely, for `n` odd a rotation of the cycle `Aₙ` by one step and the reversal
`TauCeti.AffineDynkinType.reverseD` of `Dₙ` exchange the colours. Hence a valid affine diagram has
a colour-exchanging automorphism exactly when it is `Aₙ` or `Dₙ` with `n` odd
(`TauCeti.AffineDynkinType.exists_iso_forall_coloring_eq_not_iff`). On the cycle the
classification of the individual automorphisms is by parity: one preserves the colours exactly when
it moves the node `0` an even number of steps
(`SimpleGraph.Coloring.cycleGraph_forall_apply_eq_iff_even_val_apply_zero`), and exchanges them
exactly when it moves `0` an odd number of steps
(`SimpleGraph.Coloring.cycleGraph_forall_apply_eq_not_iff_odd_val_apply_zero`); the reversal of
`Dₙ` preserves the colours exactly when `n` is even and exchanges them exactly when `n` is odd.

Third, what this does to the bipartite Coxeter element of a Coxeter system whose Coxeter graph is
the affine diagram, such as the affine Weyl group. A diagram automorphism sends the word listing
one colour class and then the other to a word of the same shape when it preserves the colours, so it
fixes the bipartite Coxeter element, and to a word listing the classes in the opposite order when it
exchanges them, so it inverts the element
(`CoxeterSystem.diagramAut_bipartiteCoxeterElement_of_forall_eq` and
`CoxeterSystem.diagramAut_bipartiteCoxeterElement_of_forall_eq_not`). Outside `Aₙ` and `Dₙ` with `n`
odd, every diagram automorphism therefore fixes it
(`TauCeti.AffineDynkinType.diagramAut_bipartiteCoxeterElement_eq_self`), for a Coxeter matrix on
any finite index type whose Coxeter graph is isomorphic to the diagram.

## Main definitions

* `TauCeti.AffineDynkinType.reverseD`: the automorphism of `Dₙ` exchanging its two ends.

## Main results

* `TauCeti.AffineDynkinType.isBipartite_graph_A_iff`: the cycle `Aₙ` is bipartite exactly when `n`
  is odd.
* `TauCeti.AffineDynkinType.isBipartite_graph_iff`: a valid affine diagram is bipartite exactly
  when it is not a cycle `A₂ₘ`.
* `TauCeti.AffineDynkinType.forall_coloring_reverseD_eq_iff`,
  `TauCeti.AffineDynkinType.forall_coloring_reverseD_eq_not_iff`: the reversal of `Dₙ` preserves
  the colours exactly when `n` is even and exchanges them exactly when `n` is odd.
* `TauCeti.AffineDynkinType.exists_iso_forall_coloring_eq_not_iff`: a valid affine diagram has a
  colour-exchanging automorphism exactly when it is `Aₙ` or `Dₙ` with `n` odd, and
  `TauCeti.AffineDynkinType.coloring_iso_eq` says that otherwise every automorphism preserves the
  colours.
* `TauCeti.AffineDynkinType.diagramAut_bipartiteCoxeterElement_eq_self`: outside those cases every
  diagram automorphism fixes the bipartite Coxeter element.

## References

* V. Kac, *Infinite dimensional Lie algebras*, 3rd ed., Chapter 4 and Table Aff 1, for the
  diagrams.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. V, §6, for the bipartite Coxeter
  element.
-/

public section

namespace TauCeti.AffineDynkinType

open SimpleGraph Finset

/-! ## Which affine diagrams are bipartite -/

/-- **The cycle `Aₙ` is bipartite exactly when `n` is odd**, that is, when it has an even number
`n + 1` of nodes. -/
theorem isBipartite_graph_A_iff {n : ℕ} (hn : 1 ≤ n) : (A n).graph.IsBipartite ↔ Odd n := by
  rw [graph_A]
  refine isBipartite_cycleGraph_iff.trans ?_
  rw [Nat.even_add_one, Nat.not_even_iff_odd]
  exact or_iff_left (by omega)

/-- **The bipartite affine simply-laced diagrams**: a valid affine diagram is bipartite exactly
when it is not a cycle `A₂ₘ` with an odd number of nodes. -/
theorem isBipartite_graph_iff {t : AffineDynkinType} (ht : t.Valid) :
    t.graph.IsBipartite ↔ ∀ m, t ≠ A (2 * m) := by
  cases t with
  | A n =>
    rw [isBipartite_graph_A_iff (valid_A.mp ht)]
    simp only [ne_eq, A.injEq]
    constructor
    · rintro ⟨k, rfl⟩ m h
      omega
    · intro h
      by_contra hodd
      obtain ⟨m, rfl⟩ := Nat.not_odd_iff_even.mp hodd
      exact h m (two_mul m).symm
  | D n => simpa using isBipartite_graph_D (valid_D.mp ht)
  | E6 => simpa using isBipartite_graph_E6
  | E7 => simpa using isBipartite_graph_E7
  | E8 => simpa using isBipartite_graph_E8

/-! ## The reversal of `Dₙ` -/

/-- The node numbers of `Dₙ` under the reversal: the path `0 - 1 - ⋯ - (n-2)` is reversed and the
two leaves `n - 1` and `n`, at its second and penultimate nodes, are exchanged. -/
private def reverseDFun (n : ℕ) (i : Fin (D n).nodes) : Fin (D n).nodes :=
  if (i : ℕ) ≤ n - 2 then ⟨n - 2 - i, by simp only [nodes_D]; omega⟩
  else if (i : ℕ) = n - 1 then ⟨n, by simp⟩ else ⟨n - 1, by simp only [nodes_D]; omega⟩

private theorem val_reverseDFun (n : ℕ) (i : Fin (D n).nodes) :
    (reverseDFun n i : ℕ) =
      if (i : ℕ) ≤ n - 2 then n - 2 - i else if (i : ℕ) = n - 1 then n else n - 1 := by
  unfold reverseDFun
  split_ifs <;> rfl

private theorem reverseDFun_involutive {n : ℕ} (hn : 4 ≤ n) :
    Function.Involutive (reverseDFun n) := fun i ↦ by
  ext
  have hi : (i : ℕ) < n + 1 := i.isLt
  rw [val_reverseDFun, val_reverseDFun]
  split_ifs <;> omega

/-- The reversal of `Dₙ` carries edges to edges. -/
private theorem adj_reverseDFun {n : ℕ} (hn : 4 ≤ n) {i j : Fin (D n).nodes}
    (h : (D n).graph.Adj i j) : (D n).graph.Adj (reverseDFun n i) (reverseDFun n j) := by
  have hi : (i : ℕ) < n + 1 := i.isLt
  have hj : (j : ℕ) < n + 1 := j.isLt
  -- `graph_D_adj` on the node type `Fin (D n).nodes` rather than `Fin (n + 1)`.
  have hadj (u v : Fin (D n).nodes) := graph_D_adj hn (i := u) (j := v)
  rw [hadj] at h
  rw [hadj, val_reverseDFun, val_reverseDFun]
  rcases h with h | h | h | h | h | h <;> split_ifs <;> omega

/-- **The reversal of `Dₙ`**: the graph automorphism reversing the path `0 - 1 - ⋯ - (n-2)` and
exchanging the leaf `n - 1` at node `1` with the leaf `n` at node `n - 3`. It exchanges the two
ends of the diagram, and it preserves the colours of a two-colouring exactly when `n` is even
(`TauCeti.AffineDynkinType.forall_coloring_reverseD_eq_iff`). -/
def reverseD {n : ℕ} (hn : 4 ≤ n) : (D n).graph ≃g (D n).graph where
  toEquiv := (reverseDFun_involutive hn).toPerm
  map_rel_iff' {i j} := by
    rw [Function.Involutive.coe_toPerm]
    refine ⟨fun h ↦ ?_, adj_reverseDFun hn⟩
    simpa only [reverseDFun_involutive hn _] using adj_reverseDFun hn h

/-- The reversal of `Dₙ` on node numbers: it reverses the path `0 - 1 - ⋯ - (n-2)` and exchanges
the leaves `n - 1` and `n`. -/
theorem val_reverseD {n : ℕ} (hn : 4 ≤ n) (i : Fin (D n).nodes) :
    (reverseD hn i : ℕ) =
      if (i : ℕ) ≤ n - 2 then n - 2 - i else if (i : ℕ) = n - 1 then n else n - 1 :=
  val_reverseDFun n i

/-- The reversal of `Dₙ` is an involution. It is not a `simp` lemma: `simp` rewrites the node type
`Fin (D n).nodes` to `Fin (n + 1)` by `TauCeti.AffineDynkinType.nodes_D` first. -/
theorem reverseD_reverseD {n : ℕ} (hn : 4 ≤ n) (i : Fin (D n).nodes) :
    reverseD hn (reverseD hn i) = i :=
  reverseDFun_involutive hn i

/-- The reversal of `Dₙ` is its own inverse. -/
@[simp]
theorem reverseD_symm {n : ℕ} (hn : 4 ≤ n) : (reverseD hn).symm = reverseD hn :=
  RelIso.ext fun i ↦ (reverseD hn).symm_apply_eq.mpr (reverseD_reverseD hn i).symm

/-- The reversal of `Dₙ` composed with itself is the identity. -/
@[simp]
theorem reverseD_trans_reverseD {n : ℕ} (hn : 4 ≤ n) :
    (reverseD hn).trans (reverseD hn) = .refl _ :=
  RelIso.ext fun i ↦ reverseD_reverseD hn i

/-- Colours alternate along the path `0 - 1 - ⋯ - (n-2)` of `Dₙ`. -/
private theorem apply_eq_apply_zero_iff_even_D {n : ℕ} (hn : 4 ≤ n)
    (c : (D n).graph.Coloring Bool) :
    ∀ (i : ℕ) (hi : i ≤ n - 2),
      c (⟨i, by simp only [nodes_D]; omega⟩ : Fin (D n).nodes) = c ⟨0, by simp⟩ ↔ Even i
  | 0, _ => by simp
  | i + 1, hi => by
    have hne := c.valid (v := (⟨i, by simp only [nodes_D]; omega⟩ : Fin (D n).nodes))
      (w := ⟨i + 1, by simp only [nodes_D]; omega⟩) ((graph_D_adj hn).2 (Or.inl ⟨rfl, hi⟩))
    rw [Nat.even_add_one, ← apply_eq_apply_zero_iff_even_D hn c i (by omega)]
    -- Adjacent nodes have different colours, so exactly one of them has the colour of `0`.
    have key : ∀ x y d : Bool, x ≠ y → (y = d ↔ ¬x = d) := by decide
    exact key _ _ _ hne

/-- **The reversal of `Dₙ` preserves the colours exactly when `n` is even**: it sends the end node
`0` of the path to the other end node `n - 2`, an even number of steps away exactly when `n` is
even. Otherwise it exchanges the two colours. -/
theorem forall_coloring_reverseD_eq_iff {n : ℕ} (hn : 4 ≤ n) (c : (D n).graph.Coloring Bool) :
    (∀ i, c (reverseD hn i) = c i) ↔ Even n := by
  have h0 : reverseD hn ⟨0, by simp⟩ = ⟨n - 2, by simp only [nodes_D]; omega⟩ :=
    Fin.ext (by rw [val_reverseD hn]; simp)
  have hpath := apply_eq_apply_zero_iff_even_D hn c (n - 2) le_rfl
  rw [← h0] at hpath
  have hev : Even (n - 2) ↔ Even n := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    simp [Nat.even_add]
  exact ⟨fun h ↦ hev.mp (hpath.mp (h _)), fun h ↦ c.forall_apply_eq_of_apply_eq
    (graph_connected (valid_D.mpr hn)).preconnected (reverseD hn).toHom (hpath.mpr (hev.mpr h))⟩

/-- **The reversal of `Dₙ` exchanges the colours exactly when `n` is odd.** -/
theorem forall_coloring_reverseD_eq_not_iff {n : ℕ} (hn : 4 ≤ n) (c : (D n).graph.Coloring Bool) :
    (∀ i, c (reverseD hn i) = !c i) ↔ Odd n := by
  constructor
  · intro h
    rw [← Nat.not_even_iff_odd, ← forall_coloring_reverseD_eq_iff hn c]
    intro h'
    have h0 := h ⟨0, by simp⟩
    rw [h'] at h0
    simp at h0
  · intro hodd
    have h := (forall_coloring_reverseD_eq_iff hn c).not.mpr (Nat.not_even_iff_odd.mpr hodd)
    push Not at h
    obtain ⟨i, hi⟩ := h
    exact c.forall_apply_eq_not_of_apply_ne (graph_connected (valid_D.mpr hn)).preconnected
      (reverseD hn).toHom hi

/-! ## Colour-exchanging automorphisms -/

/-- The two-colouring of `E₇ = T₂,₄,₄` in which the trivalent node `0` is coloured `true`. Its
colour classes have three and five nodes. -/
private def coloringE7 : E7.graph.Coloring Bool :=
  Coloring.mk (![true, false, false, true, false, false, true, false] : Fin 8 → Bool)
    (@fun v w ↦ by
      revert v w
      simp only [graph_E7_adj]
      simp only [nodes_E7]
      decide)

/-- **The affine diagrams with a colour-exchanging automorphism**: a valid affine simply-laced
diagram with a two-colouring has a graph automorphism exchanging the two colour classes exactly
when it is `Aₙ` or `Dₙ` with `n` odd. For `Aₙ` the rotation `TauCeti.cycleGraphAddRightIso 1` by
one step is one, and for `Dₙ` the reversal `TauCeti.AffineDynkinType.reverseD`. -/
theorem exists_iso_forall_coloring_eq_not_iff {t : AffineDynkinType} (ht : t.Valid)
    (c : t.graph.Coloring Bool) :
    (∃ φ : t.graph ≃g t.graph, ∀ i, c (φ i) = !c i) ↔ ∃ n, Odd n ∧ (t = A n ∨ t = D n) := by
  constructor
  · rintro ⟨φ, hφ⟩
    -- An exchanging automorphism matches the two colour classes, which partition the nodes.
    have htot := two_mul_card_filter_eq_true c φ.toEquiv hφ
    rw [Fintype.card_fin] at htot
    cases t with
    | A n =>
      exact ⟨n, (isBipartite_graph_A_iff (valid_A.mp ht)).mp (by simpa using c.colorable),
        Or.inl rfl⟩
    | D n =>
      refine ⟨n, Nat.not_even_iff_odd.mp fun ⟨m, hm⟩ ↦ ?_, Or.inr rfl⟩
      simp only [nodes_D] at htot
      omega
    | E6 =>
      simp only [nodes_E6] at htot
      omega
    | E7 =>
      rcases coloringE7.eq_or_eq_recolorOfEquiv_boolNot (graph_connected ht).preconnected c
        with rfl | rfl <;> exact absurd htot (by decide)
    | E8 =>
      simp only [nodes_E8] at htot
      omega
  · rintro ⟨n, hn, rfl | rfl⟩
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := hn.pos; omega⟩
      -- The rotation `v ↦ v + 1` of the cycle on `m + 2` nodes moves every node by one step.
      have hG := graph_A (m + 1)
      generalize (A (m + 1)).graph = G at c hG ⊢
      subst hG
      exact ⟨cycleGraphAddRightIso 1, fun i ↦ (congrArg c (cycleGraphAddRightIso_apply 1 i)).trans
        ((c.cycleGraph_apply_add_eq_not_iff_odd_val i 1).mpr (by simp))⟩
    · exact ⟨reverseD (valid_D.mp ht), (forall_coloring_reverseD_eq_not_iff _ c).mpr hn⟩

/-- **Outside `Aₙ` and `Dₙ` with `n` odd, every automorphism of a valid affine diagram preserves
the colours of a two-colouring.** -/
theorem coloring_iso_eq {t : AffineDynkinType} (ht : t.Valid)
    (h : ¬∃ n, Odd n ∧ (t = A n ∨ t = D n)) (c : t.graph.Coloring Bool) (φ : t.graph ≃g t.graph)
    (i : Fin t.nodes) : c (φ i) = c i :=
  (c.forall_apply_eq_or_forall_apply_eq_not (graph_connected ht).preconnected φ.toHom).resolve_right
    (fun hφ ↦ h ((exists_iso_forall_coloring_eq_not_iff ht c).mp ⟨φ, hφ⟩)) i

/-! ## The bipartite Coxeter element -/

/-- **Diagram automorphisms fix the bipartite Coxeter element outside `Aₙ` and `Dₙ` with `n`
odd.** Let `M` be a Coxeter matrix on any finite index type whose Coxeter graph is isomorphic to a
valid affine diagram other than these, as for the affine Weyl group of that type. Every diagram
automorphism of `M` preserves the colours of a two-colouring, so it fixes the bipartite Coxeter
element; for `Aₙ` and `Dₙ` with `n` odd, a colour-exchanging one inverts it instead
(`CoxeterSystem.diagramAut_bipartiteCoxeterElement_of_forall_eq_not`). -/
theorem diagramAut_bipartiteCoxeterElement_eq_self {t : AffineDynkinType} (ht : t.Valid)
    (h : ¬∃ n, Odd n ∧ (t = A n ∨ t = D n)) {B : Type*} [Fintype B] {M : CoxeterMatrix B}
    (ψ : M.graph ≃g t.graph) {W : Type*} [Group W] (cs : CoxeterSystem M W)
    (c : M.graph.Coloring Bool) (e : B ≃ B) (he : ∀ i i', M (e i) (e i') = M i i') :
    cs.diagramAut e he (cs.bipartiteCoxeterElement c) = cs.bipartiteCoxeterElement c := by
  refine cs.diagramAut_bipartiteCoxeterElement_of_forall_eq c e he fun i ↦ ?_
  -- Transport the colouring and the graph automorphism underlying `e` to the diagram along `ψ`.
  simpa using coloring_iso_eq ht h (c.comp ψ.symm.toHom)
    ((ψ.symm.trans (M.graphIso e he)).trans ψ) (ψ i)

end TauCeti.AffineDynkinType

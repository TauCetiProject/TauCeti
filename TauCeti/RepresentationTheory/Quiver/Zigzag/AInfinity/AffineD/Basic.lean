/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.AffineDynkinType.Basic
public import TauCeti.RepresentationTheory.Quiver.Zigzag.AInfinity.HochschildClass

/-!
# Nonzero quartic Hochschild classes of the affine `Dₙ` zigzag algebras

In the numbering of `TauCeti.AffineDynkinType.graph (D n)`, for `n ≥ 5`, the nodes `1` and `n - 3`
are the two branch nodes of the affine `Dₙ` graph: the node `1` has the neighbours `0`, `2` and
`n - 1`, the node `n - 3` has the neighbours `n - 4`, `n - 2` and `n`, and they are joined by the
path `1 - 2 - ⋯ - (n - 3)`. The general two-branch-vertex criterion
`TauCeti.not_hochschildVanishesAt_four_zigzagStrictAInfinityAlgebra_of_walk` of
`TauCeti.RepresentationTheory.Quiver.Zigzag.AInfinity.HochschildClass` therefore applies, and the
quartic Hochschild cohomology `HH^{4, -2}` of the affine `Dₙ` zigzag algebra is nonzero over every
nontrivial commutative ring. The affine `D₄` graph, whose only branch node has four neighbours, is
treated in `TauCeti.RepresentationTheory.Quiver.Zigzag.AInfinity.AffineD.Four`.

## Main results

* `TauCeti.not_hochschildVanishesAt_four_affineD`: `HH^{4, -2}` of the affine `Dₙ` zigzag algebra
  is nonzero for `n ≥ 5`.
-/

public section

namespace TauCeti

universe w

variable {k : Type w} [CommRing k] {m : ℕ}

/-- The dart from node `i` to node `j` of the affine `D_{m+5}` graph, for adjacent nodes: the
hypothesis is the adjacency condition of `TauCeti.AffineDynkinType.graph_D_adj`. -/
private def affineDDart (i j : ℕ)
    (h : (i + 1 = j ∧ j ≤ m + 3) ∨ (j + 1 = i ∧ i ≤ m + 3) ∨ (i = 1 ∧ j = m + 4) ∨
      (j = 1 ∧ i = m + 4) ∨ (i = m + 2 ∧ j = m + 5) ∨ (j = m + 2 ∧ i = m + 5)) :
    (AffineDynkinType.D (m + 5)).graph.Dart :=
  ⟨(⟨i, by simp; omega⟩, ⟨j, by simp; omega⟩),
    (AffineDynkinType.graph_D_adj (by omega)).2 (by simp only; omega)⟩

private theorem affineDDart_ne {i j i' j' : ℕ} {h h'} (hii' : i ≠ i' ∨ j ≠ j') :
    affineDDart (m := m) i j h ≠ affineDDart i' j' h' := by
  intro heq
  rw [SimpleGraph.Dart.ext_iff] at heq
  simp only [affineDDart, Prod.mk.injEq, Fin.mk.injEq] at heq
  omega

private theorem affineDDart_ne_symm {i j i' j' : ℕ} {h h'} (hii' : i ≠ j' ∨ j ≠ i') :
    affineDDart (m := m) i j h ≠ (affineDDart i' j' h').symm := by
  intro heq
  rw [SimpleGraph.Dart.ext_iff, SimpleGraph.Dart.symm_toProd] at heq
  simp only [affineDDart, Prod.swap_prod_mk, Prod.mk.injEq, Fin.mk.injEq] at heq
  omega

/-- **The quartic Hochschild cohomology `HH^{4, -2}` of the affine `Dₙ` zigzag algebra is nonzero**
for `n ≥ 5`, over every nontrivial commutative ring: the two branch nodes `1` and `n - 3` have
three neighbours each and are joined by the path `1 - 2 - ⋯ - (n - 3)`. For `n = 4` see
`TauCeti.not_hochschildVanishesAt_four_affineD4`. -/
theorem not_hochschildVanishesAt_four_affineD [Nontrivial k] {n : ℕ} (hn : 5 ≤ n) :
    ¬(zigzagStrictAInfinityAlgebra k (AffineDynkinType.exists_adj_graph (t := .D n)
      (AffineDynkinType.valid_D.2 (by omega)))).HochschildVanishesAt ⟨4, by norm_num⟩ := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
  -- The walk `1 → 2 → ⋯ → m + 2` from the branch node `1` to the branch node `m + 2 = n - 3`,
  -- whose other neighbours are `0, m + 4` and `m + 3, m + 5`.
  let f : Fin (m + 1) → (AffineDynkinType.D (m + 5)).graph.Dart := fun t ↦
    affineDDart (t + 1) (t + 2) (by omega)
  refine not_hochschildVanishesAt_four_zigzagStrictAInfinityAlgebra_of_walk
    (d := affineDDart 0 1 (by omega)) (e := affineDDart (m + 4) 1 (by omega))
    (d' := affineDDart (m + 3) (m + 2) (by omega)) (e' := affineDDart (m + 5) (m + 2) (by omega))
    (f := f) (affineDDart_ne (by omega)) rfl rfl (affineDDart_ne_symm (by omega))
    (affineDDart_ne_symm (by omega)) (fun _ ↦ rfl) (fun t ↦ affineDDart_ne_symm (by simp))
    (fun t h ↦ ?_) (affineDDart_ne (by omega)) rfl rfl (affineDDart_ne (by simp))
    (affineDDart_ne (by simp))
  have h' := congrArg Fin.val h
  simp [f, affineDDart] at h'

end TauCeti

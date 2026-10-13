/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.SimpleGraph.Connected
public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Diagram
public import Mathlib.LinearAlgebra.RootSystem.Irreducible
public import TauCeti.LinearAlgebra.RootSystem.InvariantSubmodule
public import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

/-!
# Irreducibility from a connected Dynkin diagram

This file proves the converse to the standard implication from irreducibility of a root pairing to
connectedness of its Dynkin diagram. Over a field of characteristic zero, a crystallographic root
system whose base has connected diagram is irreducible. It then checks that the standard Cartan
matrix of every valid `DynkinType` has connected diagram and packages the result in the form used by
root systems identified through `TauCeti.HasCartanType`.

The argument follows the usual proof in Humphreys, *Introduction to Lie Algebras and Representation
Theory*, §10. A nonzero reflection-invariant subspace contains a root, hence a simple root. Once
it contains one simple root, connectedness and reflection invariance propagate membership along
every edge of the Dynkin diagram, so the simple roots span the whole space inside the subspace.

## Main results

* `RootPairing.isIrreducible_of_connected_diagramGraph_cartanMatrix`: a connected base
  diagram makes a root system irreducible.
* `RootPairing.eq_bot_of_forall_root_not_mem`: a submodule invariant under the simple
  reflections and containing no simple root is trivial.
* `TauCeti.DynkinType.connected_diagramGraph_cartanMatrix`: every valid standard Dynkin diagram is
  connected.
* `TauCeti.HasCartanType.isIrreducible`: a root system of valid Cartan type is irreducible.
-/

public section

open Function Set
open Module.End (invtSubmodule)

namespace TauCeti

namespace SimpleGraph

/-- A graph containing every successor edge contains the path graph. -/
private theorem pathGraph_le_of_adj_succ {n : ℕ} {G : SimpleGraph (Fin n)}
    (h : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), G.Adj i ⟨(i : ℕ) + 1, hi⟩) :
    _root_.SimpleGraph.pathGraph n ≤ G := by
  intro i j hij
  rw [_root_.SimpleGraph.pathGraph_adj] at hij
  rcases hij with hij | hij
  · have hj : (⟨(i : ℕ) + 1, by omega⟩ : Fin n) = j := Fin.ext hij
    exact hj ▸ h i (by omega)
  · have hi : (⟨(j : ℕ) + 1, by omega⟩ : Fin n) = i := Fin.ext hij
    exact (hi ▸ h j (by omega)).symm

/-- A graph containing the path graph on the same nonempty vertex set is connected. -/
private theorem connected_of_pathGraph_le {n : ℕ} {G : SimpleGraph (Fin n)}
    [Nonempty (Fin n)] (h : _root_.SimpleGraph.pathGraph n ≤ G) : G.Connected :=
  ⟨(_root_.SimpleGraph.pathGraph_preconnected n).mono h⟩

end SimpleGraph

namespace DynkinType

private theorem adj_succ_D {n : ℕ} (hn : 4 ≤ n) (i : Fin n)
    (hi : (i : ℕ) + 1 < n - 1) :
    (diagramGraph (CartanMatrix.D n)).Adj i ⟨(i : ℕ) + 1, by omega⟩ := by
  rw [diagramGraph_adj]
  simp [CartanMatrix.D]
  simp only [Fin.ext_iff]
  omega

private theorem adj_fork_D {n : ℕ} (hn : 4 ≤ n) (i : Fin n)
    (hi : (i : ℕ) = n - 1) :
    (diagramGraph (CartanMatrix.D n)).Adj ⟨n - 3, by omega⟩ i := by
  rw [diagramGraph_adj]
  simp [CartanMatrix.D]
  simp only [Fin.ext_iff]
  omega

/-- The diagram of the standard Cartan matrix of a valid Dynkin type is connected. Validity
confines each family to its canonical rank range, which is nonempty and is what the proof uses. -/
theorem connected_diagramGraph_cartanMatrix {t : DynkinType} (ht : t.Valid) :
    (diagramGraph t.cartanMatrix).Connected := by
  -- The `A`, `B` and `C` diagrams contain every successor edge, hence the path graph.
  have path {n : ℕ} (hn : 0 < n) {G : _root_.SimpleGraph (Fin n)}
      (h : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), G.Adj i ⟨(i : ℕ) + 1, hi⟩) : G.Connected :=
    have : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
    SimpleGraph.connected_of_pathGraph_le (SimpleGraph.pathGraph_le_of_adj_succ h)
  -- In `E₆`, `E₇`, `E₈` node `1` hangs off the branch node `3`, so not every node has a smaller
  -- neighbour; their connectivity is decided by reachability from node `3`.
  cases t with
  | A n =>
      simpa only [rank_A, cartanMatrix_A] using path (valid_A.mp ht) fun i hi ↦ by
        rw [diagramGraph_adj]; simp [CartanMatrix.A]; simp only [Fin.ext_iff]; omega
  | B n =>
      simpa only [rank_B, cartanMatrix_B] using path (by have := valid_B.mp ht; omega) fun i hi ↦ by
        rw [diagramGraph_adj]; simp [CartanMatrix.B]; simp only [Fin.ext_iff]; omega
  | C n =>
      simpa only [rank_C, cartanMatrix_C] using path (by have := valid_C.mp ht; omega) fun i hi ↦ by
        rw [diagramGraph_adj]; simp [CartanMatrix.C]; simp only [Fin.ext_iff]; omega
  | D n =>
      have hn := valid_D.mp ht
      have hconn : (diagramGraph (CartanMatrix.D n)).Connected := by
        refine SimpleGraph.connected_fin_of_exists_adj_lt (by omega) fun i hi ↦ ?_
        by_cases hlast : (i : ℕ) = n - 1
        · let j : Fin n := ⟨n - 3, by omega⟩
          have hji : j = ⟨n - 3, by omega⟩ := rfl
          refine ⟨j, ?_, hji ▸ adj_fork_D hn i hlast⟩
          simp only [j]
          omega
        · let j : Fin n := ⟨(i : ℕ) - 1, by omega⟩
          have hji : (⟨(j : ℕ) + 1, by simp [j]; omega⟩ : Fin n) = i := by
            apply Fin.ext
            simp [j]
            omega
          exact ⟨j, by simp [j]; omega, hji ▸ adj_succ_D hn j (by simp [j]; omega)⟩
      simpa only [rank_D, cartanMatrix_D] using hconn
  | E6 => simpa only [rank_E6, cartanMatrix_E6] using
      (SimpleGraph.connected_iff_exists_forall_reachable
        (diagramGraph (CartanMatrix.E 6))).2 ⟨3, by decide⟩
  | E7 => simpa only [rank_E7, cartanMatrix_E7] using
      (SimpleGraph.connected_iff_exists_forall_reachable
        (diagramGraph (CartanMatrix.E 7))).2 ⟨3, by decide⟩
  | E8 => simpa only [rank_E8, cartanMatrix_E8] using
      (SimpleGraph.connected_iff_exists_forall_reachable
        (diagramGraph (CartanMatrix.E 8))).2 ⟨3, by decide⟩
  | F4 => simpa only [rank_F4, cartanMatrix_F4] using
      (SimpleGraph.connected_fin_of_exists_adj_lt (by decide) (by decide) :
        (diagramGraph CartanMatrix.F₄).Connected)
  | G2 => simpa only [rank_G2, cartanMatrix_G2] using
      (SimpleGraph.connected_fin_of_exists_adj_lt (by decide) (by decide) :
        (diagramGraph CartanMatrix.G₂.transpose).Connected)

end DynkinType

section

variable {K M N ι : Type*} [Field K] [CharZero K] [AddCommGroup M] [Module K M]
  [AddCommGroup N] [Module K N] {P : RootPairing ι K M N} [P.IsCrystallographic]

omit [P.IsCrystallographic] in
/-- **A submodule invariant under the simple reflections and containing no simple root is
trivial.** If `q` is invariant under the reflection at each element of the base's support and
misses the root there, then `q = ⊥`.

Invariance is asked at the support only, not under every reflection of `P`. -/
theorem _root_.RootPairing.eq_bot_of_forall_root_not_mem
    [P.IsRootSystem] {b : P.Base} {q : Submodule K M}
    (hinv : ∀ i : b.support, q ∈ Module.End.invtSubmodule (P.reflection i))
    (h : ∀ i : b.support, P.root i ∉ q) : q = ⊥ := by
  -- Missing every simple root puts `q` inside all the simple coroot kernels; the coweight basis
  -- then kills every pairing, and perfection of the pairing forces `q` to vanish.
  have hle : q ≤ ⨅ i : b.support, LinearMap.ker (P.coroot' i) :=
    le_iInf fun i ↦ (Submodule.mem_invtSubmodule_reflection_iff (P.flip.root_coroot_two i)
      (Submodule.disjoint_span_singleton_of_notMem (h i))).mp (hinv i)
  refine eq_bot_iff.mpr fun x hx => ?_
  apply P.toPerfPair.injective
  apply LinearMap.ext
  intro y
  rw [map_zero, ← b.toCoweightBasis.sum_repr y, map_sum]
  apply Finset.sum_eq_zero
  intro i _
  have hz : (P.toPerfPair x) (b.toCoweightBasis i) = 0 := by
    have hallker : ∀ j : b.support, x ∈ LinearMap.ker (P.coroot' j) := by
      simpa using hle hx
    simpa using LinearMap.mem_ker.mp (hallker i)
  rw [map_smul, hz, smul_zero]

/-- A crystallographic root system with a connected Dynkin diagram is irreducible.

Characteristic zero ensures that a nonzero integral Cartan entry stays nonzero in the field when
membership propagates across an edge. It also supplies the standard `2 ≠ 0` hypothesis in
Mathlib's invariant-submodule criterion for a reflection. -/
theorem _root_.RootPairing.isIrreducible_of_connected_diagramGraph_cartanMatrix
    [P.IsRootSystem] (b : P.Base)
    (hconn : (diagramGraph b.cartanMatrix).Connected) : P.IsIrreducible := by
  let _ : Nontrivial M :=
    ⟨⟨P.root hconn.nonempty.some, 0, P.ne_zero hconn.nonempty.some⟩⟩
  apply RootPairing.IsIrreducible.mk' P
  intro q hinv hq
  have hsimple : ∃ i : b.support, P.root i ∈ q := by
    by_contra! h
    exact hq (RootPairing.eq_bot_of_forall_root_not_mem (b := b) (fun i ↦ hinv i) h)
  obtain ⟨i, hi⟩ := hsimple
  -- adjacency in the diagram is exactly nonvanishing of the Cartan entry, hence of the pairing
  have propagate {u v : b.support} (hadj : (diagramGraph b.cartanMatrix).Adj u v)
      (hu : P.root u ∈ q) : P.root v ∈ q :=
    RootPairing.root_mem_of_pairing_ne_zero (hinv v)
      (fun hp ↦ (diagramGraph_adj.mp hadj).2.1
        (b.cartanMatrix_apply_eq_zero_iff_pairing.mpr hp)) hu
  have hall : ∀ j : b.support, P.root j ∈ q := by
    intro j
    obtain ⟨w⟩ := hconn.preconnected i j
    let rec along {u v : b.support} (w : (diagramGraph b.cartanMatrix).Walk u v)
        (hu : P.root u ∈ q) : P.root v ∈ q :=
      match w with
      | .nil => hu
      | .cons hadj w => along w (propagate hadj hu)
    exact along w hi
  rw [eq_top_iff, ← b.toWeightBasis.span_eq]
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨j, rfl⟩
  rw [b.toWeightBasis_apply]
  exact hall j

end

namespace HasCartanType

variable {K M N ι : Type*} [Field K] [CharZero K] [AddCommGroup M] [Module K M]
  [AddCommGroup N] [Module K N] {P : RootPairing ι K M N} [P.IsCrystallographic]

/-- A root system whose base has a valid standard Cartan type is irreducible. -/
theorem isIrreducible [P.IsRootSystem] {b : P.Base} {t : DynkinType}
    (h : HasCartanType P b t) (ht : t.Valid) :
    P.IsIrreducible := by
  obtain ⟨e, he⟩ := (hasCartanType_iff b t).mp h
  let graphIso : diagramGraph b.cartanMatrix ≃g diagramGraph t.cartanMatrix := by
    refine ⟨e, ?_⟩
    intro i j
    simp only [diagramGraph_adj, he]
    constructor
    · rintro ⟨hij, h₁, h₂⟩
      exact ⟨fun h ↦ hij (congrArg e h), h₁, h₂⟩
    · rintro ⟨hij, h₁, h₂⟩
      exact ⟨fun h ↦ hij (e.injective h), h₁, h₂⟩
  exact RootPairing.isIrreducible_of_connected_diagramGraph_cartanMatrix (P := P) b
    (graphIso.connected_iff.mpr (DynkinType.connected_diagramGraph_cartanMatrix ht))

end HasCartanType

end TauCeti

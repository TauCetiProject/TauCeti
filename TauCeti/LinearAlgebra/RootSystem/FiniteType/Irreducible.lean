/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.SimpleGraph.Connectivity.Connected
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
The argument is stated for any family of roots whose roots and coroots span, not only for the
simple roots of a base, so that it also applies to a family known to span before a base is built.

## Main results

* `RootPairing.isIrreducible_of_connected_diagramGraph_pairingIn`: a family of roots whose roots
  and coroots span, with connected diagram of Cartan integers, makes a root pairing irreducible.
* `RootPairing.isIrreducible_of_connected_diagramGraph_cartanMatrix`: a connected base
  diagram makes a root system irreducible.
* `RootPairing.nonempty_of_isIrreducible`, `RootPairing.Base.nonempty_support_of_isIrreducible`,
  and `RootPairing.Base.isIrreducible_of_cartanMatrix_equiv`: an irreducible root system has
  nonempty root index type and nonempty base support, and irreducibility transfers along an
  isomorphism of Cartan matrices of bases.
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
  ⟨(_root_.SimpleGraph.preconnected_pathGraph n).mono h⟩

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
        refine SimpleGraph.connected_of_exists_adj_lt ⟨0, by omega⟩ fun i hi ↦ ?_
        replace hi : (i : ℕ) ≠ 0 := fun h ↦ hi (Fin.ext h)
        by_cases hlast : (i : ℕ) = n - 1
        · let j : Fin n := ⟨n - 3, by omega⟩
          have hji : j = ⟨n - 3, by omega⟩ := rfl
          exact ⟨j, Fin.mk_lt_of_lt_val (by omega), hji ▸ adj_fork_D hn i hlast⟩
        · let j : Fin n := ⟨(i : ℕ) - 1, by omega⟩
          have hji : (⟨(j : ℕ) + 1, by simp [j]; omega⟩ : Fin n) = i := by
            apply Fin.ext
            simp [j]
            omega
          exact ⟨j, Fin.mk_lt_of_lt_val (by omega), hji ▸ adj_succ_D hn j (by simp [j]; omega)⟩
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
      (SimpleGraph.connected_of_exists_adj_lt 0 (by decide) :
        (diagramGraph CartanMatrix.F₄).Connected)
  | G2 => simpa only [rank_G2, cartanMatrix_G2] using
      (SimpleGraph.connected_of_exists_adj_lt 0 (by decide) :
        (diagramGraph CartanMatrix.G₂.transpose).Connected)

end DynkinType

section

variable {K M N ι : Type*} [Field K] [CharZero K] [AddCommGroup M] [Module K M]
  [AddCommGroup N] [Module K N] {P : RootPairing ι K M N} [P.IsCrystallographic]

omit [P.IsCrystallographic] [CharZero K] in
/-- **A submodule invariant under the simple reflections and containing no simple root is
trivial.** If `q` is invariant under the reflection at each element of the base's support and
misses the root there, then `q = ⊥`.

Invariance is asked at the support only, not under every reflection of `P`. -/
theorem _root_.RootPairing.eq_bot_of_forall_root_not_mem
    [NeZero (2 : K)] [P.IsRootSystem] {b : P.Base} {q : Submodule K M}
    (hinv : ∀ i : b.support, q ∈ Module.End.invtSubmodule (P.reflection i))
    (h : ∀ i : b.support, P.root i ∉ q) : q = ⊥ :=
  RootPairing.eq_bot_of_forall_root_not_mem_of_span_coroot_eq_top
    (e := ((↑) : b.support → ι)) hinv h (by simp [range_comp])

/-- **Over a field of characteristic zero, a crystallographic root pairing is irreducible when a
family of roots whose roots and coroots both span has connected diagram** of Cartan integers.
No base is needed: the family need not consist of simple roots. -/
theorem _root_.RootPairing.isIrreducible_of_connected_diagramGraph_pairingIn
    {J : Type*} (e : J → ι)
    (hroot : Submodule.span K (range (P.root ∘ e)) = ⊤)
    (hcoroot : Submodule.span K (range (P.coroot ∘ e)) = ⊤)
    (hconn : (diagramGraph (Matrix.of fun u v ↦ P.pairingIn ℤ (e u) (e v))).Connected) :
    P.IsIrreducible := by
  let _ : Nontrivial M :=
    ⟨⟨P.root (e hconn.nonempty.some), 0, P.ne_zero _⟩⟩
  apply RootPairing.IsIrreducible.mk' P
  intro q hinv hq
  have hsimple : ∃ j, P.root (e j) ∈ q := by
    by_contra! h
    exact hq (RootPairing.eq_bot_of_forall_root_not_mem_of_span_coroot_eq_top
      (fun j ↦ hinv (e j)) h hcoroot)
  obtain ⟨i, hi⟩ := hsimple
  -- adjacency in the diagram is nonvanishing of the Cartan integer, hence of the pairing
  have propagate {u v : J}
      (hadj : (diagramGraph (Matrix.of fun u v ↦ P.pairingIn ℤ (e u) (e v))).Adj u v)
      (hu : P.root (e u) ∈ q) : P.root (e v) ∈ q := by
    refine RootPairing.root_mem_of_isUnit_pairing (hinv (e v)) (Ne.isUnit fun hp ↦ ?_) hu
    apply (diagramGraph_adj.mp hadj).2.1
    apply FaithfulSMul.algebraMap_injective ℤ K
    rw [Matrix.of_apply, P.algebraMap_pairingIn, map_zero, hp]
  have hall (j : J) : P.root (e j) ∈ q := by
    obtain ⟨w⟩ := hconn.preconnected i j
    let rec along {u v : J}
        (w : (diagramGraph (Matrix.of fun u v ↦ P.pairingIn ℤ (e u) (e v))).Walk u v)
        (hu : P.root (e u) ∈ q) : P.root (e v) ∈ q :=
      match w with
      | .nil => hu
      | .cons hadj w => along w (propagate hadj hu)
    exact along w hi
  rw [eq_top_iff, ← hroot]
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨j, rfl⟩
  exact hall j

/-- A crystallographic root system with a connected Dynkin diagram is irreducible.

Characteristic zero ensures that a nonzero integral Cartan entry stays nonzero in the field when
membership propagates across an edge. It also supplies the standard `2 ≠ 0` hypothesis in
Mathlib's invariant-submodule criterion for a reflection. -/
theorem _root_.RootPairing.isIrreducible_of_connected_diagramGraph_cartanMatrix
    [P.IsRootSystem] (b : P.Base)
    (hconn : (diagramGraph b.cartanMatrix).Connected) : P.IsIrreducible := by
  have hM : (Matrix.of fun u v : b.support ↦ P.pairingIn ℤ u v) = b.cartanMatrix := by
    ext u v
    simp [RootPairing.Base.cartanMatrix, RootPairing.Base.cartanMatrixIn_def]
  exact RootPairing.isIrreducible_of_connected_diagramGraph_pairingIn ((↑) : b.support → ι)
    (by simp [range_comp]) (by simp [range_comp]) (by rwa [hM])

/-- An irreducible root system has nonempty root index type. -/
theorem _root_.RootPairing.nonempty_of_isIrreducible
    {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsIrreducible] : Nonempty ι := by
  have := RootPairing.IsIrreducible.nontrivial P
  by_contra h
  rw [not_nonempty_iff] at h
  obtain ⟨m, hm⟩ := exists_ne (0 : M)
  have hmem : m ∈ (⊥ : Submodule R M) := by
    rw [← Submodule.span_empty (R := R), ← Set.range_eq_empty_iff.mpr h,
      RootPairing.IsRootSystem.span_root_eq_top (P := P)]
    exact Submodule.mem_top
  exact hm ((Submodule.mem_bot R).1 hmem)

/-- The base of an irreducible root system has nonempty support. -/
theorem _root_.RootPairing.Base.nonempty_support_of_isIrreducible
    {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] {P : RootPairing ι R M N} [P.IsRootSystem]
    [P.IsIrreducible] (b : P.Base) : Nonempty b.support := by
  have := RootPairing.IsIrreducible.nontrivial P
  by_contra h
  rw [not_nonempty_iff] at h
  exact not_subsingleton M b.toWeightBasis.equivFun.subsingleton

/-- For a finite reduced irreducible crystallographic root system `P` over a characteristic-zero
domain, irreducibility transfers to any crystallographic root system `Q` over a characteristic-zero
field (possibly on a different root index type `ι'`) along a support equivalence of bases that
preserves the Cartan matrix. -/
theorem _root_.RootPairing.Base.isIrreducible_of_cartanMatrix_equiv
    {ι R M N : Type*} [CommRing R] [IsDomain R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing ι R M N} [Finite ι] [P.IsCrystallographic] [P.IsReduced]
    [P.IsRootSystem] [P.IsIrreducible] (b : P.Base)
    {ι' S M' N' : Type*} [Field S] [CharZero S] [AddCommGroup M'] [Module S M']
    [AddCommGroup N'] [Module S N'] {Q : RootPairing ι' S M' N'} [Q.IsRootSystem]
    [Q.IsCrystallographic] (bQ : Q.Base) (e : bQ.support ≃ b.support)
    (hC : ∀ u v, bQ.cartanMatrix u v = b.cartanMatrix (e u) (e v)) : Q.IsIrreducible := by
  have hne' : Nonempty bQ.support := b.nonempty_support_of_isIrreducible.map e.symm
  let iso : diagramGraph bQ.cartanMatrix ≃g diagramGraph b.cartanMatrix :=
    { toEquiv := e, map_rel_iff' := @fun u v ↦ by simp [diagramGraph_adj, hC] }
  refine RootPairing.isIrreducible_of_connected_diagramGraph_cartanMatrix bQ ⟨fun u v ↦ ?_⟩
  obtain ⟨w⟩ := preconnected_diagramGraph_cartanMatrix b (iso u) (iso v)
  simpa using (w.map iso.symm.toHom).reachable

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

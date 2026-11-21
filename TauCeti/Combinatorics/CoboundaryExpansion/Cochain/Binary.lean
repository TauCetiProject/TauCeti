/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.CoboundaryExpansion.Cochain.SimpleGraph
public import TauCeti.GroupTheory.Perm.Basic
import TauCeti.GroupTheory.Perm.Fin

/-!
# Binary graph–cochain dictionary

On a finite vertex type `V`, `Equiv.Perm (Fin 2)`-valued `1`-cochains on
`TauCeti.TwoComplex.complete V` are in canonical bijection with simple graphs on `V`
(`TauCeti.simpleGraphEquivPermFinTwo`): adjacent vertex pairs carry `Equiv.swap 0 1` and
non-adjacent pairs carry `1`, while the inverse map takes a cochain `α` to `α.supportGraph`.

## Main definitions and results

* `TauCeti.simpleGraphEquivPermFinTwo`: equivalence between `SimpleGraph V` and
  `Cochain (TwoComplex.complete V) (Equiv.Perm (Fin 2))`.
* `TauCeti.simpleGraphEquivPermFinTwo_symm_smul`: gauge action on binary cochains corresponds to
  complete-graph cut switching on `supportGraph`.
* `TauCeti.Cochain.isCoboundary_fin_two_iff`: an `Equiv.Perm (Fin 2)`-valued `1`-cochain on
  `TwoComplex.complete V` is a coboundary iff its support graph is a complete-graph cut.
-/

public section

open scoped symmDiff

namespace TauCeti

section PermFinTwo

/-- Simple graphs on a finite vertex type `V` are in bijection with `Equiv.Perm (Fin 2)`-valued
`1`-cochains on `TwoComplex.complete V`: adjacent vertex pairs carry `Equiv.swap 0 1` and
non-adjacent pairs carry `1`. -/
noncomputable def simpleGraphEquivPermFinTwo (V : Type*) [Fintype V] :
    SimpleGraph V ≃ Cochain (TwoComplex.complete V) (Equiv.Perm (Fin 2)) where
  toFun G := G.toCochain (Equiv.Perm.swap_isSwap_iff.mpr Fin.zero_ne_one).mul_self
  invFun α := α.supportGraph
  left_inv G :=
    SimpleGraph.supportGraph_toCochain G
      (Equiv.Perm.swap_isSwap_iff.mpr Fin.zero_ne_one).mul_self
      (Equiv.Perm.swap_isSwap_iff.mpr Fin.zero_ne_one).isCycle.ne_one
  right_inv α := by
    ext u v _
    rcases (α u v).eq_one_or_swap_fin_two with h | h <;> simp [h]

/-- `TauCeti.simpleGraphEquivPermFinTwo` agrees with `SimpleGraph.toCochain` at `Equiv.swap 0 1`. -/
theorem simpleGraphEquivPermFinTwo_eq_toCochain {V : Type*} [Fintype V] (G : SimpleGraph V) :
    simpleGraphEquivPermFinTwo V G =
      G.toCochain (Equiv.Perm.swap_isSwap_iff.mpr Fin.zero_ne_one).mul_self :=
  (rfl)

/-- `TauCeti.simpleGraphEquivPermFinTwo` assigns `Equiv.swap 0 1` to adjacent vertices. -/
@[simp, grind =]
theorem simpleGraphEquivPermFinTwo_apply_of_adj {V : Type*} [Fintype V] {G : SimpleGraph V}
    {u v : V} (h : G.Adj u v) :
    simpleGraphEquivPermFinTwo V G u v = Equiv.swap 0 1 :=
  SimpleGraph.toCochain_apply_of_adj
    (Equiv.Perm.swap_isSwap_iff.mpr (Fin.zero_ne_one : (0 : Fin 2) ≠ 1)).mul_self h

/-- `TauCeti.simpleGraphEquivPermFinTwo` assigns `1` to non-adjacent vertices. -/
@[simp, grind =]
theorem simpleGraphEquivPermFinTwo_apply_of_not_adj {V : Type*} [Fintype V] {G : SimpleGraph V}
    {u v : V} (h : ¬ G.Adj u v) :
    simpleGraphEquivPermFinTwo V G u v = 1 :=
  SimpleGraph.toCochain_apply_of_not_adj
    (Equiv.Perm.swap_isSwap_iff.mpr (Fin.zero_ne_one : (0 : Fin 2) ≠ 1)).mul_self h

/-- Explicit `ite` evaluation of `TauCeti.simpleGraphEquivPermFinTwo` when `G.Adj` is decidable. -/
theorem simpleGraphEquivPermFinTwo_apply {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (u v : V) :
    simpleGraphEquivPermFinTwo V G u v = if G.Adj u v then Equiv.swap 0 1 else 1 :=
  G.toCochain_apply
    (Equiv.Perm.swap_isSwap_iff.mpr (Fin.zero_ne_one : (0 : Fin 2) ≠ 1)).mul_self u v

/-- The inverse of `TauCeti.simpleGraphEquivPermFinTwo` is `Cochain.supportGraph`. -/
@[simp]
theorem simpleGraphEquivPermFinTwo_symm_eq_supportGraph {V : Type*} [Fintype V]
    (α : Cochain (TwoComplex.complete V) (Equiv.Perm (Fin 2))) :
    (simpleGraphEquivPermFinTwo V).symm α = α.supportGraph :=
  (rfl)

/-- The inverse of `TauCeti.simpleGraphEquivPermFinTwo` makes `u` and `v` adjacent precisely when
`α u v ≠ 1`. -/
@[grind =]
theorem simpleGraphEquivPermFinTwo_symm_adj {V : Type*} [Fintype V]
    (α : Cochain (TwoComplex.complete V) (Equiv.Perm (Fin 2))) (u v : V) :
    ((simpleGraphEquivPermFinTwo V).symm α).Adj u v ↔ α u v ≠ 1 := by
  rw [simpleGraphEquivPermFinTwo_symm_eq_supportGraph, Cochain.supportGraph_adj]

/-- Adjacency in `(simpleGraphEquivPermFinTwo V).symm α` is decidable because equality in
`Equiv.Perm (Fin 2)` is decidable. -/
instance instDecidableRelSimpleGraphEquivPermFinTwoSymm {V : Type*} [Fintype V]
    (α : Cochain (TwoComplex.complete V) (Equiv.Perm (Fin 2))) :
    DecidableRel ((simpleGraphEquivPermFinTwo V).symm α).Adj :=
  fun u v ↦ decidable_of_iff (α u v ≠ 1) (simpleGraphEquivPermFinTwo_symm_adj α u v).symm

/-- Acting on `α : Cochain (TwoComplex.complete V) (Equiv.Perm (Fin 2))` by a gauge `β` switches
its support graph by the cut `{w | β w ≠ 1}`. -/
theorem simpleGraphEquivPermFinTwo_symm_smul {V : Type*} [Fintype V]
    (β : V → Equiv.Perm (Fin 2)) (α : Cochain (TwoComplex.complete V) (Equiv.Perm (Fin 2))) :
    (simpleGraphEquivPermFinTwo V).symm (β • α) =
      (simpleGraphEquivPermFinTwo V).symm α ∆
        (⊤ : SimpleGraph V).between {w | β w ≠ 1} {w | β w ≠ 1}ᶜ := by
  classical
  have hβ : β = fun v ↦ if v ∈ {w | β w ≠ 1} then Equiv.swap 0 1 else 1 :=
    funext fun v ↦ Equiv.Perm.eq_ite_ne_one_fin_two (β v)
  have hswap : (Equiv.swap (0 : Fin 2) 1).IsSwap := Equiv.Perm.swap_isSwap_iff.mpr Fin.zero_ne_one
  conv_lhs =>
    rw [← (simpleGraphEquivPermFinTwo V).apply_symm_apply α,
      simpleGraphEquivPermFinTwo_eq_toCochain, hβ,
      ((simpleGraphEquivPermFinTwo V).symm α).smul_ite_mem_toCochain hswap.mul_self {w | β w ≠ 1}]
  exact SimpleGraph.supportGraph_toCochain _ hswap.mul_self hswap.isCycle.ne_one

/-- An `Equiv.Perm (Fin 2)`-valued `1`-cochain on `TwoComplex.complete V` is a coboundary if and
only if its support graph is a complete-graph cut. -/
theorem Cochain.isCoboundary_fin_two_iff {V : Type*} [Fintype V]
    (α : Cochain (TwoComplex.complete V) (Equiv.Perm (Fin 2))) :
    α.IsCoboundary ↔
      ∃ S : Set V, (simpleGraphEquivPermFinTwo V).symm α = (⊤ : SimpleGraph V).between S Sᶜ := by
  have hswap : (Equiv.swap (0 : Fin 2) 1).IsSwap := Equiv.Perm.swap_isSwap_iff.mpr Fin.zero_ne_one
  conv_lhs =>
    rw [← (simpleGraphEquivPermFinTwo V).apply_symm_apply α,
      simpleGraphEquivPermFinTwo_eq_toCochain]
  exact ((simpleGraphEquivPermFinTwo V).symm α).isCoboundary_toCochain_iff hswap.mul_self
    hswap.isCycle.ne_one

end PermFinTwo

end TauCeti

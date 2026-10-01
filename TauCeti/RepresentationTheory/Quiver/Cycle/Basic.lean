/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Quiver.Basic
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fintype.Basic

/-!
# The cyclically oriented cycle quiver

The **cycle quiver** on `n + 2` vertices has vertices indexed by `Fin (n + 2)` and one arrow from
each vertex to the next, the last vertex being joined back to the first. Its underlying graph is
the extended Dynkin diagram `Ã_{n+1}`, and it is the smallest family of quivers with an oriented
cycle through more than one vertex: the one-vertex case is the loop quiver
`TauCeti.Quiver.OneLoop`, which is treated on its own in
`TauCeti.RepresentationTheory.Quiver.OneLoop.Basic`, so the family starts at two vertices here.

This file carries only the vertex and arrow data, together with the induction principle that walks
a vertex back to the first one along the arrows that are not the closing one
(`TauCeti.Quiver.Cycle.induction_of_ne_last`). That principle is what makes the cycle's
representations tractable: an endomorphism of a representation whose non-closing arrows all act
by the identity is constant along the cycle, which is how
`TauCeti.RepresentationTheory.Quiver.Cycle.FiniteRepType` computes endomorphism algebras.

## Main definitions

* `TauCeti.Quiver.Cycle n`: the vertex type, a copy of `Fin (n + 2)`, with a `Quiver` instance
  whose only arrows run from a vertex to its cyclic successor.
* `TauCeti.Quiver.Cycle.succ`: the cyclic successor of a vertex, the head of the arrow out of it.
* `TauCeti.Quiver.Cycle.first` and `TauCeti.Quiver.Cycle.last`: the vertices of index `0` and
  `n + 1`; the arrow out of `last` is the one that closes the cycle.
* `TauCeti.Quiver.Cycle.arrow`: the arrow from a vertex to its cyclic successor.

## Main results

* `TauCeti.Quiver.Cycle.eq_succ_of_hom`: every arrow runs from a vertex to its cyclic successor.
* `TauCeti.Quiver.Cycle.nonempty_hom_iff` and `TauCeti.Quiver.Cycle.isEmpty_hom_iff`: there is an
  arrow from a vertex to its cyclic successor, and between no other pair of vertices.
* `TauCeti.Quiver.Cycle.succ_last`: the arrow out of the last vertex closes the cycle.
* `TauCeti.Quiver.Cycle.induction_of_ne_last`: a property of vertices that holds at `first` and
  passes along the arrow out of every vertex other than `last` holds at every vertex.

## Implementation notes

The vertex type is a one-field structure wrapping `Fin (n + 2)` rather than `Fin (n + 2)` itself,
so that the `Quiver` instance does not leak onto every `Fin`; `TauCeti.Quiver.Cycle.equivFin`
is the identification, and `TauCeti.Quiver.Cycle.index` reads the underlying index. An arrow is a
`PLift` of the proposition that the head is the cyclic successor of the tail, which makes the
arrows between any two vertices a subsingleton for free.

## References

The cycle quiver is the cyclic orientation of the extended Dynkin diagram `Ã_{n+1}`, one of the
obstructions in the non-Dynkin half of Gabriel's theorem; see I. Assem, D. Simson, A. Skowroński,
*Elements of the Representation Theory of Associative Algebras*, Volume I, Chapter VII.
-/

public section

namespace TauCeti

open _root_.Quiver

namespace Quiver

/-- The **cycle quiver** on `n + 2` vertices: the vertices are indexed by `Fin (n + 2)` and each
one has a single arrow to the next, cyclically. Its underlying graph is the extended Dynkin
diagram `Ã_{n+1}`. -/
structure Cycle (n : ℕ) where
  /-- The index of a vertex of the cycle quiver. -/
  index : Fin (n + 2)
deriving DecidableEq

namespace Cycle

variable {n : ℕ}

/-- The vertices of the cycle quiver are indexed by `Fin (n + 2)`. -/
def equivFin : Cycle n ≃ Fin (n + 2) where
  toFun := index
  invFun := mk

instance : Fintype (Cycle n) := Fintype.ofEquiv _ equivFin.symm

/-- The **cyclic successor** of a vertex, the head of the arrow out of it. At the last vertex it
wraps around to the first. -/
def succ (i : Cycle n) : Cycle n := ⟨i.index + 1⟩

/-- The first vertex of the cycle quiver, of index `0`. -/
def first : Cycle n := ⟨0⟩

/-- The last vertex of the cycle quiver, of index `n + 1`. The arrow out of it is the one that
closes the cycle. -/
def last : Cycle n := ⟨Fin.last (n + 1)⟩

@[simp] theorem index_succ (i : Cycle n) : i.succ.index = i.index + 1 := (rfl)

@[simp] theorem index_first : (first : Cycle n).index = 0 := (rfl)

@[simp] theorem index_last : (last : Cycle n).index = Fin.last (n + 1) := (rfl)

/-- Two vertices with the same index are equal. -/
@[ext] theorem ext {i j : Cycle n} (h : i.index = j.index) : i = j := by
  cases i; cases j; exact congrArg mk h

instance : _root_.Quiver (Cycle n) where
  Hom i j := PLift (j = i.succ)

instance (i j : Cycle n) : Subsingleton (i ⟶ j) :=
  ⟨fun a b ↦ by cases a; cases b; rfl⟩

/-- **The arrow out of a vertex**, running to its cyclic successor. -/
def arrow (i : Cycle n) : i ⟶ i.succ := PLift.up rfl

/-- Every arrow of the cycle quiver runs from a vertex to its cyclic successor. -/
theorem eq_succ_of_hom {i j : Cycle n} (e : i ⟶ j) : j = i.succ := e.down

/-- There is an arrow from `i` to `j` exactly when `j` is the cyclic successor of `i`. -/
@[simp]
theorem nonempty_hom_iff {i j : Cycle n} : Nonempty (i ⟶ j) ↔ j = i.succ :=
  ⟨fun ⟨e⟩ ↦ eq_succ_of_hom e, fun h ↦ ⟨PLift.up h⟩⟩

/-- The arrow type from `i` to `j` is empty unless `j` is the cyclic successor of `i`. -/
@[simp]
theorem isEmpty_hom_iff {i j : Cycle n} : IsEmpty (i ⟶ j) ↔ j ≠ i.succ := by
  rw [← not_nonempty_iff]
  exact not_congr nonempty_hom_iff

/-- **The arrow out of the last vertex closes the cycle**, running back to the first vertex. -/
@[simp] theorem succ_last : (last : Cycle n).succ = first := by
  refine ext ?_
  rw [index_succ, index_last, index_first]
  ext
  simp

/-- **Induction along the cycle, avoiding the closing arrow.** A property of vertices that holds at
the first vertex and passes from a vertex other than the last one to its cyclic successor holds at
every vertex: walking forward from `first` reaches every vertex without ever leaving `last`. -/
theorem induction_of_ne_last {P : Cycle n → Prop} (hfirst : P first)
    (hstep : ∀ i : Cycle n, i ≠ last → P i → P i.succ) (i : Cycle n) : P i := by
  -- The induction runs on the underlying natural number of the index rather than on the vertex:
  -- the successor step needs to know that the index does not wrap around, which is exactly what
  -- excluding `last` supplies.
  obtain ⟨⟨v, hv⟩⟩ := i
  induction v with
  | zero =>
    have hzero : (⟨⟨0, hv⟩⟩ : Cycle n) = first := ext (Fin.ext (by simp))
    rw [hzero]
    exact hfirst
  | succ v ih =>
    have hvlt : v < n + 2 := by omega
    have hne : (⟨⟨v, hvlt⟩⟩ : Cycle n) ≠ last := fun h ↦ by
      have := congrArg (fun j : Cycle n ↦ (j.index : ℕ)) h
      simp only [index_last, Fin.val_last] at this
      omega
    have hsucc : (⟨⟨v, hvlt⟩⟩ : Cycle n).succ = ⟨⟨v + 1, hv⟩⟩ := by
      refine ext ?_
      rw [index_succ]
      ext
      simp [Fin.val_add, Nat.mod_eq_of_lt hv]
    exact hsucc ▸ hstep _ hne (ih hvlt)

end Cycle

end Quiver

end TauCeti

end

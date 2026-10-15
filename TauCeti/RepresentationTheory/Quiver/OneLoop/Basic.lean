/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Quiver.Path
public import Mathlib.Data.Fintype.Basic

/-!
# The loop quiver

The loop quiver `•↺` has a single vertex and a single arrow from it to itself. It is the smallest
quiver that is not acyclic, which makes it the standard boundary case of the theory: its path
algebra is the infinite-dimensional `k[X]`
(`TauCeti.RepresentationTheory.Quiver.OneLoop.PathAlgebra`), and it has infinite representation
type over every field (`TauCeti.RepresentationTheory.Quiver.OneLoop.FiniteRepType`).

This file defines the vertex and arrow data and classifies paths by their length, independently
of the algebra and representation theory.

## Main definitions

* `TauCeti.Quiver.OneLoop`: the vertex type, a singleton, with a `Quiver` instance whose only
  arrow type is `PUnit`.
* `TauCeti.Quiver.OneLoop.loop`: the unique arrow, from the vertex to itself.
* `TauCeti.Quiver.OneLoop.totalPathEquivNat`: paths are classified by their length.
-/

public section

namespace TauCeti

open _root_.Quiver

namespace Quiver

/-- The quiver with one vertex and one loop. -/
inductive OneLoop : Type
  | vertex
  deriving DecidableEq

namespace OneLoop

instance : Fintype OneLoop where
  elems := {vertex}
  complete x := by cases x; simp

instance : Unique OneLoop where
  default := vertex
  uniq x := by cases x; rfl

instance : _root_.Quiver OneLoop where
  Hom _ _ := PUnit

instance (a b : OneLoop) : Subsingleton (a ⟶ b) :=
  inferInstanceAs (Subsingleton PUnit)

/-- The unique loop in the one-loop quiver. -/
def loop : (vertex : OneLoop) ⟶ vertex := PUnit.unit

private def pathOfLength : ℕ → _root_.Quiver.Path (vertex : OneLoop) vertex
  | 0 => .nil
  | n + 1 => (pathOfLength n).cons loop

@[simp]
private theorem length_pathOfLength (n : ℕ) : (pathOfLength n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [pathOfLength, ih]

/-- Paths in the one-loop quiver are classified by their length. -/
def totalPathEquivNat : (Σ a b : OneLoop, _root_.Quiver.Path a b) ≃ ℕ where
  toFun x := x.2.2.length
  invFun n := ⟨vertex, vertex, pathOfLength n⟩
  left_inv := by
    rintro ⟨a, b, p⟩
    induction p with
    | nil => cases a; rfl
    | @cons b c p e ih =>
      cases a; cases b; cases c
      simp only [Sigma.mk.injEq, heq_eq_eq, true_and] at ih
      simp [pathOfLength, ih, eq_iff_true_of_subsingleton]
  right_inv := length_pathOfLength

/-- The path classification sends each path to its length. -/
@[simp]
theorem totalPathEquivNat_apply (x : Σ a b : OneLoop, _root_.Quiver.Path a b) :
    totalPathEquivNat x = x.2.2.length := (rfl)

/-- The canonical path associated with `n` has length `n`. -/
@[simp]
theorem length_totalPathEquivNat_symm (n : ℕ) :
    (totalPathEquivNat.symm n).2.2.length = n :=
  totalPathEquivNat.apply_symm_apply n

end OneLoop

end Quiver

end TauCeti

end

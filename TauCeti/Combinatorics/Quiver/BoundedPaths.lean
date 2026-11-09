/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Finite.Sigma
public import Mathlib.Basic.Finite.Sum
public import Mathlib.Combinatorics.Quiver.Path
public import Mathlib.Data.Set.Finite.Range

/-!
# Finitely many paths of bounded length

A quiver with finitely many arrows into each vertex has only finitely many paths of length at most
`n` between any two vertices: read backwards from its target, such a path is a sequence of at most
`n` arrows, each chosen among the finitely many arrows into the vertex reached so far. When the
vertex set is finite as well, the paths of bounded length form a finite subset of the total path
space. No acyclicity is involved: the bound on the length is what makes the count finite. In an
acyclic finite quiver such a bound holds automatically, while for a bound quiver algebra the
bounded count is what its finite dimensionality rests on.

## Main results

* `TauCeti.Quiver.finite_boundedPaths`: `Quiver.Path.BoundedPaths a b n`, the paths from `a` to `b`
  of length at most `n`, is a finite type when every vertex has finitely many incoming arrows.
* `TauCeti.Quiver.finite_setOf_length_le` and `TauCeti.Quiver.finite_setOf_length_lt`: the paths of
  bounded length form a finite set of the total path space `Σ a b, Quiver.Path a b`.
-/

public section

namespace TauCeti

universe u v

namespace Quiver

variable {V : Type u} [_root_.Quiver.{v} V]

/-- **Paths of bounded length are finite** when every vertex has finitely many incoming arrows:
for each `n`, there are only finitely many paths from `a` to `b` of length at most `n`. The vertex
set itself may be infinite. -/
theorem finite_boundedPaths [∀ b : V, Finite (Σ c : V, c ⟶ b)] (n : ℕ) (a b : V) :
    Finite (_root_.Quiver.Path.BoundedPaths a b n) := by
  induction n generalizing b with
  | zero => infer_instance
  | succ n ih =>
    refine Finite.of_surjective (α := _root_.Quiver.Path.BoundedPaths a b 0 ⊕
        Σ e : (Σ c : V, c ⟶ b), _root_.Quiver.Path.BoundedPaths a e.1 n)
      (Sum.elim (fun p ↦ ⟨p.1, p.2.trans n.succ.zero_le⟩)
        fun x ↦ ⟨x.2.1.cons x.1.2, Nat.succ_le_succ x.2.2⟩) ?_
    rintro ⟨_ | ⟨p, e⟩, hp⟩
    · exact ⟨.inl ⟨.nil, le_rfl⟩, rfl⟩
    · exact ⟨.inr ⟨⟨_, e⟩, p, Nat.le_of_succ_le_succ hp⟩, rfl⟩

/-- **The paths of length at most `n` are a finite subset of the total path space.** -/
theorem finite_setOf_length_le [Finite V] [∀ a b : V, Finite (a ⟶ b)] (n : ℕ) :
    {x : Σ a b : V, _root_.Quiver.Path a b | x.2.2.length ≤ n}.Finite := by
  have (a b : V) := finite_boundedPaths n a b
  refine (Set.finite_range fun p : Σ a b : V, _root_.Quiver.Path.BoundedPaths a b n ↦
    (⟨p.1, p.2.1, p.2.2.1⟩ : Σ a b : V, _root_.Quiver.Path a b)).subset ?_
  rintro ⟨a, b, p⟩ hp
  exact ⟨⟨a, b, p, hp⟩, rfl⟩

/-- **The paths of length less than `n` are a finite subset of the total path space.** -/
theorem finite_setOf_length_lt [Finite V] [∀ a b : V, Finite (a ⟶ b)] (n : ℕ) :
    {x : Σ a b : V, _root_.Quiver.Path a b | x.2.2.length < n}.Finite :=
  (finite_setOf_length_le n).subset fun _ hx => Nat.le_of_lt hx

end Quiver

end TauCeti

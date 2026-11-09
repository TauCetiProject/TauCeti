/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Zigzag.Orientation
public import Mathlib.Combinatorics.SimpleGraph.Hasse

/-!
# The linearly oriented quiver of type A

`LineQuiver n` is the linear-order orientation of Mathlib's path graph on `Fin n`.
A directed path exists precisely when its source is at most its target, and such a path
is unique. These facts allow interval constructions to use the order of the vertices
while retaining the successor arrows of the path graph.
-/

public section

namespace TauCeti

open DoubledQuiver

/-- The linear-order orientation of the path graph `0 — 1 — ⋯ — n - 1`. -/
abbrev LineQuiver (n : ℕ) :=
  OrientedQuiver (SimpleGraph.pathGraph n) (Orientation.ofLinearOrder _)

namespace LineQuiver

variable {n : ℕ}

instance : LinearOrder (LineQuiver n) :=
  LinearOrder.lift' (OrientedQuiver.vertexEquiv (SimpleGraph.pathGraph n)
    (Orientation.ofLinearOrder _)).symm (Equiv.injective _)

/-- Comparison in the line quiver is comparison of the underlying vertex indices. -/
theorem le_iff (i j : LineQuiver n) :
    i ≤ j ↔ (OrientedQuiver.vertexEquiv _ _).symm i ≤
      (OrientedQuiver.vertexEquiv _ _).symm j := (Iff.rfl)

/-- Strict comparison in the line quiver is strict comparison of the underlying indices. -/
theorem lt_iff (i j : LineQuiver n) :
    i < j ↔ (OrientedQuiver.vertexEquiv _ _).symm i <
      (OrientedQuiver.vertexEquiv _ _).symm j := (Iff.rfl)

/-- Inclusion of graph vertices into the line quiver preserves and reflects comparison. -/
@[simp]
theorem vertex_le_vertex_iff (i j : Fin n) :
    OrientedQuiver.vertex (SimpleGraph.pathGraph n) (Orientation.ofLinearOrder _) i ≤
      OrientedQuiver.vertex (SimpleGraph.pathGraph n) (Orientation.ofLinearOrder _) j ↔
        i ≤ j := by
  rw [le_iff]
  simp only [OrientedQuiver.vertexEquiv_symm_vertex]

/-- Inclusion of graph vertices preserves and reflects strict comparison. -/
@[simp]
theorem vertex_lt_vertex_iff (i j : Fin n) :
    OrientedQuiver.vertex (SimpleGraph.pathGraph n) (Orientation.ofLinearOrder _) i <
      OrientedQuiver.vertex (SimpleGraph.pathGraph n) (Orientation.ofLinearOrder _) j ↔
        i < j := by
  rw [lt_iff]
  simp only [OrientedQuiver.vertexEquiv_symm_vertex]

/-- An arrow in the line quiver increases the vertex index by one. -/
theorem index_add_one_eq {i j : LineQuiver n} (e : i ⟶ j) :
    ((OrientedQuiver.vertexEquiv _ _).symm i : Fin n).val + 1 =
      ((OrientedQuiver.vertexEquiv _ _).symm j : Fin n).val := by
  have e' : OrientedQuiver.vertex (SimpleGraph.pathGraph n) (Orientation.ofLinearOrder _)
      ((OrientedQuiver.vertexEquiv _ _).symm i) ⟶
      OrientedQuiver.vertex (SimpleGraph.pathGraph n) (Orientation.ofLinearOrder _)
        ((OrientedQuiver.vertexEquiv _ _).symm j) := by
    simpa only [← OrientedQuiver.vertexEquiv_apply, Equiv.apply_symm_apply] using e
  have h := OrientedQuiver.homEquiv (SimpleGraph.pathGraph n)
    (Orientation.ofLinearOrder _) _ _ e'
  have hadj := SimpleGraph.pathGraph_adj.mp h.1
  have hlt : ((OrientedQuiver.vertexEquiv _ _).symm i : Fin n).val <
      ((OrientedQuiver.vertexEquiv _ _).symm j : Fin n).val :=
    (Orientation.mem_ofLinearOrder_iff _ _).mp h.2
  omega

/-- An arrow exists exactly when the target index is the successor of the source index. -/
@[simp]
theorem nonempty_hom_iff (i j : LineQuiver n) :
    Nonempty (i ⟶ j) ↔ ((OrientedQuiver.vertexEquiv _ _).symm i : Fin n).val + 1 =
      ((OrientedQuiver.vertexEquiv _ _).symm j : Fin n).val := by
  refine ⟨fun ⟨e⟩ ↦ index_add_one_eq e, fun h ↦ ?_⟩
  have hadj : (SimpleGraph.pathGraph n).Adj
      ((OrientedQuiver.vertexEquiv _ _).symm i)
      ((OrientedQuiver.vertexEquiv _ _).symm j) :=
    SimpleGraph.pathGraph_adj.mpr (Or.inl h)
  have hlt : ((OrientedQuiver.vertexEquiv _ _).symm i : Fin n).val <
      ((OrientedQuiver.vertexEquiv _ _).symm j : Fin n).val := by omega
  have e := OrientedQuiver.arrow _ (Orientation.ofLinearOrder _) hadj
    ((Orientation.mem_ofLinearOrder_iff _ _).mpr hlt)
  exact ⟨by simpa only [← OrientedQuiver.vertexEquiv_apply, Equiv.apply_symm_apply] using e⟩

private theorem nonempty_path_vertex (i j : Fin n) (hij : i ≤ j) :
    Nonempty (Quiver.Path
      (OrientedQuiver.vertex (SimpleGraph.pathGraph n) (Orientation.ofLinearOrder _) i)
      (OrientedQuiver.vertex (SimpleGraph.pathGraph n) (Orientation.ofLinearOrder _) j)) := by
  have h : i.val ≤ j.val := hij
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le h
  clear h
  induction m generalizing j with
  | zero =>
    have he : i = j := Fin.ext (by omega)
    subst j
    exact ⟨Quiver.Path.nil⟩
  | succ m ih =>
    let l : Fin n := ⟨j.val - 1, by omega⟩
    have hl : l.val = i.val + m := by dsimp [l]; omega
    obtain ⟨p⟩ := ih l (by exact_mod_cast (by omega : i.val ≤ l.val)) hl
    have hadj : (SimpleGraph.pathGraph n).Adj l j :=
      SimpleGraph.pathGraph_adj.mpr (Or.inl (by dsimp [l]; omega))
    refine ⟨p.cons (OrientedQuiver.arrow _ _ hadj ?_)⟩
    rw [Orientation.mem_ofLinearOrder_iff]
    exact (by dsimp [l]; omega : l.val < j.val)

/-- Two vertices of the line quiver are joined by a directed path exactly when they are
ordered in the direction of the arrows. -/
theorem nonempty_path_iff_le (i j : LineQuiver n) : Nonempty (Quiver.Path i j) ↔ i ≤ j := by
  refine ⟨fun ⟨p⟩ ↦ OrientedQuiver.le_of_path_ofLinearOrder _ p, fun hij ↦ ?_⟩
  have h := nonempty_path_vertex ((OrientedQuiver.vertexEquiv _ _).symm i)
    ((OrientedQuiver.vertexEquiv _ _).symm j) hij
  simpa only [← OrientedQuiver.vertexEquiv_apply, Equiv.apply_symm_apply] using h

/-- There is at most one directed path between two vertices of the line quiver. -/
instance (i j : LineQuiver n) : Subsingleton (Quiver.Path i j) := by
  refine ⟨fun p q ↦ ?_⟩
  induction p with
  | nil =>
    cases q with
    | nil => rfl
    | @cons l _ p e =>
      have h : ((OrientedQuiver.vertexEquiv _ _).symm i : Fin n).val ≤
          ((OrientedQuiver.vertexEquiv _ _).symm l : Fin n).val :=
        OrientedQuiver.le_of_path_ofLinearOrder (SimpleGraph.pathGraph n) p
      have he := index_add_one_eq e
      omega
  | @cons x y p e ih =>
    cases q with
    | nil =>
      have h : ((OrientedQuiver.vertexEquiv _ _).symm i : Fin n).val ≤
          ((OrientedQuiver.vertexEquiv _ _).symm x : Fin n).val :=
        OrientedQuiver.le_of_path_ofLinearOrder (SimpleGraph.pathGraph n) p
      have he := index_add_one_eq e
      omega
    | @cons x' _ q f =>
      have he := index_add_one_eq e
      have hf := index_add_one_eq f
      have h : x = x' := (OrientedQuiver.vertexEquiv _ _).symm.injective (Fin.ext (by omega))
      subst x'
      rw [ih q, Subsingleton.elim e f]

end LineQuiver
end TauCeti

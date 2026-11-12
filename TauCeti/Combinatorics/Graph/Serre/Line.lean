/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.OfParent
public import Mathlib.Algebra.Group.Action.TypeTags
public import Mathlib.Algebra.Group.Int.Defs

/-!
# The line

The line is the Serre graph with the integers as vertices and one geometric edge between `n` and
`n + 1`: the graph `SerreGraph.ofParent` of the parent map `n ↦ n + 1`. It is the Cayley graph of
the infinite cyclic group, that is of the free group of rank one, and it is a tree: no integer is
a proper iterate of itself under `n ↦ n + 1`, and any two integers have a common iterate.

The coordinate `SerreGraph.lineVertexEquiv` identifies the vertices with the integers, and the
integers act on the line by translation, `SerreGraph.lineShift`, with `k • n = k + n`.

## References

* J.-P. Serre, *Trees*, Chapter I, §2.2 and §6.4.
-/

public section

namespace TauCeti
namespace SerreGraph

/-- The line, the graph of the parent map `n ↦ n + 1` on the integers: the dart `(n, true)` runs
from `n` to `n + 1`, and its reverse `(n, false)` runs back. -/
@[expose] def line : SerreGraph.{0, 0} :=
  ofParent fun n : ℤ => n + 1

theorem line_src (e : ℤ × Bool) : line.src e = if e.2 then e.1 else e.1 + 1 := (rfl)

@[simp] theorem line_rev (e : ℤ × Bool) : line.rev e = (e.1, !e.2) := (rfl)

theorem line_tgt (e : ℤ × Bool) : line.tgt e = if e.2 then e.1 + 1 else e.1 := by
  obtain ⟨n, d⟩ := e
  cases d <;> rfl

/-- The vertices of the line are the integers. -/
def lineVertexEquiv : line.V ≃ ℤ :=
  Equiv.refl ℤ

@[simp] theorem lineVertexEquiv_src (e : ℤ × Bool) :
    lineVertexEquiv (line.src e) = if e.2 then e.1 else e.1 + 1 := (rfl)

/-- A dart of the line moves one step up or down according to its orientation. -/
@[simp] theorem lineVertexEquiv_tgt (e : ℤ × Bool) :
    lineVertexEquiv (line.tgt e) = lineVertexEquiv (line.src e) + if e.2 then 1 else -1 := by
  obtain ⟨n, d⟩ := e
  rw [lineVertexEquiv_src]
  -- The target of `(n, d)` is the integer `n + 1` or `n`, by the definition of the line.
  cases d
  · exact (add_neg_cancel_right n 1).symm
  · rfl

/-- The line is acyclic. -/
theorem line_isAcyclic : line.IsAcyclic :=
  ofParent_isAcyclic _ fun v m n h => by
    simp at h
    omega

/-- The line is connected. -/
theorem line_connected : line.Connected :=
  (connected_iff line).mpr ⟨⟨lineVertexEquiv.symm 0⟩, (ofParent_preconnected_iff _).mpr
    fun a b => ⟨(b - a).toNat, (a - b).toNat, by simp; omega⟩⟩

/-- The line is a tree. -/
theorem line_isTree : line.IsTree :=
  (isTree_iff line).mpr ⟨line_connected, line_isAcyclic⟩

/-- The translation action of the integers on the line, `k • n = k + n`. -/
def lineShift : Multiplicative ℤ →* line.Aut :=
  ofParentAction _ fun k n => by
    rw [← toAdd_vadd, ← toAdd_vadd, vadd_eq_add, vadd_eq_add, add_assoc]

/-- Translation adds to the coordinate of a vertex. -/
@[simp] theorem lineVertexEquiv_lineShift_smul (k : Multiplicative ℤ) (v : line.V) :
    lineVertexEquiv (lineShift k • v) = k.toAdd + lineVertexEquiv v :=
  congrArg lineVertexEquiv (ofParentAction_smul_vertex _ k v)

/-- Translation moves a dart without changing its orientation. -/
@[simp] theorem lineShift_smul_dart (k : Multiplicative ℤ) (e : line.E) :
    lineShift k • e = Prod.mk (k.toAdd + Prod.fst e) (Prod.snd e) :=
  ofParentAction_smul_dart _ k e

end SerreGraph
end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.Path.Group
public import TauCeti.Combinatorics.Graph.Serre.SpanningTree

/-!
# Based tree loops in reduced path groups

A spanning tree bases any path at a chosen vertex by adjoining the tree paths to its
endpoints. In particular, the loop through a dart follows the tree to its source, crosses
the dart, and returns through the tree. Basing respects concatenation and reversal, and
paths contained in the tree give the identity.

The comparison with spanning-tree presentations and free groups is developed in
`TauCeti.GroupTheory.GraphOfGroups.PathGroup`.

## References

* J.-P. Serre, *Trees*, Chapter I, §§2.3–3.1.
* A. Hatcher, *Algebraic Topology*, §1.A, Proposition 1A.2.
-/

public section

namespace TauCeti.SerreGraph.SpanningTree

universe u w

variable {Γ : SerreGraph.{u, w}} (T : Γ.SpanningTree) (v : Γ.V)

noncomputable section

/-- Base a path at `v` by adjoining the tree paths to its endpoints. -/
def basedPath {a b : Γ.V} (p : Γ.Path a b) : PathGroup Γ v :=
  PathGroup.ofPath (((T.path v a).comp p).comp (T.path b v))

theorem basedPath_def {a b : Γ.V} (p : Γ.Path a b) :
    T.basedPath v p = PathGroup.ofPath (((T.path v a).comp p).comp (T.path b v)) := (rfl)

@[simp] theorem basedPath_self (p : Γ.Path v v) :
    T.basedPath v p = PathGroup.ofPath p := by
  simp [basedPath]

@[simp] theorem basedPath_nil (a : Γ.V) :
    T.basedPath v (Quiver.Path.nil : Γ.Path a a) = 1 := by
  apply PathGroup.ext
  rw [basedPath, PathGroup.toPath_ofPath, Quiver.Path.comp_nil, ← T.reverse_path v a,
    Path.reduce_comp_reverse, PathGroup.toPath_one]

/-- Basing paths carries concatenation to multiplication: the two middle tree paths cancel. -/
@[simp] theorem basedPath_comp {a b c : Γ.V} (p : Γ.Path a b) (q : Γ.Path b c) :
    T.basedPath v (p.comp q) = T.basedPath v p * T.basedPath v q := by
  simp only [basedPath, ← PathGroup.ofPath_comp]
  apply (PathGroup.ofPath_eq_iff_homotopic _ _).2
  have h := (Path.Homotopic.reverse_comp Γ (T.path v b)).comp_left Γ
    ((T.path v a).comp p)
  have h' := h.comp_right Γ (q.comp (T.path c v))
  simpa only [T.reverse_path, Quiver.Path.comp_assoc, Quiver.Path.nil_comp] using h'.symm

/-- Reversing a path inverts its based tree-loop class. -/
@[simp] theorem basedPath_reverse {a b : Γ.V} (p : Γ.Path a b) :
    T.basedPath v p.reverse = (T.basedPath v p)⁻¹ := by
  simp only [basedPath, ← PathGroup.ofPath_reverse, Quiver.Path.reverse_comp,
    T.reverse_path, Quiver.Path.comp_assoc]

/-- The based tree loop through a dart. -/
def loop (e : Γ.E) : PathGroup Γ v := T.basedPath v (Γ.dart e).toPath

/-- The loop through `e` follows the tree out and back, retaining the direction of `e`. -/
theorem loop_def (e : Γ.E) :
    T.loop v e = PathGroup.ofPath
      (((T.path v (Γ.src e)).cons (Γ.dart e)).comp (T.path (Γ.tgt e) v)) := (rfl)

@[simp] theorem basedPath_toPath {a b : Γ.V} (e : a ⟶ b) :
    T.basedPath v e.toPath = T.loop v e.1 := by
  obtain ⟨e, rfl, rfl⟩ := e
  rw [loop]
  congr 2
  exact Subtype.ext (Γ.dart_val e).symm

@[simp] theorem loop_rev (e : Γ.E) : T.loop v (Γ.rev e) = (T.loop v e)⁻¹ := by
  simpa only [Quiver.Path.reverse_toPath, basedPath_toPath, Γ.reverse_val, Γ.dart_val] using
    T.basedPath_reverse v (Γ.dart e).toPath

/-- A path contained in the tree is trivial after basing it at `v`. -/
theorem basedPath_eq_one {a b : Γ.V} (p : Γ.Path a b)
    (hp : ∀ e ∈ Path.darts Γ p, e ∈ T.darts) : T.basedPath v p = 1 := by
  apply PathGroup.ext
  rw [basedPath, PathGroup.toPath_ofPath, PathGroup.toPath_one]
  apply (Γ.isAcyclic_restrict_iff T.darts T.rev_mem).mp T.isTree.isAcyclic v
    _ (Path.isReduced_reduce Γ _)
  intro e he
  have he' := (Path.darts_reduce_sublist Γ _).subset he
  simp only [Path.darts_comp, List.mem_append] at he'
  rcases he' with (he | he) | he
  · exact T.mem_of_mem_darts_path he
  · exact hp e he
  · exact T.mem_of_mem_darts_path he

/-- Tree darts represent the identity. -/
@[simp] theorem loop_eq_one {e : Γ.E} (he : e ∈ T.darts) : T.loop v e = 1 :=
  T.basedPath_eq_one v _ (by simpa using he)

end
end TauCeti.SerreGraph.SpanningTree

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.Multigraph
public import TauCeti.GroupTheory.GraphOfGroups.PathGroup

/-!
# Finite subroses of a rose, and loops versus walks

For a set `s` of petals of the rose on `α`, the darts lying over `s` form a subgraph, the subrose
on `s`; it is finite when `s` is. Its inclusion into the rose induces an injective homomorphism of
reduced path groups which sends the petal loop of each `a ∈ s` to the petal generator
`rosePetal a` of the rose, and whose image contains the petal generator of `a` only when
`a ∈ s`. So even when `α` is infinite, every finite set of petal generators of the rose comes,
faithfully, from a finite subrose.

A petal loop and its reverse forget to the same walk in the underlying multigraph, which has one
component, but they are distinct, mutually inverse elements of the reduced path group. Hence the
reduced path group does not factor through walks. For the one-petal rose the identification of
the reduced path group with `ℤ` sends the petal loop to `1` and its reverse to `-1`.

## References

* J.-P. Serre, *Trees*, Chapter I, §§2.3–3.1.
* A. Hatcher, *Algebraic Topology*, §1.A, Proposition 1A.2.
-/

public section

namespace TauCeti.Examples.SerreRose

open TauCeti.SerreGraph

variable {α : Type*} (s : Set α) (v : (rose α).V)

/-- The subrose on a set of petals has finitely many darts exactly when the set is finite. -/
theorem finite_restrict_rose_iff :
    Finite ((rose α).restrict {e | e.1 ∈ s} fun _ h => h).E ↔ s.Finite := by
  refine ⟨fun h => ?_, fun hs =>
    ((hs.prod Set.finite_univ).subset fun e he => ⟨he, trivial⟩).to_subtype⟩
  have : Finite s := Finite.of_injective
    (fun a : s => (⟨(a.val, true), a.property⟩ : ((rose α).restrict {e | e.1 ∈ s} fun _ h => h).E))
    fun a b hab => Subtype.ext (congrArg (fun e => e.val.1) hab)
  exact Set.toFinite s

/-- The inclusion of the subrose on `s` sends the petal loop of `a ∈ s` to the petal generator
of `a` in the rose. -/
theorem map_restrictInclusion_ofPath_dart (a : α) (ha : a ∈ s) :
    PathGroup.map ((rose α).restrictInclusion {e | e.1 ∈ s} fun _ h => h) (v := v) rfl
        (PathGroup.ofPath
          (((rose α).restrict {e | e.1 ∈ s} fun _ h => h).dart ⟨(a, true), ha⟩).toPath) =
      PathGroup.ofPath (rosePetal a) := by
  -- The vertex and dart types of `rose α` unfold only at default transparency, so the proof
  -- composes equations instead of rewriting inside goals that mention them.
  set T := (roseTree α).restrict {e | e.1 ∈ s} (fun _ h => h) (by simp)
  -- In the subrose and in the rose the tree paths are trivial, so tree loops are petal loops.
  have h₁ := (T.basedPath_toPath v _).symm.trans (T.basedPath_self v
    (((rose α).restrict {e | e.1 ∈ s} fun _ h => h).dart ⟨(a, true), ha⟩).toPath)
  rw [dart_val] at h₁
  have h₂ := ((roseTree α).basedPath_toPath v _).symm.trans
    ((roseTree α).basedPath_self v ((rose α).dart (a, true)).toPath)
  rw [← rosePetal_eq_toPath] at h₂
  exact (congrArg _ h₁.symm).trans
    (((roseTree α).map_restrictInclusion_loop v _ _ (by simp) rfl ⟨(a, true), ha⟩).trans
      ((congrArg ((roseTree α).loop v) ((rose α).dart_val (a, true))).symm.trans h₂))

/-- The inclusion of the subrose on `s` induces an injective homomorphism of reduced path
groups. -/
theorem map_restrictInclusion_rose_injective :
    Function.Injective (PathGroup.map ((rose α).restrictInclusion {e | e.1 ∈ s} fun _ h => h)
      (v := v) rfl) :=
  PathGroup.map_restrictInclusion_injective _ _ _

/-- The petal generator of `a` lies in the image of the reduced path group of the subrose on `s`
exactly when `a ∈ s`. -/
theorem ofPath_rosePetal_mem_range_map_restrictInclusion_iff (a : α) :
    PathGroup.ofPath (rosePetal a) ∈
        (PathGroup.map ((rose α).restrictInclusion {e | e.1 ∈ s} fun _ h => h)
          (v := v) rfl).range ↔ a ∈ s := by
  -- As above, equations are composed rather than rewritten. The petal loop is reduced, and its
  -- only dart is `(a, true)`.
  have hdarts : Path.darts (rose α) (@PathGroup.ofPath (rose α) v (rosePetal a)).toPath =
      [(a, true)] :=
    (congrArg _ ((PathGroup.toPath_ofPath _).trans
      (Path.reduce_eq_self_of_isReduced _ _ (rosePetal_isReduced a)))).trans
      ((congrArg (Path.darts (rose α)) (rosePetal_eq_toPath a)).trans
        ((Path.darts_toPath (rose α) _).trans (congrArg (fun x => [x]) ((rose α).dart_val _))))
  refine (PathGroup.mem_range_map_restrictInclusion_iff _ _ _ _).trans
    ⟨fun h => h (a, true) ((congrArg _ hdarts).mpr (List.mem_singleton_self _)),
      fun ha e he => ?_⟩
  obtain rfl := List.mem_singleton.mp (hdarts ▸ he)
  exact ha

/-! ### Loops and their forgotten walks -/

/-- A petal loop and its reverse forget to the same walk in the underlying multigraph: the two
darts of a petal lie on one undirected edge. -/
example (a : α) :
    Path.toWalk (rose α) (rosePetal a).reverse = Path.toWalk (rose α) (rosePetal a) := by
  rw [rosePetal_eq_toPath]
  exact Path.toWalk_reverse_toPath_of_loop _ _

/-- The reduced path group of a rose with a petal does not factor through the walks of the
underlying multigraph: no map on walks sends the forgotten walk of every closed path to its
class, since a petal loop and its reverse have the same walk but distinct classes. -/
example [Nonempty α] :
    ¬∃ f : (rose α).toGraph.Walk PUnit.unit PUnit.unit → PathGroup (rose α) PUnit.unit,
      ∀ p, f (Path.toWalk (rose α) p) = PathGroup.ofPath p := by
  obtain ⟨a⟩ := ‹Nonempty α›
  rintro ⟨f, hf⟩
  refine PathGroup.ofPath_reverse_rosePetal_ne a
    ((hf _).symm.trans ((congrArg f ?_).trans (hf _)))
  rw [rosePetal_eq_toPath]
  exact Path.toWalk_reverse_toPath_of_loop _ _

/-- The multigraph underlying a rose, a single vertex with loops, is connected with one
component. -/
example : (rose α).toGraph.componentCount = 1 :=
  Graph.componentCount_eq_one_iff.mpr ((connected_toGraph_iff _).mpr (rose_connected α))

/-- The one-petal rose has fundamental group `ℤ`, the petal loop mapping to `1`. -/
example (v : (rose Unit).V) : FreeGroup.mulEquivIntOfUnique
    (rosePathGroupEquivFreeGroup Unit v (PathGroup.ofPath (rosePetal ()))) =
      Multiplicative.ofAdd 1 := by
  rw [rosePathGroupEquivFreeGroup_ofPath_rosePetal]
  rfl

/-- The reversed petal loop of the one-petal rose maps to `-1`. -/
example (v : (rose Unit).V) : FreeGroup.mulEquivIntOfUnique
    (rosePathGroupEquivFreeGroup Unit v (PathGroup.ofPath (rosePetal ()).reverse)) =
      Multiplicative.ofAdd (-1) := by
  rw [rosePathGroupEquivFreeGroup_ofPath_reverse_rosePetal, map_inv]
  rfl

end TauCeti.Examples.SerreRose

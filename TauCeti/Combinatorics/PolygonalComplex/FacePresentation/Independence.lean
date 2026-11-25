/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.PolygonalComplex.FacePresentation.Basic
public import TauCeti.Combinatorics.PolygonalComplex.FaceReindex
public import Mathlib.GroupTheory.QuotientGroup.Basic
import TauCeti.Data.List.ProdOfFn
import TauCeti.Data.List.Rotate

/-!
# Independence of the face presentation from the auxiliary choices

The face presentation `PolygonalComplex.FacePresentation C T` of a polygonal complex depends on
three auxiliary choices: the spanning tree `T` whose darts are killed, the paths along which the
boundary loops of the faces are joined to a base vertex, and the starting corner and orientation
in which each face is read. None of them changes the group.

* **Connecting paths.** Joining the boundary loop of a face `f` to the base vertex `v` along a path
  `γ` gives the loop `γ ∂f γ⁻¹`. Replacing `γ` by another path `η` with the same ends conjugates
  this loop by `η γ⁻¹` (`SerreGraph.PathGroup.ofPath_comp_comp_reverse`), so the normal closure
  of the based face loops does not depend on the connecting paths
  (`SerreGraph.PathGroup.normalClosure_range_ofPath_comp_comp_reverse`). The face
  presentation is the reduced path group at `v` modulo the face loops based along any choice of
  connecting paths (`PolygonalComplex.facePresentationEquivQuotientOfPath`).
* **Spanning trees.** Both face presentations relative to two spanning trees `T` and `U` are the
  same quotient of the path group, which gives an isomorphism
  `PolygonalComplex.facePresentationTreeEquiv T U v` sending the generator of a dart `e` to the
  word along the `T`-loop of `e` at `v`. These isomorphisms are compatible with inverses and
  composition.
* **Starting corners and orientations.** Moving the starting corner of a face replaces its relator
  by a cyclic permutation, a conjugate in the free group on the darts
  (`PolygonalComplex.isConj_faceRelator_rotateFaces`). Reversing the orientation of a face
  replaces its relator by one that is its inverse as soon as the reverse of a dart is its inverse,
  as in the graph presentation (`PolygonalComplex.lift_faceRelator_reverseFaces_of_eq_true`). In
  both cases the relators of the face presentation have the same normal closure, so the face
  presentation is unchanged, with the same generators.

## Main definitions

* `TauCeti.PolygonalComplex.facePresentationEquivQuotientOfPath`: the face presentation as the
  path group modulo the face loops based along arbitrary connecting paths.
* `TauCeti.PolygonalComplex.facePresentationTreeEquiv`: the isomorphism between the face
  presentations relative to two spanning trees.

## Main results

* `TauCeti.PolygonalComplex.facePresentation_tree_independent`: the face presentations relative to
  any two spanning trees are isomorphic.
* `TauCeti.PolygonalComplex.normalClosure_faceRelators_rotateFaces`,
  `TauCeti.PolygonalComplex.normalClosure_faceRelators_reverseFaces`: changing the starting corners
  or the orientations of the faces does not change the normal closure of the relators.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, §1.2, Proposition 1.26 and
  the remark after it (independence of the normal subgroup from the connecting paths).
* J. Gallier, D. Xu, *A Guide to the Classification Theorem for Compact Surfaces*, Springer, 2013,
  Chapter 6, Definition 6.1 (cyclically ordered boundaries and inverse faces) and §6.6,
  Definition 6.7.
-/

public section

universe u v w

namespace TauCeti

namespace PolygonalComplex

variable (C : PolygonalComplex.{u, v, w})

/-! ### Connecting paths -/

/-- The face presentation relative to a spanning tree `T` is the reduced path group at `v` modulo
the normal closure of the boundary loops of the faces, each based along an arbitrary path `γ f`
from `v` to its first corner. A dart corresponds to its based tree loop. -/
noncomputable def facePresentationEquivQuotientOfPath (T : C.graph.SpanningTree) (v : C.graph.V)
    (γ : ∀ f, C.graph.Path v (C.cornerVertex ⟨f, ⟨0, C.sides_pos f⟩⟩)) :
    C.FacePresentation T.darts ≃* SerreGraph.PathGroup C.graph v ⧸ Subgroup.normalClosure
      (Set.range fun f =>
        SerreGraph.PathGroup.ofPath (((γ f).comp (C.facePath f)).comp (γ f).reverse)) :=
  (C.facePresentationEquivQuotient T v).trans <| QuotientGroup.quotientMulEquivOfEq <| by
    simpa only [SerreGraph.SpanningTree.basedPath_eq_ofPath_comp_comp_reverse] using
      SerreGraph.PathGroup.normalClosure_range_ofPath_comp_comp_reverse C.facePath
        (fun f => T.path v _) γ

/-- The generator of a dart corresponds to the class of its based tree loop. -/
@[simp] theorem facePresentationEquivQuotientOfPath_of (T : C.graph.SpanningTree) (v : C.graph.V)
    (γ : ∀ f, C.graph.Path v (C.cornerVertex ⟨f, ⟨0, C.sides_pos f⟩⟩)) (e : C.graph.E) :
    C.facePresentationEquivQuotientOfPath T v γ (PresentedGroup.of e) = ↑(T.loop v e) := by
  simp [facePresentationEquivQuotientOfPath]

/-! ### Change of spanning tree -/

/-- **Change of spanning tree.** The face presentations of `C` relative to two spanning trees `T`
and `U` are isomorphic: both are the reduced path group at `v` modulo the normal closure of the
based face loops. The generator of a dart `e` is sent to the word, in the generators relative to
`U`, along the loop through `e` based at `v` through `T`. -/
noncomputable def facePresentationTreeEquiv (T U : C.graph.SpanningTree) (v : C.graph.V) :
    C.FacePresentation T.darts ≃* C.FacePresentation U.darts :=
  (C.facePresentationEquivQuotient T v).trans <|
    (QuotientGroup.quotientMulEquivOfEq (T.normalClosure_range_basedPath v U C.facePath)).trans
      (C.facePresentationEquivQuotient U v).symm

/-- The change of spanning tree is compatible with the descriptions of both face presentations as
the same quotient of the path group. -/
@[simp] theorem facePresentationEquivQuotient_facePresentationTreeEquiv (T U : C.graph.SpanningTree)
    (v : C.graph.V) (x : C.FacePresentation T.darts) :
    C.facePresentationEquivQuotient U v (C.facePresentationTreeEquiv T U v x) =
      QuotientGroup.quotientMulEquivOfEq (T.normalClosure_range_basedPath v U C.facePath)
        (C.facePresentationEquivQuotient T v x) := by
  simp [facePresentationTreeEquiv]

/-- The change of spanning tree sends the generator of a dart `e` to the product of the generators
along the path through `T` from `v` to the source of `e`, the generator of `e`, and the
generators along the path through `T` from the target of `e` back to `v`. -/
@[simp] theorem facePresentationTreeEquiv_of (T U : C.graph.SpanningTree) (v : C.graph.V)
    (e : C.graph.E) :
    C.facePresentationTreeEquiv T U v (PresentedGroup.of e) =
      ((SerreGraph.Path.darts C.graph (T.path v (C.graph.src e))).map PresentedGroup.of).prod *
        PresentedGroup.of e * ((SerreGraph.Path.darts C.graph (T.path (C.graph.tgt e) v)).map
          PresentedGroup.of).prod := by
  simp [facePresentationTreeEquiv, SerreGraph.SpanningTree.loop_def, mul_assoc]

/-- The change of spanning tree from `T` to `T` is the identity. -/
@[simp] theorem facePresentationTreeEquiv_self (T : C.graph.SpanningTree) (v : C.graph.V) :
    C.facePresentationTreeEquiv T T v = MulEquiv.refl _ := by
  refine MulEquiv.ext fun x => ?_
  simp only [facePresentationTreeEquiv, MulEquiv.trans_apply, MulEquiv.refl_apply]
  rw [MulEquiv.symm_apply_eq]
  induction C.facePresentationEquivQuotient T v x using QuotientGroup.induction_on with
  | H g => exact QuotientGroup.quotientMulEquivOfEq_mk _ g

/-- Changing the spanning tree from `T` to `U` and then from `U` to `W` is changing it from `T` to
`W`. -/
@[simp] theorem facePresentationTreeEquiv_trans (T U W : C.graph.SpanningTree) (v : C.graph.V) :
    (C.facePresentationTreeEquiv T U v).trans (C.facePresentationTreeEquiv U W v) =
      C.facePresentationTreeEquiv T W v := by
  refine MulEquiv.ext fun x => ?_
  simp only [facePresentationTreeEquiv, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
  congr 1
  induction C.facePresentationEquivQuotient T v x using QuotientGroup.induction_on with
  | H g => simp

/-- The inverse of the change of spanning tree from `T` to `U` is the change from `U` to `T`. -/
@[simp] theorem facePresentationTreeEquiv_symm (T U : C.graph.SpanningTree) (v : C.graph.V) :
    (C.facePresentationTreeEquiv T U v).symm = C.facePresentationTreeEquiv U T v :=
  MulEquiv.ext fun x => (MulEquiv.symm_apply_eq _).2 <| by
    rw [← MulEquiv.trans_apply, facePresentationTreeEquiv_trans, facePresentationTreeEquiv_self,
      MulEquiv.refl_apply]

/-- **The face group does not depend on the spanning tree.** The face presentations of `C`
relative to any two spanning trees of its one-skeleton are isomorphic. -/
theorem facePresentation_tree_independent (T U : C.graph.SpanningTree) :
    Nonempty (C.FacePresentation T.darts ≃* C.FacePresentation U.darts) := by
  obtain ⟨v⟩ := (C.graph.connected_iff.mp (C.graph.nonempty_spanningTree_iff.mp ⟨T⟩)).1
  exact ⟨C.facePresentationTreeEquiv T U v⟩

/-! ### Starting corners -/

/-- **Moving the starting corners conjugates the face relators.** The relator of a face read from
another corner is a cyclic permutation of its relator, hence conjugate to it in the free group on
the darts. -/
theorem isConj_faceRelator_rotateFaces (k : C.Face → ℕ) (f : C.Face) :
    IsConj ((C.rotateFaces k).faceRelator f) (C.faceRelator f) := by
  have hside : (C.rotateFaces k).side f = C.side f ∘ ⇑(finRotate (C.sides f) ^ k f) :=
    funext (C.rotateFaces_side k f)
  rw [faceRelator_def, faceRelator_def, hside, List.ofFn_comp_finRotate_pow, List.map_rotate,
    ← ConjClasses.mk_eq_mk_iff_isConj]
  exact (List.IsRotated.forall _ _).apply_prod_eq fun x y =>
    ConjClasses.mk_eq_mk_iff_isConj.2 (isConj_iff.2 ⟨y, by simp [← mul_assoc]⟩)

/-- Moving the starting corners of the faces does not change the normal closure of the relators
of the face presentation: the two face presentations are the same group, with the same
generators. -/
theorem normalClosure_faceRelators_rotateFaces (k : C.Face → ℕ) (T : Set C.graph.E) :
    Subgroup.normalClosure ((C.rotateFaces k).faceRelators T) =
      Subgroup.normalClosure (C.faceRelators T) := by
  -- Relators conjugate face by face, together with the same graph relators, have the same
  -- normal closure.
  have key (x y : C.Face → FreeGroup C.graph.E) (h : ∀ f, IsConj (y f) (x f)) :
      Subgroup.normalClosure (C.graph.graphRelators T ∪ Set.range x) ≤
        Subgroup.normalClosure (C.graph.graphRelators T ∪ Set.range y) := by
    refine Subgroup.normalClosure_le_normal ?_
    rintro r (hr | ⟨f, rfl⟩)
    · exact Subgroup.subset_normalClosure (Or.inl hr)
    · exact Subgroup.conjugatesOfSet_subset_normalClosure
        (Group.mem_conjugatesOfSet_iff.2 ⟨_, Or.inr ⟨f, rfl⟩, h f⟩)
  rw [faceRelators_def, faceRelators_def]
  exact le_antisymm (key _ _ fun f => (C.isConj_faceRelator_rotateFaces k f).symm)
    (key _ _ (C.isConj_faceRelator_rotateFaces k))

/-! ### Orientations -/

/-- A face whose orientation is kept keeps its relator. -/
@[simp] theorem faceRelator_reverseFaces_of_eq_false {s : C.Face → Bool} {f : C.Face}
    (hf : s f = false) : (C.reverseFaces s).faceRelator f = C.faceRelator f := by
  simp [faceRelator_def, hf]

/-- **Reversing the orientation of a face inverts its relator** under every evaluation of the
darts in a group sending the reverse of a dart to the inverse of its value, such as the graph
presentation or the face presentation. -/
theorem lift_faceRelator_reverseFaces_of_eq_true {H : Type*} [Group H] {h : C.graph.E → H}
    (hrev : ∀ e, h (C.graph.rev e) = (h e)⁻¹) {s : C.Face → Bool} {f : C.Face} (hf : s f = true) :
    FreeGroup.lift h ((C.reverseFaces s).faceRelator f) =
      (FreeGroup.lift h (C.faceRelator f))⁻¹ := by
  simp [faceRelator_def, map_list_prod, List.map_ofFn, Function.comp_def, hf, hrev,
    List.inv_prod_ofFn]

/-- Reversing the orientations of some faces does not change the normal closure of the relators
of the face presentation: the two face presentations are the same group, with the same
generators. -/
theorem normalClosure_faceRelators_reverseFaces (s : C.Face → Bool) (T : Set C.graph.E) :
    Subgroup.normalClosure ((C.reverseFaces s).faceRelators T) =
      Subgroup.normalClosure (C.faceRelators T) := by
  refine le_antisymm (Subgroup.normalClosure_le_normal ?_) (Subgroup.normalClosure_le_normal ?_)
  · intro r hr
    obtain hr | ⟨f, rfl⟩ := mem_faceRelators_iff.1 hr
    · exact Subgroup.subset_normalClosure (mem_faceRelators_iff.2 (Or.inl hr))
    cases hf : s f
    · rw [C.faceRelator_reverseFaces_of_eq_false hf]
      exact Subgroup.subset_normalClosure (mem_faceRelators_iff.2 (Or.inr ⟨f, rfl⟩))
    · -- In the face presentation of `C`, the reversed relator is the inverse of a trivial one.
      have h := C.lift_faceRelator_reverseFaces_of_eq_true
        (h := PresentedGroup.of (rels := C.faceRelators T)) (FacePresentation.of_rev (T := T)) hf
      rw [PresentedGroup.lift_of_eq_mk, PresentedGroup.lift_of_eq_mk,
        FacePresentation.mk_faceRelator, inv_one] at h
      exact (QuotientGroup.eq_one_iff _).1 h
  · intro r hr
    obtain hr | ⟨f, rfl⟩ := mem_faceRelators_iff.1 hr
    · exact Subgroup.subset_normalClosure (mem_faceRelators_iff.2 (Or.inl hr))
    cases hf : s f
    · rw [← C.faceRelator_reverseFaces_of_eq_false hf]
      exact Subgroup.subset_normalClosure (mem_faceRelators_iff.2 (Or.inr ⟨f, rfl⟩))
    · -- In the face presentation of the reversed complex, the original relator is the inverse
      -- of the trivial reversed relator.
      have h := C.lift_faceRelator_reverseFaces_of_eq_true
        (h := PresentedGroup.of (rels := (C.reverseFaces s).faceRelators T))
        (FacePresentation.of_rev (C := C.reverseFaces s) (T := T)) hf
      rw [PresentedGroup.lift_of_eq_mk, PresentedGroup.lift_of_eq_mk,
        FacePresentation.mk_faceRelator, eq_comm, inv_eq_one] at h
      exact (QuotientGroup.eq_one_iff _).1 h

end PolygonalComplex

end TauCeti

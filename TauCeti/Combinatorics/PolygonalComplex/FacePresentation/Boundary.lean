/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.PolygonalComplex.Boundary
public import TauCeti.Combinatorics.PolygonalComplex.FacePresentation.Independence

/-!
# Boundary words in the face presentation of a surface model

A boundary circuit of a polygonal surface model `S` is a closed path of boundary darts traversing
its boundary component once. Its *boundary word* `SurfaceModel.boundaryWord` is the product, in the
face presentation of `S`, of the generators of its darts. Relative to a spanning tree `T`, it is
the class of the circuit based at a vertex `v` through `T`
(`SurfaceModel.facePresentationEquivQuotient_boundaryWord`): the tree darts of the connecting paths
disappear. Reversing the circuit inverts its boundary word, and changing the spanning tree changes
it by conjugation (`SurfaceModel.isConj_facePresentationTreeEquiv_boundaryWord`).

A homomorphism `φ` out of the face presentation *marks the boundary* by a family `p` of peripheral
elements (`SurfaceModel.MarksBoundary`) when a bijection from the boundary components to the
indices of `p` takes the boundary word of every circuit of a component to a conjugate of the
corresponding peripheral element or of its inverse. The orientation and the base vertex of a
circuit are thereby forgotten. Whether a homomorphism marks the boundary does not depend on the
spanning tree (`SurfaceModel.marksBoundary_comp_facePresentationTreeEquiv_iff`).

## Main definitions

* `TauCeti.SurfaceModel.boundaryWord`: the boundary word of a boundary circuit.
* `TauCeti.SurfaceModel.MarksBoundary`: a homomorphism out of the face presentation carries the
  boundary words to given peripheral elements, up to conjugacy and inversion.

## Main results

* `TauCeti.SurfaceModel.facePresentationEquivQuotient_boundaryWord`: the boundary word is the class
  of the boundary circuit based through the tree.
* `TauCeti.SurfaceModel.boundaryWord_reverse`: reversing a circuit inverts its boundary word.
* `TauCeti.SurfaceModel.isConj_facePresentationTreeEquiv_boundaryWord`: changing the spanning tree
  conjugates the boundary words.

## References

* J. Gallier, D. Xu, *A Guide to the Classification Theorem for Compact Surfaces*, Springer, 2013,
  §6.6 (the boundary elements `dᵢ = cᵢ hᵢ cᵢ⁻¹` of the fundamental group of a surface with
  boundary).
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, §1.2, Proposition 1.26 and
  the remark after it.
-/

public section

universe u v w

namespace TauCeti

namespace SurfaceModel

open PolygonalComplex

variable (S : SurfaceModel.{u, v, w})

/-! ### Boundary words -/

/-- The boundary word of a boundary circuit `c` in the face presentation of `S` killing the darts
of `T`: the product of the generators of the darts of `c`, in order. -/
def boundaryWord (T : Set S.graph.E) {b : S.BoundaryComponent} (c : S.BoundaryCircuit b) :
    S.FacePresentation T :=
  ((SerreGraph.Path.darts _ c.path).map fun e => PresentedGroup.of e.val).prod

theorem boundaryWord_def (T : Set S.graph.E) {b : S.BoundaryComponent} (c : S.BoundaryCircuit b) :
    S.boundaryWord T c =
      ((SerreGraph.Path.darts _ c.path).map fun e => PresentedGroup.of e.val).prod := (rfl)

/-- Reversing a boundary circuit inverts its boundary word. -/
@[simp] theorem boundaryWord_reverse (T : Set S.graph.E) {b : S.BoundaryComponent}
    (c : S.BoundaryCircuit b) : S.boundaryWord T c.reverse = (S.boundaryWord T c)⁻¹ := by
  rw [boundaryWord_def, boundaryWord_def, BoundaryCircuit.darts_path_reverse,
    List.prod_inv_reverse]
  simp [List.map_reverse, Function.comp_def]

/-- Relative to a spanning tree `T`, the boundary word of a circuit corresponds to the class of the
circuit based at `v` through `T`. -/
@[simp] theorem facePresentationEquivQuotient_boundaryWord (T : S.graph.SpanningTree)
    (v : S.graph.V) {b : S.BoundaryComponent} (c : S.BoundaryCircuit b) :
    S.facePresentationEquivQuotient T v (S.boundaryWord T.darts c) =
      ↑(T.basedPath v (S.boundaryInclusion.toPrefunctor.mapPath c.path)) := by
  rw [← MulEquiv.eq_symm_apply, facePresentationEquivQuotient_symm_basedPath,
    SerreGraph.Hom.darts_mapPath, List.map_map, boundaryWord_def]
  rfl

/-- **Changing the spanning tree conjugates the boundary words.** -/
theorem isConj_facePresentationTreeEquiv_boundaryWord (T U : S.graph.SpanningTree) (v : S.graph.V)
    {b : S.BoundaryComponent} (c : S.BoundaryCircuit b) :
    IsConj (S.facePresentationTreeEquiv T U v (S.boundaryWord T.darts c))
      (S.boundaryWord U.darts c) := by
  -- In the path group, the circuit based through `T` is a conjugate of the circuit based
  -- through `U`, the connecting paths being the two tree paths to the base of the circuit.
  set p := S.boundaryInclusion.toPrefunctor.mapPath c.path
  have hconj : IsConj (T.basedPath v p) (U.basedPath v p) := by
    rw [T.basedPath_eq_ofPath_comp_comp_reverse, U.basedPath_eq_ofPath_comp_comp_reverse]
    exact (isConj_iff.2 ⟨_, (SerreGraph.PathGroup.ofPath_comp_comp_reverse p _ _).symm⟩).symm
  have key : IsConj (S.facePresentationEquivQuotient U v
      (S.facePresentationTreeEquiv T U v (S.boundaryWord T.darts c)))
      (S.facePresentationEquivQuotient U v (S.boundaryWord U.darts c)) := by
    rw [facePresentationEquivQuotient_facePresentationTreeEquiv,
      facePresentationEquivQuotient_boundaryWord, facePresentationEquivQuotient_boundaryWord,
      QuotientGroup.quotientMulEquivOfEq_mk]
    exact (QuotientGroup.mk' _).map_isConj hconj
  simpa only [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] using
    (S.facePresentationEquivQuotient U v).symm.toMonoidHom.map_isConj key

/-! ### Marking the boundary -/

/-- A homomorphism `φ` out of the face presentation of `S` *marks the boundary* by the peripheral
elements `p` when some bijection `β` from the boundary components of `S` to the indices of `p`
takes the boundary word of every boundary circuit of each component `b` to a conjugate of
`p (β b)` or of its inverse. -/
def MarksBoundary (T : Set S.graph.E) {K : Type*} [Group K] (φ : S.FacePresentation T →* K)
    {ι : Type*} (p : ι → K) : Prop :=
  ∃ β : S.BoundaryComponent ≃ ι, ∀ b (c : S.BoundaryCircuit b),
    IsConj (φ (S.boundaryWord T c)) (p (β b)) ∨ IsConj (φ (S.boundaryWord T c)) (p (β b))⁻¹

theorem marksBoundary_iff (T : Set S.graph.E) {K : Type*} [Group K] (φ : S.FacePresentation T →* K)
    {ι : Type*} (p : ι → K) :
    S.MarksBoundary T φ p ↔ ∃ β : S.BoundaryComponent ≃ ι, ∀ b (c : S.BoundaryCircuit b),
      IsConj (φ (S.boundaryWord T c)) (p (β b)) ∨
        IsConj (φ (S.boundaryWord T c)) (p (β b))⁻¹ :=
  Iff.rfl

/-- Whether a homomorphism out of the face presentation marks the boundary does not depend on the
spanning tree: a homomorphism relative to `U` marks the boundary exactly when its composite with
the change of spanning tree from `T` does. -/
theorem marksBoundary_comp_facePresentationTreeEquiv_iff (T U : S.graph.SpanningTree)
    (v : S.graph.V) {K : Type*} [Group K] (φ : S.FacePresentation U.darts →* K) {ι : Type*}
    (p : ι → K) :
    S.MarksBoundary T.darts (φ.comp (S.facePresentationTreeEquiv T U v).toMonoidHom) p ↔
      S.MarksBoundary U.darts φ p := by
  refine exists_congr fun β => forall₂_congr fun b c => ?_
  have h := φ.map_isConj (S.isConj_facePresentationTreeEquiv_boundaryWord T U v c)
  exact or_congr ⟨h.symm.trans, h.trans⟩ ⟨h.symm.trans, h.trans⟩

end SurfaceModel

end TauCeti

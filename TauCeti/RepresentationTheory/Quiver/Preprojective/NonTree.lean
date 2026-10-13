/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.SimpleGraph.NeighborChoice
public import TauCeti.RepresentationTheory.Quiver.Preprojective.Orientation
public import TauCeti.RepresentationTheory.Quiver.Preprojective.Sinkless
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Orientation

/-!
# Koszul complexes of preprojective algebras of graphs which are not trees

Let `Π = Π_k(Q)` be the preprojective algebra of a finite quiver over a commutative ring `k`. The
Koszul complex

```text
0 ⟶ e_v Π ⟶ ⨁_{b : i ⟶ v} e_i Π ⟶ e_v Π ⟶ S_v ⟶ 0
```

of `TauCeti.RepresentationTheory.Quiver.Preprojective.KoszulComplex` is exact at its left end as
soon as `Q` has no sinks (`TauCeti.forall_preprojectiveMk_ofArrow_reverse_mul_eq_zero_iff`). This
file removes the dependence on the orientation. Since `Π` does not depend on the orientation up to
isomorphism (`TauCeti.reorientPreprojectiveAlgebraEquiv`), it is enough that *some* reorientation
of `Q` has no sinks; the isomorphism carries every doubled arrow to a doubled arrow up to sign, so
it carries the left-hand map of the Koszul complex of `Q` to that of the reorientation.

A preconnected simple graph which is not acyclic has an orientation without sinks
(`SimpleGraph.Preconnected.exists_forall_adj_and_apply_apply_ne_of_not_isAcyclic`). Hence for every
orientation of such a graph, over every commutative ring, the Koszul complex of every vertex module
is exact at its left end, so it is a projective resolution of the vertex module. This covers the
cycles `A~ₙ` (`n ≥ 2`) and every connected graph with more edges than a spanning tree, all of which
are non-Dynkin; the non-Dynkin trees, such as `D~ₙ` and `E₆~`, `E₇~`, `E₈~`, are not covered.

## Main results

* `TauCeti.forall_preprojectiveMk_ofArrow_reverse_mul_eq_zero_iff_of_reorient`: the Koszul complex
  of `Π_k(Q)` is exact at its left end if some reorientation of `Q` has no sinks.
* `TauCeti.forall_preprojectiveMk_ofArrow_reverse_mul_eq_zero_iff_of_not_isAcyclic`: **the Koszul
  complex of the preprojective algebra of any orientation of a connected graph which is not a tree
  (more generally, of a preconnected graph which is not acyclic) is exact at its left end.**

## References

* P. Etingof and C.-H. Eu, *Koszulity and the Hilbert series of preprojective algebras*, Math.
  Res. Lett. 14 (2007), Sections 2 and 3, for the Koszul complex and the Koszulity of the
  preprojective algebras of non-Dynkin quivers.
* W. Crawley-Boevey, *Quiver algebras, weighted projective lines, and the Deligne--Simpson
  problem*, Section 1, for the independence of the orientation.
-/

public section

namespace TauCeti

open _root_.Quiver PathAlgebra

universe u v w

section Reorient

variable (k : Type w) {Q : Type u} [CommRing k] [Quiver.{v} Q] [Fintype Q]
  [∀ i j : Q, Fintype (i ⟶ j)] (σ : ∀ ⦃i j : Q⦄, (i ⟶ j) → Bool)

/-- **Exactness of the Koszul complex at its left end, for a quiver with a reorientation without
sinks.** If turning around the arrows of `Q` which `σ` labels `true` leaves no vertex without an
outgoing arrow, and `y = e_v y` in `Π_k(Q)`, then `b* y = 0` for every arrow `b` of the doubled
quiver into `v` exactly when `y = 0`. -/
theorem forall_preprojectiveMk_ofArrow_reverse_mul_eq_zero_iff_of_reorient
    (hσ : ∀ u : Q, ∃ w : Q, Nonempty (reorientVertex σ u ⟶ reorientVertex σ w)) (v : Q)
    {y : preprojectiveAlgebra k Q}
    (hy : preprojectiveMk k Q (doubledVertexIdempotent k v) * y = y) :
    (∀ (i : Symmetrify Q) (b : i ⟶ Symmetrify.of.obj v),
      preprojectiveMk k Q (ofArrow (Quiver.reverse b)) * y = 0) ↔ y = 0 := by
  refine ⟨fun h => ?_, fun h i b => by rw [h, mul_zero]⟩
  set e := reorientPreprojectiveAlgebraEquiv k σ
  -- Pull `y` back to the reoriented algebra, where it lies in the corner of `v`.
  have hy' : preprojectiveMk k (Reorient Q σ) (doubledVertexIdempotent k (reorientVertex σ v)) *
      e.symm y = e.symm y :=
    e.injective (by
      rw [map_mul, reorientPreprojectiveAlgebraEquiv_preprojectiveMk_doubledVertexIdempotent,
        e.apply_symm_apply, hy])
  obtain ⟨w, ⟨a⟩⟩ := hσ v
  suffices e.symm y = 0 by rwa [map_eq_zero_iff _ e.symm.injective] at this
  refine (preprojectiveMk_ofArrow_mul_eq_zero_iff k (Q := Reorient Q σ) hσ a hy').1 ?_
  -- The isomorphism carries the outgoing arrow `a` of the reorientation to the formal reverse of
  -- an arrow of the doubled quiver of `Q` into `v`.
  refine e.injective ?_
  rw [map_mul, e.apply_symm_apply, map_zero]
  induction a using reorientHom_induction_on with
  | keep a ha =>
    rw [reorientPreprojectiveAlgebraEquiv_preprojectiveMk_ofArrow_keep]
    simpa only [reverse_reverse] using h _ (Quiver.reverse (Symmetrify.of.map a))
  | flip a ha =>
    rw [reorientPreprojectiveAlgebraEquiv_preprojectiveMk_ofArrow_flip]
    exact h _ (Symmetrify.of.map a)

end Reorient

section Graph

open DoubledQuiver

attribute [local instance] Fintype.ofFinite

variable {V : Type u} {G : SimpleGraph V}

variable (k : Type w) [CommRing k] [Finite V]

/-- **Exactness of the Koszul complex at its left end, for a graph which is not a tree.** Let `G` be
a finite preconnected simple graph which is not acyclic, and `o` any orientation of `G`. If
`y = e_v y` in the preprojective algebra of `o` over a commutative ring `k`, then `b* y = 0` for
every arrow `b` of the doubled quiver into `v` exactly when `y = 0`: the left-hand map of the
Koszul complex of `TauCeti.sum_preprojectiveMk_ofArrow_mul_eq_zero_iff` is injective. -/
theorem forall_preprojectiveMk_ofArrow_reverse_mul_eq_zero_iff_of_not_isAcyclic
    (hG : G.Preconnected) (hc : ¬G.IsAcyclic) (o : Orientation G) (v : OrientedQuiver G o)
    {y : preprojectiveAlgebra k (OrientedQuiver G o)}
    (hy : preprojectiveMk k (OrientedQuiver G o) (doubledVertexIdempotent k v) * y = y) :
    (∀ (i : Symmetrify (OrientedQuiver G o)) (b : i ⟶ Symmetrify.of.obj v),
      preprojectiveMk k (OrientedQuiver G o) (ofArrow (Quiver.reverse b)) * y = 0) ↔ y = 0 := by
  obtain ⟨f, hf⟩ := hG.exists_forall_adj_and_apply_apply_ne_of_not_isAcyclic hc
  obtain ⟨σ, hσ⟩ := exists_forall_exists_nonempty_reorient_hom o hf
  exact forall_preprojectiveMk_ofArrow_reverse_mul_eq_zero_iff_of_reorient k σ hσ v hy

end Graph

end TauCeti

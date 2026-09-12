/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Two
public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.Map
public import TauCeti.RepresentationTheory.Quiver.Preprojective.Basic
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Orientation
public import TauCeti.RepresentationTheory.Quiver.Zigzag.PathAlgebra

/-!
# The signless relation quotient of a doubled graph

The additive preprojective algebra of a quiver `Q` is the path algebra of `Quiver.Symmetrify Q`
modulo the *signed* local relations `∑_{head a = v} a a* - ∑_{tail a = v} a* a`. Those signs are
tied to the orientation of `Q`. The doubled quiver of a simple graph carries no orientation, and
the relation one can write on it without choosing one is the **signless** local relation

```text
∑_{w ∼ v} (v → w → v) = 0,
```

the sum of all backtracks based at `v`. This file defines that relation, the two-sided ideal it
spans, and the quotient algebra `TauCeti.signlessQuadraticDual`, and compares the quotient with the
additive preprojective algebra of an orientation of the graph.

The comparison runs along the algebra isomorphism
`TauCeti.DoubledQuiver.orientedPathAlgEquiv` induced by the prefunctors of
`TauCeti/RepresentationTheory/Quiver/Zigzag/Orientation.lean`, which identify the symmetrification
of an oriented graph with its doubled quiver. Under it the head backtrack of an oriented arrow
`a : i ⟶ j` becomes the backtrack at `j` along the edge `ij`, and its tail backtrack becomes the
backtrack at `i` along the same edge; so at a vertex `v` the signed local relator becomes the
difference of the two partial sums of backtracks at `v`, over the edges oriented into `v` and over
those oriented out of `v`. Two hypotheses make that difference a sign times the signless relator:

* if the orientation is **source--sink**, one of the two partial sums is empty at every vertex, so
  the signed relator is `±` the signless one and the two quotients agree. A bipartite graph admits
  such an orientation, and the roadmap's rescaling of arrows is then not needed: with every edge
  oriented out of the chosen part the two relation ideals are equal on the nose, the overall sign
  at a source being absorbed by the ideal;
* in **characteristic two** the signs disappear, so the two quotients agree for *every*
  orientation, of any finite simple graph, bipartite or not.

Outside these two cases the signless quotient is kept as an algebra of its own: nothing below
calls it a preprojective algebra without a proof.

## Main definitions

* `TauCeti.signlessRelator`: the signless local relator at a vertex.
* `TauCeti.signlessQuadraticDualIdeal` and `TauCeti.signlessQuadraticDual`: the two-sided ideal it
  spans and the relation quotient, with quotient map `TauCeti.signlessMk` and universal property
  `TauCeti.signlessLift`.
* `TauCeti.DoubledQuiver.orientedPathAlgEquiv`: the isomorphism of path algebras attached to an
  orientation of a simple graph.
* `TauCeti.IsSignedMatch`: the hypothesis that the signed local relators of an orientation become
  the signless relators up to sign.
* `TauCeti.signlessQuadraticDualEquivPreprojective`: **the comparison isomorphism** for a
  source--sink orientation, with `TauCeti.signlessQuadraticDualEquivPreprojectiveOfCharTwo` its
  characteristic-two counterpart for an arbitrary orientation, both specialising
  `TauCeti.signlessQuadraticDualEquivPreprojectiveOfSignedMatch`.

## Main results

* `TauCeti.DoubledQuiver.orientedPathAlgEquiv_headBacktrackElem` and
  `TauCeti.DoubledQuiver.orientedPathAlgEquiv_tailBacktrackElem`: the two backtracks of an
  oriented arrow, read in the doubled path algebra.
* `TauCeti.orientedPathAlgEquiv_localPreprojectiveRelator_of_source` and
  `TauCeti.orientedPathAlgEquiv_localPreprojectiveRelator_of_sink`: **at a source the signed local
  relator becomes the negative of the signless relator, and at a sink it becomes the signless
  relator itself.**
* `TauCeti.orientedPathAlgEquiv_localPreprojectiveRelator_of_charTwo`: **in characteristic two the
  signed local relator becomes the signless relator at every vertex, for every orientation.**
* `TauCeti.isSignedMatch_of_isSourceSink` and `TauCeti.isSignedMatch_of_charTwo`: the two
  hypotheses under which the comparison isomorphism is available.

## References

This is the second clause of Layer 5 of `TauCetiRoadmap/ZigzagPreprojective/README.md`, which asks
for the signless local relation `∑_{j∼i} (i→j→i) = 0` of the doubled graph, for the comparison of
its quotient with the signed preprojective presentation of a source--sink orientation of a
bipartite graph, and for the characteristic-two collapse of the sign obstruction in the
non-bipartite case. The identification of this quotient with the quadratic dual of the zigzag
algebra is the first clause of that layer and is not proved here. The declaration names follow
the target-signature prototype in `TauCetiRoadmap/ZigzagPreprojective/Suggested.lean`. See
Huerfano--Khovanov, *A category for the adjoint representation*, Section 3, and Crawley-Boevey,
*Quiver algebras, weighted projective lines, and the Deligne--Simpson problem*, Section 1.
-/

public section

namespace TauCeti

open PathAlgebra DoubledQuiver _root_.Quiver

universe u w

/-! ### The signless relator -/

section Relator

variable (k : Type w) [CommRing k] {V : Type u} (G : SimpleGraph V) [Fintype V]
  [DecidableRel G.Adj]

/-- The **signless local relator** at a vertex `v` of a simple graph: the sum, over the neighbours
`w` of `v`, of the backtrack which leaves `v` along the edge `vw` and returns along it. At an
isolated vertex the sum is empty, so the relator is zero and imposes nothing. -/
noncomputable def signlessRelator (v : V) : pathAlgebra k (DoubledQuiver G) :=
  ∑ w : V, if h : G.Adj v w then backtrackElem G k h else 0

/-- The signless relator, unfolded as a sum of backtracks over the neighbours of the vertex. This
is the defining equation, exposed for use outside this module. -/
theorem signlessRelator_def (v : V) :
    signlessRelator k G v = ∑ w : V, if h : G.Adj v w then backtrackElem G k h else 0 := by
  rw [signlessRelator]

/-- The signless relator at `v` lies in the corner cut out by the vertex idempotent at `v`. -/
@[simp]
theorem vertexIdempotent_mul_signlessRelator (v : V) :
    vertexIdempotent k (vertex G v) * signlessRelator k G v = signlessRelator k G v := by
  rw [signlessRelator_def, Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  split
  · rw [vertexIdempotent_mul_backtrackElem]
  · rw [mul_zero]

/-- The signless relator at `v` lies in the corner cut out by the vertex idempotent at `v`. -/
@[simp]
theorem signlessRelator_mul_vertexIdempotent (v : V) :
    signlessRelator k G v * vertexIdempotent k (vertex G v) = signlessRelator k G v := by
  rw [signlessRelator_def, Finset.sum_mul]
  refine Finset.sum_congr rfl fun w _ => ?_
  split
  · rw [backtrackElem_mul_vertexIdempotent]
  · rw [zero_mul]

/-! ### The relation ideal and the quotient algebra -/

/-- The two-sided ideal spanned by the signless local relators. -/
noncomputable def signlessQuadraticDualIdeal : TwoSidedIdeal (pathAlgebra k (DoubledQuiver G)) :=
  TwoSidedIdeal.span (Set.range (signlessRelator k G))

/-- The signless relation ideal is the two-sided span of the signless relators. This is the
defining equation, exposed for use outside this module. -/
theorem signlessQuadraticDualIdeal_eq_span :
    signlessQuadraticDualIdeal k G = TwoSidedIdeal.span (Set.range (signlessRelator k G)) := (rfl)

theorem signlessRelator_mem_signlessQuadraticDualIdeal (v : V) :
    signlessRelator k G v ∈ signlessQuadraticDualIdeal k G :=
  TwoSidedIdeal.subset_span ⟨v, rfl⟩

/-- The **signless relation quotient** of a finite simple graph: the path algebra of the doubled
quiver modulo the signless local relations. Its identification with the quadratic dual of the
zigzag algebra is a theorem of Layer 5 of the roadmap, not part of this definition. -/
noncomputable abbrev signlessQuadraticDual : Type _ :=
  pathAlgebra k (DoubledQuiver G) ⧸ (signlessQuadraticDualIdeal k G).asIdeal

/-- The quotient map onto the signless relation quotient. -/
noncomputable def signlessMk :
    pathAlgebra k (DoubledQuiver G) →ₐ[k] signlessQuadraticDual k G :=
  Ideal.Quotient.mkₐ k _

theorem signlessMk_apply (f : pathAlgebra k (DoubledQuiver G)) :
    signlessMk k G f = Ideal.Quotient.mk (signlessQuadraticDualIdeal k G).asIdeal f := by
  rw [signlessMk, Ideal.Quotient.mkₐ_eq_mk]

theorem signlessMk_surjective : Function.Surjective (signlessMk k G) :=
  Ideal.Quotient.mk_surjective

@[simp]
theorem signlessMk_eq_zero_iff {f : pathAlgebra k (DoubledQuiver G)} :
    signlessMk k G f = 0 ↔ f ∈ signlessQuadraticDualIdeal k G := by
  rw [signlessMk_apply, Ideal.Quotient.eq_zero_iff_mem, TwoSidedIdeal.mem_asIdeal]

@[simp]
theorem signlessMk_signlessRelator (v : V) : signlessMk k G (signlessRelator k G v) = 0 :=
  (signlessMk_eq_zero_iff k G).2 (signlessRelator_mem_signlessQuadraticDualIdeal k G v)

/-- **The defining relation of the signless quotient**, read at a vertex `v`: the backtracks based
at `v` sum to zero. -/
theorem sum_signlessMk_backtrackElem_eq_zero (v : V) :
    (∑ w : V, if h : G.Adj v w then signlessMk k G (backtrackElem G k h) else 0) = 0 := by
  have hsum : (∑ w : V, if h : G.Adj v w then signlessMk k G (backtrackElem G k h) else 0)
      = signlessMk k G (signlessRelator k G v) := by
    rw [signlessRelator_def, map_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    by_cases hw : G.Adj v w <;> simp [hw]
  rw [hsum, signlessMk_signlessRelator]

end Relator

/-! ### The universal property -/

section Lift

variable {k : Type w} {V : Type u} {B : Type*} [CommRing k] (G : SimpleGraph V) [Fintype V]
  [DecidableRel G.Adj] [Ring B] [Algebra k B] (f : pathAlgebra k (DoubledQuiver G) →ₐ[k] B)

/-- An algebra map out of the doubled path algebra which kills every signless relator kills the
whole relation ideal. -/
theorem signlessQuadraticDualIdeal_le_ker (hf : ∀ v : V, f (signlessRelator k G v) = 0) :
    signlessQuadraticDualIdeal k G ≤ TwoSidedIdeal.ker f := by
  refine TwoSidedIdeal.span_le.2 ?_
  rintro _ ⟨v, rfl⟩
  exact (TwoSidedIdeal.mem_ker f).2 (hf v)

/-- **The universal property of the signless relation quotient**: an algebra map out of the doubled
path algebra which kills every signless relator descends to the quotient. -/
noncomputable def signlessLift (hf : ∀ v : V, f (signlessRelator k G v) = 0) :
    signlessQuadraticDual k G →ₐ[k] B :=
  Ideal.Quotient.liftₐ _ f fun _ ha =>
    (TwoSidedIdeal.mem_ker f).1
      (signlessQuadraticDualIdeal_le_ker G f hf (TwoSidedIdeal.mem_asIdeal.1 ha))

theorem signlessLift_comp_signlessMk (hf : ∀ v : V, f (signlessRelator k G v) = 0) :
    (signlessLift G f hf).comp (signlessMk k G) = f := by
  rw [signlessLift, signlessMk, Ideal.Quotient.liftₐ_comp]

@[simp]
theorem signlessLift_signlessMk (hf : ∀ v : V, f (signlessRelator k G v) = 0)
    (x : pathAlgebra k (DoubledQuiver G)) :
    signlessLift G f hf (signlessMk k G x) = f x :=
  AlgHom.congr_fun (signlessLift_comp_signlessMk G f hf) x

/-- **The lift is the only one**: the quotient map is surjective, so an algebra map on the signless
quotient is determined by its composite with it. -/
theorem signlessLift_unique (hf : ∀ v : V, f (signlessRelator k G v) = 0)
    (g : signlessQuadraticDual k G →ₐ[k] B) (hg : g.comp (signlessMk k G) = f) :
    g = signlessLift G f hf := by
  refine AlgHom.ext fun y => ?_
  obtain ⟨x, rfl⟩ := signlessMk_surjective k G y
  rw [signlessLift_signlessMk, ← hg, AlgHom.comp_apply]

end Lift

/-! ### The path algebra of an orientation -/

namespace DoubledQuiver

variable (k : Type w) [CommRing k] {V : Type u} {G : SimpleGraph V} [Fintype V]
  (o : Orientation G)

/-- **The isomorphism of path algebras attached to an orientation of a simple graph**: the
symmetrification of the oriented quiver of `o` is the doubled quiver of `G`, so the two path
algebras are relabellings of one another. -/
noncomputable def orientedPathAlgEquiv :
    pathAlgebra k (Symmetrify (OrientedQuiver G o)) ≃ₐ[k] pathAlgebra k (DoubledQuiver G) :=
  PathAlgebra.mapAlgEquiv k (symmetrifyMap G o) (unsymmetrifyMap G o)
    (symmetrifyMap_comp_unsymmetrifyMap G o) (unsymmetrifyMap_comp_symmetrifyMap G o)

/-- The relabelling sends the element of an arrow to the element of its image arrow. Deliberately
not a `simp` lemma: `TauCeti.PathAlgebra.ofArrow_eq_ofPath` already rewrites its left-hand side,
and `simpNF` rejects the pair. -/
theorem orientedPathAlgEquiv_ofArrow {x y : Symmetrify (OrientedQuiver G o)} (e : x ⟶ y) :
    orientedPathAlgEquiv k o (ofArrow e) = ofArrow ((symmetrifyMap G o).map e) := by
  rw [orientedPathAlgEquiv, PathAlgebra.mapAlgEquiv_apply, PathAlgebra.mapAlgHom_ofArrow]

/-- The relabelling sends the arrow of a dart selected by the orientation to the doubled-quiver
arrow of that dart. -/
theorem orientedPathAlgEquiv_ofArrow_of {i j : V} (h : G.Adj i j)
    (ho : (⟨(i, j), h⟩ : G.Dart) ∈ o) :
    orientedPathAlgEquiv k o (ofArrow (Symmetrify.of.map (OrientedQuiver.arrow G o h ho)))
      = ofArrow (arrow G h) := by
  have hmap : (symmetrifyMap G o).map (Symmetrify.of.map (OrientedQuiver.arrow G o h ho))
      = Quiver.homOfEq (arrow G h) (symmetrifyMap_obj G o i).symm
          (symmetrifyMap_obj G o j).symm := Subsingleton.elim _ _
  rw [orientedPathAlgEquiv_ofArrow, hmap]
  exact ofArrow_homOfEq _ _ _

/-- The relabelling sends the formal reverse of the arrow of a selected dart to the doubled-quiver
arrow of the reversed dart. -/
theorem orientedPathAlgEquiv_ofArrow_reverse_of {i j : V} (h : G.Adj i j)
    (ho : (⟨(i, j), h⟩ : G.Dart) ∈ o) :
    orientedPathAlgEquiv k o
        (ofArrow (Quiver.reverse (Symmetrify.of.map (OrientedQuiver.arrow G o h ho))))
      = ofArrow (arrow G h.symm) := by
  have hmap : (symmetrifyMap G o).map
      (Quiver.reverse (Symmetrify.of.map (OrientedQuiver.arrow G o h ho)))
        = Quiver.homOfEq (arrow G h.symm) (symmetrifyMap_obj G o j).symm
            (symmetrifyMap_obj G o i).symm := Subsingleton.elim _ _
  rw [orientedPathAlgEquiv_ofArrow, hmap]
  exact ofArrow_homOfEq _ _ _

/-- **The head backtrack of an oriented arrow is the backtrack at its head.** The arrow
`a : i ⟶ j` of the orientation traverses the edge `ij`; the word `a a*` leaves `j` along that edge
and returns, so it becomes the backtrack at `j`. -/
theorem orientedPathAlgEquiv_headBacktrackElem {i j : V} (h : G.Adj i j)
    (ho : (⟨(i, j), h⟩ : G.Dart) ∈ o) :
    orientedPathAlgEquiv k o (headBacktrackElem k (OrientedQuiver.arrow G o h ho))
      = backtrackElem G k h.symm := by
  rw [← ofArrow_mul_ofArrow_reverse_eq_headBacktrackElem, map_mul,
    orientedPathAlgEquiv_ofArrow_of k o h ho, orientedPathAlgEquiv_ofArrow_reverse_of k o h ho]
  exact ofArrow_symm_mul_ofArrow G k h.symm

/-- **The tail backtrack of an oriented arrow is the backtrack at its tail.** The word `a* a`
leaves the tail `i` of `a : i ⟶ j` along the edge `ij` and returns. -/
theorem orientedPathAlgEquiv_tailBacktrackElem {i j : V} (h : G.Adj i j)
    (ho : (⟨(i, j), h⟩ : G.Dart) ∈ o) :
    orientedPathAlgEquiv k o (tailBacktrackElem k (OrientedQuiver.arrow G o h ho))
      = backtrackElem G k h := by
  rw [← ofArrow_reverse_mul_ofArrow_eq_tailBacktrackElem, map_mul,
    orientedPathAlgEquiv_ofArrow_reverse_of k o h ho, orientedPathAlgEquiv_ofArrow_of k o h ho]
  exact ofArrow_symm_mul_ofArrow G k h

end DoubledQuiver

/-! ### The corner sums of an orientation -/

section Corner

variable (k : Type w) [CommRing k] {V : Type u} {G : SimpleGraph V}
  (o : DoubledQuiver.Orientation G)

/-- The head-backtrack sum of a corner with no incoming arrow vanishes. -/
theorem sum_headBacktrackElem_eq_zero {w v : V}
    (hwv : ∀ h : G.Adj w v, (⟨(w, v), h⟩ : G.Dart) ∉ o) :
    (∑ a : (OrientedQuiver.vertex G o w ⟶ OrientedQuiver.vertex G o v),
      headBacktrackElem k a) = 0 :=
  haveI := OrientedQuiver.isEmpty_hom G o hwv
  Fintype.sum_empty _

/-- The tail-backtrack sum of a corner with no outgoing arrow vanishes. -/
theorem sum_tailBacktrackElem_eq_zero {v w : V}
    (hvw : ∀ h : G.Adj v w, (⟨(v, w), h⟩ : G.Dart) ∉ o) :
    (∑ a : (OrientedQuiver.vertex G o v ⟶ OrientedQuiver.vertex G o w),
      tailBacktrackElem k a) = 0 :=
  haveI := OrientedQuiver.isEmpty_hom G o hvw
  Fintype.sum_empty _

variable [Fintype V]

/-- A sum over the vertices of an oriented quiver is a sum over the vertices of the graph. -/
private theorem sum_orientedQuiver {M : Type*} [AddCommMonoid M]
    (F : OrientedQuiver G o → M) :
    ∑ i : OrientedQuiver G o, F i = ∑ w : V, F (OrientedQuiver.vertex G o w) := by
  rw [← Equiv.sum_comp (OrientedQuiver.vertexEquiv G o) F]
  exact Finset.sum_congr rfl fun w _ => by rw [OrientedQuiver.vertexEquiv_apply]

/-- A corner carrying an arrow into `v` contributes the backtrack at `v` along that edge. -/
theorem orientedPathAlgEquiv_sum_headBacktrackElem {v w : V} (h : G.Adj v w)
    (ho : (⟨(w, v), h.symm⟩ : G.Dart) ∈ o) :
    DoubledQuiver.orientedPathAlgEquiv k o
        (∑ a : (OrientedQuiver.vertex G o w ⟶ OrientedQuiver.vertex G o v),
          headBacktrackElem k a) = backtrackElem G k h := by
  rw [Fintype.sum_subsingleton _ (OrientedQuiver.arrow G o h.symm ho)]
  exact DoubledQuiver.orientedPathAlgEquiv_headBacktrackElem k o h.symm ho

/-- A corner carrying an arrow out of `v` contributes the backtrack at `v` along that edge. -/
theorem orientedPathAlgEquiv_sum_tailBacktrackElem {v w : V} (h : G.Adj v w)
    (ho : (⟨(v, w), h⟩ : G.Dart) ∈ o) :
    DoubledQuiver.orientedPathAlgEquiv k o
        (∑ a : (OrientedQuiver.vertex G o v ⟶ OrientedQuiver.vertex G o w),
          tailBacktrackElem k a) = backtrackElem G k h := by
  rw [Fintype.sum_subsingleton _ (OrientedQuiver.arrow G o h ho)]
  exact DoubledQuiver.orientedPathAlgEquiv_tailBacktrackElem k o h ho

/-- **Each edge at `v` contributes its backtrack exactly once**, to the incoming corner sum if it
is oriented into `v` and to the outgoing one otherwise. This is the computation which the two
comparison theorems below specialise. -/
theorem orientedPathAlgEquiv_sum_headBacktrackElem_add_sum_tailBacktrackElem
    [DecidableRel G.Adj] (v w : V) :
    DoubledQuiver.orientedPathAlgEquiv k o
        (∑ a : (OrientedQuiver.vertex G o w ⟶ OrientedQuiver.vertex G o v),
          headBacktrackElem k a)
      + DoubledQuiver.orientedPathAlgEquiv k o
        (∑ a : (OrientedQuiver.vertex G o v ⟶ OrientedQuiver.vertex G o w),
          tailBacktrackElem k a)
      = if h : G.Adj v w then backtrackElem G k h else 0 := by
  by_cases hadj : G.Adj v w
  · by_cases hd : (⟨(v, w), hadj⟩ : G.Dart) ∈ o
    · rw [sum_headBacktrackElem_eq_zero k o
        (fun h => (o.symm_mem_iff_not_mem ⟨(w, v), h⟩).1 hd), map_zero, zero_add,
        orientedPathAlgEquiv_sum_tailBacktrackElem k o hadj hd]
      simp [hadj]
    · rw [sum_tailBacktrackElem_eq_zero k o (fun _ => hd), map_zero, add_zero,
        orientedPathAlgEquiv_sum_headBacktrackElem k o hadj
          ((o.symm_mem_iff_not_mem ⟨(v, w), hadj⟩).2 hd)]
      simp [hadj]
  · rw [sum_headBacktrackElem_eq_zero k o (fun h => absurd h.symm hadj),
      sum_tailBacktrackElem_eq_zero k o (fun h => absurd h hadj), map_zero, add_zero]
    simp [hadj]

end Corner

/-! ### Comparing the two presentations -/

section Comparison

variable (k : Type w) [CommRing k] {V : Type u} {G : SimpleGraph V} [Fintype V]
  [DecidableRel G.Adj] (o : DoubledQuiver.Orientation G)

/-- **At a sink the signed local relator becomes the signless relator.** Every edge at `v` is
oriented into `v`, so the local relator has no outgoing term and its incoming terms enumerate the
backtracks at `v`. -/
theorem orientedPathAlgEquiv_localPreprojectiveRelator_of_sink (v : V)
    (hv : ∀ ⦃w : V⦄ (h : G.Adj v w), (⟨(v, w), h⟩ : G.Dart) ∉ o) :
    DoubledQuiver.orientedPathAlgEquiv k o
        (localPreprojectiveRelator k (OrientedQuiver.vertex G o v))
      = signlessRelator k G v := by
  have hhead : (∑ i : OrientedQuiver G o,
        ∑ a : (i ⟶ OrientedQuiver.vertex G o v), headBacktrackElem k a)
      = ∑ w : V, ∑ a : (OrientedQuiver.vertex G o w ⟶ OrientedQuiver.vertex G o v),
          headBacktrackElem k a := sum_orientedQuiver o _
  have htail : (∑ j : OrientedQuiver G o,
        ∑ a : (OrientedQuiver.vertex G o v ⟶ j), tailBacktrackElem k a)
      = ∑ w : V, ∑ a : (OrientedQuiver.vertex G o v ⟶ OrientedQuiver.vertex G o w),
          tailBacktrackElem k a := sum_orientedQuiver o _
  rw [localPreprojectiveRelator_def, hhead, htail,
    Finset.sum_eq_zero fun w _ => sum_tailBacktrackElem_eq_zero k o fun h => hv h, sub_zero,
    map_sum, signlessRelator_def]
  refine Finset.sum_congr rfl fun w _ => ?_
  by_cases hw : G.Adj v w
  · rw [orientedPathAlgEquiv_sum_headBacktrackElem k o hw
      ((o.symm_mem_iff_not_mem ⟨(v, w), hw⟩).2 (hv hw))]
    simp [hw]
  · rw [sum_headBacktrackElem_eq_zero k o fun h => absurd h.symm hw, map_zero]
    simp [hw]

/-- **At a source the signed local relator becomes the negative of the signless relator.** Every
edge at `v` is oriented out of `v`, so the local relator has no incoming term. The sign is absorbed
by the relation ideal, which is why no rescaling of arrows is needed below. -/
theorem orientedPathAlgEquiv_localPreprojectiveRelator_of_source (v : V)
    (hv : ∀ ⦃w : V⦄ (h : G.Adj v w), (⟨(v, w), h⟩ : G.Dart) ∈ o) :
    DoubledQuiver.orientedPathAlgEquiv k o
        (localPreprojectiveRelator k (OrientedQuiver.vertex G o v))
      = -signlessRelator k G v := by
  have hhead : (∑ i : OrientedQuiver G o,
        ∑ a : (i ⟶ OrientedQuiver.vertex G o v), headBacktrackElem k a)
      = ∑ w : V, ∑ a : (OrientedQuiver.vertex G o w ⟶ OrientedQuiver.vertex G o v),
          headBacktrackElem k a := sum_orientedQuiver o _
  have htail : (∑ j : OrientedQuiver G o,
        ∑ a : (OrientedQuiver.vertex G o v ⟶ j), tailBacktrackElem k a)
      = ∑ w : V, ∑ a : (OrientedQuiver.vertex G o v ⟶ OrientedQuiver.vertex G o w),
          tailBacktrackElem k a := sum_orientedQuiver o _
  rw [localPreprojectiveRelator_def, hhead, htail,
    Finset.sum_eq_zero fun w _ => sum_headBacktrackElem_eq_zero k o
      fun h => (o.symm_mem_iff_not_mem ⟨(w, v), h⟩).1 (hv h.symm),
    zero_sub, map_neg, map_sum, signlessRelator_def]
  refine congrArg Neg.neg (Finset.sum_congr rfl fun w _ => ?_)
  by_cases hw : G.Adj v w
  · rw [orientedPathAlgEquiv_sum_tailBacktrackElem k o hw (hv hw)]
    simp [hw]
  · rw [sum_tailBacktrackElem_eq_zero k o fun h => absurd h hw, map_zero]
    simp [hw]

/-- **In characteristic two the signed local relator becomes the signless relator**, at every
vertex and for every orientation: the two partial sums of backtracks at `v` differ by a sign which
the characteristic destroys, and together they enumerate the backtracks at `v` exactly once. -/
theorem orientedPathAlgEquiv_localPreprojectiveRelator_of_charTwo [CharP k 2] (v : V) :
    DoubledQuiver.orientedPathAlgEquiv k o
        (localPreprojectiveRelator k (OrientedQuiver.vertex G o v))
      = signlessRelator k G v := by
  have hhead : (∑ i : OrientedQuiver G o,
        ∑ a : (i ⟶ OrientedQuiver.vertex G o v), headBacktrackElem k a)
      = ∑ w : V, ∑ a : (OrientedQuiver.vertex G o w ⟶ OrientedQuiver.vertex G o v),
          headBacktrackElem k a := sum_orientedQuiver o _
  have htail : (∑ j : OrientedQuiver G o,
        ∑ a : (OrientedQuiver.vertex G o v ⟶ j), tailBacktrackElem k a)
      = ∑ w : V, ∑ a : (OrientedQuiver.vertex G o v ⟶ OrientedQuiver.vertex G o w),
          tailBacktrackElem k a := sum_orientedQuiver o _
  have hneg : ∀ y : pathAlgebra k (Symmetrify (OrientedQuiver G o)), -y = y := fun y => by
    rw [neg_eq_iff_add_eq_zero, ← two_smul k y, show ((2 : k) = 0) from by
      exact_mod_cast CharP.cast_eq_zero k 2, zero_smul]
  rw [localPreprojectiveRelator_def, hhead, htail, sub_eq_add_neg, hneg, map_add, map_sum, map_sum,
    ← Finset.sum_add_distrib, signlessRelator_def]
  exact Finset.sum_congr rfl fun w _ =>
    orientedPathAlgEquiv_sum_headBacktrackElem_add_sum_tailBacktrackElem k o v w

/-! ### The comparison isomorphism -/

/-- The two presentations **match up to sign**: at every vertex the signed local preprojective
relator of `o` becomes the signless relator, or its negative. This is the hypothesis under which
the two relation quotients agree, and the two comparison theorems above verify it. -/
def IsSignedMatch : Prop :=
  ∀ v : V, DoubledQuiver.orientedPathAlgEquiv k o
      (localPreprojectiveRelator k (OrientedQuiver.vertex G o v)) = signlessRelator k G v ∨
    DoubledQuiver.orientedPathAlgEquiv k o
      (localPreprojectiveRelator k (OrientedQuiver.vertex G o v)) = -signlessRelator k G v

/-- The defining condition of a signed match, exposed for use outside this module. -/
theorem isSignedMatch_iff :
    IsSignedMatch k o ↔ ∀ v : V, DoubledQuiver.orientedPathAlgEquiv k o
        (localPreprojectiveRelator k (OrientedQuiver.vertex G o v)) = signlessRelator k G v ∨
      DoubledQuiver.orientedPathAlgEquiv k o
        (localPreprojectiveRelator k (OrientedQuiver.vertex G o v))
          = -signlessRelator k G v := Iff.rfl

variable {k o}

private theorem signlessMk_orientedPathAlgEquiv_localPreprojectiveRelator
    (hsign : IsSignedMatch k o) (v : V) :
    signlessMk k G (DoubledQuiver.orientedPathAlgEquiv k o
      (localPreprojectiveRelator k (OrientedQuiver.vertex G o v))) = 0 := by
  rcases hsign v with h | h <;> rw [h]
  · exact signlessMk_signlessRelator k G v
  · rw [map_neg, signlessMk_signlessRelator, neg_zero]

private theorem preprojectiveMk_orientedPathAlgEquiv_symm_signlessRelator
    (hsign : IsSignedMatch k o) (v : V) :
    preprojectiveMk k (OrientedQuiver G o)
      ((DoubledQuiver.orientedPathAlgEquiv k o).symm (signlessRelator k G v)) = 0 := by
  rcases hsign v with h | h
  · rw [← h, AlgEquiv.symm_apply_apply, preprojectiveMk_localPreprojectiveRelator]
  · have h' : DoubledQuiver.orientedPathAlgEquiv k o
        (-localPreprojectiveRelator k (OrientedQuiver.vertex G o v)) = signlessRelator k G v := by
      rw [map_neg, h, neg_neg]
    rw [← h', AlgEquiv.symm_apply_apply, map_neg, preprojectiveMk_localPreprojectiveRelator,
      neg_zero]

/-- The map from the signless quotient to the preprojective algebra of a matching orientation. -/
private noncomputable def signlessToPreprojective (hsign : IsSignedMatch k o) :
    signlessQuadraticDual k G →ₐ[k] preprojectiveAlgebra k (OrientedQuiver G o) :=
  signlessLift G ((preprojectiveMk k (OrientedQuiver G o)).comp
      (DoubledQuiver.orientedPathAlgEquiv k o).symm.toAlgHom)
    (preprojectiveMk_orientedPathAlgEquiv_symm_signlessRelator hsign)

/-- The map from the preprojective algebra of a matching orientation to the signless quotient. -/
private noncomputable def preprojectiveToSignless (hsign : IsSignedMatch k o) :
    preprojectiveAlgebra k (OrientedQuiver G o) →ₐ[k] signlessQuadraticDual k G :=
  preprojectiveLiftOfForallLocalPreprojectiveRelator
    ((signlessMk k G).comp (DoubledQuiver.orientedPathAlgEquiv k o).toAlgHom)
    fun v => by
      obtain ⟨w, rfl⟩ : ∃ w : V, OrientedQuiver.vertex G o w = v :=
        ⟨(OrientedQuiver.vertexEquiv G o).symm v, by
          rw [← OrientedQuiver.vertexEquiv_apply, Equiv.apply_symm_apply]⟩
      exact signlessMk_orientedPathAlgEquiv_localPreprojectiveRelator hsign w

private theorem signlessToPreprojective_signlessMk (hsign : IsSignedMatch k o)
    (x : pathAlgebra k (DoubledQuiver G)) :
    signlessToPreprojective hsign (signlessMk k G x)
      = preprojectiveMk k (OrientedQuiver G o)
          ((DoubledQuiver.orientedPathAlgEquiv k o).symm x) :=
  signlessLift_signlessMk G _ _ x

private theorem preprojectiveToSignless_preprojectiveMk (hsign : IsSignedMatch k o)
    (x : pathAlgebra k (Symmetrify (OrientedQuiver G o))) :
    preprojectiveToSignless hsign (preprojectiveMk k (OrientedQuiver G o) x)
      = signlessMk k G (DoubledQuiver.orientedPathAlgEquiv k o x) :=
  preprojectiveLift_of_forall_localPreprojectiveRelator_preprojectiveMk _ _ x

/-- **The signless quotient is the preprojective algebra of a matching orientation.** -/
noncomputable def signlessQuadraticDualEquivPreprojectiveOfSignedMatch
    (hsign : IsSignedMatch k o) :
    signlessQuadraticDual k G ≃ₐ[k] preprojectiveAlgebra k (OrientedQuiver G o) :=
  AlgEquiv.ofAlgHom (signlessToPreprojective hsign) (preprojectiveToSignless hsign)
    (AlgHom.ext fun y => by
      obtain ⟨x, rfl⟩ := preprojectiveMk_surjective k (OrientedQuiver G o) y
      rw [AlgHom.comp_apply, preprojectiveToSignless_preprojectiveMk,
        signlessToPreprojective_signlessMk, AlgEquiv.symm_apply_apply, AlgHom.id_apply])
    (AlgHom.ext fun y => by
      obtain ⟨x, rfl⟩ := signlessMk_surjective k G y
      rw [AlgHom.comp_apply, signlessToPreprojective_signlessMk,
        preprojectiveToSignless_preprojectiveMk, AlgEquiv.apply_symm_apply, AlgHom.id_apply])

/-- The comparison isomorphism on the class of a doubled path. -/
@[simp]
theorem signlessQuadraticDualEquivPreprojectiveOfSignedMatch_signlessMk
    (hsign : IsSignedMatch k o) (x : pathAlgebra k (DoubledQuiver G)) :
    signlessQuadraticDualEquivPreprojectiveOfSignedMatch hsign (signlessMk k G x)
      = preprojectiveMk k (OrientedQuiver G o)
          ((DoubledQuiver.orientedPathAlgEquiv k o).symm x) :=
  signlessToPreprojective_signlessMk hsign x

/-- The inverse comparison isomorphism on the class of a doubled path. -/
@[simp]
theorem signlessQuadraticDualEquivPreprojectiveOfSignedMatch_symm_preprojectiveMk
    (hsign : IsSignedMatch k o) (x : pathAlgebra k (Symmetrify (OrientedQuiver G o))) :
    (signlessQuadraticDualEquivPreprojectiveOfSignedMatch hsign).symm
        (preprojectiveMk k (OrientedQuiver G o) x)
      = signlessMk k G (DoubledQuiver.orientedPathAlgEquiv k o x) :=
  preprojectiveToSignless_preprojectiveMk hsign x

/-- **A source--sink orientation matches the signless presentation**: at each vertex the signed
local relator is the signless relator at a sink and its negative at a source. -/
theorem isSignedMatch_of_isSourceSink (hss : o.IsSourceSink) : IsSignedMatch k o := fun v =>
  ((DoubledQuiver.Orientation.isSourceSink_iff G o).1 hss v).elim
    (fun hv => Or.inr (orientedPathAlgEquiv_localPreprojectiveRelator_of_source k o v hv))
    (fun hv => Or.inl (orientedPathAlgEquiv_localPreprojectiveRelator_of_sink k o v hv))

/-- **In characteristic two every orientation matches the signless presentation.** -/
theorem isSignedMatch_of_charTwo [CharP k 2] : IsSignedMatch k o := fun v =>
  Or.inl (orientedPathAlgEquiv_localPreprojectiveRelator_of_charTwo k o v)

/-- **The comparison for a source--sink orientation.** For a bipartite graph, with every edge
oriented out of one part of a bipartition, the signless relation quotient of the doubled graph is
the additive preprojective algebra of the orientation. -/
noncomputable def signlessQuadraticDualEquivPreprojective (hss : o.IsSourceSink) :
    signlessQuadraticDual k G ≃ₐ[k] preprojectiveAlgebra k (OrientedQuiver G o) :=
  signlessQuadraticDualEquivPreprojectiveOfSignedMatch (isSignedMatch_of_isSourceSink hss)

/-- The source--sink comparison on the class of a doubled path. -/
@[simp]
theorem signlessQuadraticDualEquivPreprojective_signlessMk (hss : o.IsSourceSink)
    (x : pathAlgebra k (DoubledQuiver G)) :
    signlessQuadraticDualEquivPreprojective hss (signlessMk k G x)
      = preprojectiveMk k (OrientedQuiver G o)
          ((DoubledQuiver.orientedPathAlgEquiv k o).symm x) :=
  signlessToPreprojective_signlessMk (isSignedMatch_of_isSourceSink hss) x

/-- **The comparison in characteristic two**, for an arbitrary orientation of an arbitrary finite
simple graph: the sign obstruction which forces bipartiteness above disappears. -/
noncomputable def signlessQuadraticDualEquivPreprojectiveOfCharTwo [CharP k 2] :
    signlessQuadraticDual k G ≃ₐ[k] preprojectiveAlgebra k (OrientedQuiver G o) :=
  signlessQuadraticDualEquivPreprojectiveOfSignedMatch (isSignedMatch_of_charTwo (o := o))

/-- The characteristic-two comparison on the class of a doubled path. -/
@[simp]
theorem signlessQuadraticDualEquivPreprojectiveOfCharTwo_signlessMk [CharP k 2]
    (x : pathAlgebra k (DoubledQuiver G)) :
    signlessQuadraticDualEquivPreprojectiveOfCharTwo (k := k) (o := o) (signlessMk k G x)
      = preprojectiveMk k (OrientedQuiver G o)
          ((DoubledQuiver.orientedPathAlgEquiv k o).symm x) :=
  signlessToPreprojective_signlessMk (isSignedMatch_of_charTwo (o := o)) x

end Comparison

end TauCeti

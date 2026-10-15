/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.FiniteRepType.Cycle
public import TauCeti.RepresentationTheory.Quiver.FiniteRepType.PosDef

/-!
# Gabriel equivalences

**Gabriel's theorem** says that a finite connected quiver has only finitely many isomorphism classes
of finite-dimensional indecomposable representations exactly when its underlying graph is a
Dynkin diagram of type `A`, `D` or `E`, equivalently exactly when its Tits form is positive
definite. This file proves both forms of the dichotomy for every finite connected quiver:

* `TauCeti.isFiniteRepType_iff_titsForm_posDef`: finite representation type is equivalent to
  positive definiteness of the Tits form;
* `TauCeti.isFiniteRepType_iff_card_hom_add_card_hom_le_one_and_exists_dynkinType_iso`: finite
  representation type is equivalent to the quiver having no loop, at most one arrow between any
  two vertices, counting both directions, and an underlying graph isomorphic to the diagram of a
  valid Dynkin type of type `A`, `D` or `E`.

The two halves of the first form are `TauCeti.isFiniteRepType_of_titsForm_posDef`, where finiteness
comes from the dimension vectors of indecomposables being positive roots, and
`TauCeti.IsFiniteRepType.posDef_titsForm_of_connected`, where the extended Dynkin quivers inside a
quiver that is not of Dynkin type supply infinitely many indecomposables. The second form is the
first combined with the purely combinatorial
`TauCeti.titsForm_posDef_iff_card_hom_add_card_hom_le_one_and_exists_dynkinType_iso`: the Tits form
of a quiver with at most one arrow between any two vertices is half the form of the matrix
`2I - A` of its underlying graph, and that matrix is positive definite for a connected graph
exactly when the graph is a simply-laced Dynkin diagram
(`SimpleGraph.posDef_graphCartanMatrix_iff`).

## Main results

* `TauCeti.titsForm_posDef_iff_card_hom_add_card_hom_le_one_and_exists_dynkinType_iso`: the Tits
  form of a finite connected quiver is positive definite exactly when the quiver is a simply-laced
  Dynkin diagram, oriented.
* `TauCeti.isFiniteRepType_iff_titsForm_posDef`: the Tits form version of **Gabriel's theorem**
  for finite connected quivers.
* `TauCeti.isFiniteRepType_iff_card_hom_add_card_hom_le_one_and_exists_dynkinType_iso`:
  the Dynkin diagram version of **Gabriel's theorem** for finite connected quivers.

## Implementation notes

Finite representation type is stated for representations with vertex spaces in the universe of the
base field, the universe in which the infinite families of indecomposables over the extended
Dynkin quivers are built. The finiteness proved from a positive definite Tits form holds for vertex
spaces in a larger universe and descends (`TauCeti.IsFiniteRepType.of_ulift`).

The obstructions include loops, parallel arrows, opposite arrows and cycles of length at least
three. Opposite arrows require a separate representation-theoretic argument because the
underlying simple graph records an oriented two-cycle as a single edge.

## References

* P. Gabriel, *Unzerlegbare Darstellungen I*, Manuscripta Math. **6** (1972), 71--103.
* I. N. Bernstein, I. M. Gelfand, V. A. Ponomarev, *Coxeter functors and Gabriel's theorem*,
  Russian Math. Surveys **28** (1973), 17--32.
* I. Assem, D. Simson, A. Skowroński, *Elements of the Representation Theory of Associative
  Algebras*, Volume I, Chapter VII.
-/

public section

namespace TauCeti

open _root_.TauCeti.Quiver

universe u v w

variable {Q : Type v} [_root_.Quiver.{w} Q] [Fintype Q] [∀ a b : Q, Fintype (a ⟶ b)]

/-- **The Tits form of a connected quiver is positive definite exactly when the quiver is an
oriented simply-laced Dynkin diagram**: when it has no loop, at most one arrow between any two
vertices, counting both directions, and an underlying graph isomorphic to the diagram of a valid
Dynkin type of type `A`, `D` or `E`. -/
theorem titsForm_posDef_iff_card_hom_add_card_hom_le_one_and_exists_dynkinType_iso
    (hconn : (underlyingGraph Q).Connected) :
    (titsForm Q).PosDef ↔
      (∀ a b : Q, Fintype.card (a ⟶ b) + Fintype.card (b ⟶ a) ≤ 1) ∧
        ∃ t : DynkinType, t.Valid ∧ t.IsSimplyLaced ∧
          Nonempty (underlyingGraph Q ≃g diagramGraph t.cartanMatrix) := by
  classical
  refine ⟨fun hpd ↦ ?_, fun ⟨h, t, _, ht, ⟨φ⟩⟩ ↦ ?_⟩
  · have h := card_hom_add_card_hom_le_one_of_titsForm_posDef Q hpd
    exact ⟨h, (SimpleGraph.posDef_graphCartanMatrix_iff hconn).mp
      ((titsForm_posDef_iff_posDef_graphCartanMatrix Q h).mp hpd)⟩
  · exact (titsForm_posDef_iff_posDef_graphCartanMatrix Q h).mpr
      (SimpleGraph.posDef_graphCartanMatrix_of_iso
        ((DynkinType.isSimplyLaced_cartanMatrix_iff t).mpr (.inl ht)) φ)

variable {k : Type u} [Field k]

/-- **Gabriel's theorem, Tits form version.** A finite connected quiver has finite
representation type exactly when its Tits form is positive definite. -/
theorem isFiniteRepType_iff_titsForm_posDef
    (hconn : (underlyingGraph Q).Connected) :
    IsFiniteRepType.{u, v, w, u} k Q ↔ (titsForm Q).PosDef :=
  ⟨fun h ↦ h.posDef_titsForm_of_connected hconn,
    fun hpd ↦ IsFiniteRepType.of_ulift.{u, v, w, u, max v w}
      (isFiniteRepType_of_titsForm_posDef.{u, v, w, u} hpd)⟩

omit [Fintype Q] in
/-- **Gabriel's theorem.** A finite connected quiver has finite
representation type exactly when it is an oriented simply-laced Dynkin diagram: when it has no
loop, at most one arrow between any two vertices, counting both directions, and an underlying
graph isomorphic to the diagram of a valid Dynkin type of type `A`, `D` or `E`. -/
theorem isFiniteRepType_iff_card_hom_add_card_hom_le_one_and_exists_dynkinType_iso [Finite Q]
    (hconn : (underlyingGraph Q).Connected) :
    IsFiniteRepType.{u, v, w, u} k Q ↔
      (∀ a b : Q, Fintype.card (a ⟶ b) + Fintype.card (b ⟶ a) ≤ 1) ∧
        ∃ t : DynkinType, t.Valid ∧ t.IsSimplyLaced ∧
          Nonempty (underlyingGraph Q ≃g diagramGraph t.cartanMatrix) := by
  have := Fintype.ofFinite Q
  exact (isFiniteRepType_iff_titsForm_posDef hconn).trans
    (titsForm_posDef_iff_card_hom_add_card_hom_le_one_and_exists_dynkinType_iso hconn)

end TauCeti

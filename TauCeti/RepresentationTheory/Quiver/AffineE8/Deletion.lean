/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Diagram
public import TauCeti.RepresentationTheory.Quiver.AffineE8.Basic

/-!
# Deleting the affine vertex of the `E₈` quiver

The inward quiver of affine type `E₈` is the tree with arms of lengths one, two and five. Removing
the outer vertex of the five-edge arm leaves the finite `E₈` diagram. This file gives the explicit
Bourbaki relabelling as a graph isomorphism, so the finite subdiagram can be used directly with
the finite-type root-system APIs.

The labels follow Bourbaki, *Lie Groups and Lie Algebras, Chapters 4-6*, Plate VII.
-/

public section

namespace TauCeti.Quiver.AffineE8

/-- The finite vertices of the inward affine `E₈` quiver, obtained by deleting the endpoint of its
long arm. -/
abbrev DeletedVertex := {v : AffineE8 // v ≠ .long1}

/-- The Bourbaki-labelled finite `E₈` vertex represented in the affine quiver after deleting its
affine vertex. -/
def bourbakiVertex : Fin 8 → DeletedVertex
  | 0 => ⟨.medium2, by decide⟩
  | 1 => ⟨.short, by decide⟩
  | 2 => ⟨.medium4, by decide⟩
  | 3 => ⟨.center, by decide⟩
  | 4 => ⟨.long5, by decide⟩
  | 5 => ⟨.long4, by decide⟩
  | 6 => ⟨.long3, by decide⟩
  | 7 => ⟨.long2, by decide⟩

/-- The values of the Bourbaki relabelling, in finite node order. -/
@[simp] theorem bourbakiVertex_apply (i : Fin 8) :
    bourbakiVertex i =
      (![⟨.medium2, by decide⟩, ⟨.short, by decide⟩, ⟨.medium4, by decide⟩,
        ⟨.center, by decide⟩, ⟨.long5, by decide⟩, ⟨.long4, by decide⟩,
        ⟨.long3, by decide⟩, ⟨.long2, by decide⟩] : Fin 8 → DeletedVertex) i := by
  fin_cases i <;> rfl

/-- The graph of the finite vertices left after deleting `long1` from the affine `E₈` quiver. -/
def deletedGraph : SimpleGraph DeletedVertex :=
  (Quiver.underlyingGraph AffineE8).induce (fun v : AffineE8 => v ≠ AffineE8.long1)

/-- Adjacency in the deleted graph is inherited from the affine `E₈` quiver. -/
@[simp] theorem deletedGraph_adj (u v : DeletedVertex) :
    deletedGraph.Adj u v ↔ (Quiver.underlyingGraph AffineE8).Adj u.1 v.1 :=
  SimpleGraph.induce_adj

/-- The eight arrows are exactly the edges of the three arms. -/
private theorem nonempty_hom_iff (a b : AffineE8) : Nonempty (a ⟶ b) ↔
    (a = .short ∧ b = .center) ∨
    (a = .medium2 ∧ b = .medium4) ∨
    (a = .medium4 ∧ b = .center) ∨
    (a = .long1 ∧ b = .long2) ∨
    (a = .long2 ∧ b = .long3) ∨
    (a = .long3 ∧ b = .long4) ∨
    (a = .long4 ∧ b = .long5) ∨
    (a = .long5 ∧ b = .center) := by
  constructor
  · rintro ⟨e⟩
    cases e <;> simp
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact ⟨.short⟩
    · exact ⟨.medium2⟩
    · exact ⟨.medium4⟩
    · exact ⟨.long1⟩
    · exact ⟨.long2⟩
    · exact ⟨.long3⟩
    · exact ⟨.long4⟩
    · exact ⟨.long5⟩

/-- **Deleting the affine vertex from the affine `E₈` quiver gives the finite Bourbaki `E₈`
diagram.** The isomorphism sends finite nodes `0,1,2,3,4,5,6,7` to
`medium2, short, medium4, center, long5, long4, long3, long2`, respectively. -/
def deletedGraphIso :
    diagramGraph (CartanMatrix.E 8) ≃g deletedGraph where
  toEquiv :=
    { toFun := bourbakiVertex
      invFun := fun v =>
        match v with
        | ⟨.medium2, _⟩ => 0
        | ⟨.short, _⟩ => 1
        | ⟨.medium4, _⟩ => 2
        | ⟨.center, _⟩ => 3
        | ⟨.long5, _⟩ => 4
        | ⟨.long4, _⟩ => 5
        | ⟨.long3, _⟩ => 6
        | ⟨.long2, _⟩ => 7
        | ⟨.long1, h⟩ => (h rfl).elim
      left_inv := by intro i; fin_cases i <;> rfl
      right_inv := by intro v; cases v with | mk v hv => cases v <;> simp [bourbakiVertex] at hv ⊢ }
  map_rel_iff' := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [deletedGraph, bourbakiVertex, Quiver.underlyingGraph_adj, diagramGraph_adj,
        CartanMatrix.E, nonempty_hom_iff]

/-- The graph isomorphism acts on vertices by the explicit Bourbaki relabelling. -/
@[simp] theorem deletedGraphIso_apply (i : Fin 8) :
    deletedGraphIso i = bourbakiVertex i := (rfl)

end TauCeti.Quiver.AffineE8

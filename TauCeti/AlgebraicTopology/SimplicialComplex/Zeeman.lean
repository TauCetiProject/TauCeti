/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Contractible
public import TauCeti.AlgebraicTopology.SimplicialComplex.Collapse.Triangulation
public import TauCeti.AlgebraicTopology.SimplicialComplex.Collapse.Cylinder.Basic
public import TauCeti.AlgebraicTopology.SimplicialComplex.Dimension
public import TauCeti.AlgebraicTopology.SimplicialComplex.Product
public import TauCeti.AlgebraicTopology.SimplicialComplex.Simplex.Realization

/-!
# Contractible two-dimensional simplicial complexes

This file supplies the predicate used in the statement of Zeeman's collapsibility conjecture.
An abstract simplicial complex is a **contractible 2-complex** when it has finitely many faces,
dimension at most two, and contractible geometric realization.  The finiteness condition records
the finite complexes considered by simplicial collapse, while the dimension bound is expressed
using the intrinsic dimension from `Dimension` rather than a bound on the ambient vertex type.

The standard one-simplex is provided as a nontrivial witness.  Its realization is contractible by
the homeomorphism with Mathlib's convex standard simplex, so the predicate is exercised without
assuming the desired Zeeman conclusion.

The universe-polymorphic proposition `TauCeti.ZeemanConjecture` asserts that the PL polyhedron
of the cylinder admits a collapsible triangulation for every finite contractible complex of
dimension at most two. The ordered staircase cylinder fixes the PL product, not the triangulation
in which the collapse must occur. Requiring this particular staircase triangulation to collapse
would impose an additional condition not present in the polyhedral conjecture.

The conjecture remains open. The standard one-simplex supplies a nontrivial check: its ordered
cylinder is already simplicially collapsible, so no change of triangulation is needed there.
The polyhedral formulation follows Rourke–Sanderson, *Introduction to Piecewise-Linear Topology*,
Chapter 3, p. 39, and Zeeman, *On the dunce hat*, Topology 2 (1964), 341–358.

## Main definitions

* `AbstractSimplicialComplex.Contractible2Complex`: finite, at-most-two-dimensional complexes
  with contractible realization.

## Main results

* `AbstractSimplicialComplex.contractible2Complex_iff`: the defining characterization.
* `AbstractSimplicialComplex.contractible2Complex_standardOneSimplex`: the standard one-simplex
  is a non-void contractible 2-complex (the dimension bound is at most two).
* `TauCeti.ZeemanConjecture`: the universal statement of the conjecture.
* `TauCeti.zeemanConjecture_iff`: the defining characterization.

The proposition is stated, not proved.
-/

public section

noncomputable section

open Set

namespace AbstractSimplicialComplex

variable {ι : Type*}

/-- A finite abstract simplicial complex of dimension at most two whose realization is
contractible.  This is the class of complexes occurring in Zeeman's conjecture, as stated in
R. Kirby (ed.), *Problems in Low-Dimensional Topology*, Problem 5.2 (1997), following E. C.
Zeeman, *On the dunce hat*, Topology 2 (1964), 341--358. -/
def Contractible2Complex (K : AbstractSimplicialComplex ι) : Prop :=
  K.faces.Finite ∧ dimension K ≤ (2 : WithBot ℕ∞) ∧ ContractibleSpace (Realization K)

/-- The defining finiteness, dimension, and contractibility conditions for a contractible
2-complex. -/
theorem contractible2Complex_iff {K : AbstractSimplicialComplex ι} :
    Contractible2Complex K ↔
      K.faces.Finite ∧ dimension K ≤ (2 : WithBot ℕ∞) ∧ ContractibleSpace (Realization K) :=
  Iff.rfl

namespace Contractible2Complex

variable {K : AbstractSimplicialComplex ι}

/-- A contractible 2-complex has finitely many faces. -/
theorem finite_faces (hK : Contractible2Complex K) : K.faces.Finite :=
  hK.1

/-- A contractible 2-complex has dimension at most two. -/
theorem dimension_le_two (hK : Contractible2Complex K) : dimension K ≤ (2 : WithBot ℕ∞) :=
  hK.2.1

/-- The realization of a contractible 2-complex is contractible. -/
theorem contractibleSpace (hK : Contractible2Complex K) : ContractibleSpace (Realization K) :=
  hK.2.2

end Contractible2Complex

/-- The standard one-simplex gives a concrete non-void witness for the `≤ 2` dimension bound. -/
theorem contractible2Complex_standardOneSimplex :
    Contractible2Complex (⊤ : AbstractSimplicialComplex (Fin 2)) := by
  let e := realizationOneSimplexHomeomorphUnitInterval
  let hunit : ContractibleSpace unitInterval :=
    (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0, by simp⟩
  have hreal : ContractibleSpace (Realization (⊤ : AbstractSimplicialComplex (Fin 2))) :=
    @Homeomorph.contractibleSpace _ _ _ _ hunit e
  refine ⟨?_, ?_, hreal⟩
  · have hfaces :
        (⊤ : AbstractSimplicialComplex (Fin 2)).faces =
          (⊤ : PreAbstractSimplicialComplex (Fin 2)).faces := by
      exact congrArg PreAbstractSimplicialComplex.faces
        AbstractSimplicialComplex.top_toPreAbstractSimplicialComplex
    rw [hfaces]
    simpa only [PreAbstractSimplicialComplex.simplex_univ] using
      (PreAbstractSimplicialComplex.finite_faces_simplex (Finset.univ : Finset (Fin 2)))
  · calc
      dimension (⊤ : AbstractSimplicialComplex (Fin 2)) ≤
          ((Finset.univ.card - 1 : ℕ) : WithBot ℕ∞) :=
        dimension_le_card_sub_one (V := Finset.univ) (fun _ _ => Finset.subset_univ _)
      _ = (1 : WithBot ℕ∞) := by norm_num
      _ ≤ 2 := by norm_num

end AbstractSimplicialComplex

namespace TauCeti

/-- **Zeeman's conjecture**: the PL cylinder on every finite contractible complex of dimension
at most two admits a collapsible triangulation.

The staircase complex `AbstractSimplicialComplex.orderedCylinder` represents the PL product.
The collapsible triangulation may be a different complex, PL homeomorphic to that product;
it is not required to be the staircase complex itself. -/
def ZeemanConjecture.{u} : Prop :=
  ∀ (ι : Type u) [LinearOrder ι] (K : AbstractSimplicialComplex ι),
    K.Contractible2Complex →
      PreAbstractSimplicialComplex.HasCollapsibleTriangulation.{u}
        K.orderedCylinder.toPreAbstractSimplicialComplex

namespace ZeemanConjecture

/-- A proof of Zeeman's conjecture supplies a collapsible PL triangulation of the cylinder
on any contractible two-complex. -/
theorem hasCollapsibleTriangulation_orderedCylinder {ι : Type u} [LinearOrder ι]
    (h : ZeemanConjecture.{u}) (K : AbstractSimplicialComplex ι) (hK : K.Contractible2Complex) :
    PreAbstractSimplicialComplex.HasCollapsibleTriangulation.{u}
      K.orderedCylinder.toPreAbstractSimplicialComplex :=
  h ι K hK

end ZeemanConjecture

/-- The defining characterization of Zeeman's conjecture. -/
theorem zeemanConjecture_iff :
    ZeemanConjecture.{u} ↔
      ∀ (ι : Type u) [LinearOrder ι] (K : AbstractSimplicialComplex ι),
        K.Contractible2Complex →
          PreAbstractSimplicialComplex.HasCollapsibleTriangulation.{u}
            K.orderedCylinder.toPreAbstractSimplicialComplex := Iff.rfl

/-- The cylinder on the standard one-simplex satisfies the conclusion of Zeeman's conjecture
without changing its staircase triangulation. Its polyhedron is a square. -/
theorem hasCollapsibleTriangulation_orderedCylinder_standardOneSimplex :
    PreAbstractSimplicialComplex.HasCollapsibleTriangulation.{0}
      (⊤ : AbstractSimplicialComplex (Fin 2)).orderedCylinder.toPreAbstractSimplicialComplex :=
  AbstractSimplicialComplex.collapsible_orderedCylinder_top.hasCollapsibleTriangulation

end TauCeti

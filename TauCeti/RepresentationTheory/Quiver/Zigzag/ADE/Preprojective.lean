/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Zigzag.ADE.Basic
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Preprojective

/-!
# Source--sink orientations of the named ADE examples

The Bourbaki-labelled `D₄` and `E₈` diagrams, and the arm-labelled affine `E₈` diagram,
admit explicit two-colourings. They choose source--sink orientations of the three quivers,
with arrows directed from the false class to the true class. The resulting algebra
equivalences identify the signless quadratic-dual presentation with the signed additive
preprojective presentation. The representative formula fixes the arrow identification,
including the path-product convention.

The affine colouring gives the orientation used when comparing its infinite-dimensional
preprojective algebra with the quadratic dual of its zigzag algebra.

## References

The source--sink comparison follows Huerfano--Khovanov, *A category for the adjoint
representation*, Section 3. The three graph labellings are those of the existing ADE graph API.
-/

public section

namespace TauCeti

open DoubledQuiver PathAlgebra

/-! ### Explicit colour classes -/

/-- The two-colouring of `D₄` with its trivalent Bourbaki vertex `1` coloured true. -/
def zigzagD4Coloring : zigzagD4Graph.Coloring Bool :=
  SimpleGraph.Coloring.mk (fun i : Fin 4 => decide (i = 1)) (by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [zigzagD4Graph_adj])

/-- The two-colouring of Bourbaki `E₈` with true vertices `1, 2, 4, 6`. -/
def zigzagE8Coloring : zigzagE8Graph.Coloring Bool :=
  SimpleGraph.Coloring.mk (fun i : Fin 8 => decide ((i : ℕ) ∈ [1, 2, 4, 6])) (by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [zigzagE8Graph_adj])

/-- The two-colouring of arm-labelled affine `E₈`, with true vertices `1, 2, 4, 6, 8`. -/
def zigzagAffineE8Coloring : zigzagAffineE8Graph.Coloring Bool :=
  SimpleGraph.Coloring.mk (fun i : Fin 9 => decide ((i : ℕ) ∈ [1, 2, 4, 6, 8])) (by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [zigzagAffineE8Graph_adj])

/-- The selected colour of a `D₄` vertex. -/
@[simp] theorem zigzagD4Coloring_apply (i : Fin 4) :
    zigzagD4Coloring i = decide (i = 1) := by
  simp [zigzagD4Coloring, SimpleGraph.Coloring.mk]

/-- The selected colour of an `E₈` vertex. -/
@[simp] theorem zigzagE8Coloring_apply (i : Fin 8) :
    zigzagE8Coloring i = decide ((i : ℕ) ∈ [1, 2, 4, 6]) := by
  simp [zigzagE8Coloring, SimpleGraph.Coloring.mk]

/-- The selected colour of an affine `E₈` vertex. -/
@[simp] theorem zigzagAffineE8Coloring_apply (i : Fin 9) :
    zigzagAffineE8Coloring i = decide ((i : ℕ) ∈ [1, 2, 4, 6, 8]) := by
  simp [zigzagAffineE8Coloring, SimpleGraph.Coloring.mk]

/-- The neighbors of a vertex in a finite graph form a finite type. -/
noncomputable local instance zigzagNeighborSetFintype {V : Type*} [Finite V]
    (G : SimpleGraph V) (i : V) :
    Fintype (G.neighborSet i) := Fintype.ofFinite _

/-! ### The three signed preprojective presentations -/

/-- The signless quadratic-dual presentation of `D₄` is the preprojective algebra of
the explicitly chosen source--sink orientation. -/
noncomputable def zigzagD4SignlessEquivPreprojective (k : Type*) [CommRing k] :
    signlessPreprojectiveAlgebra k (DoubledQuiver zigzagD4Graph) ≃ₐ[k]
      preprojectiveAlgebra k (OrientedQuiver zigzagD4Graph zigzagD4Coloring.sourceSink) :=
  zigzagD4Coloring.sourceSinkSignlessPreprojectiveAlgebraEquiv k

/-- The `D₄` comparison maps every doubled path through the chosen orientation. -/
@[simp] theorem zigzagD4SignlessEquivPreprojective_mk (k : Type*) [CommRing k]
    (x : pathAlgebra k (DoubledQuiver zigzagD4Graph)) :
    zigzagD4SignlessEquivPreprojective k (signlessPreprojectiveMk k _ x) =
      preprojectiveMk k _ (orientationPathAlgebraEquiv zigzagD4Coloring.sourceSink k x) :=
  zigzagD4Coloring.sourceSinkSignlessPreprojectiveAlgebraEquiv_signlessPreprojectiveMk k x

/-- The signless quadratic-dual presentation of `E₈` is the preprojective algebra of
the explicitly chosen source--sink orientation. -/
noncomputable def zigzagE8SignlessEquivPreprojective (k : Type*) [CommRing k] :
    signlessPreprojectiveAlgebra k (DoubledQuiver zigzagE8Graph) ≃ₐ[k]
      preprojectiveAlgebra k (OrientedQuiver zigzagE8Graph zigzagE8Coloring.sourceSink) :=
  zigzagE8Coloring.sourceSinkSignlessPreprojectiveAlgebraEquiv k

/-- The `E₈` comparison maps every doubled path through the chosen orientation. -/
@[simp] theorem zigzagE8SignlessEquivPreprojective_mk (k : Type*) [CommRing k]
    (x : pathAlgebra k (DoubledQuiver zigzagE8Graph)) :
    zigzagE8SignlessEquivPreprojective k (signlessPreprojectiveMk k _ x) =
      preprojectiveMk k _ (orientationPathAlgebraEquiv zigzagE8Coloring.sourceSink k x) :=
  zigzagE8Coloring.sourceSinkSignlessPreprojectiveAlgebraEquiv_signlessPreprojectiveMk k x

/-- The signless quadratic-dual presentation of affine `E₈` is the preprojective algebra
of the explicitly chosen source--sink orientation. -/
noncomputable def zigzagAffineE8SignlessEquivPreprojective (k : Type*) [CommRing k] :
    signlessPreprojectiveAlgebra k (DoubledQuiver zigzagAffineE8Graph) ≃ₐ[k]
      preprojectiveAlgebra k
        (OrientedQuiver zigzagAffineE8Graph zigzagAffineE8Coloring.sourceSink) :=
  zigzagAffineE8Coloring.sourceSinkSignlessPreprojectiveAlgebraEquiv k

/-- The affine `E₈` comparison maps every doubled path through the chosen orientation. -/
@[simp] theorem zigzagAffineE8SignlessEquivPreprojective_mk (k : Type*) [CommRing k]
    (x : pathAlgebra k (DoubledQuiver zigzagAffineE8Graph)) :
    zigzagAffineE8SignlessEquivPreprojective k (signlessPreprojectiveMk k _ x) =
      preprojectiveMk k _
        (orientationPathAlgebraEquiv zigzagAffineE8Coloring.sourceSink k x) :=
  zigzagAffineE8Coloring.sourceSinkSignlessPreprojectiveAlgebraEquiv_signlessPreprojectiveMk k x

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Homology.Bigraded.Basic
public import TauCeti.KnotTheory.Grid.Homology.KnotAlexander

/-!
# Isomorphism of the bigraded `K[U]`-modules `GH⁻` of knot grids

The unblocked grid homology `GH⁻` of a knot grid carries two gradings, the `O`-Maslov grading and
the Alexander grading (`OddComponentGridDiagram.bigradedUnblockedHomologyGrading`), and the action
of `U` lowers them by `(2, 1)`. Two knot grids, possibly of different sizes, have isomorphic `GH⁻`
as bigraded `K[U]`-modules when some `K[U]`-linear equivalence between their homologies maps each
bigraded piece into the piece of the same bidegree
(`GridDiagram.IsKnot.BigradedUnblockedHomologyIsomorphic`). This relation is reflexive,
symmetric and transitive; its inverse direction uses that both bigradings are internal direct sum
decompositions.

The comparison maps of grid moves are semilinear maps over the polynomial rings in the grid
variables; a bijective one that preserves the bigrading witnesses the relation
(`GridDiagram.IsKnot.BigradedUnblockedHomologyIsomorphic.of_semilinearMap`). Forgetting the
Maslov grading gives the Alexander-graded relation
(`GridDiagram.IsKnot.BigradedUnblockedHomologyIsomorphic.unblockedHomologyIsomorphic`), because the
Alexander grading of `GH⁻` is the coarsening of the bigrading
(`OddComponentGridDiagram.coarsen_bigradedUnblockedHomologyGrading_snd`). The invariance of the
relation under grid moves is in `Homology/Bigraded/Invariance.lean`.

## Main definitions

* `TauCeti.GridDiagram.IsKnot.BigradedUnblockedHomologyIsomorphic`: `GH⁻` of two knot grids are
  isomorphic as `(O-Maslov, Alexander)`-bigraded `K[U]`-modules.

## Main results

* `TauCeti.GridDiagram.IsKnot.BigradedUnblockedHomologyIsomorphic.of_semilinearMap`: a bijective
  bigrading-preserving map, semilinear along a ring homomorphism commuting with the evaluation of
  every variable at `U`, witnesses the relation.
* `TauCeti.GridDiagram.IsKnot.BigradedUnblockedHomologyIsomorphic.unblockedHomologyIsomorphic`:
  the relation implies isomorphism as Alexander-graded `K[U]`-modules.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Section 5.3 (the bigraded
`GH⁻` of a knot and its invariance).
-/

public section

open MvPolynomial

namespace TauCeti.GridDiagram.IsKnot

variable {n m l : ℕ} {G : GridDiagram n} {G' : GridDiagram m} {G'' : GridDiagram l}
  (hG : G.IsKnot) (hG' : G'.IsKnot) (hG'' : G''.IsKnot) (R : Type*) [CommRing R] [CharP R 2]

/-- The unblocked grid homologies of two knot grids are **isomorphic as bigraded
`R[U]`-modules**: some `R[U]`-linear equivalence `GH⁻(G) ≃ GH⁻(G')` maps each
`(O-Maslov, Alexander)` piece into the piece of the same bidegree. The two grids may have
different sizes. -/
def BigradedUnblockedHomologyIsomorphic : Prop :=
  letI := hG.unblockedHomologyModule R
  letI := hG'.unblockedHomologyModule R
  ∃ e : G.unblockedHomology R ≃ₗ[Polynomial R] G'.unblockedHomology R,
    LinearMap.IsHomogeneous e.toLinearMap
      (hG.toOddComponentGridDiagram.bigradedUnblockedHomologyGrading R).piece
      (hG'.toOddComponentGridDiagram.bigradedUnblockedHomologyGrading R).piece 0

/-- Every knot grid has `GH⁻` isomorphic to itself as a bigraded `R[U]`-module. -/
theorem BigradedUnblockedHomologyIsomorphic.refl : hG.BigradedUnblockedHomologyIsomorphic hG R := by
  let _ := hG.unblockedHomologyModule R
  exact ⟨LinearEquiv.refl _ _, LinearMap.isHomogeneous_id _⟩

variable {hG hG' hG'' R}

/-- Unfold `BigradedUnblockedHomologyIsomorphic` to the existence of a bigraded equivalence. -/
theorem bigradedUnblockedHomologyIsomorphic_def :
    hG.BigradedUnblockedHomologyIsomorphic hG' R ↔
      letI := hG.unblockedHomologyModule R
      letI := hG'.unblockedHomologyModule R
      ∃ e : G.unblockedHomology R ≃ₗ[Polynomial R] G'.unblockedHomology R,
        LinearMap.IsHomogeneous e.toLinearMap
          (hG.toOddComponentGridDiagram.bigradedUnblockedHomologyGrading R).piece
          (hG'.toOddComponentGridDiagram.bigradedUnblockedHomologyGrading R).piece 0 :=
  Iff.rfl

/-- Equal knot grids have isomorphic bigraded `GH⁻`. This transports the relation along a
propositional equation of diagrams, such as one between two descriptions of a moved diagram. -/
theorem bigradedUnblockedHomologyIsomorphic_of_eq {G₁ : GridDiagram n} {hG₁ : G₁.IsKnot}
    (h : G = G₁) : hG.BigradedUnblockedHomologyIsomorphic hG₁ R := by
  subst h
  exact .refl hG R

/-- Isomorphism of bigraded homologies is symmetric: since both bigradings are internal direct sum
decompositions, the inverse of a bigraded equivalence is bigraded. -/
theorem BigradedUnblockedHomologyIsomorphic.symm
    (h : hG.BigradedUnblockedHomologyIsomorphic hG' R) :
    hG'.BigradedUnblockedHomologyIsomorphic hG R := by
  let _ := hG.unblockedHomologyModule R
  let _ := hG'.unblockedHomologyModule R
  obtain ⟨e, he⟩ := h
  exact ⟨e.symm, he.linearEquiv_symm⟩

/-- Isomorphism of bigraded homologies is transitive: bigraded equivalences compose. -/
theorem BigradedUnblockedHomologyIsomorphic.trans
    (h : hG.BigradedUnblockedHomologyIsomorphic hG' R)
    (h' : hG'.BigradedUnblockedHomologyIsomorphic hG'' R) :
    hG.BigradedUnblockedHomologyIsomorphic hG'' R := by
  let _ := hG.unblockedHomologyModule R
  let _ := hG'.unblockedHomologyModule R
  let _ := hG''.unblockedHomologyModule R
  obtain ⟨e, he⟩ := h
  obtain ⟨e', he'⟩ := h'
  exact ⟨e.trans e', by simpa only [LinearEquiv.coe_trans, add_zero] using he'.comp he⟩

/-- Isomorphism of bigraded homologies holds in one direction exactly when it holds in the
other. -/
theorem bigradedUnblockedHomologyIsomorphic_comm :
    hG.BigradedUnblockedHomologyIsomorphic hG' R ↔ hG'.BigradedUnblockedHomologyIsomorphic hG R :=
  ⟨.symm, .symm⟩

/-- A bijection between the unblocked homologies of two knot grids makes them isomorphic as
bigraded `R[U]`-modules if it preserves the `(O-Maslov, Alexander)` bigrading and is semilinear
along a ring homomorphism `σ` of the polynomial rings that commutes with the evaluation
`V_j ↦ U`, such as a renaming of the variables. -/
theorem BigradedUnblockedHomologyIsomorphic.of_semilinearMap
    {σ : MvPolynomial (Fin n) R →+* MvPolynomial (Fin m) R}
    (hσ : ∀ p, aeval (fun _ ↦ (Polynomial.X : Polynomial R)) (σ p) =
      aeval (fun _ ↦ (Polynomial.X : Polynomial R)) p)
    (f : G.unblockedHomology R →ₛₗ[σ] G'.unblockedHomology R) (hf : Function.Bijective f)
    (hg : ∀ g y, y ∈ hG.toOddComponentGridDiagram.bigradedUnblockedHomologyPiece R g →
      f y ∈ hG'.toOddComponentGridDiagram.bigradedUnblockedHomologyPiece R g) :
    hG.BigradedUnblockedHomologyIsomorphic hG' R := by
  let _ := hG.unblockedHomologyModule R
  let _ := hG'.unblockedHomologyModule R
  refine ⟨LinearEquiv.ofBijective (hG.unblockedHomologyLinearMapOfSemilinear R hG' hσ f)
    (by rwa [coe_unblockedHomologyLinearMapOfSemilinear]),
    LinearMap.isHomogeneous_def.mpr fun g y hy ↦ ?_⟩
  rw [OddComponentGridDiagram.bigradedUnblockedHomologyGrading_piece] at hy
  rw [add_zero, OddComponentGridDiagram.bigradedUnblockedHomologyGrading_piece,
    LinearEquiv.coe_coe, LinearEquiv.ofBijective_apply, coe_unblockedHomologyLinearMapOfSemilinear]
  exact hg g y hy

/-- Knot grids whose `GH⁻` are isomorphic as bigraded `R[U]`-modules have isomorphic `GH⁻` as
Alexander-graded `R[U]`-modules, since the Alexander grading is the coarsening of the bigrading
along the Alexander degree. -/
theorem BigradedUnblockedHomologyIsomorphic.unblockedHomologyIsomorphic
    (h : hG.BigradedUnblockedHomologyIsomorphic hG' R) : hG.UnblockedHomologyIsomorphic hG' R := by
  let _ := hG.unblockedHomologyModule R
  let _ := hG'.unblockedHomologyModule R
  have := hG.isScalarTower_unblockedHomology (R := R)
  have := hG'.isScalarTower_unblockedHomology (R := R)
  obtain ⟨e, he⟩ := h
  have he' : LinearMap.IsHomogeneous (e.toLinearMap.restrictScalars R)
      (hG.toOddComponentGridDiagram.bigradedUnblockedHomologyGrading R).piece
      (hG'.toOddComponentGridDiagram.bigradedUnblockedHomologyGrading R).piece 0 :=
    LinearMap.isHomogeneous_def.mpr fun _ _ hy ↦ he.map_mem hy
  have hc := he'.coarsen_zero Prod.snd
  rw [OddComponentGridDiagram.coarsen_bigradedUnblockedHomologyGrading_snd,
    OddComponentGridDiagram.coarsen_bigradedUnblockedHomologyGrading_snd] at hc
  refine unblockedHomologyIsomorphic_def.mpr ⟨e, LinearMap.isHomogeneous_def.mpr fun _ _ hy ↦ ?_⟩
  rw [mem_alexanderUnblockedHomologyGrading_piece_iff,
    ← OddComponentGridDiagram.mem_alexanderUnblockedHomologyGrading_piece_iff] at hy ⊢
  exact hc.map_mem hy

end TauCeti.GridDiagram.IsKnot

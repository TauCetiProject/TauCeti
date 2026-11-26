/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Homology.Bigraded.Coarsen
public import TauCeti.KnotTheory.Grid.Homology.Bigraded.Relation
public import TauCeti.KnotTheory.Grid.Homology.KnotAlexander
public import TauCeti.KnotTheory.Grid.Homology.Tau
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import TauCeti.KnotTheory.Grid.Homology.Bigraded.Finite

/-!
# The Maslov--Alexander bigrading on knot grid homology over `R[U]`

For a knot grid `G`, the `(O-Maslov, Alexander)` bigrading of `GH⁻(G)` equips the `R[U]`-module
`G.unblockedHomology R` with an internal `ℤ × ℤ`-grading over `R`
(`GridDiagram.IsKnot.bigradedUnblockedHomologyGrading`). Under the knot module structure every grid
variable acts as `U`, so multiplication by `U` lowers bidegree by `(2, 1)`
(`GridDiagram.IsKnot.X_smul_mem_bigradedUnblockedHomologyGrading_piece`). Projecting bidegrees onto
their second coordinate recovers `GridDiagram.IsKnot.alexanderUnblockedHomologyGrading`.

On any grid diagram with an odd number of components whose `X`-marking state receives an even
number of counted rectangles from every grid state, each monomial multiple `V^e • λ⁻` witnesses
positive ground-ring `finrank` in bidegree `bidegree X - (2 |e|, |e|)` over a commutative ring of
characteristic two (`OddComponentGridDiagram.finrank_bigradedUnblockedHomologyPiece_pos`), giving a
positive-`finrank` `U`-tower on knot grids
(`GridDiagram.IsKnot.finrank_bigradedUnblockedHomologyGrading_piece_pos`).

Two knot grids, possibly of different sizes, have isomorphic `GH⁻` as Maslov--Alexander bigraded
`R[U]`-modules (`GridDiagram.IsKnot.BigradedUnblockedHomologyIsomorphic`, in
`TauCeti.KnotTheory.Grid.Homology.Bigraded.Relation`) when some `R[U]`-linear equivalence between
their homologies preserves bidegrees. Coarsening along `Prod.snd` shows that every bigraded
`R[U]`-isomorphism preserves `τ` (`BigradedUnblockedHomologyIsomorphic.tau_eq`), and restricting to
each bidegree gives `R`-linear equivalences on all homogeneous pieces
(`BigradedUnblockedHomologyIsomorphic.nonempty_piece_linearEquiv`), hence equal piece `finrank`s
(`BigradedUnblockedHomologyIsomorphic.finrank_piece_eq`).

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Sections 4.3, 4.6 and Chapters 5
and 6.
-/

public section

open MvPolynomial

namespace TauCeti

namespace OddComponentGridDiagram

/-- On a grid diagram with an odd number of link components, the class of the `X`-marking state is
homogeneous of bidegree `(M_O(G.val.X), A(G.val.X))`. -/
theorem XMarkingClass_mem_bigradedUnblockedHomologyPiece {n : ℕ}
    (G : OddComponentGridDiagram n) (R : Type*) [CommRing R] [CharP R 2] :
    G.val.XMarkingClass R ∈ G.bigradedUnblockedHomologyPiece R (G.bidegree G.val.X) := by
  rw [G.val.XMarkingClass_def]
  refine G.unblockedHomologyClass_mem_bigradedUnblockedHomologyPiece R ?_
  rw [G.val.coe_XMarkingCycle]
  exact G.single_one_mem_bigradedChainMinusPiece R G.val.X

/-- On an odd-component grid diagram whose `X`-marking state receives an even number of counted
rectangles from every grid state, every monomial multiple `V^e • λ⁻` witnesses positive `finrank`
in bidegree `bidegree X - (2 |e|, |e|)` over any commutative ring of characteristic two. -/
theorem finrank_bigradedUnblockedHomologyPiece_pos {n : ℕ} (G : OddComponentGridDiagram n)
    (K : Type*) [CommRing K] [CharP K 2]
    (hX : ∀ x : GridState n, Even (G.val.unblockedRectangles x G.val.X).card) (e : Fin n →₀ ℕ) :
    0 < Module.finrank K
      (G.bigradedUnblockedHomologyPiece K
        (G.bidegree G.val.X - (2 * (e.degree : ℤ), (e.degree : ℤ)))) := by
  have : Nontrivial K := CharP.nontrivial_of_char_ne_one (v := 2) (by decide)
  have hmem : (monomial e (1 : K)) • G.val.XMarkingClass K ∈
      G.bigradedUnblockedHomologyPiece K
        (G.bidegree G.val.X - (2 * (e.degree : ℤ), (e.degree : ℤ))) :=
    G.monomial_smul_mem_bigradedUnblockedHomologyPiece K e 1
      (G.XMarkingClass_mem_bigradedUnblockedHomologyPiece K)
  have hinj := G.val.injective_toSpanSingleton_monomial_smul_XMarkingClass K hX e hmem
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  rw [Module.finrank_self] at hle
  exact Nat.lt_of_lt_of_le Nat.zero_lt_one hle

end OddComponentGridDiagram

namespace GridDiagram.IsKnot

variable {n : ℕ} {G : GridDiagram n} (hG : G.IsKnot) (R : Type*)
  [CommRing R] [CharP R 2]

/-- The internal `(O-Maslov, Alexander)` bigrading of the `R[U]`-module `GH⁻` of a knot grid. -/
noncomputable def bigradedUnblockedHomologyGrading :
    InternalGrading R (G.unblockedHomology R) (ℤ × ℤ) :=
  hG.toOddComponentGridDiagram.bigradedUnblockedHomologyGrading R

/-- The degree-`g` piece of a knot grid's bigrading is `bigradedUnblockedHomologyPiece`. -/
@[simp]
theorem bigradedUnblockedHomologyGrading_piece (g : ℤ × ℤ) :
    (hG.bigradedUnblockedHomologyGrading R).piece g =
      hG.toOddComponentGridDiagram.bigradedUnblockedHomologyPiece R g := by
  rw [bigradedUnblockedHomologyGrading,
    OddComponentGridDiagram.bigradedUnblockedHomologyGrading_piece]

/-- Over any commutative ring of characteristic two, each homogeneous piece of a knot
grid's bundled bigrading on `GH⁻` is finitely generated over the ground ring. -/
instance finite_bigradedUnblockedHomologyGrading_piece (g : ℤ × ℤ) :
    Module.Finite R ((hG.bigradedUnblockedHomologyGrading R).piece g) := by
  rw [bigradedUnblockedHomologyGrading_piece]
  exact hG.toOddComponentGridDiagram.finite_bigradedUnblockedHomologyPiece R g

/-- The degree-`g` piece of a knot grid's bigrading agrees with `bigradedUnblockedHomologyPiece`
computed with any odd-component witness on the same underlying diagram. -/
theorem bigradedUnblockedHomologyGrading_piece_eq_mk
    (hodd : Odd G.componentCount) (g : ℤ × ℤ) :
    (hG.bigradedUnblockedHomologyGrading R).piece g =
      OddComponentGridDiagram.bigradedUnblockedHomologyPiece ⟨G, hodd⟩ R g := by
  rw [bigradedUnblockedHomologyGrading_piece]

/-- Coarsening a knot grid's `(O-Maslov, Alexander)` bigrading along `Prod.snd` recovers its
Alexander grading. -/
@[simp]
theorem coarsen_bigradedUnblockedHomologyGrading_snd :
    (hG.bigradedUnblockedHomologyGrading R).coarsen Prod.snd =
      hG.alexanderUnblockedHomologyGrading R := by
  refine InternalGrading.ext fun a ↦ Submodule.ext fun y ↦ ?_
  rw [bigradedUnblockedHomologyGrading,
    hG.toOddComponentGridDiagram.coarsen_bigradedUnblockedHomologyGrading_snd,
    mem_alexanderUnblockedHomologyGrading_piece_iff,
    OddComponentGridDiagram.mem_alexanderUnblockedHomologyGrading_piece_iff]

/-- Multiplication by `U` lowers the `(O-Maslov, Alexander)` bidegree of knot grid homology by
`(2, 1)`. -/
theorem X_smul_mem_bigradedUnblockedHomologyGrading_piece {g : ℤ × ℤ}
    {y : G.unblockedHomology R}
    (hy : y ∈ (hG.bigradedUnblockedHomologyGrading R).piece g) :
    letI := hG.unblockedHomologyModule R
    (Polynomial.X : Polynomial R) • y ∈
      (hG.bigradedUnblockedHomologyGrading R).piece (g - (2, 1)) := by
  let _ := hG.unblockedHomologyModule R
  let i : Fin n := ⟨0, Nat.pos_of_ne_zero hG.ne_zero⟩
  rw [bigradedUnblockedHomologyGrading_piece] at hy ⊢
  rw [hG.X_smul_unblockedHomology i y]
  exact hG.toOddComponentGridDiagram.X_smul_mem_bigradedUnblockedHomologyPiece R i hy

/-- Multiplication by `U ^ k` lowers the `(O-Maslov, Alexander)` bidegree of knot grid homology by
`(2 * k, k)`. -/
theorem X_pow_smul_mem_bigradedUnblockedHomologyGrading_piece (k : ℕ) {g : ℤ × ℤ}
    {y : G.unblockedHomology R}
    (hy : y ∈ (hG.bigradedUnblockedHomologyGrading R).piece g) :
    letI := hG.unblockedHomologyModule R
    (Polynomial.X ^ k : Polynomial R) • y ∈
      (hG.bigradedUnblockedHomologyGrading R).piece (g - (2 * (k : ℤ), (k : ℤ))) := by
  let _ := hG.unblockedHomologyModule R
  induction k with
  | zero => simpa [Prod.mk_zero_zero] using hy
  | succ k ih =>
    rw [pow_succ', mul_smul]
    have h := hG.X_smul_mem_bigradedUnblockedHomologyGrading_piece R ih
    have heq : g - (2 * (k : ℤ), (k : ℤ)) - (2, 1) =
        g - (2 * ((k + 1 : ℕ) : ℤ), ((k + 1 : ℕ) : ℤ)) := by
      apply Prod.ext <;> simp <;> omega
    rwa [heq] at h

/-- On a knot grid, the class of the `X`-marking state is homogeneous of bidegree
`(M_O(G.X), A(G.X))`. -/
theorem XMarkingClass_mem_bigradedUnblockedHomologyGrading_piece :
    G.XMarkingClass R ∈
      (hG.bigradedUnblockedHomologyGrading R).piece
        (hG.toOddComponentGridDiagram.bidegree G.X) := by
  rw [bigradedUnblockedHomologyGrading_piece]
  exact hG.toOddComponentGridDiagram.XMarkingClass_mem_bigradedUnblockedHomologyPiece R

/-- On a knot grid whose `X`-marking state receives an even number of counted rectangles from every
grid state, each `U ^ k • λ⁻` witnesses positive `finrank` in bidegree `bidegree X - (2k, k)` over
any commutative ring of characteristic two. -/
theorem finrank_bigradedUnblockedHomologyGrading_piece_pos
    (hX : ∀ x : GridState n, Even (G.unblockedRectangles x G.X).card) (k : ℕ) :
    0 < Module.finrank R ((hG.bigradedUnblockedHomologyGrading R).piece
      (hG.toOddComponentGridDiagram.bidegree G.X - (2 * (k : ℤ), (k : ℤ)))) := by
  let i : Fin n := ⟨0, Nat.pos_of_ne_zero hG.ne_zero⟩
  rw [bigradedUnblockedHomologyGrading_piece]
  have h := hG.toOddComponentGridDiagram.finrank_bigradedUnblockedHomologyPiece_pos R hX
    (Finsupp.single i k)
  rwa [Finsupp.degree_single] at h

end GridDiagram.IsKnot

/-! ### Consequences of bigraded isomorphism -/

namespace GridDiagram.IsKnot

variable {n m : ℕ} {G : GridDiagram n} {G' : GridDiagram m}
  {hG : G.IsKnot} {hG' : G'.IsKnot} {R : Type*} [CommRing R] [CharP R 2]

/-- Knot grids with isomorphic bigraded `GH⁻` have the same invariant `τ`. -/
theorem BigradedUnblockedHomologyIsomorphic.tau_eq
    (h : hG.BigradedUnblockedHomologyIsomorphic hG' R) :
    hG.tau R = hG'.tau R :=
  h.unblockedHomologyIsomorphic.tau_eq

/-- A bigraded `R[U]`-isomorphism restricts in every bidegree `g` to an `R`-linear equivalence
between the homogeneous pieces. -/
theorem BigradedUnblockedHomologyIsomorphic.nonempty_piece_linearEquiv
    (h : hG.BigradedUnblockedHomologyIsomorphic hG' R) (g : ℤ × ℤ) :
    Nonempty (((hG.bigradedUnblockedHomologyGrading R).piece g) ≃ₗ[R]
      ((hG'.bigradedUnblockedHomologyGrading R).piece g)) := by
  let _ := hG.unblockedHomologyModule R
  let _ := hG'.unblockedHomologyModule R
  have := hG.isScalarTower_unblockedHomology (R := R)
  have := hG'.isScalarTower_unblockedHomology (R := R)
  rw [bigradedUnblockedHomologyIsomorphic_def] at h
  obtain ⟨e, he⟩ := h
  exact ⟨LinearMap.IsHomogeneous.pieceEquiv (e := e.restrictScalars R)
    (he.restrictScalars R) g⟩

/-- Knot grids with isomorphic bigraded `GH⁻` have equal ground-ring `finrank` in every
Maslov--Alexander bidegree. -/
theorem BigradedUnblockedHomologyIsomorphic.finrank_piece_eq
    (h : hG.BigradedUnblockedHomologyIsomorphic hG' R) (g : ℤ × ℤ) :
    Module.finrank R ((hG.bigradedUnblockedHomologyGrading R).piece g) =
      Module.finrank R ((hG'.bigradedUnblockedHomologyGrading R).piece g) :=
  let ⟨e⟩ := h.nonempty_piece_linearEquiv g
  e.finrank_eq

end GridDiagram.IsKnot

end TauCeti

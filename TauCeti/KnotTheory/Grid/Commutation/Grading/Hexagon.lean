/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.Hexagon
public import TauCeti.KnotTheory.Grid.Grading.UnblockedChain
import Mathlib.Tactic.Linarith

/-!
# The commutation homotopy raises the Maslov grading by one

Let `C` be a validated column commutation of a grid diagram `G`, exchanging the column
`a = C.column` with the next column `b = finRotate n a`. The commutation homotopy
`H : GC⁻(G) → GC⁻(G)` (`GridDiagram.commutationHomotopy`) counts empty hexagons carrying no
`X`-marking. It is meant to satisfy `∂⁻ ∘ H + H ∘ ∂⁻ = 1 + Ψ ∘ Φ`, with `∂⁻` of bidegree `(-1, 0)`
and the commutation maps `Φ`, `Ψ` of bidegree `(0, 0)`, so it should have bidegree `(1, 0)`. This
file proves that it does.

A hexagon is the rectangle with the same corners with one column cut away, and that column holds
one `O`-marking and one `X`-marking of the rectangle
(`GridDiagram.OColumns_toGridRectangle_eq_insert_of_hexagon`,
`GridDiagram.XSet_inter_toGridRectangle_coveredSquares_of_mem_hexagons`). So for a counted
hexagon `P` from `x` to `y` the rectangle formulas give

* `M_O(y) = M_O(x) + 1 + 2 #(𝕆 ∩ P)`, since the rectangle is empty and carries `#(𝕆 ∩ P) + 1`
  `O`-markings;
* `A(y) = A(x) + #(𝕆 ∩ P)`, since the rectangle carries one `X`-marking and `#(𝕆 ∩ P) + 1`
  `O`-markings.

Since every variable has bidegree `(-2, -1)`, each term `V^{𝕆 ∩ P} · y` of `H(x)` has bidegree
`(M_O(x) + 1, A(x))`. The same holds for hexagons turning on their initial side.

## Main results

* `TauCeti.GridDiagram.maslovOℤ_eq_of_isEmpty_hexagon`,
  `TauCeti.GridDiagram.maslovOℤ_eq_of_isEmpty_initialHexagon`: the `O`-Maslov grading across an
  empty hexagon.
* `TauCeti.OddComponentGridDiagram.alexanderℤ_eq_of_mem_hexagons`,
  `TauCeti.OddComponentGridDiagram.alexanderℤ_eq_of_mem_initialHexagons`: the Alexander grading
  across a counted hexagon.
* `TauCeti.OddComponentGridDiagram.hexagonMap_mem_bigradedChainMinusPiece`,
  `TauCeti.OddComponentGridDiagram.initialHexagonMap_mem_bigradedChainMinusPiece`,
  `TauCeti.OddComponentGridDiagram.commutationHomotopy_mem_bigradedChainMinusPiece`: the hexagon
  maps and the commutation homotopy have bidegree `(1, 0)`.

## References

* P. Ozsváth, A. Stipsicz, Z. Szabó, *Grid Homology for Knots and Links*, AMS Mathematical
  Surveys and Monographs 208, 2015, Section 5.1.
* C. Manolescu, P. Ozsváth, Z. Szabó, D. Thurston, *On combinatorial link Floer homology*,
  Geom. Topol. 11 (2007), Section 3.1 (arXiv:math/0610559).
-/

public section

namespace TauCeti

open MvPolynomial

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n) (C : ColumnCommutationData G) {x y : GridState n}

/-- **The `O`-Maslov grading across an empty hexagon.** If `P` is an empty hexagon of the column
commutation `C` from `x` to `y`, then `M_O(y) = M_O(x) + 1 + 2 #(𝕆 ∩ P)`. With every variable of
weight `-2`, the term `V^{𝕆 ∩ P} · y` of the hexagon map lies one above `x` in the `O`-Maslov
grading. -/
theorem maslovOℤ_eq_of_isEmpty_hexagon
    {P : GridHexagonBetween C.column C.oppositeTurnRow C.turnRow x y} (hP : P.IsEmpty) :
    G.maslovOℤ y = G.maslovOℤ x + 1 + 2 * ((G.OColumnsOfSquares P.coveredSquares).card : ℤ) := by
  have h := G.maslovOℤ_sub_two_mul_card_OColumns hP
  rw [G.OColumns_toGridRectangle_eq_insert_of_hexagon P,
    Finset.card_insert_of_notMem (by simp [P.mem_coveredSquares])] at h
  push_cast at h
  linarith

/-- **The `O`-Maslov grading across an empty hexagon turning on its initial side**:
`M_O(y) = M_O(x) + 1 + 2 #(𝕆 ∩ P)`. -/
theorem maslovOℤ_eq_of_isEmpty_initialHexagon
    {P : GridInitialHexagonBetween C.column C.turnRow C.oppositeTurnRow x y} (hP : P.IsEmpty) :
    G.maslovOℤ y = G.maslovOℤ x + 1 + 2 * ((G.OColumnsOfSquares P.coveredSquares).card : ℤ) := by
  have h := G.maslovOℤ_sub_two_mul_card_OColumns hP
  rw [G.OColumns_toGridRectangle_eq_insert_of_initialHexagon P,
    Finset.card_insert_of_notMem (by simp [P.mem_coveredSquares])] at h
  push_cast at h
  linarith

/-- A rectangle carrying exactly one `X`-marking and one more `O`-marking than a set `S` of columns
raises the doubled Alexander grading by twice the size of `S`. -/
private theorem alexanderTwoℤ_eq_of_card {r : GridRectangleBetween x y} {S : Finset (Fin n)}
    (hO : (G.OColumns r.toGridRectangle).card = S.card + 1)
    (hX : (G.XSet ∩ r.toGridRectangle.coveredSquares).card = 1) :
    G.alexanderTwoℤ y = G.alexanderTwoℤ x + 2 * (S.card : ℤ) := by
  have h := G.alexander_sub_alexander_eq_card_sub_card r
  rw [hX, ← G.card_OColumns, hO] at h
  have hx := G.two_mul_alexander_eq_intCast x
  have hy := G.two_mul_alexander_eq_intCast y
  have hq : (G.alexanderTwoℤ y : ℚ) = G.alexanderTwoℤ x + 2 * (S.card : ℚ) := by
    push_cast at h
    linarith
  exact_mod_cast hq

/-- **The Alexander grading across a counted hexagon**, in its doubled integer form: a hexagon
counted by the hexagon map from `x` to `y` raises it by twice the number of `O`-markings it
carries, `2 A(y) = 2 A(x) + 2 #(𝕆 ∩ P)`. -/
theorem alexanderTwoℤ_eq_of_mem_hexagons
    {P : GridHexagonBetween C.column C.oppositeTurnRow C.turnRow x y}
    (hP : P ∈ G.hexagons C x y) :
    G.alexanderTwoℤ y =
      G.alexanderTwoℤ x + 2 * ((G.OColumnsOfSquares P.coveredSquares).card : ℤ) := by
  refine G.alexanderTwoℤ_eq_of_card (r := P.toGridRectangleBetween) ?_ ?_
  · rw [G.OColumns_toGridRectangle_eq_insert_of_hexagon P,
      Finset.card_insert_of_notMem (by simp [P.mem_coveredSquares])]
  · rw [G.XSet_inter_toGridRectangle_coveredSquares_of_mem_hexagons hP, Finset.card_singleton]

/-- **The Alexander grading across a counted hexagon turning on its initial side**, in its doubled
integer form: `2 A(y) = 2 A(x) + 2 #(𝕆 ∩ P)`. -/
theorem alexanderTwoℤ_eq_of_mem_initialHexagons
    {P : GridInitialHexagonBetween C.column C.turnRow C.oppositeTurnRow x y}
    (hP : P ∈ G.initialHexagons C x y) :
    G.alexanderTwoℤ y =
      G.alexanderTwoℤ x + 2 * ((G.OColumnsOfSquares P.coveredSquares).card : ℤ) := by
  refine G.alexanderTwoℤ_eq_of_card (r := P.toGridRectangleBetween) ?_ ?_
  · rw [G.OColumns_toGridRectangle_eq_insert_of_initialHexagon P,
      Finset.card_insert_of_notMem (by simp [P.mem_coveredSquares])]
  · rw [G.XSet_inter_toGridRectangle_coveredSquares_of_mem_initialHexagons hP,
      Finset.card_singleton]

end GridDiagram

namespace OddComponentGridDiagram

variable {n : ℕ} (G : OddComponentGridDiagram n) (C : GridDiagram.ColumnCommutationData G.1)
  {x y : GridState n}

/-- **The Alexander grading across a counted hexagon**: a hexagon counted by the hexagon map from
`x` to `y` raises the Alexander grading by the number of `O`-markings it carries,
`A(y) = A(x) + #(𝕆 ∩ P)`. -/
theorem alexanderℤ_eq_of_mem_hexagons
    {P : GridHexagonBetween C.column C.oppositeTurnRow C.turnRow x y}
    (hP : P ∈ G.1.hexagons C x y) :
    G.alexanderℤ y = G.alexanderℤ x + (G.1.OColumnsOfSquares P.coveredSquares).card := by
  have h := G.1.alexanderTwoℤ_eq_of_mem_hexagons C hP
  rw [← two_mul_alexanderℤ, ← two_mul_alexanderℤ] at h
  omega

/-- **The Alexander grading across a counted hexagon turning on its initial side**:
`A(y) = A(x) + #(𝕆 ∩ P)`. -/
theorem alexanderℤ_eq_of_mem_initialHexagons
    {P : GridInitialHexagonBetween C.column C.turnRow C.oppositeTurnRow x y}
    (hP : P ∈ G.1.initialHexagons C x y) :
    G.alexanderℤ y = G.alexanderℤ x + (G.1.OColumnsOfSquares P.coveredSquares).card := by
  have h := G.1.alexanderTwoℤ_eq_of_mem_initialHexagons C hP
  rw [← two_mul_alexanderℤ, ← two_mul_alexanderℤ] at h
  omega

/-- Multiplying `V^e · x` by a squarefree monomial `V^S` and passing to a state `y` raises the
bidegree by `(1, 0)` when `M_O(y) = M_O(x) + 1 + 2 |S|` and `A(y) = A(x) + |S|`. -/
private theorem monomialBidegree_add_sum_eq_add (S : Finset (Fin n)) (e : Fin n →₀ ℕ)
    (hM : G.1.maslovOℤ y = G.1.maslovOℤ x + 1 + 2 * (S.card : ℤ))
    (hA : G.alexanderℤ y = G.alexanderℤ x + S.card) :
    G.monomialBidegree y (e + ∑ c ∈ S, Finsupp.single c 1) = G.monomialBidegree x e + (1, 0) := by
  have hdeg : ((e + ∑ c ∈ S, Finsupp.single (M := ℕ) c 1).degree : ℤ) =
      (e.degree : ℤ) + (S.card : ℤ) := by
    rw [map_add, map_sum]
    simp
  refine Prod.ext ?_ ?_
  · simp only [Prod.fst_add, monomialBidegree_fst, hdeg, hM]
    ring
  · simp only [Prod.snd_add, monomialBidegree_snd, hdeg, hA]
    ring

/-- A linear map on `GC⁻` given by a matrix whose weighted transitions raise the bidegree by `δ`
sends a chain homogeneous of bidegree `g` to one homogeneous of bidegree `g + δ`. -/
private theorem mem_bigradedChainMinusPiece_add_of_matrix {R : Type*} [CommSemiring R]
    (f : GridChainMinus R n → GridChainMinus R n)
    (M : GridState n → GridState n → MvPolynomial (Fin n) R) (δ : ℤ × ℤ)
    (hf : ∀ c y, f c y = c.sum fun x p => p * M x y)
    (hM : ∀ x y, ∀ w ∈ (M x y).support, ∀ e : Fin n →₀ ℕ,
      G.monomialBidegree y (e + w) = G.monomialBidegree x e + δ)
    {g : ℤ × ℤ} {c : GridChainMinus R n} (hc : c ∈ G.bigradedChainMinusPiece R g) :
    f c ∈ G.bigradedChainMinusPiece R (g + δ) := by
  classical
  rw [mem_bigradedChainMinusPiece] at hc ⊢
  intro z d hd
  rw [hf, Finsupp.sum] at hd
  obtain ⟨w, -, hdw⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hd)
  obtain ⟨e, he, v, hv, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul _ _ hdw)
  rw [hM w z v hv e, hc w e he]

/-- Each monomial of a hexagon coefficient raises the bidegree by `(1, 0)`. -/
private theorem monomialBidegree_add_of_mem_support_hexagonCoefficient (R : Type*)
    [CommSemiring R] (x y : GridState n) (w : Fin n →₀ ℕ)
    (hw : w ∈ (G.1.hexagonCoefficient R C x y).support) (e : Fin n →₀ ℕ) :
    G.monomialBidegree y (e + w) = G.monomialBidegree x e + (1, 0) := by
  classical
  rw [GridDiagram.hexagonCoefficient_def] at hw
  obtain ⟨P, hP, hwP⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hw)
  rw [GridDiagram.hexagonWeight_eq_monomial] at hwP
  obtain rfl := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hwP)
  exact G.monomialBidegree_add_sum_eq_add _ e
    (G.1.maslovOℤ_eq_of_isEmpty_hexagon C ((G.1.mem_hexagons P).mp hP).1)
    (G.alexanderℤ_eq_of_mem_hexagons C hP)

/-- Each monomial of an initial-side hexagon coefficient raises the bidegree by `(1, 0)`. -/
private theorem monomialBidegree_add_of_mem_support_initialHexagonCoefficient (R : Type*)
    [CommSemiring R] (x y : GridState n) (w : Fin n →₀ ℕ)
    (hw : w ∈ (G.1.initialHexagonCoefficient R C x y).support) (e : Fin n →₀ ℕ) :
    G.monomialBidegree y (e + w) = G.monomialBidegree x e + (1, 0) := by
  classical
  rw [GridDiagram.initialHexagonCoefficient_def] at hw
  obtain ⟨P, hP, hwP⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hw)
  rw [GridDiagram.initialHexagonWeight_eq_monomial] at hwP
  obtain rfl := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hwP)
  exact G.monomialBidegree_add_sum_eq_add _ e
    (G.1.maslovOℤ_eq_of_isEmpty_initialHexagon C ((G.1.mem_initialHexagons P).mp hP).1)
    (G.alexanderℤ_eq_of_mem_initialHexagons C hP)

/-- **The hexagon map has bidegree `(1, 0)`.** The hexagon map of a validated column commutation
`C` sends a chain of `GC⁻(G)` homogeneous of bidegree `g` to one homogeneous of bidegree
`g + (1, 0)`: it raises the `O`-Maslov grading by one and preserves the Alexander grading. -/
theorem hexagonMap_mem_bigradedChainMinusPiece (R : Type*) [CommSemiring R] {g : ℤ × ℤ}
    {c : GridChainMinus R n} (hc : c ∈ G.bigradedChainMinusPiece R g) :
    G.1.hexagonMap R C c ∈ G.bigradedChainMinusPiece R (g + (1, 0)) :=
  G.mem_bigradedChainMinusPiece_add_of_matrix _ _ _ (G.1.hexagonMap_apply_apply R C)
    (G.monomialBidegree_add_of_mem_support_hexagonCoefficient C R) hc

/-- The map counting hexagons turning on their initial side has bidegree `(1, 0)`. -/
theorem initialHexagonMap_mem_bigradedChainMinusPiece (R : Type*) [CommSemiring R]
    {g : ℤ × ℤ} {c : GridChainMinus R n} (hc : c ∈ G.bigradedChainMinusPiece R g) :
    G.1.initialHexagonMap R C c ∈ G.bigradedChainMinusPiece R (g + (1, 0)) :=
  G.mem_bigradedChainMinusPiece_add_of_matrix _ _ _ (G.1.initialHexagonMap_apply_apply R C)
    (G.monomialBidegree_add_of_mem_support_initialHexagonCoefficient C R) hc

/-- **The commutation homotopy has bidegree `(1, 0)`.** Counting hexagons of both kinds, it sends a
chain of `GC⁻(G)` homogeneous of bidegree `g` to one homogeneous of bidegree `g + (1, 0)`. -/
theorem commutationHomotopy_mem_bigradedChainMinusPiece (R : Type*) [CommSemiring R]
    {g : ℤ × ℤ} {c : GridChainMinus R n} (hc : c ∈ G.bigradedChainMinusPiece R g) :
    G.1.commutationHomotopy R C c ∈ G.bigradedChainMinusPiece R (g + (1, 0)) := by
  rw [GridDiagram.commutationHomotopy_apply]
  exact Submodule.add_mem _ (G.hexagonMap_mem_bigradedChainMinusPiece C R hc)
    (G.initialHexagonMap_mem_bigradedChainMinusPiece C R hc)

end OddComponentGridDiagram

end TauCeti

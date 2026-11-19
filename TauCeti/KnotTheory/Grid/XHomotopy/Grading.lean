/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Grading.Unblocked.Chain
public import TauCeti.KnotTheory.Grid.XHomotopy.Complex

/-!
# The `X`-marking homotopies have bidegree `(-1, -1)`

Let `G` be a grid diagram with an odd number of link components, so that its unblocked complex
`GC⁻` carries the (`O`-Maslov, Alexander) bigrading of `Grading/Unblocked/Chain.lean`. The
`X`-marking homotopy `H_k` counts empty rectangles whose only covered `X`-marking is `X_k`. Such a
rectangle drops the `O`-Maslov grading by one once its weight `V^{O(r)}` is charged `-2` per
variable, exactly as a rectangle counted by `∂⁻` does, and, since it covers one `X`-marking, it
drops the Alexander grading by one once the weight is charged `-1` per variable. So `H_k` has
bidegree `(-1, -1)`, and so does every sum of such homotopies, for instance the null-homotopy
`GridDiagram.componentXHomotopy` of multiplication by `V_c + V_{c'}`. This matches the bidegree
`(-2, -1)` of each variable against the bidegree `(-1, 0)` of `∂⁻`.

## Main results

* `TauCeti.OddComponentGridDiagram.monomialBidegree_add_of_mem_XHomotopyRectangles`: a rectangle
  counted by `H_k` lowers the bidegree of a monomial generator by `(1, 1)`.
* `TauCeti.OddComponentGridDiagram.XHomotopy_mem_bigradedChainMinusPiece`: `H_k` has bidegree
  `(-1, -1)`.
* `TauCeti.OddComponentGridDiagram.componentXHomotopy_mem_bigradedChainMinusPiece`: the sum of the
  `X`-marking homotopies along a link component has bidegree `(-1, -1)`.
* `TauCeti.GridDiagram.IsKnot.XSmulHomotopy_mem_bigradedChainMinusPiece`: so does the
  null-homotopy of `V_c + V_c'` on a knot grid.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Lemma 4.6.9, for the homotopy
`H_{X_k}`.
-/

public section

namespace TauCeti.OddComponentGridDiagram

variable {n : ℕ} (G : OddComponentGridDiagram n) {x y : GridState n}

/-- Multiplying the basis element `V^e · x` by the weight of a rectangle counted by the `X`-marking
homotopy `H_k` and passing to the rectangle's target lowers the bidegree by `(1, 1)`. -/
theorem monomialBidegree_add_of_mem_XHomotopyRectangles {k : Fin n}
    {r : GridRectangleBetween x y} (hr : r ∈ G.1.XHomotopyRectangles k x y) (e : Fin n →₀ ℕ) :
    G.monomialBidegree y (e + ∑ c ∈ G.1.OColumns r.toGridRectangle, Finsupp.single c 1) =
      G.monomialBidegree x e - (1, 1) := by
  have hr' := (G.1.mem_XHomotopyRectangles k r).mp hr
  refine G.monomialBidegree_add_sum_OColumns_eq_sub (G.1.maslovOℤ_sub_two_mul_card_OColumns hr'.1)
    ?_ e
  rw [G.alexanderℤ_sub_card_OColumns_eq_sub_card r, Finset.inter_comm, hr'.2,
    Finset.card_singleton, Nat.cast_one]

/-- **The `X`-marking homotopy has bidegree `(-1, -1)`**: `H_k` lowers both the `O`-Maslov and
the Alexander grading of a homogeneous chain of `GC⁻` by one. -/
theorem XHomotopy_mem_bigradedChainMinusPiece {R : Type*} [CommSemiring R] (k : Fin n)
    {g : ℤ × ℤ} {c : GridChainMinus R n} (hc : c ∈ G.bigradedChainMinusPiece R g) :
    G.1.XHomotopy R k c ∈ G.bigradedChainMinusPiece R (g - (1, 1)) := by
  rw [sub_eq_add_neg]
  refine G.matrixMap_mem_bigradedChainMinusPiece_add R G (Equiv.refl _)
    (G.1.XHomotopyCoefficient R k) _ (fun c y => by simp [GridDiagram.XHomotopy_apply_apply])
    (-(1, 1)) (fun x y w hw d => ?_) hc
  obtain ⟨r, hr, rfl⟩ := G.1.exists_mem_XHomotopyRectangles_of_mem_support_XHomotopyCoefficient R hw
  rw [Equiv.coe_refl, Finsupp.mapDomain_id, ← sub_eq_add_neg,
    G.monomialBidegree_add_of_mem_XHomotopyRectangles hr d]

/-- The sum `GridDiagram.componentXHomotopy` of `X`-marking homotopies along a link component has
bidegree `(-1, -1)`. -/
theorem componentXHomotopy_mem_bigradedChainMinusPiece {R : Type*} [CommSemiring R]
    (c : Fin n) (i : ℕ) {g : ℤ × ℤ} {a : GridChainMinus R n}
    (ha : a ∈ G.bigradedChainMinusPiece R g) :
    G.1.componentXHomotopy R c i a ∈ G.bigradedChainMinusPiece R (g - (1, 1)) := by
  rw [GridDiagram.componentXHomotopy_apply]
  exact Submodule.sum_mem _ fun k _ => G.XHomotopy_mem_bigradedChainMinusPiece _ ha

end TauCeti.OddComponentGridDiagram

namespace TauCeti.GridDiagram.IsKnot

variable {n : ℕ} {G : GridDiagram n} (hG : G.IsKnot)

/-- On a knot grid, the null-homotopy `IsKnot.XSmulHomotopy` of multiplication by
`V_c + V_c'` has bidegree `(-1, -1)`. -/
theorem XSmulHomotopy_mem_bigradedChainMinusPiece {R : Type*} [CommSemiring R] (c c' : Fin n)
    {g : ℤ × ℤ} {a : GridChainMinus R n}
    (ha : a ∈ hG.toOddComponentGridDiagram.bigradedChainMinusPiece R g) :
    hG.XSmulHomotopy R c c' a ∈
      hG.toOddComponentGridDiagram.bigradedChainMinusPiece R (g - (1, 1)) := by
  rw [hG.XSmulHomotopy_eq_componentXHomotopy R]
  exact hG.toOddComponentGridDiagram.componentXHomotopy_mem_bigradedChainMinusPiece c _ ha

end TauCeti.GridDiagram.IsKnot

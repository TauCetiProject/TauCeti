/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Coxeter.Geometric.Component

/-!
# The canonical form over the components of the Coxeter graph in small cases

These checks run the component decomposition of the canonical form of a Coxeter matrix on small
examples.

* For two commuting nodes (`CoxeterMatrix.I 0`, with entry `2`) the Coxeter graph has no edge, the
  two nodes lie in different components, the simple roots are orthogonal, and the canonical form is
  the dot product.
* Two distinct nodes with infinite entry (entry `0`) are joined in the Coxeter graph, since
  `0 ≠ 2`, and the canonical form vanishes at `αᵢ + αⱼ`, so it is not positive definite. Reading
  adjacency as `3 ≤ M i j` on the stored natural number would disconnect them.
-/

public section

open Real Finsupp

namespace TauCeti

/-! ### Two commuting nodes -/

/-- For the entry `2` the two nodes are not adjacent in the Coxeter graph. -/
example : ¬(CoxeterMatrix.I 0).graph.Adj 0 1 := by
  simp [CoxeterMatrix.I]

/-- For the entry `2` the two nodes lie in different connected components. -/
example : (CoxeterMatrix.I 0).graph.connectedComponentMk 0 ≠
    (CoxeterMatrix.I 0).graph.connectedComponentMk 1 := by
  have hbot : (CoxeterMatrix.I 0).graph = ⊥ := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [CoxeterMatrix.I]
  rw [Ne, SimpleGraph.ConnectedComponent.eq, hbot, SimpleGraph.reachable_bot]
  decide

/-- For the entry `2` the two simple roots are orthogonal. -/
example : (CoxeterMatrix.I 0).geometricForm (single 0 1) (single 1 1) = 0 :=
  CoxeterMatrix.geometricForm_eq_zero_of_eq_two _ fun i hi j hj ↦ by
    obtain ⟨rfl, -⟩ := (mem_support_single _ _ _).mp hi
    obtain ⟨rfl, -⟩ := (mem_support_single _ _ _).mp hj
    simp [CoxeterMatrix.I]

/-- For the entry `2` the canonical form is the dot product of coefficient vectors. -/
example (x y : Fin 2 →₀ ℝ) :
    (CoxeterMatrix.I 0).geometricForm x y = x 0 * y 0 + x 1 * y 1 := by
  have hx : x = single 0 (x 0) + single 1 (x 1) := by ext i; fin_cases i <;> simp
  have hy : y = single 0 (y 0) + single 1 (y 1) := by ext i; fin_cases i <;> simp
  rw [hx, hy]
  simp [CoxeterMatrix.I]

/-! ### An infinite entry -/

/-- An infinite entry, stored as `0`, is an edge of the Coxeter graph, since `0 ≠ 2`. -/
example {B : Type*} (M : CoxeterMatrix B) {i j : B} (hij : i ≠ j) (h : M i j = 0) :
    M.graph.Adj i j := by
  simp [hij, h]

/-- At an infinite entry the canonical form vanishes at `αᵢ + αⱼ`, so it is not positive
definite. -/
example {B : Type*} (M : CoxeterMatrix B) {i j : B} (h : M i j = 0) :
    M.geometricForm (single i 1 + single j 1) (single i 1 + single j 1) = 0 := by
  simp [M.symmetric j i, h]

end TauCeti

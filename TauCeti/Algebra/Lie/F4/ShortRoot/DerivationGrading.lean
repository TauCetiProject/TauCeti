/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.DerivationEntry

/-!
# The root-lattice grading of the type-F4 derivation equations

The matrix entry in row `i` and column `j` has degree equal to the difference between the weights
of the two coordinate vectors.  This integral grading remains meaningful in characteristic two,
where distinct weights need not define distinct eigenvalues of the Lie algebra of the torus.
-/

public section

namespace TauCeti.F4ShortRoot

open TauCeti.DynkinType

/-- The root-lattice degree of a matrix entry. -/
@[expose] def entryDegree (i j : Fin 26) : Fin 4 → ℤ :=
  fun k => f4ShortRootWeight i k - f4ShortRootWeight j k

/-- A matrix is homogeneous of degree `d` when its entries outside that degree vanish. -/
@[expose] def IsHomogeneous {R : Type*} [Zero R] (d : Fin 4 → ℤ)
    (X : Matrix (Fin 26) (Fin 26) R) : Prop :=
  ∀ i j, entryDegree i j ≠ d → X i j = 0

/-- An entry outside the degree of a homogeneous matrix vanishes. -/
theorem IsHomogeneous.eq_zero {R : Type*} [Zero R] {d : Fin 4 → ℤ}
    {X : Matrix (Fin 26) (Fin 26) R} (hX : IsHomogeneous d X) (i j : Fin 26)
    (hij : entryDegree i j ≠ d) : X i j = 0 :=
  hX i j hij

/-- Equal weights occur only on the diagonal and between the two zero-weight vectors. -/
theorem weight_eq_iff (i j : Fin 26) :
    f4ShortRootWeight i = f4ShortRootWeight j ↔
      i = j ∨ (i = 12 ∧ j = 13) ∨ (i = 13 ∧ j = 12) := by
  revert i j
  decide +kernel

/-- Every diagonal matrix entry has degree zero. -/
@[simp]
theorem entryDegree_self (i : Fin 26) : entryDegree i i = 0 := by
  funext k
  simp [entryDegree]

/-- Degree zero means that the row and column weights agree. -/
theorem entryDegree_eq_zero_iff (i j : Fin 26) :
    entryDegree i j = 0 ↔ f4ShortRootWeight i = f4ShortRootWeight j := by
  constructor
  · intro h
    funext k
    exact sub_eq_zero.mp (congrFun h k)
  · intro h
    funext k
    exact sub_eq_zero.mpr (congrFun h k)

end TauCeti.F4ShortRoot

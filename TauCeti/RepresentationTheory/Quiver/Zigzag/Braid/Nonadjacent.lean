/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.TensorProduct.Balanced.Corner
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Componentwise.Corner

/-!
# The middle tensor factor at nonadjacent zigzag vertices

For distinct nonadjacent vertices `i, j` of a finite simple graph, the corner
`e_i Z e_j` of the componentwise zigzag algebra is zero. Consequently
`e_i Z ⊗[Z] Z e_j` vanishes. This is the middle factor of the product
`(Z e_i ⊗[k] e_i Z) ⊗[Z] (Z e_j ⊗[k] e_j Z)` occurring in the commuting
relation for zigzag braid complexes.

The calculation includes isolated vertices, whose factors in the public algebra
are dual numbers. These results identify the middle factor; they do not provide
a full bimodule tensor product isomorphism or a commuting isomorphism of complexes.

See Huerfano--Khovanov, *A category for the adjoint representation*, for the
graph braid action.
-/

public section

namespace TauCeti

open MulOpposite

variable (k : Type*) [CommRing k] {V : Type*} (G : SimpleGraph V) [Finite V]

local notation "Z" => AlgCat.carrier (zigzagAlgebra k G)
local notation "e" => fun i : V ↦ zigzagAlgebraBasis k G (Sum.inl i)

/-- The balanced tensor product `e_i Z ⊗[Z] Z e_j` vanishes at distinct
nonadjacent vertices. The right ideal is represented in `Zᵐᵒᵖ`. -/
theorem subsingleton_balancedTensorProduct_zigzagAlgebra_of_ne_of_not_adj {i j : V}
    (hij : i ≠ j) (hadj : ¬ G.Adj i j) :
    Subsingleton (BalancedTensorProduct k Z (Ideal.span {op (e i)} : Ideal Zᵐᵒᵖ)
      (Ideal.span {e j} : Ideal Z)) := by
  exact (subsingleton_spanSingleton_balancedTensorProduct_iff_cornerSubmodule_eq_bot k
    (isIdempotentElem_zigzagAlgebraBasis_inl k G i)
    (isIdempotentElem_zigzagAlgebraBasis_inl k G j)).2
    (cornerSubmodule_zigzagAlgebra_eq_bot_of_ne_of_not_adj k G hij hadj)

end TauCeti

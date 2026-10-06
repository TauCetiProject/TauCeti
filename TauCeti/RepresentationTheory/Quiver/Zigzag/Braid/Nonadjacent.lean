/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.TensorProduct.Balanced.Corner
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Componentwise.Multiplication

/-!
# The middle tensor factor at nonadjacent zigzag vertices

For distinct nonadjacent vertices `i, j` of a finite simple graph, the corner
`e_i Z e_j` of the componentwise zigzag algebra is zero. Consequently
`e_i Z ⊗[Z] Z e_j` vanishes. This is the middle factor of the product
`(Z e_i ⊗[k] e_i Z) ⊗[Z] (Z e_j ⊗[k] e_j Z)` occurring in the commuting
relation for zigzag braid complexes.

The calculation includes isolated vertices, whose factors in the public algebra
are dual numbers. It does not identify the full bimodule tensor product or assert
a commuting isomorphism of complexes; associativity and the outer bimodule factors
still have to be assembled.

The proof uses the componentwise multiplication table and
`TauCeti.spanSingletonBalancedTensorEquivCorner`. See Huerfano--Khovanov,
*A category for the adjoint representation*, for the graph braid action.
-/

public section

namespace TauCeti

open MulOpposite

variable (k : Type*) [CommRing k] {V : Type*} (G : SimpleGraph V) [Finite V]

local notation "Z" => AlgCat.carrier (zigzagAlgebra k G)
local notation "e" => fun i : V ↦ zigzagAlgebraBasis k G (Sum.inl i)

/-- Distinct nonadjacent vertex idempotents cut out a zero corner of the public
zigzag algebra, including its isolated-vertex dual-number factors. -/
theorem cornerSubmodule_zigzagAlgebra_eq_bot_of_not_adj {i j : V}
    (hij : i ≠ j) (hadj : ¬ G.Adj i j) : cornerSubmodule k (e i) (e j) = ⊥ := by
  classical
  have hzero : cornerMap k (e i) (e j) = 0 := by
    apply (zigzagAlgebraBasis k G).ext
    intro b
    simp only [cornerMap_apply, LinearMap.zero_apply]
    rcases b with v | d | v
    · by_cases h : i = v
      · subst v
        simp [hij]
      · simp [h]
    · by_cases h : i = d.snd
      · by_cases h' : d.fst = j
        · have ha : G.Adj i j := by simpa only [h, ← h'] using d.adj.symm
          exact (hadj ha).elim
        · simp [h, Ne.symm h']
      · simp [h]
    · by_cases h : i = v
      · subst v
        simp [hij]
      · simp [h]
  exact (cornerSubmodule_eq_bot_iff k (e i) (e j)).2 fun x ↦ by
    simpa only [cornerMap_apply, LinearMap.zero_apply] using LinearMap.congr_fun hzero x

/-- The balanced tensor product `e_i Z ⊗[Z] Z e_j` vanishes at distinct
nonadjacent vertices. The right ideal is represented in `Zᵐᵒᵖ`. -/
theorem subsingleton_balancedTensorProduct_zigzagAlgebra_of_not_adj {i j : V}
    (hij : i ≠ j) (hadj : ¬ G.Adj i j) :
    Subsingleton (BalancedTensorProduct k Z (Ideal.span {op (e i)} : Ideal Zᵐᵒᵖ)
      (Ideal.span {e j} : Ideal Z)) := by
  have hid (v : V) : IsIdempotentElem (e v) := by simp [IsIdempotentElem]
  exact (subsingleton_spanSingleton_balancedTensorProduct_iff k (hid i) (hid j)).2
    (cornerSubmodule_zigzagAlgebra_eq_bot_of_not_adj k G hij hadj)

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.TensorProduct.Balanced.Corner
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Componentwise.Corner.Adjacent

/-!
# The middle tensor factor at adjacent zigzag vertices

At adjacent vertices `i` and `j`, multiplication identifies the balanced product
`e_i Z ⊗[Z] Z e_j` with the corner `e_i Z e_j`. The corner has one basis vector,
the arrow from `j` to `i`, so its arrow coordinate identifies the balanced product
with the ground ring. The pure-tensor formula records the order of multiplication
in Tau Ceti's later-factor-first path convention.

This is the middle factor in the product of adjacent vertex bimodules
`(Z e_i ⊗[k] e_i Z) ⊗[Z] (Z e_j ⊗[k] e_j Z)`.

See Huerfano--Khovanov, *A category for the adjoint representation*, Section 3.
-/

public section

noncomputable section

namespace TauCeti

open MulOpposite

variable (k : Type*) [CommRing k] {V : Type*} (G : SimpleGraph V) [Finite V]

local notation "Z" => AlgCat.carrier (zigzagAlgebra k G)
local notation "e" => fun v : V ↦ zigzagAlgebraBasis k G (Sum.inl v)

/-- Multiplication followed by the arrow coordinate identifies the balanced middle factor
of adjacent vertex braid bimodules with one copy of the ground ring. -/
def zigzagAdjacentBalancedTensorEquiv {i j : V} (h : G.Adj j i) :
    BalancedTensorProduct k Z (Ideal.span {op (e i)} : Ideal Zᵐᵒᵖ)
      (Ideal.span {e j} : Ideal Z) ≃ₗ[k] k :=
  (spanSingletonBalancedTensorProductEquivCorner k
    (isIdempotentElem_zigzagAlgebraBasis_inl k G i)
    (isIdempotentElem_zigzagAlgebraBasis_inl k G j)).trans
      (zigzagAlgebraAdjacentCornerEquiv k G h)

/-- On pure tensors, the adjacent middle-factor coordinate is the arrow coordinate
of the product in the zigzag algebra. -/
@[simp]
theorem zigzagAdjacentBalancedTensorEquiv_tmul {i j : V} (h : G.Adj j i)
    (m : (Ideal.span {op (e i)} : Ideal Zᵐᵒᵖ))
    (n : (Ideal.span {e j} : Ideal Z)) :
    zigzagAdjacentBalancedTensorEquiv k G h (BalancedTensorProduct.tmul k Z m n) =
      (zigzagAlgebraBasis k G).repr (unop (m : Zᵐᵒᵖ) * (n : Z))
        (.inr (.inl (⟨(j, i), h⟩ : G.Dart))) := by
  rw [zigzagAdjacentBalancedTensorEquiv, LinearEquiv.trans_apply,
    zigzagAlgebraAdjacentCornerEquiv_apply,
    coe_spanSingletonBalancedTensorProductEquivCorner_tmul]

/-- The inverse adjacent middle-factor coordinate inserts the right-ideal generator and
the corresponding multiple of the arrow in the left ideal. -/
@[simp]
theorem zigzagAdjacentBalancedTensorEquiv_symm_apply {i j : V} (h : G.Adj j i)
    (a : k) :
    (zigzagAdjacentBalancedTensorEquiv k G h).symm a =
      BalancedTensorProduct.tmul k Z
        (spanSingletonGenerator (op (e i)))
        ⟨((zigzagAlgebraAdjacentCornerEquiv k G h).symm a : Z),
          mem_span_singleton_of_mem_cornerSubmodule
            (isIdempotentElem_zigzagAlgebraBasis_inl k G j)
            ((zigzagAlgebraAdjacentCornerEquiv k G h).symm a).property⟩ := by
  rw [zigzagAdjacentBalancedTensorEquiv, LinearEquiv.symm_trans_apply,
    spanSingletonBalancedTensorProductEquivCorner_symm_apply]

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Opposite
public import Mathlib.RingTheory.TensorProduct.Basic
public import TauCeti.Algebra.Algebra.Frobenius.Casimir
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Componentwise.Trace

/-!
# The Casimir element of the componentwise zigzag algebra

Let `Z` be the zigzag algebra `TauCeti.zigzagAlgebra` of a finite simple graph. Its vertex, arrow
and volume basis `TauCeti.zigzagAlgebraBasis` is dual, for the symmetric Frobenius pairing
`(x, y) ↦ tr (x * y)` of `TauCeti.zigzagAlgebraTrace`, to its reindexing by
`TauCeti.zigzagDualIndex`. This file defines the **Casimir element** `∑_b b ⊗ b^∨` of that pairing
in the enveloping algebra `Z ⊗[k] Zᵐᵒᵖ` and proves that it commutes with `Z`, as the Casimir
element of any trace does (`TauCeti.sum_mul_tmul_eq_sum_tmul_mul`).

## Main definitions

* `TauCeti.zigzagCasimir`: the Casimir element `∑_b b ⊗ b^∨` of the trace pairing.

## Main results

* `TauCeti.zigzagCasimir_eq_sum`: the Casimir element as a sum over the basis.
* `TauCeti.tmul_one_mul_zigzagCasimir`: the Casimir element commutes with `Z`.

## References

* L. Kadison, *New examples of Frobenius extensions*, University Lecture Series 14, AMS, 1999
  (dual bases and Casimir elements of Frobenius algebras).
-/

public section

namespace TauCeti

open MulOpposite
open scoped TensorProduct

universe u w

variable (k : Type w) [CommRing k] {V : Type u} (G : SimpleGraph V)

/-- The zigzag algebra, in this file. -/
local notation "𝒵" => AlgCat.carrier (zigzagAlgebra k G)

/-- The enveloping algebra of the zigzag algebra, in this file. -/
local notation "𝒵ᵉ" =>
  AlgCat.carrier (zigzagAlgebra k G) ⊗[k] (AlgCat.carrier (zigzagAlgebra k G))ᵐᵒᵖ

variable [Finite V]

/-- **The Casimir element of the zigzag algebra**, `∑_b b ⊗ b^∨` in `Z ⊗[k] Zᵐᵒᵖ`, with `b` running
over the vertex, arrow and volume basis and `b^∨` over its dual basis for the trace pairing,
indexed by `TauCeti.zigzagDualIndex`. -/
noncomputable def zigzagCasimir : 𝒵ᵉ := by
  classical
  let _ : Fintype V := Fintype.ofFinite V
  exact ∑ b, zigzagAlgebraBasis k G b ⊗ₜ[k] op (zigzagAlgebraBasis k G (zigzagDualIndex G b))

variable {k G}

/-- The Casimir element as a sum over the basis, for any choice of finiteness and decidability
instances. -/
theorem zigzagCasimir_eq_sum [Fintype V] [DecidableRel G.Adj] :
    zigzagCasimir k G =
      ∑ b, zigzagAlgebraBasis k G b ⊗ₜ[k] op (zigzagAlgebraBasis k G (zigzagDualIndex G b)) := by
  rw [zigzagCasimir]
  convert rfl

/-- **The Casimir element commutes with the zigzag algebra**: `(a ⊗ 1) C = (1 ⊗ a) C`, that is,
`a C = C a` for the bimodule structure of `Z ⊗[k] Zᵐᵒᵖ`. -/
theorem tmul_one_mul_zigzagCasimir (a : 𝒵) :
    (a ⊗ₜ[k] (1 : 𝒵ᵐᵒᵖ)) * zigzagCasimir k G = ((1 : 𝒵) ⊗ₜ[k] op a) * zigzagCasimir k G := by
  classical
  cases nonempty_fintype V
  -- The basis and its dual basis are dual for the trace in the sense of the Casimir lemma.
  have hx (y : 𝒵) : ∑ b, zigzagAlgebraTrace k G
      (y * zigzagAlgebraBasis k G (zigzagDualIndex G b)) • zigzagAlgebraBasis k G b = y := by
    simp_rw [zigzagAlgebraTrace_mul_zigzagAlgebraBasis_zigzagDualIndex]
    exact (zigzagAlgebraBasis k G).sum_repr y
  have hy (y : 𝒵) : ∑ b, zigzagAlgebraTrace k G
      (zigzagAlgebraBasis k G b * y) • zigzagAlgebraBasis k G (zigzagDualIndex G b) = y := by
    rw [← Equiv.sum_comp (zigzagDualIndex_involutive G).toPerm]
    simp only [Function.Involutive.coe_toPerm, zigzagDualIndex_zigzagDualIndex]
    simp_rw [zigzagAlgebraTrace_mul_comm k G _ y]
    exact hx y
  have key := sum_mul_tmul_eq_sum_tmul_mul (zigzagAlgebraTrace k G)
    (zigzagAlgebraTrace_mul_comm k G) hx hy a
  have := congrArg (TensorProduct.map LinearMap.id (opLinearEquiv k).toLinearMap) key
  simp only [map_sum, TensorProduct.map_tmul, LinearMap.id_coe, id_eq, LinearEquiv.coe_coe,
    coe_opLinearEquiv] at this
  rw [zigzagCasimir_eq_sum, Finset.mul_sum, Finset.mul_sum]
  simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← op_mul]
  exact this

end TauCeti

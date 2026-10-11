/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Idempotents.TensorProduct
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Braid.Basic
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Componentwise.Corner.Basic

/-!
# Tensor factors of the zigzag vertex bimodule

The cyclic enveloping-algebra ideal used for `zigzagBraidBimodule` is
`Z e_i ⊗[k] e_i Z`. The right ideal is represented in `Zᵐᵒᵖ`.
We identify these presentations using `spanSingletonTensorProductEquiv` and
`LinearEquiv.ofEq`, and compute the two outer actions on the tensor factors.

This carrier identification is the input for extracting the middle corner from
balanced products of vertex bimodules. In particular it supplies a prerequisite
for the self-tensor decomposition used in the inverse braid homotopy equivalence.
The construction covers isolated vertices of the public componentwise algebra.
-/

public section

noncomputable section

namespace TauCeti

open MulOpposite
open scoped TensorProduct

variable (k : Type*) [CommRing k] {V : Type*} (G : SimpleGraph V) [Finite V]

local notation "Z" => AlgCat.carrier (zigzagAlgebra k G)
local notation "E" => Z ⊗[k] Zᵐᵒᵖ
local notation "e" => fun i : V ↦ zigzagAlgebraBasis k G (Sum.inl i)
local notation "L" => fun i : V ↦ (Ideal.span {e i} : Ideal Z)
local notation "R" => fun i : V ↦ (Ideal.span {op (e i)} : Ideal Zᵐᵒᵖ)

private theorem vertexBimodule_eq_span (i : V) :
    (Ideal.span {e i ⊗ₜ[k] op (e i)} : Ideal E) = zigzagBraidBimodule k G i := by
  ext u
  have he := isIdempotentElem_zigzagAlgebraBasis_inl k G i
  rw [mem_span_singleton_iff_mul_eq_self
    (he.tmul (k := k) (by rw [IsIdempotentElem, ← op_mul, he.eq])),
    mem_zigzagBraidBimodule_iff]

/-- Identify the actual vertex bimodule with its left and right idempotent-ideal factors. -/
def zigzagBraidBimoduleFactorsEquiv (i : V) :
    zigzagBraidBimodule k G i ≃ₗ[k] L i ⊗[k] R i :=
  ((LinearEquiv.ofEq _ _ (vertexBimodule_eq_span k G i)).restrictScalars k).symm.trans
    (spanSingletonTensorProductEquiv k (isIdempotentElem_zigzagAlgebraBasis_inl k G i)
      (by rw [IsIdempotentElem, ← op_mul,
        (isIdempotentElem_zigzagAlgebraBasis_inl k G i).eq])).symm

/-- Including the tensor factors gives the enveloping-algebra representative of the bimodule. -/
theorem coe_zigzagBraidBimoduleFactorsEquiv_symm_apply (i : V) (t : L i ⊗[k] R i) :
    ((zigzagBraidBimoduleFactorsEquiv k G i).symm t : E) =
      TensorProduct.map ((L i).subtype.restrictScalars k)
        ((R i).subtype.restrictScalars k) t := by
  simp only [zigzagBraidBimoduleFactorsEquiv, LinearEquiv.symm_trans_apply,
    LinearEquiv.symm_symm, LinearEquiv.restrictScalars_apply,
    LinearEquiv.coe_ofEq_apply, coe_spanSingletonTensorProductEquiv_apply]

/-- The inverse identifies a pure tensor of the two ideals with the same ambient pure tensor. -/
@[simp]
theorem coe_zigzagBraidBimoduleFactorsEquiv_symm_tmul (i : V) (x : L i) (y : R i) :
    ((zigzagBraidBimoduleFactorsEquiv k G i).symm (x ⊗ₜ[k] y) : E) =
      (x : Z) ⊗ₜ[k] (y : Zᵐᵒᵖ) := by
  rw [coe_zigzagBraidBimoduleFactorsEquiv_symm_apply, TensorProduct.map_tmul]
  rfl

/-- The inverse factor identification carries the two outer actions to the enveloping action. -/
@[simp]
theorem zigzagBraidBimoduleFactorsEquiv_symm_map_smul (i : V) (a b : Z)
    (t : L i ⊗[k] R i) :
    (zigzagBraidBimoduleFactorsEquiv k G i).symm
        (TensorProduct.map ((Algebra.lsmul k k (L i)) a)
          ((Algebra.lsmul k k (R i)) (op b)) t) =
      (a ⊗ₜ[k] op b) • (zigzagBraidBimoduleFactorsEquiv k G i).symm t := by
  simp only [zigzagBraidBimoduleFactorsEquiv, LinearEquiv.symm_trans_apply,
    LinearEquiv.symm_symm, spanSingletonTensorProductEquiv_map_smul,
    LinearEquiv.restrictScalars_apply, map_smul]

/-- The factor identification sends the enveloping action to the two factor actions. -/
@[simp]
theorem zigzagBraidBimoduleFactorsEquiv_tmul_smul (i : V) (a b : Z)
    (u : zigzagBraidBimodule k G i) :
    zigzagBraidBimoduleFactorsEquiv k G i ((a ⊗ₜ[k] op b) • u) =
      TensorProduct.map ((Algebra.lsmul k k (L i)) a)
        ((Algebra.lsmul k k (R i)) (op b)) (zigzagBraidBimoduleFactorsEquiv k G i u) := by
  apply (zigzagBraidBimoduleFactorsEquiv k G i).symm.injective
  rw [LinearEquiv.symm_apply_apply, zigzagBraidBimoduleFactorsEquiv_symm_map_smul,
    LinearEquiv.symm_apply_apply]

end TauCeti

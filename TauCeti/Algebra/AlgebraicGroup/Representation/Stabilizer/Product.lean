/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.Stabilizer
public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Product

/-!
# Subspace stabilizers in a direct sum

Embedding a subspace in the first summand of a direct-sum representation preserves its
scheme-theoretic stabilizer. In particular, the line through `(m, 0)` has the same stabilizer
as the line through `m`. The proof compares the defining matrix coefficients, so it applies
to nonreduced subgroup schemes over any field.

This supplies the direct-sum step in FlagVarieties Layer 4.0(c)'s faithful Chevalley line.
-/

public section

open TauCeti

universe u v w x

namespace Submodule

variable {k : Type u} [Field k] {H : Type v} [CommRing H] [HopfAlgebra k H]
  {M : Type w} {V : Type x} [AddCommGroup M] [Module k M] [Comodule k H M]
  [AddCommGroup V] [Module k V] [Comodule k H V]

attribute [local instance] Comodule.Prod

/-- Adding a direct summand preserves the stabilizer of a subspace in the first summand. -/
theorem stabilizerHopfIdeal_map_inl (W : Submodule k M) :
    (W.map (LinearMap.inl k M V)).stabilizerHopfIdeal H = W.stabilizerHopfIdeal H := by
  let U := W.map (LinearMap.inl k M V)
  apply le_antisymm
  · rw [stabilizerHopfIdeal_le_iff]
    intro ψ y hy
    obtain ⟨z, hz, rfl⟩ := hy
    let f := (ψ ∘ₗ U.mkQ) ∘ₗ LinearMap.inl k M V
    have hf : W ≤ LinearMap.ker f := by
      intro z hz
      change ψ (U.mkQ (LinearMap.inl k M V z)) = 0
      rw [mkQ_apply, (Quotient.mk_eq_zero U).mpr (mem_map_of_mem hz), map_zero]
    change Comodule.matrixCoefficient (R := k) (C := H) (ψ ∘ₗ U.mkQ)
      (Comodule.prodInl (R := k) (C := H) (N := V) z) ∈ _
    rw [Comodule.matrixCoefficient_map]
    simpa only [liftQ_mkQ, Comodule.prodInl_toLinearMap] using
      W.matrixCoefficient_mem_stabilizerHopfIdeal (W.liftQ f hf) hz
  · rw [stabilizerHopfIdeal_le_iff]
    intro ψ z hz
    let f := (ψ ∘ₗ W.mkQ) ∘ₗ LinearMap.fst k M V
    have hf : U ≤ LinearMap.ker f := by
      rintro y ⟨z, hz, rfl⟩
      change ψ (W.mkQ z) = 0
      rw [mkQ_apply, (Quotient.mk_eq_zero W).mpr hz, map_zero]
    have h := U.matrixCoefficient_mem_stabilizerHopfIdeal (H := H) (U.liftQ f hf)
      (show LinearMap.inl k M V z ∈ U from mem_map_of_mem hz)
    simpa only [liftQ_mkQ, f, Comodule.matrixCoefficient_prod_inl] using h

/-- The line through `(m, 0)` has the same stabilizer as the line through `m`. -/
theorem stabilizerHopfIdeal_span_singleton_prod_zero (m : M) :
    (k ∙ (m, (0 : V))).stabilizerHopfIdeal H = (k ∙ m).stabilizerHopfIdeal H := by
  simpa only [map_span, Set.image_singleton, LinearMap.inl_apply] using
    stabilizerHopfIdeal_map_inl (H := H) (V := V) (k ∙ m)

end Submodule


/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.RingTheory.FiniteType.PointSeparation
public import TauCeti.LinearAlgebra.TensorProduct.Separation

/-!
# Point separation after tensoring

Points of a reduced finite-type algebra valued in an algebraically closed extension detect
not only its elements but also tensors with any vector space. This allows identities in a
family of vectors to be checked at every geometric point of the parameter algebra.
-/

public section

open scoped TensorProduct

namespace TauCeti

/-- Algebraically closed specializations of the first factor detect equality of tensors when
that factor is a reduced finite-type algebra over a field. -/
theorem tensor_eq_of_forall_map_algHom_eq
    {k B M K : Type*} [Field k] [Field K] [Algebra k K] [IsAlgClosed K]
    [CommRing B] [Algebra k B] [Algebra.FiniteType k B] [IsReduced B]
    [AddCommGroup M] [Module k M] {x y : B ⊗[k] M}
    (h : ∀ p : B →ₐ[k] K,
      TensorProduct.map p.toLinearMap LinearMap.id x =
        TensorProduct.map p.toLinearMap LinearMap.id y) : x = y := by
  apply sub_eq_zero.mp
  apply tensor_eq_zero_of_forall_rTensor_eq_zero
    (fun p : B →ₐ[k] K ↦ p.toLinearMap)
    (fun b hb ↦ eq_of_forall_algHom_apply_eq (k := k) (K := K)
      fun p ↦ (hb p).trans (map_zero p).symm)
  intro p
  simpa only [LinearMap.rTensor_def, map_sub, sub_eq_zero] using h p

end TauCeti

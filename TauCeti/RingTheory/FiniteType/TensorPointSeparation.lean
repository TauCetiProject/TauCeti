/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.RingTheory.FiniteType.PointSeparation
public import TauCeti.LinearAlgebra.TensorProduct.Basis

/-!
# Point separation after tensoring

Points of a reduced finite-type algebra valued in an algebraically closed extension detect
not only its elements but also tensors with any vector space. This allows identities in a
family of vectors to be checked at every geometric point of the parameter algebra.
The proof uses `TensorProduct.tensor_eq_of_forall_tensorComponent_eq` to reduce to the
Nullstellensatz point-separation theorem `eq_of_forall_algHom_apply_eq`.
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
  apply TensorProduct.tensor_eq_of_forall_tensorComponent_eq
  intro φ
  apply eq_of_forall_algHom_apply_eq (k := k) (K := K)
  intro p
  simpa only [LinearMap.tensorComponent_map, LinearMap.comp_id,
    AlgHom.toLinearMap_apply] using congrArg (LinearMap.tensorComponent φ) (h p)

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.AlgebraicClosure
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.RingTheory.Flat.Basic

/-!
# Relative algebraic closure and extension of scalars to an algebraically closed field

Let `K / k` be a field extension and `L` an algebraically closed field containing `k`. If
`K ⊗[k] L` is a domain, then `k` is algebraically closed in `K`: the relative algebraic closure
`algebraicClosure k K` is `⊥`.

Indeed, `E = algebraicClosure k K` is algebraic over `k`, and `L ⊗[k] E` embeds in the domain
`L ⊗[k] K` because every `k`-module is flat. So `L ⊗[k] E` is a domain that is integral over the
algebraically closed field `L`, hence equal to `L`; comparing dimensions, `[E : k] = 1`.

This is the field-theoretic content of the fact that the function field of a geometrically
integral scheme over `k` contains no nontrivial algebraic extension of `k`: there `K ⊗[k] L` is a
localization of the ring of functions on an affine open of the base change of the scheme to `L`,
which is integral.

## Main results

* `TauCeti.algebraicClosure_eq_bot_of_isDomain_tensorProduct`: if `K ⊗[k] L` is a domain for an
  algebraically closed field `L` over `k`, then `algebraicClosure k K = ⊥`.
-/

public section

open scoped TensorProduct

namespace TauCeti

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- If `K ⊗[k] L` is a domain for some algebraically closed field `L` over `k`, then `k` is
algebraically closed in `K`. -/
theorem algebraicClosure_eq_bot_of_isDomain_tensorProduct (L : Type*) [Field L] [Algebra k L]
    [IsAlgClosed L] [IsDomain (K ⊗[k] L)] : algebraicClosure k K = ⊥ := by
  let E := algebraicClosure k K
  -- `L ⊗[k] E` is a subring of the domain `L ⊗[k] K`, since `L` is flat over the field `k`.
  let f : L ⊗[k] E →ₐ[L] L ⊗[k] K :=
    Algebra.TensorProduct.map (AlgHom.id L L) (IsScalarTower.toAlgHom k E K)
  have hf : Function.Injective f :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := L)
      (IsScalarTower.toAlgHom k E K).toLinearMap Subtype.val_injective
  have : IsDomain (L ⊗[k] K) :=
    (Algebra.TensorProduct.comm k K L).toMulEquiv.isDomain_iff.mp inferInstance
  have : IsDomain (L ⊗[k] E) := hf.isDomain f.toRingHom
  -- A domain integral over the algebraically closed field `L` is `L` itself.
  have hrank := (LinearEquiv.ofBijective (Algebra.linearMap L (L ⊗[k] E))
    (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := L) (K := L ⊗[k] E))).lift_rank_eq
  rw [Module.rank_self, Module.rank_baseChange, Cardinal.lift_one, Cardinal.lift_lift,
    eq_comm, Cardinal.lift_eq_one] at hrank
  exact IntermediateField.rank_eq_one_iff.mp hrank

end TauCeti

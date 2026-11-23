/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Equiv.Basic

/-!
# The underlying bijection of a continuous linear equivalence

A continuous linear equivalence `e : M₁ ≃SL[σ₁₂] M₂` has an underlying bijection `e.toEquiv`,
reached through `e.toLinearEquiv`. This file records that, as functions, `e.toEquiv` is `e` and
its inverse is `e.symm`, the continuous counterparts of Mathlib's `LinearEquiv.coe_toEquiv` and
`LinearEquiv.coe_toEquiv_symm`. They let constructions on bijections, such as pullbacks along an
`Equiv`, be specialised to continuous linear equivalences by a named rewrite. It also records
`ContinuousLinearEquiv.eqRec_refl_apply`, identifying evaluation of the reflexive equivalence
transported along a base-point equality with casting between fibres.
-/

public section

namespace ContinuousLinearEquiv

variable {R₁ R₂ M₁ M₂ : Type*} [Semiring R₁] [Semiring R₂] {σ₁₂ : R₁ →+* R₂} {σ₂₁ : R₂ →+* R₁}
  [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂] [TopologicalSpace M₁] [AddCommMonoid M₁]
  [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R₁ M₁] [Module R₂ M₂]

/-- The underlying bijection of a continuous linear equivalence is the equivalence itself, as a
function. -/
theorem coe_toEquiv (e : M₁ ≃SL[σ₁₂] M₂) : ⇑e.toEquiv = e :=
  rfl

/-- The inverse of the underlying bijection of a continuous linear equivalence is its inverse, as
a function. -/
theorem coe_toEquiv_symm (e : M₁ ≃SL[σ₁₂] M₂) : ⇑e.toEquiv.symm = e.symm :=
  rfl

/-- Applying the reflexive continuous linear equivalence transported along `h : x₀ = x₁` is
casting along `E` by `h`. -/
theorem eqRec_refl_apply {R X : Type*} [Semiring R] {E : X → Type*}
    [∀ x, TopologicalSpace (E x)] [∀ x, AddCommMonoid (E x)] [∀ x, Module R (E x)]
    {x₀ x₁ : X} (h : x₀ = x₁) (v : E x₀) :
    (show E x₀ ≃L[R] E x₁ from h ▸ ContinuousLinearEquiv.refl R (E x₀)) v =
      cast (congrArg E h) v := by
  cases h
  rfl

end ContinuousLinearEquiv

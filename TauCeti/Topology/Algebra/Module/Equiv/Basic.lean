/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Equiv.Basic

/-!
# The underlying bijection of a continuous linear equivalence, and `ULift`

A continuous linear equivalence `e : M₁ ≃SL[σ₁₂] M₂` has an underlying bijection `e.toEquiv`,
reached through `e.toLinearEquiv`. This file records that, as functions, `e.toEquiv` is `e` and
its inverse is `e.symm`, the continuous counterparts of Mathlib's `LinearEquiv.coe_toEquiv` and
`LinearEquiv.coe_toEquiv_symm`. They let constructions on bijections, such as pullbacks along an
`Equiv`, be specialised to continuous linear equivalences by a named rewrite.

It also evaluates Mathlib's `ContinuousLinearEquiv.ulift : ULift M ≃L[R] M` and its inverse as
`ULift.down` and `ULift.up` (`ContinuousLinearEquiv.ulift_apply`,
`ContinuousLinearEquiv.ulift_symm_apply`), as `ULift.moduleEquiv_apply` and
`ULift.moduleEquiv_symm_apply` do for the linear equivalence.

Finally, it records that continuous linear equivalences `e` and `e'` intertwine continuous linear
maps `f` and `g`, `g ∘ e = e' ∘ f`, exactly when their inverses intertwine them the other way
round, `f ∘ e⁻¹ = e'⁻¹ ∘ g` (`ContinuousLinearEquiv.comp_symm_eq_symm_comp_iff`).
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

section ULift

universe w

variable {R M : Type*} [Semiring R] [TopologicalSpace M] [AddCommMonoid M] [Module R M]

/-- `ContinuousLinearEquiv.ulift` is `ULift.down`. -/
@[simp] theorem ulift_apply (x : ULift.{w} M) : (ulift : ULift.{w} M ≃L[R] M) x = x.down :=
  rfl

/-- The inverse of `ContinuousLinearEquiv.ulift` is `ULift.up`. -/
@[simp] theorem ulift_symm_apply (x : M) :
    (ulift : ULift.{w} M ≃L[R] M).symm x = ULift.up x :=
  rfl

end ULift

section Intertwine

variable {R N₁ N₂ : Type*} [Semiring R] [TopologicalSpace N₁] [AddCommMonoid N₁]
  [TopologicalSpace N₂] [AddCommMonoid N₂] [Module R N₁] [Module R N₂]
  {P₁ P₂ : Type*} [TopologicalSpace P₁] [AddCommMonoid P₁] [TopologicalSpace P₂]
  [AddCommMonoid P₂] [Module R P₁] [Module R P₂]

/-- Continuous linear equivalences `e : N₁ ≃L[R] N₂` and `e' : P₁ ≃L[R] P₂` intertwine
`f : N₁ →L[R] P₁` and `g : N₂ →L[R] P₂` the other way round, `f ∘ e⁻¹ = e'⁻¹ ∘ g`, exactly when
`g ∘ e = e' ∘ f`. -/
theorem comp_symm_eq_symm_comp_iff (e : N₁ ≃L[R] N₂) (e' : P₁ ≃L[R] P₂) {f : N₁ →L[R] P₁}
    {g : N₂ →L[R] P₂} :
    f.comp (e.symm : N₂ →L[R] N₁) = (e'.symm : P₂ →L[R] P₁).comp g ↔
      g.comp (e : N₁ →L[R] N₂) = (e' : P₁ →L[R] P₂).comp f := by
  refine ⟨fun h ↦ ContinuousLinearMap.ext fun x ↦ ?_, fun h ↦ ContinuousLinearMap.ext fun y ↦ ?_⟩
  · simpa using congr(e' ($h (e x))).symm
  · apply e'.injective
    simpa using congr($h (e.symm y)).symm

end Intertwine

end ContinuousLinearEquiv

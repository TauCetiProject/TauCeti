/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Equiv.Basic

/-!
# Conjugating automorphism groups along a semilinear equivalence

Mathlib conjugates general linear groups with
`LinearMap.GeneralLinearGroup.congrLinearEquiv : GL R₁ M₁ ≃* GL R₂ M₂`, and algebra automorphisms
with `AlgEquiv.autCongr`. Groups of linear automorphisms cut out by a structure they preserve — an
orthogonal group, an isometry group — are subgroups of `M ≃ₗ[R] M` rather than of `GL R M`, so what
they need is the same conjugation stated directly on `M ≃ₗ[R] M`, which this file records as
`LinearEquiv.autCongr`, the linear counterpart of `AlgEquiv.autCongr`.

Conjugation needs no more than a semilinear equivalence, which is the generality
`congrLinearEquiv` already supplies: `e : M₁ ≃ₛₗ[σ₁₂] M₂` carries `R₁`-automorphisms of `M₁` to
`R₂`-automorphisms of `M₂`, the scalars travelling along `σ₁₂`. The two inverse-pair assumptions
give a round trip on each scalar ring — `σ₂₁ ∘ σ₁₂` is the identity on `R₁` and `σ₁₂ ∘ σ₂₁` the
identity on `R₂` — and it is the latter that makes the conjugate `R₂`-linear.

## Main definitions

* `LinearEquiv.autCongr`: conjugation by `e : M₁ ≃ₛₗ[σ₁₂] M₂`, as an isomorphism
  `(M₁ ≃ₗ[R₁] M₁) ≃* (M₂ ≃ₗ[R₂] M₂)`.

## Main statements

* `LinearEquiv.autCongr_apply_apply`: conjugating `f` by `e` sends `m` to `e (f (e.symm m))`.
* `LinearEquiv.autCongr_refl`, `LinearEquiv.autCongr_symm` and `LinearEquiv.autCongr_trans'`:
  conjugation along the identity is the identity, the inverse of conjugation by `e` is
  conjugation by `e.symm`, and conjugation is compatible with composition, as for
  `AlgEquiv.autCongr`; `LinearEquiv.autCongr_trans` is the `simp` form of the last for linear
  equivalences.
* `LinearEquiv.autCongr_apply` and `LinearEquiv.autCongr_symm_apply`: conjugation and its inverse
  as equalities of linear equivalences, for consumers that read the conjugate as a map rather than
  at a point.
-/

public section

namespace LinearEquiv

variable {R₁ R₂ R₃ M₁ M₂ M₃ : Type*} [Semiring R₁] [Semiring R₂] [Semiring R₃]
  [AddCommMonoid M₁] [Module R₁ M₁] [AddCommMonoid M₂] [Module R₂ M₂]
  [AddCommMonoid M₃] [Module R₃ M₃]
  {σ₁₂ : R₁ →+* R₂} {σ₂₁ : R₂ →+* R₁} [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]

/-- Conjugation by a semilinear equivalence `e : M₁ ≃ₛₗ[σ₁₂] M₂`, as an isomorphism of automorphism
groups: `f` is sent to `e ∘ f ∘ e.symm`. It is the counterpart on `M ≃ₗ[R] M` of Mathlib's
`LinearMap.GeneralLinearGroup.congrLinearEquiv` on general linear groups. -/
def autCongr (e : M₁ ≃ₛₗ[σ₁₂] M₂) : (M₁ ≃ₗ[R₁] M₁) ≃* (M₂ ≃ₗ[R₂] M₂) where
  toFun f := (e.symm.trans f).trans e
  invFun g := (e.trans g).trans e.symm
  left_inv f := by ext; simp
  right_inv g := by ext; simp
  map_mul' f g := by ext; simp

/-- Conjugation by `e`, as an equality of linear equivalences: `autCongr e f` is `f` precomposed
with `e.symm` and postcomposed with `e`. Structural consumers — determinants, traces, anything
reading the conjugate as a map rather than at a point — want this form. -/
-- Not `@[simp]`: the pointwise `autCongr_apply_apply` is the simp normal form here, and rewriting
-- `autCongr e f` to the composite first would leave that lemma unable to fire.
theorem autCongr_apply (e : M₁ ≃ₛₗ[σ₁₂] M₂) (f : M₁ ≃ₗ[R₁] M₁) :
    autCongr e f = (e.symm.trans f).trans e :=
  (rfl)

/-- Inverse conjugation by `e`, as an equality of linear equivalences: `(autCongr e).symm g` is `g`
precomposed with `e` and postcomposed with `e.symm`. -/
theorem autCongr_symm_apply (e : M₁ ≃ₛₗ[σ₁₂] M₂) (g : M₂ ≃ₗ[R₂] M₂) :
    (autCongr e).symm g = (e.trans g).trans e.symm :=
  (rfl)

/-- Conjugating `f` by `e` sends `m` to `e (f (e.symm m))`. -/
@[simp]
theorem autCongr_apply_apply (e : M₁ ≃ₛₗ[σ₁₂] M₂) (f : M₁ ≃ₗ[R₁] M₁) (m : M₂) :
    autCongr e f m = e (f (e.symm m)) :=
  (rfl)

/-- Inverse conjugation by `e` sends `m` to `e.symm (g (e m))`. -/
-- Not `@[simp]`: `autCongr_symm` rewrites `(autCongr e).symm` to `autCongr e.symm`, after which
-- `autCongr_apply_apply` and `LinearEquiv.symm_symm` give the same right-hand side.
theorem autCongr_symm_apply_apply (e : M₁ ≃ₛₗ[σ₁₂] M₂) (g : M₂ ≃ₗ[R₂] M₂) (m : M₁) :
    (autCongr e).symm g m = e.symm (g (e m)) :=
  (rfl)

variable (R₁ M₁) in
/-- Conjugation along the identity is the identity. -/
@[simp]
theorem autCongr_refl : autCongr (refl R₁ M₁) = MulEquiv.refl (M₁ ≃ₗ[R₁] M₁) :=
  (rfl)

/-- The inverse of conjugation by `e` is conjugation by `e.symm`. -/
@[simp]
theorem autCongr_symm (e : M₁ ≃ₛₗ[σ₁₂] M₂) : (autCongr e).symm = autCongr e.symm :=
  (rfl)

/-- Conjugating by `e₁₂` and then by `e₂₃` is conjugating by their composite. For semilinear
equivalences, see `LinearEquiv.autCongr_trans'`. -/
@[simp]
theorem autCongr_trans {R N₁ N₂ N₃ : Type*} [Semiring R] [AddCommMonoid N₁] [Module R N₁]
    [AddCommMonoid N₂] [Module R N₂] [AddCommMonoid N₃] [Module R N₃]
    (e₁₂ : N₁ ≃ₗ[R] N₂) (e₂₃ : N₂ ≃ₗ[R] N₃) :
    (autCongr e₁₂).trans (autCongr e₂₃) = autCongr (e₁₂.trans e₂₃) :=
  (rfl)

/-- Conjugating by `e₁₂` and then by `e₂₃` is conjugating by their composite, for semilinear
equivalences. Not a `simp` lemma, as `σ₁₃` and `σ₃₁` cannot be inferred from the left-hand side;
`LinearEquiv.autCongr_trans` is the `simp` form for linear equivalences. -/
theorem autCongr_trans' {σ₂₃ : R₂ →+* R₃} {σ₃₂ : R₃ →+* R₂} {σ₁₃ : R₁ →+* R₃} {σ₃₁ : R₃ →+* R₁}
    [RingHomInvPair σ₂₃ σ₃₂] [RingHomInvPair σ₃₂ σ₂₃]
    [RingHomInvPair σ₁₃ σ₃₁] [RingHomInvPair σ₃₁ σ₁₃]
    [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [RingHomCompTriple σ₃₂ σ₂₁ σ₃₁]
    (e₁₂ : M₁ ≃ₛₗ[σ₁₂] M₂) (e₂₃ : M₂ ≃ₛₗ[σ₂₃] M₃) :
    (autCongr e₁₂).trans (autCongr e₂₃) = autCongr (e₁₂.trans e₂₃) :=
  (rfl)

end LinearEquiv

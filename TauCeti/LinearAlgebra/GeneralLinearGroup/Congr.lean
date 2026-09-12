/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic

/-!
# Conjugating automorphism groups along a semilinear equivalence

Mathlib conjugates general linear groups with
`LinearMap.GeneralLinearGroup.congrLinearEquiv : GL R₁ M₁ ≃* GL R₂ M₂`, and identifies `GL R M` with
the automorphisms `M ≃ₗ[R] M` through `LinearMap.GeneralLinearGroup.generalLinearEquiv`. Groups of
linear automorphisms cut out by a structure they preserve — an orthogonal group, an isometry
group — are subgroups of `M ≃ₗ[R] M` rather than of `GL R M`, so what they need is the composite of
those two, which this file records as `LinearEquiv.autCongr`.

Conjugation needs no more than a semilinear equivalence, which is the generality
`congrLinearEquiv` already supplies: `e : M₁ ≃ₛₗ[σ₁₂] M₂` carries `R₁`-automorphisms of `M₁` to
`R₂`-automorphisms of `M₂`, the scalars travelling along `σ₁₂`. The two inverse-pair assumptions
give a round trip on each scalar ring — `σ₂₁ ∘ σ₁₂` is the identity on `R₁` and `σ₁₂ ∘ σ₂₁` the
identity on `R₂` — and it is the latter that makes the conjugate `R₂`-linear.

## Main definitions

* `LinearEquiv.autCongr`: conjugation by `e : M₁ ≃ₛₗ[σ₁₂] M₂`, as an isomorphism
  `(M₁ ≃ₗ[R₁] M₁) ≃* (M₂ ≃ₗ[R₂] M₂)`.

## Main statements

* `LinearEquiv.autCongr_apply` and `LinearEquiv.autCongr_symm_apply`: conjugation and its inverse
  as equalities of linear equivalences, for consumers that read the conjugate as a map rather than
  at a point. The pointwise `autCongr_apply_apply` and `autCongr_symm_apply_apply` are the same
  facts evaluated at `m`.
-/

public section

namespace TauCeti

namespace LinearEquiv

open LinearMap.GeneralLinearGroup

section Bridge

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

/-- The linear automorphism underlying the general linear group element
`(generalLinearEquiv R M).symm f` is `f` itself.

Mathlib records how `generalLinearEquiv` computes on coercions (`coeFn_generalLinearEquiv`,
`coe_toLinearEquiv`) rather than at the level of `M ≃ₗ[R] M`, so both evaluation lemmas for
`autCongr` below need this bridge; it is stated once here. -/
private theorem toLinearEquiv_generalLinearEquiv_symm (f : M ≃ₗ[R] M) :
    ((generalLinearEquiv R M).symm f).toLinearEquiv = f := by
  ext m
  rw [coe_toLinearEquiv, ← coeFn_generalLinearEquiv]
  exact DFunLike.congr_fun ((generalLinearEquiv R M).apply_symm_apply f) m

end Bridge

section Semilinear

variable {R₁ R₂ M₁ M₂ : Type*} [Semiring R₁] [Semiring R₂]
  [AddCommMonoid M₁] [Module R₁ M₁] [AddCommMonoid M₂] [Module R₂ M₂]
  {σ₁₂ : R₁ →+* R₂} {σ₂₁ : R₂ →+* R₁} [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]

/-- Conjugation by a semilinear equivalence `e : M₁ ≃ₛₗ[σ₁₂] M₂`, as an isomorphism of automorphism
groups: Mathlib's `LinearMap.GeneralLinearGroup.congrLinearEquiv` read through
`LinearMap.GeneralLinearGroup.generalLinearEquiv`.

The two evaluation lemmas below are its characteristic API. -/
def _root_.LinearEquiv.autCongr (e : M₁ ≃ₛₗ[σ₁₂] M₂) : (M₁ ≃ₗ[R₁] M₁) ≃* (M₂ ≃ₗ[R₂] M₂) :=
  ((generalLinearEquiv R₁ M₁).symm.trans (congrLinearEquiv e)).trans (generalLinearEquiv R₂ M₂)

/-- Conjugating `f` by `e` sends `m` to `e (f (e.symm m))`. -/
@[simp]
theorem _root_.LinearEquiv.autCongr_apply_apply (e : M₁ ≃ₛₗ[σ₁₂] M₂) (f : M₁ ≃ₗ[R₁] M₁) (m : M₂) :
    LinearEquiv.autCongr e f m = e (f (e.symm m)) := by
  rw [LinearEquiv.autCongr, MulEquiv.trans_apply, MulEquiv.trans_apply]
  simp only [congrLinearEquiv_apply, coeFn_generalLinearEquiv, coe_ofLinearEquiv,
    LinearEquiv.trans_apply, toLinearEquiv_generalLinearEquiv_symm]

/-- Inverse conjugation by `e` sends `m` to `e.symm (g (e m))`. -/
@[simp]
theorem _root_.LinearEquiv.autCongr_symm_apply_apply (e : M₁ ≃ₛₗ[σ₁₂] M₂) (g : M₂ ≃ₗ[R₂] M₂)
    (m : M₁) :
    (LinearEquiv.autCongr e).symm g m = e.symm (g (e m)) := by
  rw [LinearEquiv.autCongr, MulEquiv.symm_trans_apply, MulEquiv.symm_trans_apply,
    congrLinearEquiv_symm]
  simp only [congrLinearEquiv_apply, MulEquiv.symm_symm, coeFn_generalLinearEquiv,
    coe_ofLinearEquiv, LinearEquiv.symm_symm, LinearEquiv.trans_apply,
    toLinearEquiv_generalLinearEquiv_symm]

/-- Conjugation by `e`, as an equality of linear equivalences: `autCongr e f` is `f` precomposed
with `e.symm` and postcomposed with `e`. Structural consumers — determinants, traces, anything
reading the conjugate as a map rather than at a point — want this form. -/
-- Not `@[simp]`: the pointwise `autCongr_apply_apply` is the simp normal form here, and rewriting
-- `autCongr e f` to the composite first would leave that lemma unable to fire.
theorem _root_.LinearEquiv.autCongr_apply (e : M₁ ≃ₛₗ[σ₁₂] M₂) (f : M₁ ≃ₗ[R₁] M₁) :
    LinearEquiv.autCongr e f = (e.symm.trans f).trans e :=
  LinearEquiv.ext fun m ↦ LinearEquiv.autCongr_apply_apply e f m

/-- Inverse conjugation by `e`, as an equality of linear equivalences: `(autCongr e).symm g` is `g`
precomposed with `e` and postcomposed with `e.symm`. -/
-- Proved by characterising the inverse rather than unfolding `autCongr` a second time: applying
-- `autCongr e` to both sides reduces it to `autCongr_apply`, so the coercion transport across
-- `toLinearEquiv` happens once, in `autCongr_apply_apply`, and not again here.
theorem _root_.LinearEquiv.autCongr_symm_apply (e : M₁ ≃ₛₗ[σ₁₂] M₂) (g : M₂ ≃ₗ[R₂] M₂) :
    (LinearEquiv.autCongr e).symm g = (e.trans g).trans e.symm := by
  rw [MulEquiv.symm_apply_eq, LinearEquiv.autCongr_apply]
  exact LinearEquiv.ext fun m ↦ by simp

end Semilinear

end LinearEquiv

end TauCeti

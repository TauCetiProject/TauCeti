/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Invertible
public import Mathlib.Algebra.Module.Basic
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Basic.Real.Basic

/-!
# Doubling is invertible on a real vector space

For a real vector space `N`, multiplication by `2` is a bijection, so the doubling map is a unit
of the endomorphism ring — and it remains one when `N` is regarded only as a `ℤ`-module, where
`2` itself is not invertible. This file records that as an `Invertible (2 : Module.End ℤ N)`
instance, together with the rewrite rule identifying its inverse with the real scalar `(2 : ℝ)⁻¹`.

## Main definitions

* `TauCeti.invertibleTwoModuleEnd`: for an `R`-module `N` that is also a module over a semiring
  `S` in which `2` is invertible, doubling is invertible on the `R`-endomorphisms of `N`. No
  compatibility between the two actions is assumed: halving by `⅟(2 : S)` is automatically
  `R`-linear, since it inverts the additive map `x ↦ x + x`.

## Main results

* `TauCeti.invOf_two_moduleEnd_apply`: the inverse of doubling is halving by the `S`-scalar,
  for whichever `Invertible (2 : Module.End R N)` instance is in scope.
* `TauCeti.half_moduleEnd_apply_eq_inv_two_smul`: on a real vector space, that inverse acts as
  the scalar `(2 : ℝ)⁻¹`. This extends Mathlib's `QuadraticMap.half_moduleEnd_apply_eq_half_smul`
  to scalar rings `R` such as `ℤ`, where its `Invertible (2 : R)` hypothesis is unavailable; here
  the halving scalar comes from the real structure instead of from the ring.
* `TauCeti.instInvertibleTwoModuleEndInt`: the instance for `R = ℤ` and `S = ℝ`, so that
  doubling is invertible on any real vector space viewed as an endomorphism of its underlying
  `ℤ`-module.

## The consumer this exists for

Mathlib builds the bilinear map associated with a quadratic map by halving the polar form:
`QuadraticMap.associatedHom` is `⅟(2 : Module.End R N) • QuadraticMap.polarBilin`, with
`QuadraticMap.associated'` the `ℤ`-linear specialisation. Halving needs
`Invertible (2 : Module.End R N)`, and Mathlib's docstring for `associatedHom` names exactly the
case this file supplies:

> Note that this makes the bijection available in more cases than the simpler condition
> `Invertible (2 : R)`, e.g., when `R = ℤ` and `N = ℝ`.

Mathlib provides no instance reaching it: its only route is
`[Invertible (2 : R)] → Invertible (2 : Module.End R M)`, which for `R = ℤ` asks for
`Invertible (2 : ℤ)` and fails. With the instance below, `associated'` and its API —
`associated_apply`, `associated_isSymm`, `associated_flip`, `associated_eq_self_apply` — become
usable on `ℤ`-quadratic maps with values in a real vector space.

## Implementation notes

The construction is stated for general semirings `R` and `S` but is a `def` rather than an
`instance`, because `S` appears nowhere in the conclusion `Invertible (2 : Module.End R N)` and
so could never be inferred by instance search. Instances are registered by applying it to the
rings that are wanted; `R = ℤ`, `S = ℝ` is the one this repository needs. Registering it for a
general `R` would overlap Mathlib's `Invertible (2 : R)` instance (for example at `R = ℝ`) with
a different, non-defeq inverse.

-/

public section

namespace TauCeti

section General

variable {R N : Type*} [Semiring R] [AddCommMonoid N] [Module R N]

/-- **Doubling is invertible on the `R`-endomorphisms of a module that also carries an action of a
semiring `S` in which `2` is invertible.** The inverse is halving by `⅟(2 : S)`, which is
automatically `R`-linear: no compatibility between the `R`- and `S`-actions is needed. -/
-- A `def`, not an `instance`: `S` occurs nowhere in the conclusion, so instance search could never
-- infer it. Instances are registered for the scalar rings that are wanted, `ℝ` below.
@[instance_reducible]
noncomputable def invertibleTwoModuleEnd (S : Type*) [Semiring S] [Module S N]
    [Invertible (2 : S)] : Invertible (2 : Module.End R N) :=
  -- Halving by `⅟(2 : S)` is a two-sided inverse of the `R`-linear doubling, so
  -- `LinearMap.inverse` makes it `R`-linear; no `SMulCommClass R S N` is needed.
  have half_double (x : N) : ⅟(2 : S) • (2 : Module.End R N) x = x := by
    rw [Module.End.ofNat_apply, two_nsmul, smul_add, invOf_two_smul_add_invOf_two_smul]
  have double_half (x : N) : (2 : Module.End R N) (⅟(2 : S) • x) = x := by
    rw [Module.End.ofNat_apply, two_nsmul, invOf_two_smul_add_invOf_two_smul]
  { invOf := LinearMap.inverse 2 (⅟(2 : S) • ·) half_double double_half
    invOf_mul_self := LinearMap.ext half_double
    mul_invOf_self := LinearMap.ext double_half }

/-- **The inverse of doubling is halving by the scalar**, for whichever
`Invertible (2 : Module.End R N)` instance is in scope. -/
-- Instance-independent because the inverse `y` of doubling satisfies `y x + y x = x`, and halving
-- by `⅟(2 : S)` recovers `y x` from that sum; the proof never unfolds `invertibleTwoModuleEnd`,
-- so the definition needs no `@[expose]`.
theorem invOf_two_moduleEnd_apply (S : Type*) [Semiring S] [Module S N] [Invertible (2 : S)]
    [Invertible (2 : Module.End R N)] (x : N) :
    ⅟(2 : Module.End R N) x = ⅟(2 : S) • x := by
  have h := congr($(mul_invOf_self (2 : Module.End R N)) x)
  rw [Module.End.mul_apply, Module.End.ofNat_apply, two_nsmul, Module.End.one_apply] at h
  conv_rhs => rw [← h, smul_add, invOf_two_smul_add_invOf_two_smul]

/-- The inverse of doubling acts as the real scalar `(2 : ℝ)⁻¹`, for whichever
`Invertible (2 : Module.End R N)` instance is in scope. -/
-- Stated with function application rather than `•`, because `simp` normalises a `Module.End`
-- action to application (`Module.End.smul_def`).
@[simp]
theorem half_moduleEnd_apply_eq_inv_two_smul [Module ℝ N] [Invertible (2 : Module.End R N)]
    (x : N) : ⅟(2 : Module.End R N) x = (2 : ℝ)⁻¹ • x := by
  rw [invOf_two_moduleEnd_apply ℝ, invOf_eq_inv]

end General

/-- **Doubling is invertible on a real vector space**, as an endomorphism of its `ℤ`-module
structure. -/
-- Registered for `ℤ` only; see the implementation notes. Named rather than anonymous: Lean's
-- generated name for the anonymous form carries an underscore
-- (`instInvertibleEndIntOfNat_tauCeti`), which the `defsWithUnderscore` linter rejects.
noncomputable instance instInvertibleTwoModuleEndInt {N : Type*} [AddCommGroup N] [Module ℝ N] :
    Invertible (2 : Module.End ℤ N) :=
  invertibleTwoModuleEnd ℝ

end TauCeti

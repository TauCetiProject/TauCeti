/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.Algebra.Module.Injective
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Data.ZMod.QuotientRing
public import TauCeti.Algebra.Module.Injective.PrincipalIdealRing

/-!
# `ℤ/nℤ` is an injective module over itself

For `n ≠ 0` the ring `ℤ/nℤ` is self-injective: every `ℤ/nℤ`-linear map from an ideal of `ℤ/nℤ`
to `ℤ/nℤ` extends to the whole ring, which is Baer's criterion (`Module.Baer`) for the module
`ℤ/nℤ` over itself. Consequently `Hom(-, ℤ/nℤ)` is exact on the abelian groups killed by `n`, which
is what makes the dual `M ↦ Hom(M, ℤ/nℤ)` of a finite abelian group of exponent dividing `n` behave
like the dual of a vector space; the duality statements for the finite `ℤ/pⁱ[G]`-modules of a
profinite group rest on this.

The ring `ℤ/nℤ` is the quotient of the principal ideal domain `ℤ` by the nonzero ideal `(n)`
(`Int.quotientSpanNatEquivZMod`), so this is the special case `Module.Injective.quotient_self` of
the self-injectivity of a principal ideal domain modulo a nonzero ideal, transported along that ring
isomorphism by Mathlib's `Module.Injective.of_ringEquiv`. The hypothesis `n ≠ 0` is necessary: `ℤ`
is not injective over itself, since the map `2ℤ → ℤ`, `2 ↦ 1`, does not extend.

## Main results

* `Module.Baer.zmod_self`: `ℤ/nℤ` satisfies Baer's criterion over itself, for `n ≠ 0`.
* `Module.Baer.of_addEquiv_zmod`: a `ℤ/nℤ`-module isomorphic to `ℤ/nℤ` as an additive group
  satisfies Baer's criterion, for `n ≠ 0`.
* `Module.Baer.exists_module_of_addEquiv_zmod`: an additive group isomorphic to `ℤ/nℤ` carries a
  `ℤ/nℤ`-module structure satisfying Baer's criterion, for `n ≠ 0`.
-/

public section

/-- **`ℤ/nℤ` is self-injective**, in the form of Baer's criterion: for `n ≠ 0`, every
`ZMod n`-linear map from an ideal of `ZMod n` to `ZMod n` extends to a linear map on `ZMod n`.
By `Module.Baer.extension_property`, every `ZMod n`-linear map into `ZMod n` then extends along
any injective linear map of `ZMod n`-modules. This is `Module.Injective.quotient_self` for
`ℤ ⧸ (n)`, transported along `Int.quotientSpanNatEquivZMod`. -/
theorem Module.Baer.zmod_self (n : ℕ) [NeZero n] : Module.Baer (ZMod n) (ZMod n) :=
  have := Module.Injective.quotient_self (I := Ideal.span {(n : ℤ)}) <| by
    simpa only [ne_eq, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero] using NeZero.ne n
  .of_injective <| .of_ringEquiv (Int.quotientSpanNatEquivZMod n)
    (Int.quotientSpanNatEquivZMod n).toSemilinearEquiv

/-- **A `ℤ/nℤ`-module additively isomorphic to `ℤ/nℤ` is self-injective**: for `n ≠ 0`, a
`ZMod n`-module `W` with an additive isomorphism `W ≃+ ZMod n` satisfies Baer's criterion over
`ZMod n`. Every additive homomorphism of `ZMod n`-modules is linear, so the isomorphism transports
`Module.Baer.zmod_self`. -/
theorem Module.Baer.of_addEquiv_zmod {n : ℕ} [NeZero n] {W : Type*} [AddCommGroup W]
    [Module (ZMod n) W] (e : W ≃+ ZMod n) : Module.Baer (ZMod n) W :=
  Module.Baer.of_equiv (e.symm.toLinearEquiv fun c x => ZMod.map_smul _ c x)
    (Module.Baer.zmod_self n)

/-- **An additive group isomorphic to `ℤ/nℤ` is a self-injective `ℤ/nℤ`-module**: for `n ≠ 0`, an
additive group `W` with `W ≃+ ZMod n` is killed by `n`, so it carries a `ZMod n`-module structure
(`AddCommGroup.zmodModule`), and for it `W` satisfies Baer's criterion over `ZMod n`
(`Module.Baer.of_addEquiv_zmod`). -/
theorem Module.Baer.exists_module_of_addEquiv_zmod {n : ℕ} [NeZero n] {W : Type*}
    [AddCommGroup W] (e : W ≃+ ZMod n) : ∃ _ : Module (ZMod n) W, Module.Baer (ZMod n) W :=
  let : Module (ZMod n) W := AddCommGroup.zmodModule fun x ↦ e.injective <| by
    rw [map_nsmul, map_zero, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  ⟨this, Module.Baer.of_addEquiv_zmod e⟩

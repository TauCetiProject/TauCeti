/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.ZMod
public import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity

/-!
# `ℤ/k` and the `k`-th roots of unity

A primitive `k`-th root of unity generates the group of all `k`-th roots of unity, so Mathlib's
`IsPrimitiveRoot.zmodEquivZPowers`, which identifies `ℤ/k` with the powers of a chosen primitive
root, identifies it with the whole of `μ_k`.

Both halves are in Mathlib — `IsPrimitiveRoot.zmodEquivZPowers` and `IsPrimitiveRoot.zpowers_eq` —
but not the composite, which is what a consumer phrased in terms of `μ_k` rather than a chosen
generator needs.

Independently of any primitive root, `μ_k` of any commutative monoid is killed by `k`, so written
additively it is a `ZMod k`-module.

Conversely, `ℤ/n` written multiplicatively is itself a group of `n`-th roots of unity: `ofAdd 1` is
a primitive `n`-th root of unity, and the group is cyclic, so `Multiplicative (ZMod n)` has enough
`n`-th roots of unity in the sense of Mathlib's duality theory for finite abelian groups. This is
what lets that theory serve the groups killed by `n`, whose characters with values in `ℤ/n` are
their additive homomorphisms to `ZMod n`.

## Main results

* `TauCeti.nsmul_additive_rootsOfUnity_eq_zero`: `k` kills `μ_k`, written additively, so that it
  is a `ZMod k`-module.
* `TauCeti.ZMod.isPrimitiveRoot_ofAdd_one`: `ofAdd 1` is a primitive `n`-th root of unity in
  `Multiplicative (ZMod n)`.
* `TauCeti.instHasEnoughRootsOfUnityMultiplicativeZMod`: `Multiplicative (ZMod n)` has enough
  `n`-th roots of unity.
* `TauCeti.hasEnoughRootsOfUnity_multiplicative_zmod_exponent`: `Multiplicative (ZMod n)` has
  enough `e`-th roots of unity for the exponent `e` of any additive monoid killed by `n`.
* `IsPrimitiveRoot.zmodEquivRootsOfUnity`: `ℤ/k ≃+ Additive (μ_k)`, given a primitive `k`-th root.
* `IsPrimitiveRoot.coe_zmodEquivRootsOfUnity_apply_intCast` and
  `IsPrimitiveRoot.coe_zmodEquivRootsOfUnity_apply_natCast`: it sends `i` to `ζ ^ i`.
* `IsPrimitiveRoot.zmodEquivRootsOfUnity_symm_apply_zpow` and
  `IsPrimitiveRoot.zmodEquivRootsOfUnity_symm_apply_pow`: its inverse sends `ζ ^ i` back to `i`.

## Provenance

`IsPrimitiveRoot.zmodEquivRootsOfUnity` is ported from AINTLIB (`github.com/CBirkbeck/AINTLIB`,
Apache-2.0) @ `a302aeacd86053f9d5f991fbbf664e1cc1051d08`, source file
`projects/HasseWeil/HasseWeil/HasseBound/WeilPairing/RootsOfUnity.lean`, declaration
`rootsOfUnity_addEquiv_zmod`. Three changes: the direction is reversed to start from `ZMod k`, so
that it reads like `IsPrimitiveRoot.zmodEquivZPowers` which it extends; the base is a domain rather
than a field, which is all `zpowers_eq` asks for; and the four characterising lemmas below — the
equivalence and its inverse, each at an integer and at a natural exponent — are added, none of
which the source has. The remaining declarations of this file — the `ZMod k`-module structure on
`μ_k` written additively and the roots of unity of `Multiplicative (ZMod n)` — have no counterpart
in that source.
-/

public section

namespace TauCeti

variable {M : Type*} [CommMonoid M] (k : ℕ)

/-- **`μ_k` is killed by `k`**: written additively, `ζ ^ k = 1` reads `k • ζ = 0`. -/
@[simp]
theorem nsmul_additive_rootsOfUnity_eq_zero (x : Additive (rootsOfUnity k M)) : k • x = 0 :=
  Additive.toMul.injective <| Subtype.ext <| by
    simpa [toMul_nsmul] using (mem_rootsOfUnity k _).1 x.toMul.2

/-- `μ_k`, written additively, is a `ZMod k`-module, being killed by `k`. -/
instance instModuleZModAdditiveRootsOfUnity : Module (ZMod k) (Additive (rootsOfUnity k M)) :=
  AddCommGroup.zmodModule (nsmul_additive_rootsOfUnity_eq_zero k)

namespace ZMod

/-- **`ofAdd 1` is a primitive `n`-th root of unity in `ℤ/n` written multiplicatively**: its order
is the additive order of `1 : ZMod n`, which is `n`. -/
theorem isPrimitiveRoot_ofAdd_one (n : ℕ) :
    IsPrimitiveRoot (Multiplicative.ofAdd (1 : ZMod n)) n := by
  have := IsPrimitiveRoot.orderOf (Multiplicative.ofAdd (1 : ZMod n))
  rwa [orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one] at this

end ZMod

/-- **`ℤ/n` written multiplicatively has enough `n`-th roots of unity**: `ofAdd 1` is a primitive
one, and its roots of unity form a cyclic group, being a subgroup of the cyclic group of units of
`Multiplicative (ZMod n)`. -/
instance instHasEnoughRootsOfUnityMultiplicativeZMod (n : ℕ) :
    HasEnoughRootsOfUnity (Multiplicative (ZMod n)) n where
  prim := ⟨_, ZMod.isPrimitiveRoot_ofAdd_one n⟩
  cyc := by
    have : IsCyclic (Multiplicative (ZMod n))ˣ :=
      isCyclic_of_surjective toUnits toUnits.surjective
    infer_instance

/-- **`ℤ/n` written multiplicatively has enough roots of unity for every monoid killed by `n`**:
the exponent of such a monoid divides `n`. This is the hypothesis of Mathlib's duality theory for
finite abelian groups, `CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity` and
`CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity`, with the target `Multiplicative (ZMod n)`. -/
theorem hasEnoughRootsOfUnity_multiplicative_zmod_exponent {n : ℕ} [NeZero n] {M : Type*}
    [AddMonoid M] (hM : ∀ x : M, n • x = 0) :
    HasEnoughRootsOfUnity (Multiplicative (ZMod n)) (Monoid.exponent (Multiplicative M)) :=
  HasEnoughRootsOfUnity.of_dvd _ (Monoid.exponent_dvd_of_forall_pow_eq_one fun g => by
    rw [← ofAdd_toAdd g, ← ofAdd_nsmul, hM, ofAdd_zero])

end TauCeti

namespace IsPrimitiveRoot

variable {R : Type*} [CommRing R] [IsDomain R] {k : ℕ} [NeZero k] {ζ : Rˣ}

/-- **`ℤ/k` is the group of `k`-th roots of unity**, written additively, once a primitive `k`-th
root of unity is chosen: that root generates `μ_k`, so `zmodEquivZPowers` already lands on all of
it. -/
noncomputable def zmodEquivRootsOfUnity (h : IsPrimitiveRoot ζ k) :
    ZMod k ≃+ Additive (rootsOfUnity k R) :=
  h.zmodEquivZPowers.trans (MulEquiv.toAdditive (MulEquiv.subgroupCongr h.zpowers_eq))

/-- **The equivalence sends the class of an integer `i` to `ζ ^ i`**, which determines it on all
of `ZMod k` since every class is the class of an integer. -/
@[simp]
theorem coe_zmodEquivRootsOfUnity_apply_intCast (h : IsPrimitiveRoot ζ k) (i : ℤ) :
    ((h.zmodEquivRootsOfUnity (i : ZMod k)).toMul : Rˣ) = ζ ^ i := by
  simp [zmodEquivRootsOfUnity]

/-- **The equivalence sends the class of a natural number `i` to `ζ ^ i`**, the natural-exponent
reading of `coe_zmodEquivRootsOfUnity_apply_intCast`. -/
@[simp]
theorem coe_zmodEquivRootsOfUnity_apply_natCast (h : IsPrimitiveRoot ζ k) (i : ℕ) :
    ((h.zmodEquivRootsOfUnity (i : ZMod k)).toMul : Rˣ) = ζ ^ i := by
  simpa using coe_zmodEquivRootsOfUnity_apply_intCast h i

/-- **The inverse sends `ζ ^ i` back to the class of `i`**, for an integer exponent. -/
@[simp]
theorem zmodEquivRootsOfUnity_symm_apply_zpow (h : IsPrimitiveRoot ζ k) (i : ℤ)
    (hi : ζ ^ i ∈ rootsOfUnity k R) :
    h.zmodEquivRootsOfUnity.symm (Additive.ofMul ⟨ζ ^ i, hi⟩) = (i : ZMod k) :=
  (AddEquiv.symm_apply_eq _).2 (Additive.toMul.injective (Subtype.ext
    (coe_zmodEquivRootsOfUnity_apply_intCast h i).symm))

/-- **The inverse sends `ζ ^ i` back to the class of `i`**, for a natural exponent. -/
@[simp]
theorem zmodEquivRootsOfUnity_symm_apply_pow (h : IsPrimitiveRoot ζ k) (i : ℕ)
    (hi : ζ ^ i ∈ rootsOfUnity k R) :
    h.zmodEquivRootsOfUnity.symm (Additive.ofMul ⟨ζ ^ i, hi⟩) = (i : ZMod k) :=
  (AddEquiv.symm_apply_eq _).2 (Additive.toMul.injective (Subtype.ext
    (coe_zmodEquivRootsOfUnity_apply_natCast h i).symm))

end IsPrimitiveRoot

end

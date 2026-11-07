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

A primitive `k`-th root of unity in a commutative monoid generates the group `μ_k` of all `k`-th
roots of unity as soon as that group is cyclic (as it is over any domain), so `μ_k` has exactly `k`
elements and Mathlib's `zmodAddEquivOfGenerator` identifies `ℤ/k` with the whole of `μ_k`.

Mathlib has `IsPrimitiveRoot.zmodEquivZPowers`, which identifies `ℤ/k` with the powers of a
primitive root in a commutative ring, and proves that the powers exhaust `μ_k` over a domain
(`IsPrimitiveRoot.zpowers_eq`), but not the composite, which is what a consumer phrased in terms of
`μ_k` rather than a chosen generator needs.

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
* `IsPrimitiveRoot.zpowers_eq_of_isCyclic`: a primitive `k`-th root generates `μ_k` once `μ_k` is
  cyclic.
* `IsPrimitiveRoot.zmodEquivRootsOfUnity`: `ℤ/k ≃+ Additive (μ_k)`, given a primitive `k`-th root
  and a cyclic `μ_k`.
* `IsPrimitiveRoot.coe_zmodEquivRootsOfUnity_apply_intCast` and
  `IsPrimitiveRoot.coe_zmodEquivRootsOfUnity_apply_natCast`: it sends `i` to `ζ ^ i`.
* `IsPrimitiveRoot.zmodEquivRootsOfUnity_symm_apply_zpow` and
  `IsPrimitiveRoot.zmodEquivRootsOfUnity_symm_apply_pow`: its inverse sends `ζ ^ i` back to `i`.

## Provenance

`IsPrimitiveRoot.zmodEquivRootsOfUnity` is ported from AINTLIB (`github.com/CBirkbeck/AINTLIB`,
Apache-2.0) @ `a302aeacd86053f9d5f991fbbf664e1cc1051d08`, source file
`projects/HasseWeil/HasseWeil/HasseBound/WeilPairing/RootsOfUnity.lean`, declaration
`rootsOfUnity_addEquiv_zmod`. Three changes: the direction is reversed to start from `ZMod k`, so
that it reads like `IsPrimitiveRoot.zmodEquivZPowers` which it extends; the base is generalised from
a field to any commutative monoid whose `k`-th roots of unity form a cyclic group, which is all
`zpowers_eq_of_isCyclic` asks for; and the four characterising lemmas below — the equivalence and
its inverse, each at an integer and at a natural exponent — are added, none of which the source
has. The remaining declarations of this file — `zpowers_eq_of_isCyclic`, the `ZMod k`-module
structure on `μ_k` written additively and the roots of unity of `Multiplicative (ZMod n)` — have no
counterpart in that source.
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
  simpa using IsPrimitiveRoot.orderOf (Multiplicative.ofAdd (1 : ZMod n))

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
  HasEnoughRootsOfUnity.of_dvd _ <|
    Monoid.exponent_multiplicative (G := M) ▸ AddMonoid.exponent_dvd_of_forall_nsmul_eq_zero hM

end TauCeti

namespace IsPrimitiveRoot

variable {M : Type*} [CommMonoid M] {k : ℕ} [NeZero k] [IsCyclic (rootsOfUnity k M)] {ζ : Mˣ}

/-- **A primitive `k`-th root of unity generates `μ_k` once `μ_k` is cyclic**. This extends
Mathlib's `IsPrimitiveRoot.zpowers_eq` from domains, where `μ_k` is always cyclic, to any
commutative monoid. -/
theorem zpowers_eq_of_isCyclic (h : IsPrimitiveRoot ζ k) :
    Subgroup.zpowers ζ = rootsOfUnity k M := by
  have : HasEnoughRootsOfUnity M k := ⟨⟨ζ, coe_units_iff.2 h⟩, ‹_›⟩
  refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le_of_mem h.pow_eq_one) ?_
  rw [HasEnoughRootsOfUnity.natCard_rootsOfUnity, Nat.card_zpowers, h.eq_orderOf]

/-- **`ℤ/k` is the group of `k`-th roots of unity**, written additively, once a primitive `k`-th
root of unity is chosen and `μ_k` is cyclic (as it is over a domain): that root then generates
`μ_k`, which therefore has `k` elements, so `zmodAddEquivOfGenerator` applies to it. -/
noncomputable def zmodEquivRootsOfUnity (h : IsPrimitiveRoot ζ k) :
    ZMod k ≃+ Additive (rootsOfUnity k M) :=
  zmodAddEquivOfGenerator (g := Additive.ofMul ⟨ζ, h.mem_rootsOfUnity⟩)
    (fun x => by
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 (h.zpowers_eq_of_isCyclic.ge x.toMul.2)
      exact ⟨i, Additive.toMul.injective (Subtype.ext hi)⟩)
    (by rw [Nat.card_congr Additive.toMul, ← h.zpowers_eq_of_isCyclic, Nat.card_zpowers,
      h.eq_orderOf])

/-- **The equivalence sends the class of an integer `i` to `ζ ^ i`**, which determines it on all
of `ZMod k` since every class is the class of an integer. -/
@[simp]
theorem coe_zmodEquivRootsOfUnity_apply_intCast (h : IsPrimitiveRoot ζ k) (i : ℤ) :
    ((h.zmodEquivRootsOfUnity (i : ZMod k)).toMul : Mˣ) = ζ ^ i := by
  simp [zmodEquivRootsOfUnity]

/-- **The equivalence sends the class of a natural number `i` to `ζ ^ i`**, the natural-exponent
reading of `coe_zmodEquivRootsOfUnity_apply_intCast`. -/
@[simp]
theorem coe_zmodEquivRootsOfUnity_apply_natCast (h : IsPrimitiveRoot ζ k) (i : ℕ) :
    ((h.zmodEquivRootsOfUnity (i : ZMod k)).toMul : Mˣ) = ζ ^ i := by
  simpa using coe_zmodEquivRootsOfUnity_apply_intCast h i

/-- **The inverse sends `ζ ^ i` back to the class of `i`**, for an integer exponent. -/
@[simp]
theorem zmodEquivRootsOfUnity_symm_apply_zpow (h : IsPrimitiveRoot ζ k) (i : ℤ)
    (hi : ζ ^ i ∈ rootsOfUnity k M) :
    h.zmodEquivRootsOfUnity.symm (Additive.ofMul ⟨ζ ^ i, hi⟩) = (i : ZMod k) :=
  (AddEquiv.symm_apply_eq _).2 (Additive.toMul.injective (Subtype.ext
    (coe_zmodEquivRootsOfUnity_apply_intCast h i).symm))

/-- **The inverse sends `ζ ^ i` back to the class of `i`**, for a natural exponent. -/
@[simp]
theorem zmodEquivRootsOfUnity_symm_apply_pow (h : IsPrimitiveRoot ζ k) (i : ℕ)
    (hi : ζ ^ i ∈ rootsOfUnity k M) :
    h.zmodEquivRootsOfUnity.symm (Additive.ofMul ⟨ζ ^ i, hi⟩) = (i : ZMod k) :=
  (AddEquiv.symm_apply_eq _).2 (Additive.toMul.injective (Subtype.ext
    (coe_zmodEquivRootsOfUnity_apply_natCast h i).symm))

end IsPrimitiveRoot

end

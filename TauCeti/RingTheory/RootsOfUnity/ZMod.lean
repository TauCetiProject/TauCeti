/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# The `k`-th roots of unity of a domain, as `ℤ/k`

A primitive `k`-th root of unity generates the group of all `k`-th roots of unity, so Mathlib's
`IsPrimitiveRoot.zmodEquivZPowers`, which identifies `ℤ/k` with the powers of a chosen primitive
root, identifies it with the whole of `μ_k`.

Both halves are in Mathlib — `IsPrimitiveRoot.zmodEquivZPowers` and `IsPrimitiveRoot.zpowers_eq` —
but not the composite, which is what a consumer phrased in terms of `μ_k` rather than a chosen
generator needs.

## Main results

* `IsPrimitiveRoot.zmodEquivRootsOfUnity`: `ℤ/k ≃+ Additive (μ_k)`, given a primitive `k`-th root.
* `IsPrimitiveRoot.coe_zmodEquivRootsOfUnity_apply_intCast` and
  `IsPrimitiveRoot.coe_zmodEquivRootsOfUnity_apply_natCast`: it sends `i` to `ζ ^ i`.
* `IsPrimitiveRoot.zmodEquivRootsOfUnity_symm_apply_zpow` and
  `IsPrimitiveRoot.zmodEquivRootsOfUnity_symm_apply_pow`: its inverse sends `ζ ^ i` back to `i`.

## Provenance

Ported from AINTLIB (`github.com/CBirkbeck/AINTLIB`, Apache-2.0) @
`a302aeacd86053f9d5f991fbbf664e1cc1051d08`, source file
`projects/HasseWeil/HasseWeil/HasseBound/WeilPairing/RootsOfUnity.lean`, declaration
`rootsOfUnity_addEquiv_zmod`. Three changes: the direction is reversed to start from `ZMod k`, so
that it reads like `IsPrimitiveRoot.zmodEquivZPowers` which it extends; the base is a domain rather
than a field, which is all `zpowers_eq` asks for; and the four characterising lemmas below — the
equivalence and its inverse, each at an integer and at a natural exponent — are added, none of
which the source has.
-/

public section

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

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Central.Defs
public import Mathlib.Algebra.Star.Basic

import Mathlib.Algebra.Star.Center

/-!
# The involution induced on the centre of a central star algebra

Let `B` be a star ring which is a central algebra over a field `K`. The involution `x ↦ x*` maps
the centre of `B`, the image of `K`, into itself, and since `K` is commutative it restricts to a
ring endomorphism `σ` of `K` with `σ² = id` (`TauCeti.Algebra.centerInvolution`). An involution of
a central simple algebra is of the first kind when `σ` is the identity and of the second kind
otherwise.

## Main definitions

* `TauCeti.Algebra.centerInvolution K B`: the involution induced on the centre `K` of `B`.

## Main results

* `TauCeti.Algebra.algebraMap_centerInvolution`: `σ` is the restriction of `x ↦ x*`.
* `TauCeti.Algebra.centerInvolution_centerInvolution`: `σ² = id`.

## References

* M.-A. Knus, A. Merkurjev, M. Rost, J.-P. Tignol, *The Book of Involutions*, §2.
-/

public section

namespace TauCeti.Algebra

variable (K : Type*) [Field K] (B : Type*) [Ring B] [StarRing B] [Algebra K B]
  [Algebra.IsCentral K B]

/-- The involution maps the image of `K` into itself. -/
theorem exists_algebraMap_eq_star (x : K) : ∃ y : K, algebraMap K B y = star (algebraMap K B x) :=
  Algebra.mem_bot.mp <| Algebra.IsCentral.out <|
    Set.star_mem_center ((Subalgebra.center K B).algebraMap_mem x)

variable [Nontrivial B]

/-- The **involution induced on the centre** `K` of `B`: `σ(x)` is the element of `K` with image
`(algebraMap K B x)*`. It is a ring endomorphism since `K` is commutative. -/
noncomputable def centerInvolution : K →+* K :=
  have hinj : Function.Injective (algebraMap K B) := (algebraMap K B).injective
  have hspec (x : K) : algebraMap K B (exists_algebraMap_eq_star K B x).choose =
      star (algebraMap K B x) := (exists_algebraMap_eq_star K B x).choose_spec
  { toFun x := (exists_algebraMap_eq_star K B x).choose
    map_one' := hinj (by rw [hspec, map_one, star_one])
    -- `star` reverses products, which is harmless since `algebraMap K B` has central image.
    map_mul' x y := hinj (by
      rw [hspec, map_mul, map_mul, hspec, hspec, Algebra.commutes, star_mul])
    map_zero' := hinj (by rw [hspec, map_zero, star_zero])
    map_add' x y := hinj (by rw [hspec, map_add, map_add, star_add, hspec, hspec]) }

/-- The induced involution is the restriction of `x ↦ x*` to `K`. -/
@[simp]
theorem algebraMap_centerInvolution (x : K) :
    algebraMap K B (centerInvolution K B x) = star (algebraMap K B x) :=
  (exists_algebraMap_eq_star K B x).choose_spec

/-- The induced involution of `K` is an involution: `σ(σ(x)) = x`. -/
@[simp]
theorem centerInvolution_centerInvolution (x : K) :
    centerInvolution K B (centerInvolution K B x) = x :=
  (algebraMap K B).injective <| by
    rw [algebraMap_centerInvolution, algebraMap_centerInvolution, star_star]

end TauCeti.Algebra

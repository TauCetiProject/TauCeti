/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.G2.ShortRoot.Frobenius
public import TauCeti.Algebra.Lie.G2.ShortRoot.SpecialIsogeny

/-!
# The special isogeny against the Frobenius of the type-G2 carrier

`Matrix.g2SpecialIsogeny` is the matrix formula for the special isogeny `τ` of type `G₂` in
characteristic three, and `TauCeti.G2ShortRoot.points` realizes the short-root carrier's points as
a subgroup of `GL₇`. The pinning equations on the carrier's four numbered simple root subgroups are
read off the weight basis in `TauCeti.Algebra.Lie.G2.ShortRoot.SpecialIsogeny`. This file adds the
remaining pinned equation: in characteristic three the square relation on the numbered simple root
subgroups is the carrier's own Frobenius at exponent one.

Only those elements are covered. The formula is not shown here to be multiplicative, to carry
points of the carrier to points of the carrier, or to have any property at a point outside the
pinned subgroups; the square relation below is the one on those elements, not an identity of
endomorphisms. The carrier is not identified with the pinned simply connected group scheme of type
`G₂`, and constructions made here transfer to that group scheme only along such an identification.

## Main results

* `TauCeti.G2ShortRoot.g2SpecialIsogeny_g2SpecialIsogeny_coe_rootSubgroupPoints_eq_frobenius`:
  **the square relation** on the carrier's numbered simple root subgroups, against the carrier's
  own Frobenius at exponent one.

## References

* R. Steinberg, *Endomorphisms of linear algebraic groups*, Memoirs AMS **80** (1968), §11.
* R. W. Carter, *Simple Groups of Lie Type*, §§12.3 and 13.4.
-/

public section

open Matrix

namespace TauCeti.G2ShortRoot

universe v

variable {A : Type v} [CommRing A]

/-- **The square relation on the carrier's numbered simple root subgroups**: applying the special
isogeny twice to a numbered simple-root point gives the carrier's Frobenius at exponent one of that
point. -/
theorem g2SpecialIsogeny_g2SpecialIsogeny_coe_rootSubgroupPoints_eq_frobenius [CharP A 3]
    (k : Fin 2 ⊕ Fin 2) (t : A) :
    g2SpecialIsogeny (g2SpecialIsogeny
        ((rootSubgroupPoints k A (Multiplicative.ofAdd t) :
          _root_.Matrix.GeneralLinearGroup (Fin 7) A) : Matrix (Fin 7) (Fin 7) A)) =
      ((frobenius 3 1 A (rootSubgroupPoints k A (Multiplicative.ofAdd t)) :
        _root_.Matrix.GeneralLinearGroup (Fin 7) A) : Matrix (Fin 7) (Fin 7) A) := by
  rw [frobenius_rootSubgroupPoints, g2SpecialIsogeny_g2SpecialIsogeny_coe_rootSubgroupPoints,
    toAdd_ofAdd]
  norm_num

end TauCeti.G2ShortRoot

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Two
public import Mathlib.Algebra.RingQuot
public import TauCeti.RingTheory.MilnorK.Basic
import Mathlib.Data.ZMod.Basic

/-!
# The Milnor K-ring modulo two

For a commutative ring `R`, the **Milnor K-ring modulo two** `TauCeti.MilnorK.ModTwo R` is the
quotient `K_*ᴹ(R) / 2` of the Milnor K-ring `TauCeti.MilnorK R` by the relation identifying `2`
with `0`. This file gives its quotient map, its universal property for ring homomorphisms out of
`K_*ᴹ(R)` killing `2`, its extensionality lemmas, and shows that it has characteristic two.

## Main definitions

* `TauCeti.MilnorK.ModTwo R`: the Milnor K-ring modulo two `K_*ᴹ(R) / 2`.
* `TauCeti.MilnorK.ModTwo.mk`: the quotient map `K_*ᴹ(R) →+* K_*ᴹ(R) / 2`.
* `TauCeti.MilnorK.ModTwo.lift`: a ring homomorphism out of `K_*ᴹ(R)` sending `2` to `0`
  descends to `K_*ᴹ(R) / 2`.

## Main results

* `TauCeti.MilnorK.ModTwo.ringHom_ext`: ring homomorphisms out of `K_*ᴹ(R) / 2` agreeing on the
  classes of degree-one symbols are equal.
* `TauCeti.MilnorK.ModTwo.instCharP`: `K_*ᴹ(R) / 2` has characteristic two.

## References

* J. Milnor, *Algebraic K-theory and quadratic forms*, Invent. Math. 9 (1970), 318–344, §1.
-/

public section

noncomputable section

namespace TauCeti

namespace MilnorK

variable {R : Type*} [CommRing R]

variable (R) in
/-- The **Milnor K-ring modulo two** `K_*ᴹ(R) / 2`: the quotient of the Milnor K-ring by the
relation identifying `2` with `0`. -/
abbrev ModTwo : Type _ :=
  RingQuot fun x y : MilnorK R ↦ x = 2 ∧ y = 0

/-- The quotient map `K_*ᴹ(R) →+* K_*ᴹ(R) / 2`. -/
def ModTwo.mk : MilnorK R →+* ModTwo R :=
  RingQuot.mkRingHom _

theorem ModTwo.mk_surjective : Function.Surjective (ModTwo.mk (R := R)) :=
  RingQuot.mkRingHom_surjective _

/-- `2 = 0` in the Milnor K-ring modulo two. -/
theorem ModTwo.two_eq_zero : (2 : ModTwo R) = 0 := by
  rw [← map_ofNat (ModTwo.mk (R := R)) 2, ← map_zero (ModTwo.mk (R := R))]
  exact RingQuot.mkRingHom_rel ⟨rfl, rfl⟩

/-- The **universal property** of the Milnor K-ring modulo two: a ring homomorphism out of
`K_*ᴹ(R)` sending `2` to `0` descends to `K_*ᴹ(R) / 2`. -/
def ModTwo.lift {A : Type*} [Semiring A] (f : MilnorK R →+* A) (hf : f 2 = 0) :
    ModTwo R →+* A :=
  RingQuot.lift ⟨f, by
    rintro _ _ ⟨rfl, rfl⟩
    rw [hf, map_zero]⟩

@[simp]
theorem ModTwo.lift_mk {A : Type*} [Semiring A] (f : MilnorK R →+* A) (hf : f 2 = 0)
    (x : MilnorK R) : ModTwo.lift f hf (ModTwo.mk x) = f x :=
  RingQuot.lift_mkRingHom_apply _ _ x

/-- Two ring homomorphisms out of the Milnor K-ring modulo two agreeing after composition with
`ModTwo.mk` are equal. -/
theorem ModTwo.ringHom_ext_mk {A : Type*} [Semiring A] {f g : ModTwo R →+* A}
    (h : f.comp ModTwo.mk = g.comp ModTwo.mk) : f = g :=
  RingQuot.ringQuot_ext _ _ h

/-- Ring homomorphisms out of the Milnor K-ring modulo two agreeing on the classes of degree-one
symbols are equal. -/
@[ext]
theorem ModTwo.ringHom_ext {A : Type*} [Semiring A] {f g : ModTwo R →+* A}
    (h : ∀ a : Rˣ, f (ModTwo.mk (ofUnit a)) = g (ModTwo.mk (ofUnit a))) : f = g :=
  ModTwo.ringHom_ext_mk (MilnorK.ringHom_ext h)

/-- The Milnor K-ring modulo two has characteristic two: `2 = 0`, and `1 ≠ 0` since the ring
homomorphism `K_*ᴹ(R) →+* ZMod 2` killing every degree-one class descends to it. -/
instance ModTwo.instCharP : CharP (ModTwo R) 2 :=
  CharTwo.of_one_ne_zero_of_two_eq_zero (fun h ↦ by
    let f : ModTwo R →+* ZMod 2 := ModTwo.lift (MilnorK.lift 0 fun _ _ _ ↦ zero_mul _) <| by
      rw [map_ofNat]
      exact CharTwo.two_eq_zero
    simpa using congrArg f h) ModTwo.two_eq_zero

end MilnorK

end TauCeti

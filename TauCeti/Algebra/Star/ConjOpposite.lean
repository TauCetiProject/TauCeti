/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Opposite
public import Mathlib.Basic.Complex.Basic

/-!
# The conjugate opposite of a complex algebra

For a complex algebra `A`, `TauCeti.ConjOpposite A` is the opposite ring `Aᵐᵒᵖ` on which complex
scalars act through complex conjugation, `r • x = conj r • x`. A complex algebra map
`B →ₐ[ℂ] ConjOpposite A` is the same as a conjugate-linear antimultiplicative map `B → A`, so star
structures on algebras given by a presentation are obtained from the universal property of the
presentation as complex algebra maps into `ConjOpposite`.

## Main definitions

* `TauCeti.ConjOpposite`: the opposite ring with conjugated complex scalar action.
* `TauCeti.ConjOpposite.toConj`, `TauCeti.ConjOpposite.ofConj`: the identifications with `A`.

## Implementation notes

The algebra structure is `Algebra.compHom` along `starRingEnd ℂ`. The scalars are fixed to `ℂ`
rather than an arbitrary commutative star ring because a type synonym taking the scalar ring as
an argument would not use it in its body.
-/

public section

namespace TauCeti

/-- The opposite ring of a complex algebra `A`, on which complex scalars act through complex
conjugation. A complex algebra map into it is a conjugate-linear antimultiplicative map into `A`. -/
@[expose]
def ConjOpposite (A : Type*) : Type _ := Aᵐᵒᵖ

namespace ConjOpposite

variable {A : Type*}

/-- An element of `A`, viewed in the conjugate opposite algebra. -/
def toConj (x : A) : ConjOpposite A := MulOpposite.op x

/-- The underlying element of `A` of an element of the conjugate opposite algebra. -/
def ofConj (x : ConjOpposite A) : A := MulOpposite.unop x

@[simp] theorem ofConj_toConj (x : A) : ofConj (toConj x) = x := (rfl)

@[simp] theorem toConj_ofConj (x : ConjOpposite A) : toConj (ofConj x) = x := (rfl)

theorem ofConj_injective : Function.Injective (ofConj : ConjOpposite A → A) :=
  MulOpposite.unop_injective

theorem toConj_injective : Function.Injective (toConj : A → ConjOpposite A) :=
  MulOpposite.op_injective

variable [Ring A]

instance : Ring (ConjOpposite A) := inferInstanceAs (Ring Aᵐᵒᵖ)

instance [Algebra ℂ A] : Algebra ℂ (ConjOpposite A) :=
  Algebra.compHom Aᵐᵒᵖ (starRingEnd ℂ)

@[simp] theorem ofConj_zero : ofConj (0 : ConjOpposite A) = 0 := (rfl)

@[simp] theorem ofConj_one : ofConj (1 : ConjOpposite A) = 1 := (rfl)

@[simp] theorem ofConj_add (x y : ConjOpposite A) : ofConj (x + y) = ofConj x + ofConj y := (rfl)

@[simp] theorem ofConj_sub (x y : ConjOpposite A) : ofConj (x - y) = ofConj x - ofConj y := (rfl)

@[simp] theorem ofConj_neg (x : ConjOpposite A) : ofConj (-x) = -ofConj x := (rfl)

/-- Multiplication in the conjugate opposite algebra is reversed. -/
@[simp] theorem ofConj_mul (x y : ConjOpposite A) : ofConj (x * y) = ofConj y * ofConj x := (rfl)

variable [Algebra ℂ A]

/-- Complex scalars act on the conjugate opposite algebra through complex conjugation. -/
@[simp] theorem ofConj_smul (r : ℂ) (x : ConjOpposite A) :
    ofConj (r • x) = star r • ofConj x := (rfl)

@[simp] theorem ofConj_algebraMap (r : ℂ) :
    ofConj (algebraMap ℂ (ConjOpposite A) r) = algebraMap ℂ A (star r) := (rfl)

end ConjOpposite

end TauCeti

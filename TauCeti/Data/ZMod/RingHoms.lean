/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.Data.ZMod.Basic

/-!
# Surjectivity of integer reduction

The canonical map from `ℤ` to `ZMod n` is surjective, including at modulus zero.
The instance makes semilinear submodule images along integer reduction available.
It also supplies the unique canonical ring homomorphism `ZMod.castULiftHom : ULift (ZMod n) →+* R`
when `(n : R) = 0`, used at `n = 2` for scalar extension of mod-two manifold orientations.
-/

public section

universe u

namespace ZMod

/-- Integer reduction is surjective for every modulus. -/
instance (n : ℕ) : RingHomSurjective (Int.castRingHom (ZMod n)) :=
  ⟨intCast_surjective⟩

/-- There is at most one ring homomorphism out of `ULift (ZMod n)`. -/
instance subsingleton_ulift_ringHom {n : ℕ} {R : Type*} [Semiring R] :
    Subsingleton (ULift.{u} (ZMod n) →+* R) :=
  ⟨fun f g ↦ let e : ZMod n →+* ULift.{u} (ZMod n) := ULift.ringEquiv.symm.toRingHom
    have h : f.comp e = g.comp e := Subsingleton.elim _ _
    RingHom.ext fun x ↦ by simpa [e] using RingHom.congr_fun h (ULift.ringEquiv x)⟩
/-- The canonical ring homomorphism `ULift (ZMod n) →+* R` into any ring with `(n : R) = 0`. -/
noncomputable def castULiftHom {n : ℕ} (R : Type*) [Ring R] (hn : (n : R) = 0) :
    ULift.{u} (ZMod n) →+* R := (castHom (ringChar.dvd hn) R).comp ULift.ringEquiv.toRingHom
/-- `ZMod.castULiftHom` evaluates on `ULift.up a` as `ZMod.cast a`. -/
@[simp] theorem castULiftHom_up {n : ℕ} (R : Type*) [Ring R] (hn : (n : R) = 0) (a : ZMod n) :
    castULiftHom.{u} R hn (ULift.up a) = cast a := castHom_apply (h := ringChar.dvd hn) a
end ZMod

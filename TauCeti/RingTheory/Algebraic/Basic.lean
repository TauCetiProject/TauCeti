/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Algebraic.Basic
public import Mathlib.RingTheory.Algebraic.Integral

/-!
# Transcendental elements under translations and algebra maps

Adding a base-ring constant to a transcendental element preserves transcendence, over an
arbitrary commutative ring and in an arbitrary ring algebra. So does applying an injective algebra
homomorphism, the transcendental counterpart of Mathlib's `isAlgebraic_algHom_iff`.
An algebraic extension of scalars without zero divisors also preserves transcendence
under an injective algebra map into a common overring.
Dually, every root in `A` of a polynomial over `R` is algebraic over `R`
(`isAlgebraic_of_mem_aroots`).
-/

public section

open Polynomial

/-- A root in `A` of a polynomial over `R` is algebraic over `R`. -/
theorem isAlgebraic_of_mem_aroots {R A : Type*} [CommRing R] [CommRing A] [IsDomain A]
    [Algebra R A] {p : R[X]} {x : A} (hx : x ∈ p.aroots A) : IsAlgebraic R x :=
  ⟨p, fun hp ↦ by simp [hp] at hx, (mem_aroots'.1 hx).2⟩

namespace Transcendental

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A] {x : A}

/-- Translating a transcendental element by a constant keeps it transcendental. -/
theorem add_algebraMap (hx : Transcendental R x) (c : R) :
    Transcendental R (x + algebraMap R A c) := by
  rw [transcendental_iff] at hx ⊢
  intro p hp
  apply (comp_X_add_C_eq_zero_iff (t := c)).mp
  apply hx
  simpa only [aeval_comp, map_add, aeval_X, aeval_C] using hp

/-- An injective algebra homomorphism carries a transcendental element to a transcendental
element. -/
protected theorem algHom {B G : Type*} [Ring B] [Algebra R B] [FunLike G A B] [AlgHomClass G R A B]
    (f : G) (hf : Function.Injective f) (hx : Transcendental R x) : Transcendental R (f x) :=
  (isAlgebraic_algHom_iff (AlgHom.ofClass f) hf).not.mpr hx

/-- An algebraic extension of scalars without zero divisors preserves transcendence after an
injective algebra map into a common overring. -/
theorem algebraMap_of_isAlgebraic {R S A B : Type*}
    [CommRing R] [CommRing S] [NoZeroDivisors S] [CommRing A] [Ring B]
    [Algebra R S] [Algebra R A] [Algebra R B] [Algebra S B] [Algebra A B]
    [IsScalarTower R S B] [IsScalarTower R A B] [Algebra.IsAlgebraic R S]
    [FaithfulSMul A B] {x : A} (hx : Transcendental R x) :
    Transcendental S (algebraMap A B x) :=
  ((transcendental_algebraMap_iff (FaithfulSMul.algebraMap_injective A B)).2 hx).extendScalars S

end Transcendental

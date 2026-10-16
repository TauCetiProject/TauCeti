/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Ideal.Quotient.Defs

/-!
# The `p`-th power map modulo a square-zero ideal

Let `B` be a commutative ring in which a prime `p` is zero, and let `I` be an ideal of `B` with
`I ^ 2 = ⊥`. Two lifts of an element of `B ⧸ I` differ by some `i ∈ I`, and `i ^ p = 0`, so their
`p`-th powers agree. The `p`-th power map of `B` therefore factors through `B ⧸ I` as a ring
homomorphism `B ⧸ I →+* B`.

## Main definitions

* `Ideal.Quotient.powLift`: the ring homomorphism `B ⧸ I →+* B` sending the class of `b` to
  `b ^ p`.
-/

public section

namespace Ideal.Quotient

variable {B : Type*} [CommRing B] (p : ℕ) [hp : Fact p.Prime]

/-- Modulo a square-zero ideal of a ring in which `p = 0`, the `p`-th power of a lift does not
depend on the lift: the `p`-th power map factors through `B ⧸ I`. -/
def powLift (hpB : (p : B) = 0) {I : Ideal B} (hI : I ^ 2 = ⊥) : B ⧸ I →+* B :=
  lift I
    { toFun := (· ^ p)
      map_one' := one_pow p
      map_mul' := fun x y ↦ mul_pow x y p
      map_zero' := zero_pow hp.out.ne_zero
      map_add' := fun x y ↦ by
        simp only [add_pow_prime_eq' hp.out, hpB, zero_mul, add_zero] }
    fun i hi ↦ by
      have hi2 : i ^ 2 = 0 := by simpa [hI] using pow_mem_pow hi 2
      exact pow_eq_zero_of_le hp.out.two_le hi2

variable (hpB : (p : B) = 0) {I : Ideal B} (hI : I ^ 2 = ⊥)

/-- `powLift` sends the class of `b` to `b ^ p`. -/
@[simp]
theorem powLift_mk (b : B) : powLift p hpB hI (mk I b) = b ^ p :=
  lift_mk _ _ _

/-- Reducing `powLift p hpB hI z` modulo `I` gives `z ^ p`. -/
@[simp]
theorem mk_powLift (z : B ⧸ I) : mk I (powLift p hpB hI z) = z ^ p := by
  obtain ⟨b, rfl⟩ := mk_surjective z
  rw [powLift_mk, map_pow]

end Ideal.Quotient

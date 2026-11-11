/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import TauCeti.Algebra.CharP.Frobenius.PowRingHom

/-!
# The `p`-th power map modulo an ideal whose `p`-th power vanishes

Let `B` be a commutative ring in which a prime `p` is zero, and let `I` be an ideal of `B` with
`I ^ p = ⊥`, for instance a square-zero ideal. Two lifts of an element of `B ⧸ I` differ by some
`i ∈ I`, and `i ^ p = 0`, so their `p`-th powers agree. The `p`-th power map `TauCeti.powRingHom`
of `B` therefore factors through `B ⧸ I` as a ring homomorphism `B ⧸ I →+* B`.

## Main definitions

* `Ideal.Quotient.powLift`: the ring homomorphism `B ⧸ I →+* B` sending the class of `b` to
  `b ^ p`.
-/

public section

namespace Ideal.Quotient

variable {B : Type*} [CommRing B] (p : ℕ) [Fact p.Prime]

/-- Modulo an ideal `I` with `I ^ p = ⊥` of a ring in which the prime `p` vanishes, the `p`-th
power of a lift does not depend on the lift: the `p`-th power map factors through `B ⧸ I`. -/
def powLift (hpB : (p : B) = 0) {I : Ideal B} (hI : I ^ p = ⊥) : B ⧸ I →+* B :=
  lift I (TauCeti.powRingHom B p hpB) fun i hi ↦ by simpa [hI] using pow_mem_pow hi p

variable (hpB : (p : B) = 0) {I : Ideal B} (hI : I ^ p = ⊥)

/-- `powLift` sends the class of `b` to `b ^ p`. -/
@[simp]
theorem powLift_mk (b : B) : powLift p hpB hI (mk I b) = b ^ p := by
  rw [powLift, lift_mk, TauCeti.powRingHom_apply]

/-- Reducing `powLift p hpB hI z` modulo `I` gives `z ^ p`. -/
@[simp]
theorem mk_powLift (z : B ⧸ I) : mk I (powLift p hpB hI z) = z ^ p := by
  obtain ⟨b, rfl⟩ := mk_surjective z
  rw [powLift_mk, map_pow]

end Ideal.Quotient

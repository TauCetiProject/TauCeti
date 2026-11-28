/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Artinian.Module
import TauCeti.RingTheory.Semisimple.NilpotentIdeal

/-!
# Semiprime semiprimary rings are semisimple

A ring `R` is *semiprime* when no nonzero `x : R` has `x * y * x = 0` for every `y : R`, that is,
when `R` has no nonzero two-sided ideal of square zero. For a semiprimary ring, one whose Jacobson
radical is nilpotent with semisimple quotient, in particular for an Artinian ring, this condition
is equivalent to semisimplicity:

* a semisimple ring is semiprime: if `x * y * x = 0` for all `y`, the left ideal `R x` has
  square zero, and a semisimple ring has no nonzero nil left ideal;
* a semiprime semiprimary ring is semisimple: its Jacobson radical `J` is nilpotent, and if
  `J ^ (n + 2) = 0` then every `x ∈ J ^ (n + 1)` has `x * y * x ∈ J ^ (n + 2) = 0`, so descending
  in `n` gives `J = 0`, and then `R = R ⧸ J` is semisimple.

The condition is stated elementwise because it is the form in which it is verified on the span of
a representation, where it reads `x * ρ g * x = 0` for all `g`. For commutative rings it is
reducedness, and the second statement extends `IsArtinianRing.isSemisimpleRing_of_isReduced`.

## Main results

* `IsSemisimpleRing.eq_zero_of_forall_mul_mul_eq_zero`: a semisimple ring is semiprime.
* `IsSemiprimaryRing.isSemisimpleRing_of_forall_eq_zero_of_forall_mul_mul_eq_zero`: a semiprime
  semiprimary ring, for instance a semiprime Artinian ring, is semisimple.
* `IsSemiprimaryRing.isSemisimpleRing_iff_forall_eq_zero_of_forall_mul_mul_eq_zero`: the two
  together.

## References

* T. Y. Lam, *A First Course in Noncommutative Rings*, second edition, §10 (semiprime rings).
-/

public section

variable {R : Type*} [Ring R]

/-- **A semisimple ring is semiprime.** If `x * y * x = 0` for every `y`, then `x = 0`. -/
theorem IsSemisimpleRing.eq_zero_of_forall_mul_mul_eq_zero [IsSemisimpleRing R] {x : R}
    (h : ∀ y, x * y * x = 0) : x = 0 := by
  -- The left ideal `R x` has square zero: `(a * x) * (a * x) = a * (x * a * x) = 0`.
  have hI : Submodule.span R {x} = ⊥ := Submodule.eq_bot_of_forall_isNilpotent fun z hz ↦ by
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hz
    refine ⟨2, ?_⟩
    rw [smul_eq_mul, pow_two, mul_assoc, ← mul_assoc x, h, mul_zero]
  simpa using hI

namespace IsSemiprimaryRing

/-- **A semiprime semiprimary ring is semisimple.** If no nonzero `x` has `x * y * x = 0` for
every `y`, then the Jacobson radical, which is nilpotent, vanishes. This applies to every Artinian
ring. -/
theorem isSemisimpleRing_of_forall_eq_zero_of_forall_mul_mul_eq_zero [IsSemiprimaryRing R]
    (h : ∀ x : R, (∀ y, x * y * x = 0) → x = 0) : IsSemisimpleRing R := by
  set J := Ring.jacobson R
  -- If `J ^ (n + 2) = 0`, each `x ∈ J ^ (n + 1)` has `x * y * x ∈ J ^ (n + 1) * J = J ^ (n + 2)`.
  have step (n : ℕ) (hn : J ^ (n + 2) = ⊥) : J ^ (n + 1) = ⊥ := by
    refine eq_bot_iff.mpr fun x hx ↦ (Submodule.mem_bot R).mpr <| h x fun y ↦ ?_
    have hxJ : x ∈ J := by
      rw [Ideal.IsTwoSided.pow_succ] at hx
      exact Ideal.mul_le_left hx
    have hmem : x * y * x ∈ J ^ (n + 2) := by
      rw [Ideal.IsTwoSided.pow_add (I := J) (n + 1) 1, Submodule.pow_one]
      exact Submodule.mul_mem_mul (Ideal.mul_mem_right y _ hx) hxJ
    simpa [hn] using hmem
  have desc (n : ℕ) (hn : J ^ (n + 1) = ⊥) : J = ⊥ := by
    induction n with
    | zero => simpa only [zero_add, Submodule.pow_one] using hn
    | succ n ih => exact ih (step n hn)
  have hJ : J = ⊥ := by
    obtain ⟨n, hn⟩ := IsSemiprimaryRing.isNilpotent (R := R)
    cases n with
    | zero =>
      -- `J ^ 0 = ⊤`, so the hypothesis says `⊤ = ⊥`.
      rw [Submodule.pow_zero, Ideal.one_eq_top] at hn
      exact le_bot_iff.mp (le_top.trans_eq (hn.trans Submodule.zero_eq_bot))
    | succ n => exact desc n hn
  -- `R ⧸ J` is semisimple, and `R ⧸ J = R ⧸ ⊥ ≃ R`.
  exact ((Ideal.quotEquivOfEq hJ).trans (RingEquiv.quotientBot R)).isSemisimpleRing

/-- **A semiprimary ring, for instance an Artinian ring, is semisimple exactly when it is
semiprime**: when no nonzero `x` has `x * y * x = 0` for every `y`. -/
theorem isSemisimpleRing_iff_forall_eq_zero_of_forall_mul_mul_eq_zero [IsSemiprimaryRing R] :
    IsSemisimpleRing R ↔ ∀ x : R, (∀ y, x * y * x = 0) → x = 0 :=
  ⟨fun _ _ ↦ IsSemisimpleRing.eq_zero_of_forall_mul_mul_eq_zero,
    isSemisimpleRing_of_forall_eq_zero_of_forall_mul_mul_eq_zero⟩

end IsSemiprimaryRing

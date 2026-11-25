/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.ZMod.LocalRing
public import TauCeti.Data.ZMod.LocalRing
public import TauCeti.Data.ZMod.Nilpotent
public import TauCeti.LinearAlgebra.Quotient.ScalarMap
public import TauCeti.RingTheory.LocalRing.MaximalIdeal.Generator

/-!
# Checks for multiplication by a scalar between quotients by ideals

Over `ℤ ⧸ p ^ 2`, with maximal ideal `(p)`:

* the kernel of multiplication by `p` on `ℤ ⧸ p ^ 2` is the ideal `(p)`, so multiplication by `p`
  is an injective map `(ℤ ⧸ p ^ 2) ⧸ (p) → ℤ ⧸ p ^ 2`;
* the scalar `1` does not carry the ideal `(p)` into `0`, so it defines no such map;
* for the module `M = (ℤ ⧸ p ^ 2) ⧸ (p)`, which is not free, multiplication by `p` from `M ⧸ p M`
  to `M` is zero on a nonzero module, although the colon condition `(0 : p) = (p)` holds; freeness
  cannot be dropped from `Ideal.smulMapQ_injective_iff`.
-/

public section

open IsLocalRing

namespace TauCeti.ScalarMapChecks

variable (p : ℕ) [Fact p.Prime]

/-- The kernel of multiplication by `p` on `ℤ ⧸ p ^ 2` is the ideal `(p)`. -/
example : (⊥ : Ideal (ZMod (p ^ 2))).colon {(p : ZMod (p ^ 2))} =
    Ideal.span {(p : ZMod (p ^ 2))} := by
  have h := TauCeti.IsLocalRing.maximalIdeal_pow_colon_pow
    (ZMod.maximalIdeal_prime_pow_eq_span p 2) (by norm_num : 1 ≤ 2)
    (by simpa using ZMod.natCast_self_pow_ne_zero (Fact.out : p.Prime).one_lt one_lt_two)
  -- The square of the maximal ideal `(p)` is zero.
  have hsq : maximalIdeal (ZMod (p ^ 2)) ^ 2 = ⊥ := by
    rw [ZMod.maximalIdeal_prime_pow_eq_span, Ideal.span_singleton_pow, ← Nat.cast_pow,
      ZMod.natCast_self, Ideal.span_singleton_eq_bot]
  rwa [hsq, pow_one, pow_one, ZMod.maximalIdeal_prime_pow_eq_span] at h

/-- Multiplication by `p` is injective from `R ⧸ (p)` to `R ⧸ 0`, for `R = ℤ ⧸ p ^ 2`. -/
example : Function.Injective (Ideal.smulMapQ (ZMod (p ^ 2)) ((p : ZMod (p ^ 2)) ^ (2 - 1))
    (Ideal.pow_le_colon_singleton_pow (I := maximalIdeal (ZMod (p ^ 2)))
      (TauCeti.IsLocalRing.mem_maximalIdeal_of_eq_span (ZMod.maximalIdeal_prime_pow_eq_span p 2))
      (by norm_num : 1 ≤ 2))) :=
  Ideal.smulMapQ_injective_pow (ZMod.maximalIdeal_prime_pow_eq_span p 2) (by norm_num)
    (by simpa using ZMod.natCast_self_pow_ne_zero (Fact.out : p.Prime).one_lt one_lt_two)

/-- The scalar `1` does not carry `(p)` into `0` in `ℤ ⧸ p ^ 2`. -/
example : ¬ Ideal.span {(p : ZMod (p ^ 2))} ≤ (⊥ : Ideal (ZMod (p ^ 2))).colon {1} := fun h ↦
  ZMod.natCast_self_pow_ne_zero (Fact.out : p.Prime).one_lt one_lt_two
    (by simpa using h (Ideal.mem_span_singleton_self _))

/-- Over `R = ℤ ⧸ p ^ 2`, multiplication by `p` from `M ⧸ p M` to `M` is not injective for the
nonfree module `M = R ⧸ (p)`, although `(0 : p) = (p)`. -/
example
    (h : Ideal.span {(p : ZMod (p ^ 2))} ≤ (⊥ : Ideal (ZMod (p ^ 2))).colon {(p : ZMod (p ^ 2))}) :
    ¬ Function.Injective
      (Ideal.smulMapQ (ZMod (p ^ 2) ⧸ Ideal.span {(p : ZMod (p ^ 2))}) (p : ZMod (p ^ 2)) h) := by
  intro hinj
  set I := Ideal.span {(p : ZMod (p ^ 2))}
  -- `p` kills `R ⧸ (p)`, so `(p) • (R ⧸ (p))` is zero.
  have hbot : I • (⊤ : Submodule (ZMod (p ^ 2)) (ZMod (p ^ 2) ⧸ I)) = ⊥ := by
    refine eq_bot_iff.mpr (Submodule.smul_le.mpr fun a ha y _ ↦ ?_)
    induction y using Submodule.Quotient.induction_on with | H y => ?_
    rw [Submodule.mem_bot, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact I.mul_mem_right y ha
  have hone : Ideal.Quotient.mk I 1 ≠ 0 := by
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem, ← Ideal.eq_top_iff_one, Ideal.span_singleton_eq_top]
    intro hu
    exact (mem_maximalIdeal _).mp
      (TauCeti.IsLocalRing.mem_maximalIdeal_of_eq_span (ZMod.maximalIdeal_prime_pow_eq_span p 2)) hu
  have hzero : Ideal.smulMapQ (ZMod (p ^ 2) ⧸ I) (p : ZMod (p ^ 2)) h
      (Submodule.Quotient.mk (Ideal.Quotient.mk I 1)) =
      Ideal.smulMapQ (ZMod (p ^ 2) ⧸ I) (p : ZMod (p ^ 2)) h 0 := by
    rw [Ideal.smulMapQ_mk, map_zero, Submodule.Quotient.mk_eq_zero]
    simpa [Algebra.smul_def] using
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self (p : ZMod (p ^ 2)))
  have := hinj hzero
  rw [Submodule.Quotient.mk_eq_zero, hbot, Submodule.mem_bot] at this
  exact hone this

end TauCeti.ScalarMapChecks

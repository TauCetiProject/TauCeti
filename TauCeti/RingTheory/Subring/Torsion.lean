/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients.Basic
public import Mathlib.RingTheory.QuotSMulTop

/-!
# Integer torsion and reduction in subrings

Let `S` be a subring of `R`, and let `n : ℕ` have nonzero image in `R`. If `R` has no zero
divisors, then `S` has no `n`-torsion. If `S` is commutative and has finite quotients by nonzero
ideals, then its additive reduction `S ⧸ nS` is finite.

The hypotheses use the cast into the ambient ring, so these instances apply directly to rings
of integers in valued fields without a separate nonvanishing assumption on the subring cast.

## Main results

* `Subring.subsingleton_torsionBy`: no `n`-torsion in a subring of a ring without zero divisors.
* `Subring.finite_quotSMulTop`: finite reduction modulo `n` in a subring with finite quotients.
-/

public section

open scoped Pointwise

namespace Subring

/-- A subring of a ring without zero divisors has no `n`-torsion when `n` is nonzero in the
ambient ring. -/
instance subsingleton_torsionBy {R : Type*} [Ring R] [NoZeroDivisors R] (S : Subring R)
    (n : ℕ) [NeZero (n : R)] : Subsingleton (Submodule.torsionBy ℤ S (n : ℤ)) := by
  have hn : (n : S) ≠ 0 := fun h ↦ NeZero.ne (n : R) (congrArg Subtype.val h)
  rw [Submodule.subsingleton_iff_eq_bot, Submodule.eq_bot_iff]
  intro x hx
  simpa only [Submodule.mem_torsionBy_iff, natCast_zsmul, nsmul_eq_mul, mul_eq_zero, hn,
    false_or] using hx

/-- The additive reduction of a subring with finite quotients modulo `n` is finite when `n` is
nonzero in the ambient ring. -/
instance finite_quotSMulTop {R : Type*} [CommRing R] (S : Subring R)
    [Ring.HasFiniteQuotients S] (n : ℕ) [NeZero (n : R)] :
    Finite (QuotSMulTop (n : ℤ) S) := by
  have hn : (n : S) ≠ 0 := fun h ↦ NeZero.ne (n : R) (congrArg Subtype.val h)
  have : Finite (S ⧸ Ideal.span {(n : S)}) :=
    Ring.HasFiniteQuotients.finiteQuotient (Ideal.span_singleton_eq_bot.not.mpr hn)
  have h : (n : ℤ) • (⊤ : Submodule ℤ S) = (Ideal.span {(n : S)}).restrictScalars ℤ := by
    rw [← Submodule.restrictScalars_top (S := ℤ) (R := S), ← element_smul_restrictScalars]
    simp [← Submodule.ideal_span_singleton_smul]
  rw [QuotSMulTop, h]
  exact Finite.of_equiv _ (Submodule.Quotient.restrictScalarsEquiv ℤ _).toEquiv.symm

end Subring

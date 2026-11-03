/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import TauCeti.RingTheory.Perfectoid.Integral

/-!
# Checks for integral perfectoid rings

* `𝔽_p`, and the non-domain `𝔽_p × 𝔽_p`, are integral perfectoid, with adic element `0`; over
  `𝔽_p` the kernel of Fontaine's map is computed to be `(p)`, and Frobenius `A ⧸ π → A ⧸ π ^ p`
  is surjective for the adic element `π = 0`.
* The zero ring is integral perfectoid, although `p` is a unit there.
* `ℤ_p` is not integral perfectoid, although Frobenius on `ℤ_p ⧸ p = 𝔽_p` is bijective: `π ^ p ∣ p`
  forces `π` to be a unit, and `ℤ_p` is not complete for a unit. So the adic element cannot be
  dropped.
* `𝔽_p[X]` is not integral perfectoid, although it is complete for `π = 0`: `X` is not a `p`-th
  power. So the Frobenius condition cannot be dropped.
-/

open Ideal TauCeti.Perfectoid

namespace TauCeti.Examples

variable (p : ℕ) [hp : Fact p.Prime]

/-! ### Perfect rings of characteristic `p` -/

example : IsIntegralPerfectoid p (ZMod p) := inferInstance

-- Integral perfectoid rings need not be domains.
example : IsIntegralPerfectoid p (ZMod p × ZMod p) := inferInstance

-- Over `𝔽_p`, `p` is not a unit, and the kernel of Fontaine's map `W(𝔽_p♭) → 𝔽_p` is `(p)`;
-- `p`-adic completeness comes from the integral perfectoid structure.
example : letI : Fact ¬IsUnit (p : ZMod p) := ⟨IsIntegralPerfectoid.not_isUnit_natCast⟩
    RingHom.ker (WittVector.fontaineTheta (ZMod p) p) =
      span {(p : WittVector p (PreTilt (ZMod p) p))} :=
  letI : Fact ¬IsUnit (p : ZMod p) := ⟨IsIntegralPerfectoid.not_isUnit_natCast⟩
  WittVector.ker_fontaineTheta_eq_span_p

-- With `π = 0`, the Frobenius `𝔽_p ⧸ 0 → 𝔽_p ⧸ 0` is surjective.
example (h : (0 : ZMod p) ^ p ∣ (p : ZMod p)) : Function.Surjective (frobeniusModPow p h) :=
  IsIntegralPerfectoid.frobeniusModPow_surjective h

/-! ### The zero ring -/

example : IsIntegralPerfectoid p PUnit := .of_subsingleton p PUnit

-- In the zero ring `p` is a unit, so Mathlib's Fontaine map is not available there.
example : IsUnit (p : PUnit) := isUnit_of_subsingleton _

/-! ### Non-examples -/

-- `ℤ_p` is not integral perfectoid: completeness for `π` puts `π` in the Jacobson radical, so `π`
-- is not a unit and `p ∣ π`; then `p ^ p ∣ π ^ p ∣ p` would make `p` a unit.
example : ¬IsIntegralPerfectoid p ℤ_[p] := by
  rintro ⟨⟨π, hπ, hc⟩, -, -⟩
  have hπu : ¬IsUnit π := IsAdicComplete.not_isUnit_of_mem (mem_span_singleton_self π)
  have hpπ : (p : ℤ_[p]) ∣ π :=
    (PadicInt.norm_lt_one_iff_dvd π).mp (PadicInt.not_isUnit_iff.mp hπu)
  obtain ⟨c, hc⟩ := (pow_dvd_pow_of_dvd hpπ p).trans hπ
  -- `p = p ^ p c`, so cancelling `p` makes `p ^ (p - 1)` a unit
  have h1 : (p : ℤ_[p]) * 1 = p * (p ^ (p - 1) * c) := by
    rw [mul_one, ← mul_assoc, ← pow_succ', Nat.sub_add_cancel hp.out.one_le]
    exact hc
  have hunit : IsUnit ((p : ℤ_[p]) ^ (p - 1)) :=
    .of_mul_eq_one c (mul_left_cancel₀ (by exact_mod_cast hp.out.ne_zero) h1).symm
  exact PadicInt.not_isUnit_iff.mpr ((PadicInt.norm_lt_one_iff_dvd _).mpr dvd_rfl)
    ((isUnit_pow_iff (Nat.sub_ne_zero_of_lt hp.out.one_lt)).mp hunit)

-- `𝔽_p[X]` is not integral perfectoid: in characteristic `p`, `X` would have to be a `p`-th power,
-- whose degree is divisible by `p`.
example : ¬IsIntegralPerfectoid p (Polynomial (ZMod p)) := by
  intro h
  obtain ⟨y, hy⟩ := IsIntegralPerfectoid.exists_natCast_dvd_sub_pow (p := p)
    (Polynomial.X : Polynomial (ZMod p))
  rw [CharP.cast_eq_zero, zero_dvd_iff, sub_eq_zero] at hy
  have hdeg := congrArg Polynomial.natDegree hy
  rw [Polynomial.natDegree_X, Polynomial.natDegree_pow] at hdeg
  exact hp.out.ne_one (Nat.eq_one_of_mul_eq_one_right hdeg.symm)

-- But `𝔽_p[X]` does satisfy the adic condition, with `π = 0`.
example : ∃ π : Polynomial (ZMod p), π ^ p ∣ (p : Polynomial (ZMod p)) ∧
    IsAdicComplete (span {π}) (Polynomial (ZMod p)) :=
  ⟨0, by simp, inferInstance⟩

end TauCeti.Examples

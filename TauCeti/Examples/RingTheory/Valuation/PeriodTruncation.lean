/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.NumberTheory.Padics.ValuativeRel
import TauCeti.RingTheory.Valuation.PeriodTruncation
import TauCeti.RingTheory.WittVector.Frobenius

/-!
# Checks for Fontaine's filtered truncation over `ℚ_p`

For `E = ℚ_p` with its `p`-adic valuation and `r < p - 1`, the valuation of an integer is an
integer power of `v p`, so the period ideal `{x | v₀ x > r / (p - 1)}` is the maximal ideal
`{x | v₀ x ≥ 1}` and the truncation `A(ℚ_p)` is the residue field `𝔽_p`: it has
characteristic `p`, and `Fil¹ A(ℚ_p) = 0`, since `v₀ x ≥ 1 / p` already forces `v₀ x ≥ 1`. The
general theorem `Valuation.periodFiltration_eq_bot` only gives `Filⁱ = 0` for `i > r`.

For a perfect ring `k` of characteristic `p` and any ring map `W(k) → v.integer`, the divided
Frobenius is semilinear for the Witt-vector Frobenius `σ`.
-/

namespace Padic

open Valuation WithZero

variable {p : ℕ} [hp : Fact p.Prime] {r : ℕ}

-- The truncation `A(ℚ_p)` has characteristic `p`.
example (hr : r + 1 < p) : CharP ((mulValuation (p := p)).PeriodTruncation p r) p :=
  charP_periodTruncation (Nat.cast_ne_zero.2 hp.out.ne_zero) (valuation_p_lt_one _) hr

-- `Fil¹ A(ℚ_p) = 0`, even when `r ≥ 1`.
example (hr : r + 1 < p) : (mulValuation (p := p)).periodFiltration p r 1 = ⊥ := by
  refine eq_bot_iff.2 fun a ha => ?_
  obtain ⟨x, hx, rfl⟩ := mem_periodFiltration.1 ha
  rw [Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem,
    mem_periodIdeal (Nat.cast_ne_zero.2 hp.out.ne_zero)]
  have hx1 : mulValuation (x : ℚ_[p]) ≤ 1 := x.property
  by_cases h0 : (x : ℚ_[p]) = 0
  · simp [h0, zero_pow (show p - 1 ≠ 0 by have := hp.out.two_le; omega), hp.out.ne_zero,
      pos_iff_ne_zero]
  simp only [mulValuation_toFun, h0, (Nat.cast_ne_zero.2 hp.out.ne_zero : (p : ℚ_[p]) ≠ 0),
    ↓reduceIte, valuation_p, ← exp_nsmul, exp_le_exp, exp_lt_exp, ← exp_zero] at hx hx1 ⊢
  -- With `k = v₀ x`: `p * k ≥ 1` forces `k ≥ 1`, so `(p - 1) * k ≥ p - 1 > r`.
  simp only [nsmul_eq_mul] at hx ⊢
  push_cast [hp.out.one_le] at hx ⊢
  have : (2 : ℤ) ≤ p := mod_cast hp.out.two_le
  have : (r : ℤ) + 1 < p := mod_cast hr
  have hk : 1 ≤ (x : ℚ_[p]).valuation := by
    by_contra! h
    nlinarith
  nlinarith

end Padic

-- `φᵢ ([f w] • a) = [f (σ w)] * φᵢ a` along a ring map `f : W(k) → v.integer`.
example {E Γ₀ : Type*} [Field E] [LinearOrderedCommGroupWithZero Γ₀] {v : Valuation E Γ₀}
    {p r i : ℕ} [Fact p.Prime] (hp0 : (p : E) ≠ 0) (hp1 : v (p : E) < 1) (hr : r + 1 < p)
    {k : Type*} [CommRing k] [CharP k p] [PerfectRing k p] (f : WittVector p k →+* v.integer)
    (w : WittVector p k) (a : v.periodFiltration p r i) :
    v.periodFrobenius p r i (Ideal.Quotient.mk (v.periodIdeal p r) (f w) • a) =
      Ideal.Quotient.mk _ (f (WittVector.frobenius w)) * v.periodFrobenius p r i a :=
  Valuation.periodFrobenius_smul_of_isFrobeniusLift hp0 hp1 hr
    (WittVector.isFrobeniusLift_frobenius p k) f w a

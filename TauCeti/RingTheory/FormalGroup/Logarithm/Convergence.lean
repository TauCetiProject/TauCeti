/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.Logarithm.Basic
public import TauCeti.RingTheory.PowerSeries.OpenDisc.Basic

/-!
# Convergence of integral formal logarithms

For a formal group law over a ring `R`, the coefficient of degree `n` in its logarithm
becomes integral after multiplication by `n`. Consequently, if a ring homomorphism
`f : R →+* K` to a normed field of characteristic zero takes values in the closed unit ball,
the logarithm of `F.map f` has coefficient norms bounded by `‖(n : K)⁻¹‖`. These denominators
have subexponential growth, so the logarithm lies on the open unit disc and converges
absolutely there. Completeness is needed only to sum the series in `K`.

This applies, for instance, to the formal group of a Weierstrass curve over the integers
of a complete p-adic field, at parameters of norm less than one.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.4–6.
-/

public section

namespace FormalGroup

variable {R : Type*} [CommRing R]

variable {K : Type*} [NormedField K] [Algebra ℚ K]
    (F : FormalGroup R) (f : R →+* K) (hf : ∀ a, ‖f a‖ ≤ 1)

local instance : CharZero K := Algebra.charZero_of_charZero ℚ K

include hf

/-- The coefficients of an integral formal logarithm are bounded by the norms of the
inverse natural numbers. -/
theorem norm_coeff_log_le_inv_norm_natCast (n : ℕ) :
    ‖PowerSeries.coeff n (F.map f).log‖ ≤ ‖(n : K)⁻¹‖ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [PowerSeries.coeff_zero_eq_constantCoeff_apply]
  · have hnK : (n : K) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    obtain ⟨a, ha⟩ := F.natCast_mul_coeff_log_mem_range f n
    have h : ‖(n : K)‖ * ‖PowerSeries.coeff n (F.map f).log‖ ≤ 1 := by
      simpa only [ha, norm_mul] using hf a
    rw [norm_inv, ← one_div]
    exact (le_div_iff₀ (norm_pos_iff.mpr hnK)).mpr (by simpa [mul_comm] using h)

/-- The logarithm of an integral formal group lies on the full open unit disc, over any
normed field of characteristic zero. -/
theorem onOpenDisc_log : (F.map f).log.OnOpenDisc 1 :=
  PowerSeries.onOpenDisc_one_of_norm_coeff_le (F.norm_coeff_log_le_inv_norm_natCast f hf)

/-- The formal logarithm of an integral formal group converges absolutely at every parameter
in the open unit ball. -/
theorem summable_norm_coeff_log_mul_pow {t : K} (ht : ‖t‖ < 1) :
    Summable fun n : ℕ ↦ ‖PowerSeries.coeff n (F.map f).log * t ^ n‖ :=
  (F.onOpenDisc_log f hf).summable_norm_coeff_mul_pow' ht

/-- In a complete normed field the logarithm series of an integral formal group is summable
throughout the open unit ball. -/
theorem summable_coeff_log_mul_pow [CompleteSpace K] {t : K} (ht : ‖t‖ < 1) :
    Summable fun n : ℕ ↦ PowerSeries.coeff n (F.map f).log * t ^ n :=
  (F.onOpenDisc_log f hf).summable_coeff_mul_pow ht

end FormalGroup

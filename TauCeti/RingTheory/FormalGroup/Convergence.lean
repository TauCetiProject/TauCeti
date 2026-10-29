/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.Logarithm
public import TauCeti.RingTheory.PowerSeries.OpenDisc.Basic
import TauCeti.Analysis.Normed.Field.NatCast

/-!
# Convergence of integral formal logarithms

For a formal group law over a ring `R`, the coefficient of degree `n` in its logarithm
becomes integral after multiplication by `n`. Consequently, if a ring homomorphism
`f : R →+* K` to a normed field of characteristic zero takes values in the closed unit ball,
the logarithm of `F.map f` has coefficient norms bounded by `‖(n : K)⁻¹‖`. These denominators
have subexponential growth, so the logarithm lies on the open unit disc and converges
absolutely there. Completeness is needed only to sum the series in `K`.

In particular, this evaluates the logarithm of an elliptic formal group on parameters in
the maximal ideal of a complete p-adic field. It supplies convergence, not yet the evaluated
homomorphism law or an analytic inverse to the formal exponential.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.4–6.
-/

public section

namespace FormalGroup

variable {R S : Type*} [CommRing R] [CommRing S]

/-- Every logarithm coefficient becomes integral after multiplication by its degree. -/
theorem nat_mul_coeff_log_mem_range (F : FormalGroup R) [Algebra ℚ S]
    (f : R →+* S) (n : ℕ) :
    n * PowerSeries.coeff n (F.map f).log ∈ Set.range f := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨0, by simp⟩
  · refine ⟨PowerSeries.coeff (n - 1) F.invariantDifferential, ?_⟩
    have h := congrArg (PowerSeries.coeff (n - 1)) (F.map f).derivative_log
    rw [PowerSeries.coeff_derivative, ← Nat.cast_add_one, Nat.sub_add_cancel hn,
      mul_comm] at h
    rw [← F.map_invariantDifferential f, PowerSeries.coeff_map] at h
    exact h.symm

variable {K : Type*} [NormedField K] [Algebra ℚ K]
    (F : FormalGroup R) (f : R →+* K) (hf : ∀ a, ‖f a‖ ≤ 1)

local instance : CharZero K := Algebra.charZero_of_charZero ℚ K

include hf

/-- The coefficients of an integral formal logarithm are bounded by the norms of the
inverse natural numbers. -/
theorem norm_coeff_log_le_inv_norm_natCast (n : ℕ) :
    ‖PowerSeries.coeff n (F.map f).log‖ ≤ ‖(n : K)‖⁻¹ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [PowerSeries.coeff_zero_eq_constantCoeff_apply]
  · have hnK : (n : K) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    obtain ⟨a, ha⟩ := F.nat_mul_coeff_log_mem_range f n
    have h : ‖(n : K)‖ * ‖PowerSeries.coeff n (F.map f).log‖ ≤ 1 := by
      simpa only [ha, norm_mul] using hf a
    rw [← one_div]
    exact (le_div_iff₀ (norm_pos_iff.mpr hnK)).mpr (by simpa [mul_comm] using h)

/-- The logarithm of an integral formal group lies on the full open unit disc, over any
normed field of characteristic zero. -/
theorem onOpenDisc_log : (F.map f).log.OnOpenDisc 1 := by
  apply PowerSeries.onOpenDisc_iff.mpr
  intro r hr hr1
  rw [PowerSeries.isRestricted_iff']
  exact squeeze_zero (fun n ↦ by positivity)
    (fun n ↦ mul_le_mul_of_nonneg_right
      (F.norm_coeff_log_le_inv_norm_natCast f hf n) (pow_nonneg hr.le n))
    (by simpa only [norm_inv] using
      NormedField.tendsto_norm_inv_natCast_mul_pow K hr.le hr1)

/-- The formal logarithm of an integral formal group converges absolutely at every parameter
in the open unit ball. -/
theorem summable_norm_coeff_log_mul_pow {t : K} (ht : ‖t‖ < 1) :
    Summable fun n : ℕ ↦ ‖PowerSeries.coeff n (F.map f).log * t ^ n‖ := by
  simpa only [norm_mul, norm_pow] using
    (F.onOpenDisc_log f hf).summable_norm_coeff_mul_pow (by simpa using ht)

/-- In a complete normed field the logarithm series of an integral formal group is summable
throughout the open unit ball. -/
theorem summable_coeff_log_mul_pow [CompleteSpace K] {t : K} (ht : ‖t‖ < 1) :
    Summable fun n : ℕ ↦ PowerSeries.coeff n (F.map f).log * t ^ n :=
  (F.summable_norm_coeff_log_mul_pow f hf ht).of_norm

end FormalGroup

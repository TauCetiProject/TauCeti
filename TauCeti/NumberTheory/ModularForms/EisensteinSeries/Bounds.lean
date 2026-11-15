/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.EisensteinSeries.Subspace
public import TauCeti.NumberTheory.ArithmeticFunction.DivisorBounds

/-!
# Fourier coefficient bounds for the Eisenstein series with character

For weight `k ≥ 3`, the positive Fourier coefficients of each normalized raised character
Eisenstein series are bounded by `n^(k-1) ∑' d, d^(-(k-1))`. The constant is independent
of the characters and the raising parameter, so the coefficients are `O(n^(k-1))`. In weight
`k ≥ 3` these series span the Eisenstein part of `M_k(Γ₁(N))`, so this is the Eisenstein half of
the bound `aₙ = O(n^(k-1))` for all modular forms on `Γ₁(N)`
(`TauCeti.ModularFormClass.qExpansion_isBigO_of_Gamma1_le`). We do not assert this power bound
in weight two, where the untwisted divisor sum is not `O(n)`.

## Main results

* `TauCeti.EisensteinSeries.CharIndex.norm_qExpansion_form_coeff_le`: a uniform bound for
  the generators at positive indices.
* `TauCeti.EisensteinSeries.CharIndex.isBigO_qExpansion_form_coeff`: the generators have
  coefficients `O(n^(k-1))`.

## References

* F. Diamond and J. Shurman, *A First Course in Modular Forms*, §4.5 and Proposition 5.9.1.
-/

public noncomputable section

open UpperHalfPlane CongruenceSubgroup Matrix.SpecialLinearGroup Filter Asymptotics
open scoped MatrixGroups

namespace TauCeti

namespace EisensteinSeries.CharIndex

variable {N k : ℕ} [NeZero N] (a : CharIndex N k)

/-- A normalized raised character Eisenstein series has positive Fourier coefficients
bounded by `n^(k-1)` times the reciprocal-power series, uniformly in its indexing data. -/
theorem norm_qExpansion_form_coeff_le (hk : 3 ≤ (k : ℤ)) {n : ℕ} (hn : n ≠ 0) :
    ‖(qExpansion 1 (a.form hk)).coeff n‖ ≤
      (n : ℝ) ^ (k - 1) * ∑' d : ℕ, ((d : ℝ) ^ (k - 1))⁻¹ := by
  have he : 1 < k - 1 := by omega
  rw [a.form_def,
    qExpansion_normalizedCharEisensteinSeriesMFRaise_coeff
      a.psi a.phi hk a.level_dvd a.parity a.phi_primitive hn]
  split_ifs
  · calc
      ‖DirichletCharacter.twistedDivisorSum (k - 1) a.psi a.phi (n / a.t)‖ ≤
          ∑ d ∈ (n / a.t).divisors, (d : ℝ) ^ (k - 1) :=
        norm_twistedDivisorSum_le _ _ _ _
      _ ≤ ((n / a.t : ℕ) : ℝ) ^ (k - 1) * ∑' d : ℕ, ((d : ℝ) ^ (k - 1))⁻¹ :=
        sum_divisors_pow_le _ he _
      _ ≤ (n : ℝ) ^ (k - 1) * ∑' d : ℕ, ((d : ℝ) ^ (k - 1))⁻¹ := by
        gcongr
        exact_mod_cast Nat.div_le_self n a.t
  · simpa using mul_nonneg (by positivity : 0 ≤ (n : ℝ) ^ (k - 1))
      (tsum_nonneg fun d ↦ by positivity : 0 ≤ ∑' d : ℕ, ((d : ℝ) ^ (k - 1))⁻¹)

/-- The coefficients of a normalized raised character Eisenstein series are `O(n^(k-1))`.
The constant coefficient does not affect the estimate at infinity. -/
theorem isBigO_qExpansion_form_coeff (hk : 3 ≤ (k : ℤ)) :
    (fun n ↦ (qExpansion 1 (a.form hk)).coeff n) =O[atTop]
      (fun n : ℕ ↦ (n : ℝ) ^ (k - 1)) := by
  refine isBigO_iff.mpr ⟨∑' d : ℕ, ((d : ℝ) ^ (k - 1))⁻¹, ?_⟩
  filter_upwards [eventually_ne_atTop 0] with n hn
  simpa [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (n : ℝ) ^ (k - 1)),
    mul_comm] using a.norm_qExpansion_form_coeff_le hk hn

end EisensteinSeries.CharIndex

end TauCeti

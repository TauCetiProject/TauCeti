/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Degree.Lemmas

/-!
# Divisibility of polynomials with invertible leading coefficient

Over an arbitrary semiring `R`, if a polynomial `p` with invertible leading coefficient divides a
polynomial `q` of degree at most `p.natDegree`, then `q` is a constant right multiple of `p`. In
particular, if `p` and `q` also agree at an index where `p` has a left-regular coefficient, then
`q = p` (`Polynomial.eq_of_dvd_of_natDegree_le_of_coeff_eq`).

## Main results

* `Polynomial.eq_of_dvd_of_natDegree_le_of_coeff_eq`: a polynomial `q` divisible by `p` with
  invertible leading coefficient, `q.natDegree ≤ p.natDegree`, and agreeing with `p` at a
  left-regular coefficient equals `p`.
-/

public section

namespace Polynomial

variable {R : Type*} [Semiring R]

/-- If a polynomial `p` with invertible leading coefficient divides `q`,
`q.natDegree ≤ p.natDegree`, and `p` and `q` share a left-regular coefficient
`q.coeff k = p.coeff k`, then `q = p`. -/
theorem eq_of_dvd_of_natDegree_le_of_coeff_eq {p q : R[X]}
    (hp : IsUnit p.leadingCoeff) (hdvd : p ∣ q) (hdeg : q.natDegree ≤ p.natDegree)
    {k : ℕ} (hpk : IsLeftRegular (p.coeff k)) (hk : q.coeff k = p.coeff k) :
    q = p := by
  obtain ⟨u, hu⟩ := hp
  have hp₁ : (p * C (↑u⁻¹ : R)).Monic :=
    monic_mul_C_of_leadingCoeff_mul_eq_one (hu ▸ u.mul_inv)
  have hdeg₁ : (p * C (↑u⁻¹ : R)).natDegree = p.natDegree :=
    natDegree_mul_C_eq_of_mul_eq_one u.inv_mul
  have hp_eq : p * C (↑u⁻¹ : R) * C (u : R) = p := by
    rw [mul_assoc, ← C_mul, u.inv_mul, C_1, mul_one]
  have hdvd₁ : p * C (↑u⁻¹ : R) ∣ q :=
    (dvd_mul_right _ (C (u : R))).trans (hp_eq.symm ▸ hdvd)
  have hq :=
    eq_mul_leadingCoeff_of_monic_of_dvd_of_natDegree_le hp₁ hdvd₁ (hdeg.trans_eq hdeg₁.symm)
  rw [mul_assoc, ← C_mul] at hq
  have hc : (↑u⁻¹ : R) * q.leadingCoeff = 1 :=
    hpk (by
      simpa only [coeff_mul_C, hk, mul_one] using congrArg (fun f : R[X] ↦ f.coeff k) hq.symm)
  simpa [hc] using hq

end Polynomial

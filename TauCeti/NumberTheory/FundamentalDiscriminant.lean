/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.FundamentalDiscriminant
import TauCeti.Algebra.Squarefree
import Mathlib.Algebra.GCDMonoid.Nat

/-!
# Fundamental discriminants: basic API

Generic facts about Mathlib's `Int.IsFundamentalDiscr`, independent of any quadratic-field or
prime-discriminant theory.

## Main results

* `Int.IsFundamentalDiscr.mul`: coprime fundamental discriminants have fundamental product.
* `Int.IsFundamentalDiscr.not_isSquare_rat`: a fundamental discriminant other than `1` is not a
  rational square, so `ℚ(√D)` is a genuine quadratic field.
-/

public section

namespace Int

/-- A product of coprime fundamental discriminants is a fundamental discriminant. -/
theorem IsFundamentalDiscr.mul {D E : ℤ} (hD : IsFundamentalDiscr D)
    (hE : IsFundamentalDiscr E) (hcop : IsCoprime D E) : IsFundamentalDiscr (D * E) := by
  wlog hDodd : D % 4 = 1 generalizing D E
  · have hEodd : E % 4 = 1 := by
      by_contra hEodd
      have hD4 : (4 : ℤ) ∣ D :=
        Int.dvd_of_emod_eq_zero (hD.emod_four_eq_zero_or_one.resolve_right hDodd)
      have hE4 : (4 : ℤ) ∣ E :=
        Int.dvd_of_emod_eq_zero (hE.emod_four_eq_zero_or_one.resolve_right hEodd)
      have := hcop.isUnit_of_dvd' hD4 hE4
      norm_num [Int.isUnit_iff] at this
    simpa only [mul_comm] using this hE hD hcop.symm hEodd
  have hDsf : Squarefree D :=
    (isFundamentalDiscr_iff_squarefree.mp hD).resolve_right (by omega) |>.2
  rcases isFundamentalDiscr_iff_squarefree.mp hE with ⟨hEodd, hEsf⟩ | ⟨hE4, hEsf, hEmod⟩
  · exact isFundamentalDiscr_iff_squarefree.mpr <| Or.inl
      ⟨by rw [Int.mul_emod, hDodd, hEodd]; norm_num,
        squarefree_mul_iff.mpr ⟨hcop.isRelPrime, hDsf, hEsf⟩⟩
  · obtain ⟨e, rfl⟩ : (4 : ℤ) ∣ E := Int.dvd_of_emod_eq_zero hE4
    simp only [Int.mul_ediv_cancel_left _ (by norm_num : (4 : ℤ) ≠ 0)] at hEsf hEmod
    rw [mul_left_comm D 4 e, isFundamentalDiscr_four_mul]
    refine ⟨squarefree_mul_iff.mpr
      ⟨(hcop.of_isCoprime_of_dvd_right (dvd_mul_left e 4)).isRelPrime, hDsf, hEsf⟩, ?_⟩
    simpa only [Int.mul_emod, hDodd, one_mul, Int.emod_emod] using hEmod

/-- A fundamental discriminant other than `1` is not a rational square. Consequently `ℚ(√D)` is a
genuine quadratic field: this is what keeps the genus-field constructions non-degenerate. -/
theorem IsFundamentalDiscr.not_isSquare_rat {D : ℤ} (hD : IsFundamentalDiscr D)
    (h1 : D ≠ 1) : ¬ IsSquare ((D : ℤ) : ℚ) := by
  rcases isFundamentalDiscr_iff_squarefree.mp hD with ⟨-, hsf⟩ | ⟨h0, hmsf, hm4⟩
  · exact not_isSquare_intCast_of_squarefree_of_ne_one hsf h1
  · obtain ⟨m, rfl⟩ : (4 : ℤ) ∣ D := Int.dvd_of_emod_eq_zero h0
    rw [Int.mul_ediv_cancel_left m four_ne_zero] at hmsf hm4
    have hm1 : m ≠ 1 := by rcases hm4 with h | h <;> omega
    have hcast : ((4 * m : ℤ) : ℚ) = 4 * ((m : ℤ) : ℚ) := by push_cast; ring
    rw [hcast]
    exact fun h => not_isSquare_intCast_of_squarefree_of_ne_one hmsf hm1
      (by simpa using h.div (⟨2, by norm_num⟩ : IsSquare (4 : ℚ)))

end Int

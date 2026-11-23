/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import TauCeti.NumberTheory.LSeries.Quadratic.Siegel
import TauCeti.NumberTheory.NumberField.Quadratic.DedekindZeta

/-!
# Siegel's lower bound for class numbers of imaginary quadratic fields

For every `ε > 0` there is `C > 0` such that every imaginary quadratic field `K` has class number
`h(K) ≥ C |disc K| ^ (1 / 2 - ε)` (`TauCeti.NumberField.imaginary_classNumber_lower_bound`). This
combines Siegel's theorem `L(1, χ_D) ≥ c |D| ^ (-ε)`
(`TauCeti.Multiquadratic.quadratic_LFunction_siegel`), applied to the quadratic character `χ_D` of
the discriminant `D` of `K` at its level `|D|`, with the class number formula in the form
`h ≥ √|D| L(1, χ_D) / π` (`TauCeti.NumberField.sqrt_mul_LFunction_one_re_div_le_classNumber`).

Taking `ε = 1 / 4` bounds the discriminant of an imaginary quadratic field in terms of its class
number (`TauCeti.NumberField.imaginary_discr_bounded_of_classNumber_le`). The bounds are
ineffective, because the constant in Siegel's theorem is.

## Main results

* `TauCeti.NumberField.imaginary_classNumber_lower_bound`: `h(K) ≥ C |disc K| ^ (1 / 2 - ε)`.
* `TauCeti.NumberField.imaginary_discr_bounded_of_classNumber_le`: for every `B` there is `C` with
  `|disc K| ≤ C` whenever `h(K) ≤ B`.

## References

* H. Davenport, *Multiplicative Number Theory*, Chapter 21.
-/

public section

open Module NumberField TauCeti.Multiquadratic

namespace TauCeti.NumberField

universe u

/-- **Siegel's lower bound for class numbers.** For every `ε > 0` there is `C > 0` such that every
imaginary quadratic field `K` has class number at least `C |disc K| ^ (1 / 2 - ε)`. The constant is
ineffective. -/
theorem imaginary_classNumber_lower_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C > 0, ∀ (K : Type u) [Field K] [NumberField K] [IsTotallyComplex K], finrank ℚ K = 2 →
      C * |(discr K : ℝ)| ^ (1 / 2 - ε) ≤ classNumber K := by
  obtain ⟨c, hc, hS⟩ := quadratic_LFunction_siegel hε
  refine ⟨c / Real.pi, div_pos hc Real.pi_pos, fun K _ _ _ hK ↦ ?_⟩
  have hfd := isFundamentalDiscr_discr hK
  have := hfd.neZero_natAbs
  have hχ := hS _ ((fundamentalDiscriminantChar (discr K) hfd).ringHomComp (Int.castRingHom ℂ))
    ((fundamentalDiscriminantChar_isQuadratic hfd).comp _)
    (ringHomComp_fundamentalDiscriminantChar_discr_ne_one hK)
  rw [Nat.cast_natAbs, Int.cast_abs] at hχ
  have hD : 0 < |(discr K : ℝ)| := abs_pos.mpr (Int.cast_ne_zero.mpr (discr_ne_zero K))
  calc c / Real.pi * |(discr K : ℝ)| ^ (1 / 2 - ε)
      = √|(discr K : ℝ)| * (c * |(discr K : ℝ)| ^ (-ε)) / Real.pi := by
        rw [Real.sqrt_eq_rpow, sub_eq_add_neg, Real.rpow_add hD]
        ring
    _ ≤ √|(discr K : ℝ)| * (DirichletCharacter.LFunction
          ((fundamentalDiscriminantChar (discr K) hfd).ringHomComp (Int.castRingHom ℂ)) 1).re /
            Real.pi := by
        gcongr
    _ ≤ classNumber K := sqrt_mul_LFunction_one_re_div_le_classNumber hK

/-- **Discriminants of bounded class number are bounded.** For every `B` there is `C` such that
every imaginary quadratic field `K` with class number at most `B` has `|disc K| ≤ C`. The bound is
ineffective. -/
theorem imaginary_discr_bounded_of_classNumber_le (B : ℕ) :
    ∃ C : ℝ, ∀ (K : Type u) [Field K] [NumberField K] [IsTotallyComplex K], finrank ℚ K = 2 →
      classNumber K ≤ B → |(discr K : ℝ)| ≤ C := by
  obtain ⟨C, hC, h⟩ := imaginary_classNumber_lower_bound.{u} (ε := 1 / 4) (by norm_num)
  refine ⟨(B / C) ^ 4, fun K _ _ _ hK hB ↦ ?_⟩
  have hD : 0 ≤ |(discr K : ℝ)| := abs_nonneg _
  have h4 : |(discr K : ℝ)| ^ (1 / 4 : ℝ) ≤ B / C := by
    rw [le_div_iff₀ hC, mul_comm]
    have := h K hK
    norm_num at this
    exact this.trans (by exact_mod_cast hB)
  calc |(discr K : ℝ)| = (|(discr K : ℝ)| ^ (1 / 4 : ℝ)) ^ 4 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hD]
        norm_num
    _ ≤ (B / C) ^ 4 := by gcongr

end TauCeti.NumberField

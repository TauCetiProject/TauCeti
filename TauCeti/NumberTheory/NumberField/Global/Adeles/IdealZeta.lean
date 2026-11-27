/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Basic
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.FiniteIndexIdeal
import TauCeti.Analysis.SpecialFunctions.Log.Bounds
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Estimates
import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Logarithm.DedekindZeta.Basic
import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Logarithm.DedekindZeta.ExpBound

/-!
# The ideal zeta sum of the integral finite adeles of a number field

Let `E` be a number field of degree `d = [E : ℚ]` and `Ô` its integral finite adeles. The ideal
zeta sum `ζ_Ô(s) = ∑_I [Ô : I]^(-s)`, over the ideals of finite index of `Ô`
(`Module.submoduleZeta`), equals the ideal zeta sum of `𝓞 E`
(`IsDedekindDomain.FiniteAdeleRing.submoduleZeta_integralAdeles`), which is the sum of `N(𝔟)^(-s)`
over the nonzero ideals `𝔟` of `𝓞 E`. For `s ≥ 2` it is therefore the value `ζ_E(s)` of the
Dedekind zeta function (`TauCeti.submoduleZeta_eq_ofReal_dedekindZeta_re`), whose logarithm is at
most `2 ^ (3 - s) d` (`TauCeti.log_dedekindZeta_re_le_two_rpow_mul_finrank`). So the powers of
`ζ_Ô(s)` are bounded above by `1 + 2^(-u)`, uniformly in fields of bounded degree: if
`n d ≤ 2 ^ v`, then `ζ_Ô(u + v + 4)^n ≤ 1 + 2^(-u)` for every `u`, since a real power `z^n` with
`n log z ≤ ε ≤ 1 / 2` is at most `1 + 2 ε` (`TauCeti.pow_le_one_add_two_mul_of_log_le`). Such
bounds control the integrals over the frequencies of the Gauss sums of a hermitian form of large
rank over `Ô`.

## Main results

* `TauCeti.submoduleZeta_integralAdeles_pow_le`: if `n [E : ℚ] ≤ 2 ^ v`, then
  `ζ_Ô(u + v + 4)^n ≤ 1 + 2^(-u)`.

## Attribution

`TauCeti.submoduleZeta_integralAdeles_pow_le` and its proof plan (compare the ideals of finite
index of `Ô` with those of `𝓞 E`, then bound the logarithm of `ζ_E(s)` by its Euler product)
follow `New.idealZeta_intAdeles_pow_le` in the file `src/Lib/SiegelWeil/Mass.lean` of grh-lean
(https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC). Here `E` is any
number field.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §5 (the Euler product of `ζ_E`).
-/

public section

open IsDedekindDomain IsDedekindDomain.FiniteAdeleRing NumberField
open scoped ENNReal

namespace TauCeti

variable {E : Type*} [Field E] [NumberField E]

/-- **Powers of the ideal zeta sum of the integral finite adeles are at most `1 + 2^(-u)`.**
Let `Ô` be the integral finite adeles of a number field `E`. If `n [E : ℚ] ≤ 2 ^ v`, then
`ζ_Ô(u + v + 4)^n ≤ 1 + 2^(-u)` for every `u`, where `ζ_Ô(s) = ∑_I [Ô : I]^(-s)` over the ideals of
finite index of `Ô`. -/
theorem submoduleZeta_integralAdeles_pow_le {n u v : ℕ} (h : n * Module.finrank ℚ E ≤ 2 ^ v) :
    Module.submoduleZeta (integralAdeles (𝓞 E) E) (integralAdeles (𝓞 E) E) (u + v + 4) ^ n ≤
      1 + 2⁻¹ ^ u := by
  have hs : 2 ≤ u + v + 4 := by omega
  rw [submoduleZeta_integralAdeles, submoduleZeta_eq_ofReal_dedekindZeta_re hs]
  have hz := dedekindZeta_re_pos (K := E) (s := (u + v + 4 : ℕ)) (by norm_cast)
  have h_log := log_dedekindZeta_re_le_two_rpow_mul_finrank (K := E) (s := (u + v + 4 : ℕ))
    (by norm_cast)
  rw [Complex.ofReal_natCast] at hz h_log
  have h_bound : (1 : ℝ≥0∞) + 2⁻¹ ^ u = ENNReal.ofReal (1 + 2 * 2⁻¹ ^ (u + 1)) := by
    rw [pow_succ, mul_left_comm, mul_inv_cancel₀ two_ne_zero, mul_one,
      ENNReal.ofReal_add zero_le_one (by positivity), ENNReal.ofReal_one,
      ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_inv_of_pos two_pos, ENNReal.ofReal_ofNat]
  have h_half : (2⁻¹ : ℝ) ^ (u + 1) ≤ 1 / 2 := by
    rw [pow_succ, one_div]
    exact mul_le_of_le_one_left (by norm_num) (pow_le_one₀ (by norm_num) (by norm_num))
  rw [← ENNReal.ofReal_pow hz.le, h_bound]
  refine ENNReal.ofReal_le_ofReal
    (TauCeti.pow_le_one_add_two_mul_of_log_le h_log ?_ (by positivity) h_half)
  -- `n · 2^(3 - s) [E : ℚ] ≤ 2^v · 2^(3 - s) = 2^(-(u + 1))` for `s = u + v + 4`.
  -- Writing the exponent `3 - s` as the negated natural cast `-(u + 1 + v)` lets `Real.rpow_neg`
  -- and `Real.rpow_natCast` turn the real power of `2` into a natural power of `2⁻¹`.
  have h_exp : (3 : ℝ) - ((u + v + 4 : ℕ) : ℝ) = -((u + 1 + v : ℕ) : ℝ) := by push_cast; ring
  have h_two : (2 : ℝ) ^ (3 - ((u + v + 4 : ℕ) : ℝ)) = 2⁻¹ ^ (u + 1) * 2⁻¹ ^ v := by
    rw [h_exp, Real.rpow_neg zero_le_two, Real.rpow_natCast, ← inv_pow, pow_add]
  have h_cast : (n : ℝ) * Module.finrank ℚ E ≤ 2 ^ v := by exact_mod_cast h
  calc (n : ℝ) * (2 ^ (3 - ((u + v + 4 : ℕ) : ℝ)) * Module.finrank ℚ E)
    _ = 2⁻¹ ^ (u + 1) * (2⁻¹ ^ v * (n * Module.finrank ℚ E)) := by rw [h_two]; ring
    _ ≤ 2⁻¹ ^ (u + 1) * (2⁻¹ ^ v * 2 ^ v) := by gcongr
    _ = 2⁻¹ ^ (u + 1) := by rw [← mul_pow, inv_mul_cancel₀ two_ne_zero, one_pow, mul_one]

end TauCeti

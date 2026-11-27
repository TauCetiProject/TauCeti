/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.DedekindZeta
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
over the nonzero ideals `𝔟` of `𝓞 E`. For `s ≥ 2` it is therefore at most the value `ζ_E(s)` of
the Dedekind zeta function (`TauCeti.submoduleZeta_le_ofReal_dedekindZeta_re`), whose logarithm
is at most `2 ^ (3 - s) d` (`TauCeti.log_dedekindZeta_re_le_two_rpow_mul_finrank`). So `ζ_Ô(s)`
tends to `1` exponentially fast as `s` grows, uniformly in fields of bounded degree: if
`n d ≤ 2 ^ v`, then `ζ_Ô(u + v + 4)^n ≤ 1 + 2^(-u)` for every `u`, since a power whose logarithm
is small is close to `1` (`Real.pow_le_one_add_inv_two_pow_of_log_le`). Such bounds control the
integrals over the frequencies of the Gauss sums of a hermitian form of large rank over `Ô`.

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

/-- **The ideal zeta sum of the integral finite adeles tends to `1`.** Let `Ô` be the integral
finite adeles of a number field `E`. If `n [E : ℚ] ≤ 2 ^ v`, then `ζ_Ô(u + v + 4)^n ≤ 1 + 2^(-u)`
for every `u`, where `ζ_Ô(s) = ∑_I [Ô : I]^(-s)` over the ideals of finite index of `Ô`. -/
theorem submoduleZeta_integralAdeles_pow_le {n u v : ℕ} (h : n * Module.finrank ℚ E ≤ 2 ^ v) :
    Module.submoduleZeta (integralAdeles (𝓞 E) E) (integralAdeles (𝓞 E) E) (u + v + 4) ^ n ≤
      1 + 2⁻¹ ^ u := by
  rw [submoduleZeta_integralAdeles]
  have hs : 2 ≤ u + v + 4 := by omega
  have hz := dedekindZeta_re_pos (K := E) (s := (u + v + 4 : ℕ)) (by norm_cast)
  have h_log := log_dedekindZeta_re_le_two_rpow_mul_finrank (K := E) (s := (u + v + 4 : ℕ))
    (by norm_cast)
  rw [Complex.ofReal_natCast] at hz h_log
  have h_bound : (1 : ℝ≥0∞) + 2⁻¹ ^ u = ENNReal.ofReal (1 + 2⁻¹ ^ u) := by
    rw [ENNReal.ofReal_add zero_le_one (by positivity), ENNReal.ofReal_one,
      ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_inv_of_pos two_pos, ENNReal.ofReal_ofNat]
  refine (pow_le_pow_left₀ zero_le (submoduleZeta_le_ofReal_dedekindZeta_re hs) n).trans ?_
  rw [← ENNReal.ofReal_pow hz.le, h_bound]
  refine ENNReal.ofReal_le_ofReal (Real.pow_le_one_add_inv_two_pow_of_log_le h_log ?_)
  -- `n · 2^(3 - s) [E : ℚ] ≤ 2^v · 2^(3 - s) = 2^(-(u + 1))` for `s = u + v + 4`.
  have h_two : (2 : ℝ) ^ (3 - ((u + v + 4 : ℕ) : ℝ)) = 2⁻¹ ^ (u + 1) * 2⁻¹ ^ v := by
    rw [show (3 : ℝ) - ((u + v + 4 : ℕ) : ℝ) = -((u + 1 + v : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_neg zero_le_two, Real.rpow_natCast, ← inv_pow, pow_add]
  have h_cast : (n : ℝ) * Module.finrank ℚ E ≤ 2 ^ v := by exact_mod_cast h
  calc (n : ℝ) * (2 ^ (3 - ((u + v + 4 : ℕ) : ℝ)) * Module.finrank ℚ E)
    _ = 2⁻¹ ^ (u + 1) * (2⁻¹ ^ v * (n * Module.finrank ℚ E)) := by rw [h_two]; ring
    _ ≤ 2⁻¹ ^ (u + 1) * (2⁻¹ ^ v * 2 ^ v) := by gcongr
    _ = 2⁻¹ ^ (u + 1) := by rw [← mul_pow, inv_mul_cancel₀ two_ne_zero, one_pow, mul_one]

end TauCeti

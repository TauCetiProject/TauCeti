/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.DedekindZeta.Completed
import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Analytic
import TauCeti.NumberTheory.NumberField.DedekindZeta

/-!
# Nonvanishing of the continued Dedekind zeta function on `Re s ≥ 1`

The Euler product gives nonvanishing on the open half-plane. On its boundary we
apply `TauCeti.ne_zero_of_eqOn_dedekindZeta`, the `3-4-1` criterion for any
local continuation agreeing with the Dirichlet series, to the canonical continuation.
-/

public section

namespace TauCeti.LFunctions

variable (K : Type*) [Field K] [NumberField K]

/-- The continued Dedekind zeta function does not vanish on `Re s ≥ 1` away from its pole. -/
theorem dedekindZetaC_ne_zero_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) (hs₁ : s ≠ 1) :
    dedekindZetaC K s ≠ 0 := by
  rcases hs.lt_or_eq with h | h
  · rw [dedekindZetaC_eq_dedekindZeta K h]
    exact dedekindZeta_ne_zero_of_one_lt_re h
  · exact ne_zero_of_eqOn_dedekindZeta h.symm hs₁
      (analyticAt_dedekindZetaC K hs₁).differentiableAt fun _ hz ↦
        dedekindZetaC_eq_dedekindZeta K hz

/-- The repaired product `s(s - 1) Λ_K(s)` does not vanish on `Re s ≥ 1`. -/
theorem toMeromorphicNFOn_mul_completedDedekindZeta_ne_zero_of_one_le_re {s : ℂ}
    (hs : 1 ≤ s.re) :
    toMeromorphicNFOn (fun s : ℂ ↦ s * (s - 1) * completedDedekindZeta K s) Set.univ s ≠ 0 := by
  rcases eq_or_ne s 1 with rfl | h₁
  · rw [toMeromorphicNFOn_mul_completedDedekindZeta_one]
    exact mul_ne_zero (Nat.cast_ne_zero.mpr (NumberField.classNumber_pos K).ne')
      (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr (mellinConstant_ne_zero K)))
  have h₀ := Complex.ne_zero_of_re_pos (zero_lt_one.trans_le hs)
  have hn := dedekindZetaC_ne_zero_of_one_le_re K hs h₁
  rw [dedekindZetaC_eq_mul_completedDedekindZeta K h₀ h₁] at hn
  rw [toMeromorphicNFOn_mul_completedDedekindZeta_eq K h₀ h₁]
  exact mul_ne_zero (mul_ne_zero h₀ (sub_ne_zero.mpr h₁)) (right_ne_zero_of_mul hn)

/-- The zeros of the repaired product `s(s - 1) Λ_K(s)` lie in `Re s < 1`. -/
theorem re_lt_one_of_toMeromorphicNFOn_mul_completedDedekindZeta_eq_zero {ρ : ℂ}
    (hρ : toMeromorphicNFOn (fun s : ℂ ↦ s * (s - 1) * completedDedekindZeta K s) Set.univ ρ =
      0) :
    ρ.re < 1 :=
  lt_of_not_ge fun h ↦ toMeromorphicNFOn_mul_completedDedekindZeta_ne_zero_of_one_le_re K h hρ

end TauCeti.LFunctions

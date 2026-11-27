/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Riesz.Basic
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Riesz.RemainderMellin
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.VonMangoldt
public import TauCeti.NumberTheory.LFunctions.DedekindZeta.EulerKronecker
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Prime.DedekindZeta
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Riesz.Mellin

/-!
# The Mellin transform of the first Dedekind zeta Riesz remainder

For a number field `K`, take the first Riesz sum of the norm coefficients of `Λ_K` and
subtract `y log y - (1 + EK(K)) y`, where `EK(K)` is the Euler–Kronecker constant. Its upper
Mellin transform on `Re s > 1` equals the meromorphic expression `rieszRemainderMellin` for
`dedekindZetaC K`. This connects the smoothed prime-ideal count to the meromorphic expression
used for explicit formulas and one-sided bounds.

Over `ℚ` this normalization is that of L. Alpöge's `Deduction.mellin_Gchi_modOne`.
The Euler–Kronecker constant is normalized as in Y. Ihara, *On the Euler–Kronecker constants
of global fields and primes with small norms*, §1.
-/

public section

open Complex Filter MeasureTheory NumberField Set
open scoped Topology

namespace TauCeti.LFunctions

variable (K : Type*) [Field K] [NumberField K]

/-- The value at `1` after the Riesz main-term subtraction. The derivative in the formula
is the linear coefficient of the Laurent expansion of `ζ_K′/ζ_K` there. -/
theorem rieszRemainderMellin_dedekindZetaC_one :
    rieszRemainderMellin (dedekindZetaC K) 1 =
      1 + (eulerKroneckerConstant K : ℂ) - deriv (logDeriv (dedekindZetaPoleRemoved K)) 1 := by
  have h := (meromorphic_dedekindZetaC K).rieszRemainderMellin_eventuallyEq_dslope
    (analyticAt_logDeriv_dedekindZetaPoleRemoved_one K)
    (logDeriv_dedekindZetaC_sub_order_eventuallyEq K)
  simpa [meromorphicOrderAt_dedekindZetaC_one, dslope_same, add_comm] using h.eq_of_nhds

/-- The first Riesz sum of the norm coefficients of `Λ_K`, corrected by the Dedekind zeta main
term `(1 + EK(K)) y - y log y`, has absolutely convergent upper Mellin transform
`rieszRemainderMellin (dedekindZetaC K)` on `Re s > 1`. -/
theorem integrableOn_and_integral_rieszSum_normCoeff_vonMangoldt_add_mul_cpow {s : ℂ}
    (hs : 1 < s.re) :
    IntegrableOn (fun y : ℝ ↦ (rieszSum (normCoeff K IdealArithmeticFunction.vonMangoldt) y +
      ((1 + (eulerKroneckerConstant K : ℂ)) * y - y * Real.log y)) * (y : ℂ) ^ (-s - 1))
      (Ioi 1) ∧
    (∫ y in Ioi (1 : ℝ), (rieszSum (normCoeff K IdealArithmeticFunction.vonMangoldt) y +
      ((1 + (eulerKroneckerConstant K : ℂ)) * y - y * Real.log y)) * (y : ℂ) ^ (-s - 1)) =
        rieszRemainderMellin (dedekindZetaC K) s := by
  have h₁ : s ≠ 1 := by rintro rfl; norm_num at hs
  have heq : EqOn (dedekindZetaC K) (dedekindZeta K) {z : ℂ | 1 < z.re} :=
    fun _ hz ↦ dedekindZetaC_eq_dedekindZeta K hz
  have hζ := (logDeriv_congr_nhds
    (heq.eventuallyEq_of_mem ((isOpen_lt continuous_const continuous_re).mem_nhds hs))).eq_of_nhds
  have hsum := regroupByNorm K (hasSum_idealTerm_vonMangoldt (K := K) hs)
  have hne := dedekindZetaC_eq_dedekindZeta K hs ▸ dedekindZeta_ne_zero_of_one_lt_re hs
  have hLS : LSeries (normCoeff K IdealArithmeticFunction.vonMangoldt) s =
      -logDeriv (dedekindZetaC K) s := by
    rw [hsum.LSeries_eq, neg_div, ← logDeriv_apply, ← hζ]
  have hmain (y : ℝ) : (1 + (eulerKroneckerConstant K : ℂ)) * y - y * Real.log y =
      (logDerivFinitePart (dedekindZetaC K) 1 -
        (meromorphicOrderAt (dedekindZetaC K) 1).untop₀) * y +
        (meromorphicOrderAt (dedekindZetaC K) 1).untop₀ * y * Real.log y := by
    simp only [logDerivFinitePart_dedekindZetaC_one, meromorphicOrderAt_dedekindZetaC_one,
      WithTop.untop₀_coe, Int.cast_neg, Int.cast_one]
    ring
  simp_rw [hmain]
  exact Meromorphic.integrableOn_and_integral_rieszSum_add_mul_cpow_eq_rieszRemainderMellin
    (meromorphic_dedekindZetaC K) hs hsum.LSeriesSummable hLS (analyticAt_dedekindZetaC K h₁) hne

end TauCeti.LFunctions

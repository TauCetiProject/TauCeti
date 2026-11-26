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
import TauCeti.Analysis.LaplaceTransform.Elementary
import TauCeti.Analysis.LaplaceTransform.Mellin
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

/-- The finite part at `1` of the logarithmic derivative of the Dedekind zeta function is
the Euler–Kronecker constant. -/
@[simp] theorem logDerivFinitePart_dedekindZetaC_one :
    logDerivFinitePart (dedekindZetaC K) 1 = (eulerKroneckerConstant K : ℂ) := by
  rw [(analyticAt_logDeriv_dedekindZetaPoleRemoved_one K).logDerivFinitePart_eq,
    logDeriv_dedekindZetaPoleRemoved_one]
  simpa [meromorphicOrderAt_dedekindZetaC_one, neg_div, sub_neg_eq_add, one_div] using
    logDeriv_dedekindZetaC_add_inv_eventuallyEq K

/-- The value at `1` after the Riesz main-term subtraction. The derivative in the formula
is the linear coefficient of the Laurent expansion of `ζ_K′/ζ_K` there. -/
theorem rieszRemainderMellin_dedekindZetaC_one :
    rieszRemainderMellin (dedekindZetaC K) 1 =
      1 + (eulerKroneckerConstant K : ℂ) - deriv (logDeriv (dedekindZetaPoleRemoved K)) 1 := by
  have h := (meromorphic_dedekindZetaC K).rieszRemainderMellin_eventuallyEq_dslope
    (analyticAt_logDeriv_dedekindZetaPoleRemoved_one K) (by
      simpa [meromorphicOrderAt_dedekindZetaC_one, neg_div, sub_neg_eq_add, one_div] using
        logDeriv_dedekindZetaC_add_inv_eventuallyEq K)
  simpa [meromorphicOrderAt_dedekindZetaC_one, dslope_same, add_comm] using h.eq_of_nhds

private theorem mellin_dedekindZeta_main {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun y : ℝ ↦
      ((1 + (eulerKroneckerConstant K : ℂ)) * y - y * Real.log y) * (y : ℂ) ^ (-s - 1))
      (Ioi 1) ∧
    (∫ y in Ioi (1 : ℝ),
      ((1 + (eulerKroneckerConstant K : ℂ)) * y - y * Real.log y) * (y : ℂ) ^ (-s - 1)) =
        (1 + (eulerKroneckerConstant K : ℂ)) * (s - 1)⁻¹ - 1 / (s - 1) ^ 2 := by
  let c : ℂ := 1 + (eulerKroneckerConstant K : ℂ)
  have hlin := (hasLaplace_cexp_mul (w := 1) (by simpa using hs)).const_smul c
  have hlog := hasLaplace_cexp_mul_pow 1 (w := 1) (by simpa using hs)
  have heq : -(s + 1) = -s - 1 := by ring
  have h := (hlin.sub hlog).congr_ae (g := (fun y : ℝ ↦ c * y - (y : ℂ) * Real.log y) ∘ Real.exp)
    (Eventually.of_forall fun u ↦ by simp [smul_eq_mul, ofReal_exp])
  simpa only [c, smul_eq_mul, Real.exp_zero, heq, mul_comm, Nat.factorial_one, Nat.cast_one] using
    (hasLaplace_comp_exp_iff _ _ _ 0).mp h

/-- The first Riesz sum of `Λ_K`, corrected by the Dedekind zeta main term, has absolutely
convergent upper Mellin transform `rieszRemainderMellin (dedekindZetaC K)` on `Re s > 1`. -/
theorem mellin_rieszSum_vonMangoldt_sub_main {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun y : ℝ ↦ (rieszSum (normCoeff K IdealArithmeticFunction.vonMangoldt) y +
      ((1 + (eulerKroneckerConstant K : ℂ)) * y - y * Real.log y)) * (y : ℂ) ^ (-s - 1))
      (Ioi 1) ∧
    (∫ y in Ioi (1 : ℝ), (rieszSum (normCoeff K IdealArithmeticFunction.vonMangoldt) y +
      ((1 + (eulerKroneckerConstant K : ℂ)) * y - y * Real.log y)) * (y : ℂ) ^ (-s - 1)) =
        rieszRemainderMellin (dedekindZetaC K) s := by
  have h₀ : s ≠ 0 := by rintro rfl; norm_num at hs
  have h₁ : s ≠ 1 := by rintro rfl; norm_num at hs
  have heq : EqOn (dedekindZetaC K) (dedekindZeta K) {z : ℂ | 1 < z.re} :=
    fun _ hz ↦ dedekindZetaC_eq_dedekindZeta K hz
  have hζ := (logDeriv_congr_nhds
    (heq.eventuallyEq_of_mem ((isOpen_lt continuous_const continuous_re).mem_nhds hs))).eq_of_nhds
  have hsum := regroupByNorm K (hasSum_idealTerm_vonMangoldt (K := K) hs)
  have hR := integrableOn_rieszSum_mul_cpow hs hsum.LSeriesSummable
  obtain ⟨hM, hval⟩ := mellin_dedekindZeta_main K hs
  -- Split the transform into the prime-ideal contribution and the main-term correction.
  conv in (occs := *) (rieszSum _ _ + _) * _ => rw [add_mul]
  refine ⟨hR.add hM, ?_⟩
  rw [integral_add hR hM, integral_rieszSum_mul_cpow hs hsum.LSeriesSummable,
    hsum.LSeries_eq, hval, neg_div, ← logDeriv_apply, ← hζ]
  have hne := dedekindZetaC_eq_dedekindZeta K hs ▸ dedekindZeta_ne_zero_of_one_lt_re hs
  rw [((meromorphic_dedekindZetaC K).rieszRemainderMellin_eq_and_analyticAt h₀ h₁
    (analyticAt_dedekindZetaC K h₁) hne).1]
  simp only [logDerivFinitePart_dedekindZetaC_one, meromorphicOrderAt_dedekindZetaC_one,
    WithTop.untop₀_coe, Int.cast_neg, Int.cast_one]
  field_simp [h₀, sub_ne_zero.mpr h₁]
  ring

end TauCeti.LFunctions

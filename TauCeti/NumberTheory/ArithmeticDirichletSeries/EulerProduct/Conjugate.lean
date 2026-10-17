/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Analytic
public import TauCeti.NumberTheory.LSeries.Conjugate

/-!
# Conjugation of local Euler factors

Conjugating an ideal coefficient system conjugates its prime-power power series and reflects its
local Euler factors across the real axis. Absolute convergence is preserved, both locally and
for the norm-regrouped series. Thus the algebraic conjugation on `TauCeti.EulerProductData`
agrees with complex conjugation of the evaluated local Euler factors.

The identities for the totalized series hold at every complex argument, without a convergence
hypothesis. The convergence equivalences separately specify where these identities represent
convergent series rather than junk values.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII.
* The local coefficient constructions in `EulerProduct/Basic.lean` and Mathlib's `LSeries.term`.
-/

public section

namespace TauCeti

open scoped nonZeroDivisors NumberField
open IsDedekindDomain (HeightOneSpectrum)

namespace EulerProductData

variable {K : Type*} [Field K] [NumberField K]

/-- The local power series of conjugate Euler-product data is the coefficientwise conjugate. -/
@[simp]
theorem localPowerSeries_star (D : EulerProductData K)
    (P : HeightOneSpectrum (𝓞 K)) :
    (star D).localPowerSeries P = (D.localPowerSeries P).map (starRingEnd ℂ) := by
  simpa only [localPowerSeries_def, toIdealArithmeticFunction_star] using
    IdealArithmeticFunction.localPowerSeries_star D.toIdealArithmeticFunction P

/-- Conjugation of bundled Euler-product data conjugates each local arithmetic coefficient. -/
@[simp]
theorem localArithmeticFactor_star_apply (D : EulerProductData K)
    (P : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    (star D).localArithmeticFactor P n = star (D.localArithmeticFactor P n) := by
  simp only [localArithmeticFactor_eq, toIdealArithmeticFunction_star,
    IdealArithmeticFunction.localArithmeticFactor_star_apply]

/-- Conjugating Euler-product data reflects its local Euler factors across the real axis. -/
@[simp]
theorem eulerFactor_star (D : EulerProductData K) (P : HeightOneSpectrum (𝓞 K)) (s : ℂ) :
    (star D).eulerFactor P ((starRingEnd ℂ) s) = star (D.eulerFactor P s) := by
  rw [eulerFactor_def, eulerFactor_def, ← LSeries.LSeries_star]
  exact LSeries_congr (fun _ ↦ D.localArithmeticFactor_star_apply P _) _

/-- A local factor converges absolutely exactly where its conjugate does after reflection. -/
@[simp]
theorem LSeriesSummable_localArithmeticFactor_star_iff (D : EulerProductData K)
    (P : HeightOneSpectrum (𝓞 K)) (s : ℂ) :
    LSeriesSummable ((star D).localArithmeticFactor P) ((starRingEnd ℂ) s) ↔
      LSeriesSummable (D.localArithmeticFactor P) s := by
  rw [LSeriesSummable_congr ((starRingEnd ℂ) s) (fun _ ↦ D.localArithmeticFactor_star_apply P _)]
  exact LSeries.LSeriesSummable_star_iff _ _

end EulerProductData

end TauCeti

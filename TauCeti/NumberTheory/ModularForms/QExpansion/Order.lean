/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.QExpansion.Order
public import TauCeti.Analysis.Analytic.Order
public import TauCeti.Analysis.Complex.Periodic
public import Mathlib.RingTheory.PowerSeries.Expand

import TauCeti.Analysis.Analytic.OfScalars
import TauCeti.NumberTheory.ModularForms.QExpansion.Basic

/-!
# The `q`-expansion and its order under period rescaling

The order of the `q`-expansion of a periodic, bounded, holomorphic function on the upper
half-plane equals the analytic order of its `cuspFunction` at `0`; consequently, passing
from period `h` to period `m * h` multiplies the order by `m`. This is the vanishing-order
bookkeeping feeding the finite-index Sturm bound. The expansion itself is rescaled the same way:
since `𝕢 (m * h) ^ m = 𝕢 h`, the expansion at period `m * h` is the expansion at period `h` in
the variable `q ^ m`. This is what lets expansions at cusps of different widths be compared at a
common period. The rescaling only needs the cusp function to be analytic at `0`, not the function
to be holomorphic and bounded on the whole upper half-plane, so it also applies to the twisted
functions `𝕢 ^ k * f` through which Laurent expansions of meromorphic functions are defined.

## Main declarations

* `TauCeti.qExpansion_nat_mul`: `qExpansion (m * h) g = expand m (qExpansion h g)`.
* `TauCeti.qExpansion_nat_mul_order`: `(qExpansion (m * h) g).order = (qExpansion h g).order * m`.

## References

* [Mathlib PR #39083](https://github.com/leanprover-community/mathlib4/pull/39083)
  (Chris Birkbeck) — the upstream draft this file ports onto the current Mathlib pin.
-/

public noncomputable section

open UpperHalfPlane Complex Function SlashInvariantForm Periodic

open scoped ModularForm Topology Filter Manifold

namespace TauCeti

variable {h : ℝ}

/-- Off `q = 0`, the cusp function at period `m * h` of an `h`-periodic function is its cusp
function at period `h` composed with the `m`-th power map. -/
lemma cuspFunction_nat_mul_eventuallyEq_nhdsNE {g : ℍ → ℂ} {m : ℕ} (hh : h ≠ 0) (hm : m ≠ 0)
    (hg_per : Periodic (g ∘ ofComplex) h) :
    cuspFunction (m * h : ℝ) g =ᶠ[𝓝[≠] 0] fun q : ℂ ↦ cuspFunction h g (q ^ m) := by
  have hmh : (m * h : ℝ) ≠ 0 := mul_ne_zero (Nat.cast_ne_zero.mpr hm) hh
  refine eventually_nhdsWithin_of_forall fun q hq ↦ ?_
  dsimp only
  rw [← Periodic.qParam_right_inv hmh hq, TauCeti.Periodic.qParam_nat_mul_pow hm]
  exact (Periodic.eq_cuspFunction hmh (by simpa using hg_per.nat_mul m) _).trans
    (Periodic.eq_cuspFunction hh hg_per _).symm

/-- If the cusp function at period `h` of an `h`-periodic function is continuous at `0`, then near
`0` its cusp function at period `m * h` is the cusp function at period `h` composed with the
`m`-th power map. -/
lemma cuspFunction_nat_mul_eventuallyEq {g : ℍ → ℂ} {m : ℕ} (hh : h ≠ 0)
    (hm : 0 < m) (hg_per : Periodic (g ∘ ofComplex) h) (hg : ContinuousAt (cuspFunction h g) 0) :
    cuspFunction (m * h : ℝ) g =ᶠ[𝓝 0] fun q : ℂ ↦ cuspFunction h g (q ^ m) :=
  TauCeti.UpperHalfPlane.cuspFunction_eventuallyEq_nhds_of_continuousAt
    (cuspFunction_nat_mul_eventuallyEq_nhdsNE hh hm.ne' hg_per)
    (hg.comp_of_eq (by fun_prop) (zero_pow hm.ne'))

/-- If the cusp function at period `h` of an `h`-periodic function is analytic at `0`, then so is
its cusp function at period `m * h`. -/
lemma analyticAt_cuspFunction_nat_mul {g : ℍ → ℂ} {m : ℕ} (hh : h ≠ 0) (hm : 0 < m)
    (hg_per : Periodic (g ∘ ofComplex) h) (hg : AnalyticAt ℂ (cuspFunction h g) 0) :
    AnalyticAt ℂ (cuspFunction (m * h : ℝ) g) 0 :=
  (hg.comp_of_eq (analyticAt_id.pow m) (zero_pow hm.ne')).congr
    (cuspFunction_nat_mul_eventuallyEq hh hm hg_per hg.continuousAt).symm

/-- **The `q`-expansion at period `m * h` is the expansion at period `h` in the variable
`q ^ m`**, for an `h`-periodic function whose cusp function at period `h` is analytic at `0`: its
coefficients are those at period `h`, placed at the multiples of `m`. -/
lemma qExpansion_nat_mul {g : ℍ → ℂ} {m : ℕ} (hh : h ≠ 0) (hm : 0 < m)
    (hg_per : Periodic (g ∘ ofComplex) h) (hg : AnalyticAt ℂ (cuspFunction h g) 0) :
    qExpansion (m * h : ℝ) g = PowerSeries.expand m hm.ne' (qExpansion h g) := by
  set G := cuspFunction h g
  have hcomp : AnalyticAt ℂ (fun q : ℂ ↦ G (q ^ m)) 0 :=
    hg.comp_of_eq (analyticAt_id.pow m) (zero_pow hm.ne')
  -- the Taylor series of `G` at `0`, read in the variable `q ^ m` on a ball of radius `≤ 1`
  obtain ⟨r, hr⟩ := hg.hasFPowerSeriesAt
  have hexp := ((hr.mono (lt_min hr.r_pos zero_lt_one) (min_le_left _ _)).comp_pow_ofScalars
    (min_le_right _ _) hm).hasFPowerSeriesAt.eq_formalMultilinearSeries hcomp.hasFPowerSeriesAt
  ext n
  have hn := congrArg (FormalMultilinearSeries.coeff · n) hexp
  simp only [FormalMultilinearSeries.coeff_ofScalars] at hn
  rw [_root_.UpperHalfPlane.qExpansion_coeff, (cuspFunction_nat_mul_eventuallyEq
      hh hm hg_per hg.continuousAt).iteratedDeriv_eq, PowerSeries.coeff_expand,
    _root_.UpperHalfPlane.qExpansion_coeff, ← div_eq_inv_mul, ← div_eq_inv_mul, ← hn]

/-- The order of the `q`-expansion at period `m * h` is `m` times the order at period `h`. -/
lemma qExpansion_nat_mul_order {g : ℍ → ℂ} {m : ℕ} (hh : 0 < h) (hm : 0 < m)
    (hg_per : Periodic (g ∘ ofComplex) h) (hg_bdd : IsBoundedAtImInfty g) (hg_mdiff : MDiff g) :
    (qExpansion (m * h : ℝ) g).order = (qExpansion h g).order * m := by
  have han : AnalyticAt ℂ (cuspFunction h g) 0 :=
    analyticAt_cuspFunction_zero hh hg_per hg_mdiff hg_bdd
  rw [qExpansion_order_eq_analyticOrderAt_cuspFunction han,
    qExpansion_order_eq_analyticOrderAt_cuspFunction (analyticAt_cuspFunction_zero
      (by positivity) (by simpa using hg_per.nat_mul m) hg_mdiff hg_bdd),
    analyticOrderAt_congr (cuspFunction_nat_mul_eventuallyEq hh.ne' hm hg_per han.continuousAt),
    TauCeti.analyticOrderAt_comp_pow_zero han hm]

/-- The order of the `q`-expansion at period `h` is at most its order at period `m * h`. -/
lemma qExpansion_order_le_qExpansion_nat_mul_order {g : ℍ → ℂ} {m : ℕ} (hh : 0 < h) (hm : 0 < m)
    (hg_per : Periodic (g ∘ ofComplex) h) (hg_bdd : IsBoundedAtImInfty g) (hg_mdiff : MDiff g) :
    (qExpansion h g).order ≤ (qExpansion (m * h : ℝ) g).order :=
  (ENat.self_le_mul_right _ (mod_cast hm.ne')).trans
    (qExpansion_nat_mul_order hh hm hg_per hg_bdd hg_mdiff).ge

end TauCeti

end

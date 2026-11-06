/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DiophantineApproximation.ContinuedFractions.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-!
# Partial quotients and the irrationality exponent

For an irrational real number `ξ = [a₀; a₁, a₂, …]`, with convergent denominators `qₖ`,
the irrationality exponent is `2 + limsup log(aₖ₊₁) / log(qₖ)` in `ℝ≥0∞`.
This completes the denominator-growth formula with a formula in the continued-fraction
digits themselves, including unbounded limit superior.

We use Mathlib's partial denominators: `(GenContFract.of ξ).partDens.get? k` is
`some aₖ₊₁`. The default `1` in the statement is never used for irrational `ξ`.
The terms with `qₖ = 1` are assigned `0` by real division and do not affect the limit superior.
The recurrence gives `aₖ₊₁ qₖ ≤ qₖ₊₁ ≤ 2 aₖ₊₁ qₖ`, so the two logarithmic growth
sequences differ by `1` and an error bounded by `log 2 / log qₖ`, which tends to zero.

## References

* J. Sondow, *Irrationality measures, irrationality bases, and a theorem of Jarnik*,
  §3, Theorem 1.
* J.-H. Evertse, *Diophantine Approximation*, lecture notes (2019), ch. 1, Exercise 1.7.
-/

public section

open Filter GenContFract
open GenContFract (of)
open scoped Topology

namespace TauCeti

variable {ξ : ℝ}

private theorem log_den_convergent_bounds (hξ : Irrational ξ) {k : ℕ}
    (hq : 1 < (ξ.convergent k).den) :
    1 + Real.log (((of ξ).partDens.get? k).getD 1) / Real.log (ξ.convergent k).den ≤
        Real.log (ξ.convergent (k + 1)).den / Real.log (ξ.convergent k).den ∧
      Real.log (ξ.convergent (k + 1)).den / Real.log (ξ.convergent k).den ≤
        1 + Real.log (((of ξ).partDens.get? k).getD 1) / Real.log (ξ.convergent k).den +
          Real.log 2 / Real.log (ξ.convergent k).den := by
  obtain ⟨gp, hs⟩ := Option.ne_none_iff_exists'.mp (hξ.not_of_terminatedAt k)
  have hb := partDen_eq_s_b hs
  rw [hb, Option.getD_some]
  have ha : 1 ≤ gp.b := of_one_le_get?_partDen hb
  have hqR : (1 : ℝ) < (ξ.convergent k).den := by exact_mod_cast hq
  have hlq : 0 < Real.log (ξ.convergent k).den := Real.log_pos hqR
  have hlow := le_of_succ_get?_den hb
  have hupp := of_den_le_partDen_add_one_mul_den hb
  rw [← Real.den_convergent, ← Real.den_convergent] at hlow hupp
  have hlowlog := Real.log_le_log (by positivity) hlow
  have hupp' : ((ξ.convergent (k + 1)).den : ℝ) ≤
      2 * gp.b * (ξ.convergent k).den := by nlinarith
  have hupplog := Real.log_le_log (by positivity) hupp'
  rw [Real.log_mul (by positivity) (by positivity)] at hlowlog
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity)] at hupplog
  constructor
  · apply (le_div_iff₀ hlq).mpr
    nlinarith [div_mul_cancel₀ (Real.log gp.b) hlq.ne']
  · apply (div_le_iff₀ hlq).mpr
    nlinarith [div_mul_cancel₀ (Real.log gp.b) hlq.ne',
      div_mul_cancel₀ (Real.log 2) hlq.ne']

/-- **The irrationality exponent through partial quotients** (Sondow, Theorem 1).
For `ξ = [a₀; a₁, …]` irrational, `μ(ξ) = 2 + limsup log(aₖ₊₁) / log(qₖ)`.
The limit superior is taken in `ℝ≥0∞`, so the formula includes Liouville numbers.
Mathlib indexes `aₖ₊₁` as the `k`-th partial denominator. -/
theorem _root_.Irrational.irrationalityExponent_eq_two_add_limsup (hξ : Irrational ξ) :
    irrationalityExponent ξ = 2 + limsup (fun k : ℕ ↦ ENNReal.ofReal
      (Real.log (((of ξ).partDens.get? k).getD 1) / Real.log (ξ.convergent k).den)) atTop := by
  let a (k : ℕ) := ENNReal.ofReal
    (Real.log (((of ξ).partDens.get? k).getD 1) / Real.log (ξ.convergent k).den)
  let r (k : ℕ) := ENNReal.ofReal
    (Real.log (ξ.convergent (k + 1)).den / Real.log (ξ.convergent k).den)
  let e (k : ℕ) := ENNReal.ofReal (Real.log 2 / Real.log (ξ.convergent k).den)
  have he : Tendsto e atTop (𝓝 0) := by
    simpa only [e, Function.comp_apply, ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal
      (((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).comp
        (Real.tendsto_den_convergent hξ)).const_div_atTop (Real.log 2))
  have hbounds : ∀ᶠ k in atTop, 1 + a k ≤ r k ∧ r k ≤ (1 + a k) + e k := by
    filter_upwards [(Real.tendsto_den_convergent hξ).eventually_gt_atTop 1] with k hk
    obtain ⟨gp, hs⟩ := Option.ne_none_iff_exists'.mp (hξ.not_of_terminatedAt k)
    have hb := partDen_eq_s_b hs
    have ha : 0 ≤ Real.log (((of ξ).partDens.get? k).getD 1) := by
      rw [hb, Option.getD_some]
      exact Real.log_nonneg (of_one_le_get?_partDen hb)
    have hq : 0 ≤ Real.log (ξ.convergent k).den := Real.log_nonneg (by exact_mod_cast hk.le)
    have h := log_den_convergent_bounds hξ hk
    simpa only [a, r, e, ENNReal.ofReal_add (by positivity : (0 : ℝ) ≤ 1) (div_nonneg ha hq),
      ENNReal.ofReal_add (by positivity : 0 ≤ 1 + Real.log
        (((of ξ).partDens.get? k).getD 1) / Real.log (ξ.convergent k).den)
        (by positivity : 0 ≤ Real.log 2 / Real.log (ξ.convergent k).den),
      ENNReal.ofReal_one] using
      And.intro (ENNReal.ofReal_le_ofReal h.1) (ENNReal.ofReal_le_ofReal h.2)
  have hlim : limsup r atTop = limsup (fun k ↦ 1 + a k) atTop := by
    apply le_antisymm
    · exact (limsup_le_limsup (hbounds.mono fun _ h ↦ h.2)).trans_eq
        (ENNReal.limsup_add_of_right_tendsto_zero he (fun k ↦ 1 + a k))
    · exact limsup_le_limsup (hbounds.mono fun _ h ↦ h.1)
  rw [irrationalityExponent_eq_one_add_limsup hξ, hlim,
    limsup_const_add atTop a 1 (by isBoundedDefault) (by isBoundedDefault), ← add_assoc]
  norm_num [a]

end TauCeti

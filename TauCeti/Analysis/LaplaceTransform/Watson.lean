/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import TauCeti.Analysis.Asymptotics.AsymptoticExpansion
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import TauCeti.Analysis.LaplaceTransform.Basic
import TauCeti.Analysis.LaplaceTransform.Remainder
import TauCeti.Analysis.SpecialFunctions.Gamma.IntegralComplexRate
import TauCeti.MeasureTheory.Integral.Exp.Damped

/-!
# Watson's lemma on the real line

Let `α : ℕ → ℂ` have exponents with positive real parts, let `c : ℕ → ℂ`, and let `q : ℝ → ℂ`
have `t ↦ e^{-σt} q(t)` integrable on `(0, ∞)` for some real `σ` and, for every `N`,

`q(t) - ∑_{s<N} c_s t^{α_s - 1} = O(t^{Re α_N - 1})`   as `t → 0+`.

Then the Laplace integral has the asymptotic expansion

`∫₀^∞ e^{-xt} q(t) dt ∼ ∑ Γ(α_s) c_s x^{-α_s}`   as `x → +∞`

(DLMF 2.3.7–2.3.8, where `α_s = (s + λ)/μ`; for a general sequence of exponents this is the
extension of Bleistein and Handelsman, *Asymptotic Expansions of Integrals*, §4.1). Formally the
conclusion is `Asymptotics.HasAsymptoticExpansion`: for every `N` the remainder after `N` terms
is `O(x^{-Re α_N})`. It is an asymptotic expansion in DLMF's sense when `Re α_s` is strictly
increasing, which makes `fun s x => (x : ℂ) ^ (-α s)` an `Asymptotics.IsAsymptoticScale`; without
that, the statement is only this family of remainder bounds and the coefficients need not be
unique. The terms
are Gamma integrals. For the remainder one splits the integral at a small `δ`: near `0` the
bound on `q` gives `O(x^{-Re α_N})` through the Gamma integral, and beyond `δ` the factor
`e^{-xt}` contributes `O(e^{-δx})`, which is smaller than every power of `x`.

Near `0` the hypothesis gives `q(t) = O(t^{Re α_0 - 1})`, which is integrable, so the
integrability of `e^{-σt} q(t)` on `(0, ∞)` amounts to local integrability of `q` on `(0, ∞)`
together with integrability of `e^{-σt} q(t)` on `(1, ∞)`: see
`TauCeti.integrableOn_exp_neg_mul_smul_iff` in `TauCeti.MeasureTheory.Integral.Asymptotics`.

## Main results

* `Asymptotics.hasAsymptoticExpansion_laplace`: Watson's lemma.

The remainder is bounded by `TauCeti.isBigO_integral_exp_neg_mul_smul` of
`TauCeti.Analysis.LaplaceTransform.Remainder`: if `G(t) = O(t^{s-1})` as `t → 0+`, then
`∫₀^∞ e^{-xt} G(t) dt = O(x^{-s})` as `x → +∞`.

The integrability of `e^{-xt} G(t)` for `x ≥ σ` is in
`TauCeti.MeasureTheory.Integral.Exp.Damped`. The terms are evaluated by
`Complex.integral_cpow_mul_exp_neg_mul_Ioi_of_re_pos` at a real rate.

The proofs are adapted from the lean-DLMF project (<https://github.com/bjbraams/lean-DLMF>):
the remainder bound and Watson's lemma with exponents in steps of `1` from
`DLMFMathlib/Analysis/Asymptotics/Watson.lean`, and the statement for an arbitrary sequence of
exponents from `DLMF/AsymptoticApproximations/Integrals/Watson.lean`
(`hasAsymptoticExpansion_integral_exp_smul_rpow_seq` on the real line with real exponents,
`hasAsymptoticExpansion_integral_cexp_smul_cpow_seq` in a sector with complex exponents). The
form here, on the real line with complex exponents, combines those two statements.

## References

* DLMF §2.3(ii), <https://dlmf.nist.gov/2.3.ii>.
* N. Bleistein and R. A. Handelsman, *Asymptotic Expansions of Integrals*, §4.1.
-/

public section

noncomputable section

open MeasureTheory Set Filter Finset Complex TauCeti
open scoped Topology

namespace Asymptotics

/-- **Watson's lemma** (DLMF 2.3.7–2.3.8, for a general sequence of exponents). Let `α : ℕ → ℂ`
have `Re α_s > 0` for all `s`, and let `q : ℝ → ℂ` have `t ↦ e^{-σt} q(t)` integrable on
`(0, ∞)` and, for every `N`, `q(t) - ∑_{s<N} c_s t^{α_s - 1} = O(t^{Re α_N - 1})` as
`t → 0+`. Then `∫₀^∞ e^{-xt} q(t) dt ∼ ∑ Γ(α_s) c_s x^{-α_s}` as `x → +∞`, in the sense of
`HasAsymptoticExpansion`: for every `N` the remainder after `N` terms is `O(x^{-Re α_N})`. This is
an asymptotic expansion in DLMF's sense when `Re α_s` is strictly increasing, which makes
`fun s x => (x : ℂ) ^ (-α s)` an `IsAsymptoticScale`; otherwise it is only this family of
remainder bounds, and the coefficients need not be unique.

If instead `q` is locally integrable on `(0, ∞)` (`hloc`) and `t ↦ e^{-σt} q(t)` is integrable
on `(1, ∞)` (`hint₁`), pass `(TauCeti.integrableOn_exp_neg_mul_smul_iff (hα 0) hq0).mpr
⟨hloc, hint₁⟩` as `hint`, where `hq0 : q =O[𝓝[>] 0] fun t => t ^ ((α 0).re - 1)` is
`by simpa using hq 0`. -/
theorem hasAsymptoticExpansion_laplace {q : ℝ → ℂ} {α c : ℕ → ℂ} {σ : ℝ}
    (hα : ∀ s, 0 < (α s).re) (hint : IntegrableOn (fun t => Real.exp (-σ * t) • q t) (Ioi 0))
    (hq : ∀ N, (fun t : ℝ => q t - ∑ s ∈ range N, c s * (t : ℂ) ^ (α s - 1))
      =O[𝓝[>] 0] fun t => t ^ ((α N).re - 1)) :
    HasAsymptoticExpansion atTop (fun s (x : ℝ) => (x : ℂ) ^ (-α s)) (fun s => Gamma (α s) * c s)
      fun x : ℝ => ∫ t in Ioi (0 : ℝ), cexp (-(x * t)) * q t := by
  refine HasAsymptoticExpansion.of_isBigO fun N => ?_
  have hb := TauCeti.isBigO_integral_exp_neg_mul_smul (hq N)
  -- compare the real power `x^{-Re α_N}` with the norm of the complex scale
  have hnorm : (fun x : ℝ => x ^ (-(α N).re)) =ᶠ[atTop] fun x => ‖(x : ℂ) ^ (-α N)‖ := by
    filter_upwards [eventually_gt_atTop 0] with x hx
    rw [norm_cpow_eq_rpow_re_of_pos hx, neg_re]
  refine (isBigO_norm_right.mp (hb.congr' EventuallyEq.rfl hnorm)).congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_ge_atTop σ, eventually_gt_atTop 0] with x hxσ hx
  have hx' : 0 < (x : ℂ).re := by rwa [ofReal_re]
  have hkernel (t : ℝ) (z : ℂ) : Real.exp (-x * t) • z = cexp (-(x : ℂ) * t) • z := by
    simp [Complex.real_smul]
  -- the Laplace transforms of `q` and of the Gamma terms `t^{α_s - 1}`
  have hLq : HasLaplace q x (∫ t in Ioi (0 : ℝ), cexp (-(x * t)) * q t) :=
    have hI : IntegrableOn (fun t => Real.exp (-x * t) • q t) (Ioi 0) :=
      integrable_exp_neg_mul_smul_of_le hint
        ((ae_restrict_mem measurableSet_Ioi).mono fun _ ht => le_of_lt ht) hxσ
    HasLaplace.intro (hI.congr_fun (fun t _ => hkernel t (q t)) measurableSet_Ioi)
      (setIntegral_congr_fun measurableSet_Ioi fun t _ => by simp)
  have hLs (s : ℕ) :
      HasLaplace (fun t : ℝ => (t : ℂ) ^ (α s - 1)) x (Gamma (α s) * (x : ℂ) ^ (-α s)) := by
    refine HasLaplace.intro ((integrableOn_cpow_mul_exp_neg_mul_Ioi (hα s) hx').congr_fun
      (fun t _ => by simp [mul_comm]) measurableSet_Ioi) ?_
    rw [← integral_cpow_mul_exp_neg_mul_Ioi_of_re_pos (hα s) hx']
    exact setIntegral_congr_fun measurableSet_Ioi fun t _ => by simp [mul_comm]
  have hL := (hLq.sub (hasLaplace_sum (u := range N) fun s _ =>
    (hLs s).const_smul (c s))).integral_eq
  refine (setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_).trans (hL.trans ?_)
  · simp only [hkernel, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  · refine congrArg (_ - ·) (sum_congr rfl fun s _ => ?_)
    simp only [smul_eq_mul]
    ring

end Asymptotics

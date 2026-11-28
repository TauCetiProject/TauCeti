/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import TauCeti.Analysis.Asymptotics.AsymptoticExpansion
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import TauCeti.Analysis.Complex.Sector.RealPart
import TauCeti.Analysis.LaplaceTransform.Basic
import TauCeti.Analysis.LaplaceTransform.Remainder
import TauCeti.Analysis.SpecialFunctions.Gamma.IntegralComplexRate
import TauCeti.MeasureTheory.Integral.Exp.Complex

/-!
# Watson's lemma

Let `α : ℕ → ℂ` have exponents with positive real parts, let `c : ℕ → ℂ`, and let `q : ℝ → ℂ`
have `t ↦ e^{-σt} q(t)` integrable on `(0, ∞)` for some real `σ` and, for every `N`,

`q(t) - ∑_{s<N} c_s t^{α_s - 1} = O(t^{Re α_N - 1})`   as `t → 0+`.

Then the Laplace integral has the asymptotic expansion

`∫₀^∞ e^{-zt} q(t) dt ∼ ∑ Γ(α_s) c_s z^{-α_s}`

as `z = x → +∞` along the real line (DLMF 2.3.7–2.3.8) and, more generally, as `z → ∞` in every
closed sector `|arg z| ≤ π/2 - δ` with `δ > 0` (DLMF 2.4.1). DLMF has `α_s = (s + λ)/μ`; for a
general sequence of exponents this is the extension of Bleistein and Handelsman, *Asymptotic
Expansions of Integrals*, §4.1. Formally the conclusion is `Asymptotics.HasAsymptoticExpansion`:
for every `N` the remainder after `N` terms is `O(z^{-α_N})`. It is an asymptotic expansion in
DLMF's sense when `Re α_s` is strictly increasing, which makes `fun s z => z ^ (-α s)` an
`Asymptotics.IsAsymptoticScale`; on the real line the theorem is stated without that hypothesis,
and then it is only this family of remainder bounds and the coefficients need not be unique.

The terms are Gamma integrals, `Complex.integral_cpow_mul_exp_neg_mul_Ioi_of_re_pos`, so the
remainder after `N` terms is the Laplace integral of `q(t) - ∑_{s<N} c_s t^{α_s - 1}`
(`Asymptotics.integral_cexp_neg_mul_mul_sub_sum_eq`). That integral is `O((re z)^{-Re α_N})` as
`re z → +∞`, by `TauCeti.isBigO_integral_cexp_neg_mul_smul` of
`TauCeti.Analysis.LaplaceTransform.Remainder`. On the sector `re z` is comparable to `‖z‖`
(`TauCeti.isTheta_re_norm_principal_abs_arg_le` of `TauCeti.Analysis.Complex.Sector.RealPart`),
and `‖z‖^{-Re α_N}` is comparable to `‖z^{-α_N}‖`.

Near `0` the hypothesis gives `q(t) = O(t^{Re α_0 - 1})`, which is integrable, so the
integrability of `e^{-σt} q(t)` on `(0, ∞)` amounts to local integrability of `q` on `(0, ∞)`
together with integrability of `e^{-σt} q(t)` on `(1, ∞)`: see
`TauCeti.integrableOn_exp_neg_mul_smul_iff` in `TauCeti.MeasureTheory.Integral.Asymptotics`.

## Main results

* `Asymptotics.integral_cexp_neg_mul_mul_sub_sum_eq`: the remainder of the expansion is the
  Laplace integral of the remainder of `q`, for `σ ≤ re z` and `0 < re z`.
* `Asymptotics.hasAsymptoticExpansion_laplace`: Watson's lemma on the real line.
* `Asymptotics.hasAsymptoticExpansion_laplace_sector_of_re_pos`: Watson's lemma in the sector
  `|arg z| ≤ π/2 - δ`.
* `Asymptotics.hasAsymptoticExpansion_laplace_sector`: the same for strictly increasing `Re α_s`,
  when it is an asymptotic expansion in DLMF's sense.

The proofs are adapted from the lean-DLMF project (<https://github.com/bjbraams/lean-DLMF>):
the remainder bound and Watson's lemma with exponents in steps of `1` from
`DLMFMathlib/Analysis/Asymptotics/Watson.lean`, the sector form from
`DLMFMathlib/Analysis/Asymptotics/WatsonSector.lean`
(`hasAsymptoticExpansion_integral_cexp_smul_sector`), and the statements for an arbitrary
sequence of exponents from `DLMF/AsymptoticApproximations/Integrals/Watson.lean`
(`hasAsymptoticExpansion_integral_exp_smul_rpow_seq` on the real line with real exponents,
`hasAsymptoticExpansion_integral_cexp_smul_cpow_seq` in a sector with complex exponents). There
the sector is written `δ ‖z‖ ≤ re z` (`Asymptotics.sectorAtTop`); here it is the sector
`|arg z| ≤ π/2 - δ` of DLMF.

## References

* DLMF §2.3(ii), <https://dlmf.nist.gov/2.3.ii>, and §2.4(i), <https://dlmf.nist.gov/2.4.i>.
* N. Bleistein and R. A. Handelsman, *Asymptotic Expansions of Integrals*, §4.1.
-/

public section

noncomputable section

open MeasureTheory Set Filter Finset Complex TauCeti
open scoped Topology Real

namespace Asymptotics

/-- The remainder of Watson's expansion is a Laplace integral. If `Re α_s > 0` for `s < N`,
`t ↦ e^{-σt} q(t)` is integrable on `(0, ∞)`, `σ ≤ re z` and `0 < re z`, then
`∫₀^∞ e^{-zt} q(t) dt - ∑_{s<N} Γ(α_s) c_s z^{-α_s}` is the Laplace integral at `z` of
`q(t) - ∑_{s<N} c_s t^{α_s - 1}`. -/
theorem integral_cexp_neg_mul_mul_sub_sum_eq {q : ℝ → ℂ} {α c : ℕ → ℂ} {σ : ℝ} {N : ℕ} {z : ℂ}
    (hα : ∀ s < N, 0 < (α s).re)
    (hint : IntegrableOn (fun t => Real.exp (-σ * t) • q t) (Ioi 0)) (hσ : σ ≤ z.re)
    (hz : 0 < z.re) :
    (∫ t in Ioi (0 : ℝ), cexp (-(z * t)) * q t) - ∑ s ∈ range N, z ^ (-α s) • (Gamma (α s) * c s) =
      ∫ t in Ioi (0 : ℝ), cexp (-(z * t)) • (q t - ∑ s ∈ range N, c s * (t : ℂ) ^ (α s - 1)) := by
  -- the Laplace transforms of `q` and of the Gamma terms `t^{α_s - 1}`
  have hLq : HasLaplace q z (∫ t in Ioi (0 : ℝ), cexp (-(z * t)) * q t) := by
    have hσ' : IntegrableOn (fun t : ℝ => cexp (-(σ : ℂ) * t) • q t) (Ioi 0) :=
      hint.congr_fun (fun t _ => by simp [Complex.real_smul]) measurableSet_Ioi
    exact HasLaplace.intro (integrable_cexp_neg_mul_smul_of_re_le hσ'
      ((ae_restrict_mem measurableSet_Ioi).mono fun _ ht => le_of_lt ht) (by simpa using hσ))
      (setIntegral_congr_fun measurableSet_Ioi fun t _ => by simp)
  have hLs (s : ℕ) (hs : s < N) :
      HasLaplace (fun t : ℝ => (t : ℂ) ^ (α s - 1)) z (Gamma (α s) * z ^ (-α s)) := by
    refine HasLaplace.intro ((integrableOn_cpow_mul_exp_neg_mul_Ioi (hα s hs) hz).congr_fun
      (fun t _ => by simp [mul_comm]) measurableSet_Ioi) ?_
    rw [← integral_cpow_mul_exp_neg_mul_Ioi_of_re_pos (hα s hs) hz]
    exact setIntegral_congr_fun measurableSet_Ioi fun t _ => by simp [mul_comm]
  have hL := (hLq.sub (hasLaplace_sum (u := range N) fun s hs =>
    (hLs s (mem_range.mp hs)).const_smul (c s))).integral_eq
  have hsum : ∑ s ∈ range N, z ^ (-α s) • (Gamma (α s) * c s) =
      ∑ s ∈ range N, c s • (Gamma (α s) * z ^ (-α s)) :=
    sum_congr rfl fun s _ => by
      simp only [smul_eq_mul]
      ring
  rw [hsum, ← hL]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, neg_mul]

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
  have hre : Tendsto re (map ofReal atTop) atTop :=
    tendsto_map'_iff.mpr (tendsto_id.congr fun x => (ofReal_re x).symm)
  have hb := (isBigO_integral_cexp_neg_mul_smul hre (hq N)).comp_tendsto tendsto_map
  simp only [Function.comp_def, ofReal_re] at hb
  -- compare the real power `x^{-Re α_N}` with the norm of the complex scale
  have hnorm : (fun x : ℝ => x ^ (-(α N).re)) =ᶠ[atTop] fun x => ‖(x : ℂ) ^ (-α N)‖ := by
    filter_upwards [eventually_gt_atTop 0] with x hx
    rw [norm_cpow_eq_rpow_re_of_pos hx, neg_re]
  refine (isBigO_norm_right.mp (hb.congr' EventuallyEq.rfl hnorm)).congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_ge_atTop σ, eventually_gt_atTop 0] with x hxσ hx
  exact (integral_cexp_neg_mul_mul_sub_sum_eq (fun s _ => hα s) hint (by simpa using hxσ)
    (by simpa using hx)).symm

/-- **Watson's lemma in a sector** (DLMF 2.4.1, for a general sequence of exponents). Let
`α : ℕ → ℂ` have `Re α_s > 0` for all `s`, and let `q : ℝ → ℂ` have `t ↦ e^{-σt} q(t)`
integrable on `(0, ∞)` and, for every `N`, `q(t) - ∑_{s<N} c_s t^{α_s - 1} = O(t^{Re α_N - 1})`
as `t → 0+`. Then for every `δ > 0`, `∫₀^∞ e^{-zt} q(t) dt ∼ ∑ Γ(α_s) c_s z^{-α_s}` as `z → ∞`
in the sector `|arg z| ≤ π/2 - δ`, with principal powers, in the sense of
`HasAsymptoticExpansion`: for every `N` the remainder after `N` terms is `O(z^{-α_N})`. This is
an asymptotic expansion in DLMF's sense when `Re α_s` is strictly increasing
(`Asymptotics.hasAsymptoticExpansion_laplace_sector`); otherwise it is only this family of
remainder bounds. The Laplace integral converges for `re z ≥ σ`, which holds eventually along
the sector filter. For `δ > π/2` the sector is empty, and for `δ = π/2` it is the nonnegative
real axis. -/
theorem hasAsymptoticExpansion_laplace_sector_of_re_pos {q : ℝ → ℂ} {α c : ℕ → ℂ} {σ δ : ℝ}
    (hα : ∀ s, 0 < (α s).re) (hδ : 0 < δ)
    (hint : IntegrableOn (fun t => Real.exp (-σ * t) • q t) (Ioi 0))
    (hq : ∀ N, (fun t : ℝ => q t - ∑ s ∈ range N, c s * (t : ℂ) ^ (α s - 1))
      =O[𝓝[>] 0] fun t => t ^ ((α N).re - 1)) :
    HasAsymptoticExpansion (Bornology.cobounded ℂ ⊓ 𝓟 {z | |arg z| ≤ π / 2 - δ})
      (fun s z => z ^ (-α s)) (fun s => Gamma (α s) * c s)
      fun z => ∫ t in Ioi (0 : ℝ), cexp (-(z * t)) * q t := by
  have hθ : π / 2 - δ < π / 2 := by linarith
  have hre := tendsto_re_cobounded_inf_principal_abs_arg_le hθ
  refine HasAsymptoticExpansion.of_isBigO fun N => ?_
  -- on the sector, `(re z)^{-Re α_N}` is comparable to `‖z‖^{-Re α_N}`, hence to `z^{-α_N}`
  have hscale : (fun z : ℂ => z.re ^ (-(α N).re)) =O[Bornology.cobounded ℂ ⊓
      𝓟 {z | |arg z| ≤ π / 2 - δ}] fun z => z ^ (-α N) := by
    have h1 := ((isTheta_re_norm_principal_abs_arg_le hθ).mono inf_le_right).rpow
      (r := -(α N).re) (hre.eventually (eventually_ge_atTop 0))
      (Eventually.of_forall fun z => norm_nonneg z)
    have h2 := isTheta_cpow_const_rpow (l := Bornology.cobounded ℂ ⊓
      𝓟 {z | |arg z| ≤ π / 2 - δ}) (f := id) (b := -α N) fun h => by
        simp only [neg_re, neg_eq_zero] at h
        exact absurd h (hα N).ne'
    exact h1.isBigO.trans h2.symm.isBigO
  refine ((isBigO_integral_cexp_neg_mul_smul hre (hq N)).trans hscale).congr' ?_ EventuallyEq.rfl
  filter_upwards [hre.eventually (eventually_ge_atTop σ), hre.eventually (eventually_gt_atTop 0)]
    with z hσ hz
  exact (integral_cexp_neg_mul_mul_sub_sum_eq (fun s _ => hα s) hint hσ hz).symm

/-- **Watson's lemma in a sector** (DLMF 2.4.1, for a general sequence of exponents). Let
`α : ℕ → ℂ` have `Re α_0 > 0` and strictly increasing real parts, and let `q : ℝ → ℂ` have
`t ↦ e^{-σt} q(t)` integrable on `(0, ∞)` and, for every `N`,
`q(t) - ∑_{s<N} c_s t^{α_s - 1} = O(t^{Re α_N - 1})` as `t → 0+`. Then for every `δ > 0`,
`∫₀^∞ e^{-zt} q(t) dt ∼ ∑ Γ(α_s) c_s z^{-α_s}` as `z → ∞` in the sector `|arg z| ≤ π/2 - δ`,
with principal powers: for every `N` the remainder after `N` terms is `O(z^{-α_N})`, and the
strictly increasing real parts make `fun s z => z ^ (-α s)` an asymptotic scale. DLMF's case is
`α_s = (s + λ)/μ`, and `Asymptotics.hasAsymptoticExpansion_laplace` is the restriction to the
positive real axis. This is `Asymptotics.hasAsymptoticExpansion_laplace_sector_of_re_pos`, which
needs only `Re α_s > 0` for all `s`. -/
theorem hasAsymptoticExpansion_laplace_sector {q : ℝ → ℂ} {α c : ℕ → ℂ} {σ δ : ℝ}
    (hα0 : 0 < (α 0).re) (hα : StrictMono fun s => (α s).re) (hδ : 0 < δ)
    (hint : IntegrableOn (fun t => Real.exp (-σ * t) • q t) (Ioi 0))
    (hq : ∀ N, (fun t : ℝ => q t - ∑ s ∈ range N, c s * (t : ℂ) ^ (α s - 1))
      =O[𝓝[>] 0] fun t => t ^ ((α N).re - 1)) :
    HasAsymptoticExpansion (Bornology.cobounded ℂ ⊓ 𝓟 {z | |arg z| ≤ π / 2 - δ})
      (fun s z => z ^ (-α s)) (fun s => Gamma (α s) * c s)
      fun z => ∫ t in Ioi (0 : ℝ), cexp (-(z * t)) * q t :=
  hasAsymptoticExpansion_laplace_sector_of_re_pos
    (fun s => hα0.trans_le (hα.monotone (Nat.zero_le s))) hδ hint hq

end Asymptotics

/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import TauCeti.Analysis.Asymptotics.AsymptoticExpansion
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import TauCeti.Analysis.SpecialFunctions.Gamma.IntegralComplexRate
import TauCeti.MeasureTheory.Integral.Exp.Damped
import TauCeti.MeasureTheory.Integral.RpowLaplace
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Watson's lemma on the real line

Let `α : ℕ → ℂ` have exponents with positive real parts, let `c : ℕ → ℂ`, and let `q : ℝ → ℂ`
have `t ↦ e^{-σt} q(t)` integrable on `(0, ∞)` for some real `σ` and, for every `N`,

`q(t) - ∑_{s<N} c_s t^{α_s - 1} = O(t^{Re α_N - 1})`   as `t → 0+`.

Then the Laplace integral has the asymptotic expansion

`∫₀^∞ e^{-xt} q(t) dt ∼ ∑ Γ(α_s) c_s x^{-α_s}`   as `x → +∞`

(DLMF 2.3.7–2.3.8, where `α_s = (s + λ)/μ`; for a general sequence of exponents this is the
extension of Bleistein and Handelsman, *Asymptotic Expansions of Integrals*, §4.1). The terms
are Gamma integrals. For the remainder one splits the integral at a small `δ`: near `0` the
bound on `q` gives `O(x^{-Re α_N})` through the Gamma integral, and beyond `δ` the factor
`e^{-xt}` contributes `O(e^{-δx})`, which is smaller than every power of `x`.

Near `0` the hypothesis gives `q(t) = O(t^{Re α_0 - 1})`, which is integrable, so the
integrability of `e^{-σt} q(t)` on `(0, ∞)` amounts to local integrability of `q` on `(0, ∞)`
together with integrability of `e^{-σt} q(t)` on `(1, ∞)`.

## Main results

* `Asymptotics.isBigO_integral_exp_neg_mul_smul`: if `G(t) = O(t^{s-1})` as `t → 0+`, then
  `∫₀^∞ e^{-xt} G(t) dt = O(x^{-s})` as `x → +∞`.
* `Asymptotics.hasAsymptoticExpansion_laplace`: Watson's lemma, and
  `Asymptotics.hasAsymptoticExpansion_laplace_of_locallyIntegrableOn`, the same with the second
  form of the integrability hypothesis.

The integrability of `e^{-xt} G(t)` for `x ≥ σ`, the equivalence of the two forms of the
integrability hypothesis (`TauCeti.integrableOn_exp_neg_mul_smul_iff`) and the tail bound beyond
`δ` are in `TauCeti.MeasureTheory.Integral.Exp.Damped`, the bound near `0` through the Gamma
integral in `TauCeti.MeasureTheory.Integral.RpowLaplace`.

The proofs are adapted from the lean-DLMF project (<https://github.com/bjbraams/lean-DLMF>),
file `DLMFMathlib/Analysis/Asymptotics/Watson.lean`, and generalized from exponents in steps
of `1` to an arbitrary sequence of complex exponents.

## References

* DLMF §2.3(ii), <https://dlmf.nist.gov/2.3.ii>.
* N. Bleistein and R. A. Handelsman, *Asymptotic Expansions of Integrals*, §4.1.
-/

public section

noncomputable section

open MeasureTheory Set Filter Finset Complex
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace Asymptotics

/-- `isBigO_integral_exp_neg_mul_smul` when `t ↦ e^{-σt} G(t)` is integrable on `(0, ∞)`. -/
private theorem isBigO_integral_exp_neg_mul_smul_of_integrableOn {G : ℝ → E} {s σ : ℝ}
    (hint : IntegrableOn (fun t => Real.exp (-σ * t) • G t) (Ioi 0))
    (hG : G =O[𝓝[>] 0] fun t => t ^ (s - 1)) :
    (fun x : ℝ => ∫ t in Ioi (0 : ℝ), Real.exp (-x * t) • G t) =O[atTop] fun x => x ^ (-s) := by
  set A := ∫ t in Ioi (0 : ℝ), ‖Real.exp (-σ * t) • G t‖
  rcases le_or_gt s 0 with hs | hs
  · -- for `s ≤ 0` the integral is at most `A ≤ A x^{-s}`
    refine IsBigO.of_bound A ?_
    filter_upwards [eventually_ge_atTop σ, eventually_ge_atTop 1] with x hxσ hx1
    have h := TauCeti.norm_setIntegral_Ioi_exp_neg_mul_smul_le hint hxσ
    rw [mul_zero, Real.exp_zero, one_mul] at h
    refine h.trans (le_mul_of_one_le_right (integral_nonneg fun _ => norm_nonneg _) ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    exact Real.one_le_rpow hx1 (neg_nonneg.mpr hs)
  -- the bound `‖G t‖ ≤ K t^{s-1}` on `(0, δ]`
  obtain ⟨K, hK0, hK⟩ := hG.exists_pos
  obtain ⟨δ, hδ0, hδ⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp hK.bound
  have hδ0 : 0 < δ := hδ0
  have hGb (t : ℝ) (ht : t ∈ Ioc 0 δ) : ‖G t‖ ≤ K * t ^ (s - 1) := by
    simpa [abs_of_nonneg (Real.rpow_nonneg ht.1.le _)] using hδ ht
  have hAle : ∫ t in Ioi δ, ‖Real.exp (-σ * t) • G t‖ ≤ A :=
    setIntegral_mono_set hint.norm (Eventually.of_forall fun _ => norm_nonneg _)
      (Eventually.of_forall (Ioi_subset_Ioi hδ0.le))
  -- `e^{-δx}` is eventually smaller than `x^{-s}`
  have hexp : ∀ᶠ x in atTop, Real.exp (-δ * x) ≤ x ^ (-s) := by
    filter_upwards [(isLittleO_exp_neg_mul_rpow_atTop hδ0 (-s)).bound one_pos,
      eventually_gt_atTop 0] with x hx hx0
    rwa [one_mul, Real.norm_of_nonneg (Real.exp_pos _).le,
      Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _)] at hx
  refine IsBigO.of_bound (K * Real.Gamma s + Real.exp (σ * δ) * A) ?_
  filter_upwards [hexp, eventually_ge_atTop σ, eventually_gt_atTop 0] with x hxe hxσ hx0
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _), add_mul]
  have hI := hint.exp_neg_mul_smul_of_le hxσ
  rw [← Ioc_union_Ioi_eq_Ioi hδ0.le, setIntegral_union (Ioc_disjoint_Ioi le_rfl)
    measurableSet_Ioi (hI.mono_set Ioc_subset_Ioi_self) (hI.mono_set (Ioi_subset_Ioi hδ0.le))]
  refine (norm_add_le _ _).trans
    (add_le_add (TauCeti.norm_setIntegral_Ioc_exp_neg_mul_smul_le hs hx0 hK0.le hGb) ?_)
  -- the tail: `e^{-(x-σ)δ} = e^{σδ} e^{-δx}`
  refine (TauCeti.norm_setIntegral_Ioi_exp_neg_mul_smul_le
    (hint.mono_set (Ioi_subset_Ioi hδ0.le)) hxσ).trans ?_
  have hsplit : -(x - σ) * δ = σ * δ + -δ * x := by ring
  rw [hsplit, Real.exp_add, mul_right_comm]
  gcongr

/-- **Watson's remainder bound.** If `G(t) = O(t^{s-1})` as `t → 0+`, then
`∫₀^∞ e^{-xt} G(t) dt = O(x^{-s})` as `x → +∞`. If `t ↦ e^{-xt} G(t)` is integrable on `(0, ∞)`
for no `x`, every integral is `0` and the bound holds trivially. -/
theorem isBigO_integral_exp_neg_mul_smul {G : ℝ → E} {s : ℝ}
    (hG : G =O[𝓝[>] 0] fun t => t ^ (s - 1)) :
    (fun x : ℝ => ∫ t in Ioi (0 : ℝ), Real.exp (-x * t) • G t) =O[atTop] fun x => x ^ (-s) := by
  by_cases hex : ∃ σ, IntegrableOn (fun t => Real.exp (-σ * t) • G t) (Ioi 0)
  · obtain ⟨σ, hint⟩ := hex
    exact isBigO_integral_exp_neg_mul_smul_of_integrableOn hint hG
  · simp only [not_exists] at hex
    have h0 : (fun x : ℝ => ∫ t in Ioi (0 : ℝ), Real.exp (-x * t) • G t) = 0 :=
      funext fun x => integral_undef (hex x)
    rw [h0]
    exact isBigO_zero _ _

/-- **Watson's lemma** (DLMF 2.3.7–2.3.8, for a general sequence of exponents). Let `α : ℕ → ℂ`
have `Re α_s > 0` for all `s`, and let `q : ℝ → ℂ` have `t ↦ e^{-σt} q(t)` integrable on
`(0, ∞)` and, for every `N`, `q(t) - ∑_{s<N} c_s t^{α_s - 1} = O(t^{Re α_N - 1})` as
`t → 0+`. Then `∫₀^∞ e^{-xt} q(t) dt ∼ ∑ Γ(α_s) c_s x^{-α_s}` as `x → +∞`. -/
theorem hasAsymptoticExpansion_laplace {q : ℝ → ℂ} {α c : ℕ → ℂ} {σ : ℝ}
    (hα : ∀ s, 0 < (α s).re) (hint : IntegrableOn (fun t => Real.exp (-σ * t) • q t) (Ioi 0))
    (hq : ∀ N, (fun t : ℝ => q t - ∑ s ∈ range N, c s * (t : ℂ) ^ (α s - 1))
      =O[𝓝[>] 0] fun t => t ^ ((α N).re - 1)) :
    HasAsymptoticExpansion atTop (fun s (x : ℝ) => (x : ℂ) ^ (-α s)) (fun s => Gamma (α s) * c s)
      fun x : ℝ => ∫ t in Ioi (0 : ℝ), cexp (-(x * t)) * q t := by
  refine HasAsymptoticExpansion.of_isBigO fun N => ?_
  have hsmul (x t : ℝ) (z : ℂ) : Real.exp (-x * t) • z = cexp (-(x * t)) * z := by
    simp [Complex.real_smul]
  -- each term `e^{-xt} c_s t^{α_s - 1}` is integrable for `x > 0`
  have hterm (x : ℝ) (hx : 0 < x) (s : ℕ) :
      IntegrableOn (fun t : ℝ => Real.exp (-x * t) • (c s * (t : ℂ) ^ (α s - 1))) (Ioi 0) := by
    refine IntegrableOn.congr_fun
      ((integrableOn_cpow_mul_exp_neg_mul_Ioi (hα s) (w := x) (by simpa using hx)).const_mul
        (c s)) (fun t _ => ?_) measurableSet_Ioi
    rw [hsmul]
    ring
  have hsum (x : ℝ) (hx : 0 < x) : IntegrableOn
      (fun t : ℝ => ∑ s ∈ range N, Real.exp (-x * t) • (c s * (t : ℂ) ^ (α s - 1))) (Ioi 0) :=
    integrable_finsetSum _ fun s _ => hterm x hx s
  have hb := isBigO_integral_exp_neg_mul_smul (hq N)
  -- compare the real power `x^{-Re α_N}` with the norm of the complex scale
  have hnorm : (fun x : ℝ => x ^ (-(α N).re)) =ᶠ[atTop] fun x => ‖(x : ℂ) ^ (-α N)‖ := by
    filter_upwards [eventually_gt_atTop 0] with x hx
    rw [norm_cpow_eq_rpow_re_of_pos hx, neg_re]
  refine (isBigO_norm_right.mp (hb.congr' EventuallyEq.rfl hnorm)).congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_ge_atTop σ, eventually_gt_atTop 0] with x hxσ hx
  simp only [smul_sub, Finset.smul_sum]
  rw [integral_sub (hint.exp_neg_mul_smul_of_le hxσ) (hsum x hx),
    integral_finsetSum _ fun s _ => hterm x hx s]
  congr 1
  · exact setIntegral_congr_fun measurableSet_Ioi fun t _ => hsmul x t (q t)
  refine sum_congr rfl fun s _ => ?_
  have hx' : 0 < (x : ℂ).re := by simpa using hx
  simp_rw [hsmul]
  rw [smul_eq_mul, ← mul_assoc, mul_comm ((x : ℂ) ^ (-α s)),
    ← integral_cpow_mul_exp_neg_mul_Ioi_of_re_pos (hα s) hx', ← integral_mul_const]
  exact setIntegral_congr_fun measurableSet_Ioi fun t _ => by ring

/-- **Watson's lemma** with the integrability hypothesis in its second form: `q` locally
integrable on `(0, ∞)` and `t ↦ e^{-σt} q(t)` integrable on `(1, ∞)`. -/
theorem hasAsymptoticExpansion_laplace_of_locallyIntegrableOn {q : ℝ → ℂ} {α c : ℕ → ℂ} {σ : ℝ}
    (hα : ∀ s, 0 < (α s).re) (hloc : LocallyIntegrableOn q (Ioi 0))
    (hint : IntegrableOn (fun t => Real.exp (-σ * t) • q t) (Ioi 1))
    (hq : ∀ N, (fun t : ℝ => q t - ∑ s ∈ range N, c s * (t : ℂ) ^ (α s - 1))
      =O[𝓝[>] 0] fun t => t ^ ((α N).re - 1)) :
    HasAsymptoticExpansion atTop (fun s (x : ℝ) => (x : ℂ) ^ (-α s)) (fun s => Gamma (α s) * c s)
      fun x : ℝ => ∫ t in Ioi (0 : ℝ), cexp (-(x * t)) * q t := by
  have hq0 : q =O[𝓝[>] 0] fun t => t ^ ((α 0).re - 1) := by simpa using hq 0
  exact hasAsymptoticExpansion_laplace hα
    ((TauCeti.integrableOn_exp_neg_mul_smul_iff (hα 0) hq0).mpr ⟨hloc, hint⟩) hq

end Asymptotics

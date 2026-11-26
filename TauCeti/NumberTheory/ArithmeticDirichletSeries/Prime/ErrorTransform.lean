/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Meromorphic.TrailingCoefficient
public import TauCeti.Analysis.LaplaceTransform.Basic
public import TauCeti.Analysis.Meromorphic.ZeroFree
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Prime.Psi
public import TauCeti.NumberTheory.LFunctions.DedekindZeta.Basic
import TauCeti.Analysis.Contour.Residue.LogDeriv
import TauCeti.Analysis.LaplaceTransform.Elementary
import TauCeti.Analysis.SpecialFunctions.Pow.Complex
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Prime.PrimeIdealTheorem
import TauCeti.NumberTheory.LFunctions.DedekindZeta.Completed
import TauCeti.NumberTheory.LSeries.SumCoeff

/-!
# The transform of the prime ideal counting error

The Laplace transform of `u ↦ ψ_K(exp u) - exp u` is
`-(ζ_K′/ζ_K)(s) / s - 1/(s - 1)` for `Re s > 1`, by partial summation of the ideal von
Mangoldt series. Its meromorphic normal form is analytic at `1`. Elsewhere in `Re s > 0`,
a zero `ρ` of `ζ_K` of multiplicity `m` contributes a simple pole of residue `-m/ρ`,
and there are no other poles there. This sign is needed for one-sided Landau arguments.

The partial summation uses Mathlib's `LSeries_eq_mul_integral`, and the local analysis at
the poles uses `TauCeti.Contour.logDeriv_eventuallyEq_principalPart` and the residue of
`logDeriv` in `TauCeti.Contour.residue_logDeriv_eq_meromorphicOrderAt`.
-/

public section
noncomputable section

open Asymptotics Complex Filter Finset MeasureTheory Set
open scoped Topology

namespace TauCeti

open LFunctions

variable (K : Type*) [Field K] [NumberField K]

/-- The meromorphic normal form of the transform of `ψ_K(x) - x` in logarithmic coordinates. -/
def primePsiErrorTransform : ℂ → ℂ :=
  toMeromorphicNFOn (fun s ↦ -logDeriv (dedekindZetaC K) s / s - (s - 1)⁻¹) univ

private theorem meromorphic_primePsiErrorExpression :
    Meromorphic (fun s ↦ -logDeriv (dedekindZetaC K) s / s - (s - 1)⁻¹) := by
  have h := (meromorphic_dedekindZetaC K).logDeriv
  have hid : Meromorphic (fun s : ℂ ↦ s) := by fun_prop
  refine (h.neg.div hid).sub ?_
  fun_prop

/-- The transform has the punctured germ of the logarithmic-derivative expression everywhere. -/
theorem primePsiErrorTransform_eventuallyEq (s : ℂ) :
    primePsiErrorTransform K =ᶠ[𝓝[≠] s]
      fun z ↦ -logDeriv (dedekindZetaC K) z / z - (z - 1)⁻¹ :=
  MeromorphicOn.toMeromorphicNFOn_eq_self_on_nhdsNE
    (meromorphicOn_univ.mpr (meromorphic_primePsiErrorExpression K)) (mem_univ s)

/-- The transform is meromorphic in normal form on the whole plane. -/
theorem meromorphicNFOn_primePsiErrorTransform : MeromorphicNFOn (primePsiErrorTransform K) univ :=
  meromorphicNFOn_toMeromorphicNFOn _ _

private theorem analyticAt_primePsiErrorExpression {s : ℂ} (h₀ : s ≠ 0)
    (hζ : dedekindZetaC K s ≠ 0) :
    AnalyticAt ℂ (fun z ↦ -logDeriv (dedekindZetaC K) z / z - (z - 1)⁻¹) s := by
  have h₁ : s ≠ 1 := by
    rintro rfl
    have hnf := meromorphicNFOn_dedekindZetaC K (mem_univ (1 : ℂ))
    have hord := hnf.meromorphicOrderAt_eq_zero_iff.mpr hζ
    simp [meromorphicOrderAt_dedekindZetaC_one] at hord
  have hlog := (analyticAt_dedekindZetaC K h₁).logDeriv hζ
  exact (hlog.neg.div analyticAt_id h₀).sub
    ((analyticAt_id.sub analyticAt_const).inv (sub_ne_zero.mpr h₁))

/-- At a nonzero point where the normal form of `ζ_K` is nonzero, the transform agrees
pointwise with the logarithmic-derivative expression. This excludes the pole at `1`, where
`dedekindZetaC K` takes its normal-form value `0`. -/
theorem primePsiErrorTransform_apply {s : ℂ} (h₀ : s ≠ 0) (hζ : dedekindZetaC K s ≠ 0) :
    primePsiErrorTransform K s = -logDeriv (dedekindZetaC K) s / s - (s - 1)⁻¹ :=
  toMeromorphicNFOn_apply_of_analyticAt (meromorphic_primePsiErrorExpression K)
    (analyticAt_primePsiErrorExpression K h₀ hζ)

/-- On `Re s > 1`, the Laplace transform of `u ↦ ψ_K(exp u)` converges absolutely and is
`-(ζ_K′/ζ_K)(s) / s`. -/
theorem hasLaplace_primePsi_exp {s : ℂ} (hs : 1 < s.re) :
    HasLaplace (fun u ↦ (primePsi K univ (Real.exp u) : ℂ)) s
      (-logDeriv (dedekindZetaC K) s / s) := by
  let a : ℕ → ℂ := fun n ↦ (primeVonMangoldtCoeff K univ n : ℂ)
  have hpsi (x : ℝ) : ∑ n ∈ Icc 1 ⌊x⌋₊, a n = (primePsi K univ x : ℂ) := by
    simp only [a, primePsi_eq_sum_Icc, ofReal_sum]
  have hO : (fun n : ℕ ↦ ∑ j ∈ Icc 1 n, a j) =O[atTop] fun n : ℕ ↦ (n : ℝ) ^ (1 : ℝ) := by
    apply isBigO_norm_left.mp
    have h := (primeIdealTheorem K).1.isBigO.comp_tendsto tendsto_natCast_atTop_atTop
    refine (h.norm_left.congr_left fun n ↦ ?_).congr_right fun n ↦ by simp
    rw [Function.comp_apply, ← Complex.norm_real, ← hpsi]
    simp
  have hsum := LSeriesHasSum_primeVonMangoldtCoeff_univ (K := K) hs
  have hM := LSeries_eq_mul_integral a zero_le_one hs hsum.LSeriesSummable hO
  have hM_int := LSeries.integrableOn_sum_mul_cpow_of_isBigO a hO hs
  have hζ : logDeriv (dedekindZetaC K) s = logDeriv (NumberField.dedekindZeta K) s := by
    apply Filter.EventuallyEq.eq_of_nhds
    apply logDeriv_congr_nhds
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds hs] with z hz
    exact dedekindZetaC_eq_dedekindZeta K hz
  have h₀ : s ≠ 0 := by rintro rfl; norm_num at hs
  have hsub (u : ℝ) :
      Real.exp u • ((∑ j ∈ Icc 1 ⌊Real.exp u⌋₊, a j) * (Real.exp u : ℂ) ^ (-(s + 1))) =
        cexp (-s * u) • (primePsi K univ (Real.exp u) : ℂ) := by
    rw [Complex.real_smul, ofReal_exp_cpow, ofReal_exp, smul_eq_mul]
    rw [hpsi]
    rw [mul_comm (primePsi K univ (Real.exp u) : ℂ), ← mul_assoc, ← Complex.exp_add]
    congr 2
    ring
  -- The substitution `x = exp u` absorbs the factor `x⁻¹` in the Mellin weight.
  refine HasLaplace.intro ?_ ?_
  · rw [← Real.exp_zero, ← integrableOn_comp_exp_Ioi] at hM_int
    simpa only [IntegrableOn, hsub] using hM_int
  · rw [← Real.exp_zero, ← integral_comp_exp_Ioi] at hM
    rw [hsum.LSeries_eq, neg_div, ← logDeriv_apply, ← hζ, mul_comm s] at hM
    simpa only [hsub] using (eq_div_iff_mul_eq h₀).2 hM.symm

/-- On `Re s > 1`, the Laplace transform of `u ↦ ψ_K(exp u) - exp u` converges absolutely
and equals the meromorphic transform. -/
theorem hasLaplace_primePsi_sub_exp {s : ℂ} (hs : 1 < s.re) :
    HasLaplace (fun u ↦ ((primePsi K univ (Real.exp u) - Real.exp u : ℝ) : ℂ)) s
      (primePsiErrorTransform K s) := by
  have h₀ : s ≠ 0 := by rintro rfl; norm_num at hs
  have hζ : dedekindZetaC K s ≠ 0 :=
    dedekindZetaC_eq_dedekindZeta K hs ▸ dedekindZeta_ne_zero_of_one_lt_re hs
  rw [primePsiErrorTransform_apply K h₀ hζ]
  refine ((hasLaplace_primePsi_exp K hs).sub
    (hasLaplace_cexp_mul (w := 1) (by simpa using hs))).congr_ae ?_
  exact Eventually.of_forall fun u ↦ by simp [Pi.sub_apply, ofReal_exp]

/-- The subtraction of the main term cancels the pole of the transform at `1`. -/
theorem analyticAt_primePsiErrorTransform_one : AnalyticAt ℂ (primePsiErrorTransform K) 1 := by
  have horder : meromorphicOrderAt (dedekindZetaC K) 1 = ((-1 : ℤ) : WithTop ℤ) :=
    meromorphicOrderAt_dedekindZetaC_one K
  obtain ⟨g, hga, hg₀, he⟩ := Contour.logDeriv_eventuallyEq_principalPart
    (meromorphic_dedekindZetaC K 1) horder
  have ha : AnalyticAt ℂ (fun z ↦ -(1 + logDeriv g z) / z) 1 :=
    ((analyticAt_const.add (hga.logDeriv hg₀)).neg.div analyticAt_id one_ne_zero)
  -- The two polar terms combine as `(1 / z - 1) / (z - 1) = -1 / z`.
  have hgerm : primePsiErrorTransform K =ᶠ[𝓝[≠] (1 : ℂ)] fun z ↦ -(1 + logDeriv g z) / z := by
    filter_upwards [primePsiErrorTransform_eventuallyEq K 1, he, self_mem_nhdsWithin,
      (eventually_ne_nhds (one_ne_zero : (1 : ℂ) ≠ 0)).filter_mono nhdsWithin_le_nhds]
      with z hz hlog hz₁ hz₀
    rw [hz, hlog]
    push_cast
    field_simp [sub_ne_zero.mpr hz₁, hz₀]
    ring
  have hnf := meromorphicNFOn_primePsiErrorTransform K (mem_univ (1 : ℂ))
  exact hnf.meromorphicOrderAt_nonneg_iff_analyticAt.mp <|
    (meromorphicOrderAt_congr hgerm).symm ▸ ha.meromorphicOrderAt_nonneg

private theorem tendsto_sub_mul_primePsiErrorTransform {ρ : ℂ} (h₀ : ρ ≠ 0) (h₁ : ρ ≠ 1)
    {m : ℤ} (hm : meromorphicOrderAt (dedekindZetaC K) ρ = m) :
    Tendsto (fun z ↦ (z - ρ) * primePsiErrorTransform K z) (𝓝[≠] ρ) (𝓝 (-(m : ℂ) / ρ)) := by
  have hζ := meromorphic_dedekindZetaC K ρ
  have h := Contour.tendsto_sub_mul_nhds_residue hζ.logDeriv
    (Contour.neg_one_le_meromorphicOrderAt_logDeriv hζ)
  rw [Contour.residue_logDeriv_eq_meromorphicOrderAt hζ hm] at h
  have ht : Tendsto (fun z : ℂ ↦ z) (𝓝[≠] ρ) (𝓝 ρ) := nhdsWithin_le_nhds
  have hreg : Tendsto (fun z ↦ (z - ρ) * (z - 1)⁻¹) (𝓝[≠] ρ) (𝓝 0) := by
    simpa using (ht.sub_const ρ).mul ((ht.sub_const 1).inv₀ (sub_ne_zero.mpr h₁))
  refine ((h.neg.div ht h₀).sub hreg).congr' ?_ |>.trans_eq (by simp)
  filter_upwards [primePsiErrorTransform_eventuallyEq K ρ] with z hz
  rw [hz]
  dsimp only [Pi.sub_apply, Pi.div_apply, Pi.neg_apply]
  ring

/-- At a nonzero point `ρ` where `ζ_K` vanishes with multiplicity `m`, the error transform
has a simple pole with residue `-m/ρ`. The latter is the trailing coefficient at a simple pole. -/
theorem primePsiErrorTransform_simplePole {ρ : ℂ} (h₀ : ρ ≠ 0)
    (hz : 0 < meromorphicOrderAt (dedekindZetaC K) ρ) :
    meromorphicOrderAt (primePsiErrorTransform K) ρ = -1 ∧
      meromorphicTrailingCoeffAt (primePsiErrorTransform K) ρ =
        -((meromorphicOrderAt (dedekindZetaC K) ρ).untop₀ : ℂ) / ρ := by
  have h₁ : ρ ≠ 1 := by
    rintro rfl
    rw [meromorphicOrderAt_dedekindZetaC_one] at hz
    exact absurd hz (by decide)
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp (meromorphicOrderAt_dedekindZetaC_ne_top K ρ)
  have hm₀ : 0 < m := by exact_mod_cast (hm ▸ hz)
  have ht := tendsto_sub_mul_primePsiErrorTransform K h₀ h₁ hm.symm
  have hf := (meromorphicNFOn_primePsiErrorTransform K (mem_univ ρ)).meromorphicAt
  have hord := hf.meromorphicOrderAt_eq_neg_one_of_tendsto_sub_smul
    (div_ne_zero (neg_ne_zero.mpr (Int.cast_ne_zero.mpr hm₀.ne')) h₀) ht
  refine ⟨hord, ?_⟩
  rw [← Contour.residue_eq_meromorphicTrailingCoeffAt_of_order_eq_neg_one hord, ← hm,
    WithTop.untop₀_coe]
  exact Contour.residue_eq_of_tendsto_sub_mul hf ht

/-- Except at `0`, the poles of the prime ideal error transform are exactly the zeros of the
continued Dedekind zeta function. The pole of `ζ_K` at `1` does not contribute a pole. -/
theorem meromorphicOrderAt_primePsiErrorTransform_neg_iff {ρ : ℂ} (h₀ : ρ ≠ 0) :
    meromorphicOrderAt (primePsiErrorTransform K) ρ < 0 ↔
      0 < meromorphicOrderAt (dedekindZetaC K) ρ := by
  rcases eq_or_ne ρ 1 with rfl | h₁
  · have h := (analyticAt_primePsiErrorTransform_one K).meromorphicOrderAt_nonneg
    exact iff_of_false (not_lt.mpr h) (by simp [meromorphicOrderAt_dedekindZetaC_one])
  refine ⟨fun hp ↦ ?_, fun hz ↦ ?_⟩
  · by_contra! hn
    have hne := (analyticAt_dedekindZetaC K h₁).meromorphicOrderAt_nonpos_iff.mp hn
    have he := analyticAt_primePsiErrorExpression K h₀ hne
    exact (not_lt.mpr he.meromorphicOrderAt_nonneg)
      ((meromorphicOrderAt_congr (primePsiErrorTransform_eventuallyEq K ρ)) ▸ hp)
  · rw [(primePsiErrorTransform_simplePole K h₀ hz).1]
    exact WithTop.coe_lt_coe.mpr (neg_one_lt_zero : (-1 : ℤ) < 0)

/-- On a right half-plane not containing the origin, zero-freeness of `ζ_K` is equivalent
to absence of poles of the prime ideal error transform. -/
theorem zeroFreeRightOf_dedekindZetaC_iff_primePsiErrorTransform {θ : ℝ} (hθ : 0 ≤ θ) :
    ZeroFreeRightOf θ (dedekindZetaC K) ↔
      ∀ s : ℂ, θ < s.re → 0 ≤ meromorphicOrderAt (primePsiErrorTransform K) s := by
  rw [zeroFreeRightOf_iff]
  refine forall₂_congr fun s hs ↦ ?_
  have h₀ : s ≠ 0 := fun he ↦ by simpa [he] using hθ.trans_lt hs
  have he := meromorphicOrderAt_primePsiErrorTransform_neg_iff K h₀
  simpa only [not_lt] using he.not.symm

/-- The residue at a positive real pole of the prime ideal error transform has negative real
part. -/
theorem re_meromorphicTrailingCoeffAt_primePsiErrorTransform_neg {β : ℝ} (hβ : 0 < β)
    (hp : meromorphicOrderAt (primePsiErrorTransform K) (β : ℂ) < 0) :
    (meromorphicTrailingCoeffAt (primePsiErrorTransform K) (β : ℂ)).re < 0 := by
  have h₀ := Complex.ofReal_ne_zero.mpr hβ.ne'
  have hz := (meromorphicOrderAt_primePsiErrorTransform_neg_iff K h₀).mp hp
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp (meromorphicOrderAt_dedekindZetaC_ne_top K β)
  have hm₀ : 0 < m := by exact_mod_cast (hm ▸ hz)
  rw [(primePsiErrorTransform_simplePole K h₀ hz).2, ← hm, WithTop.untop₀_coe]
  have hcast : -(m : ℂ) / (β : ℂ) = ((-(m : ℝ) / β : ℝ) : ℂ) := by push_cast; rfl
  rw [hcast, Complex.ofReal_re]
  exact div_neg_of_neg_of_pos (neg_neg_of_pos (Int.cast_pos.mpr hm₀)) hβ

end TauCeti

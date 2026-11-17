/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Calculus.DSlope
public import TauCeti.Analysis.Analytic.MultiIndex.Taylor
import Mathlib.Analysis.Analytic.Composition
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Normed.Group.InfiniteSum

/-!
# Coordinate division and analyticity of one-variable divided differences

This file establishes division of a multivariable analytic function by a power of a single
coordinate `(z i - x i) ^ m`, and deduces that the one-coordinate divided difference
`z ↦ dslope (fun w ↦ f (Function.update z i w)) ζ (z i)` is analytic across the hyperplane
`z i = ζ` as well as away from it.

## Main results

* `TauCeti.exists_hasFPowerSeriesOnBall_eq_pow_smul`: if `f (x + z)` has a normally convergent
  multi-index expansion on the open polydisc of radius `ρ` whose coefficients vanish whenever
  `α i < m`, then `f (x + z) = z i ^ m • g z` for an analytic function `g` on the same polydisc
  whose coefficients are shifted by `Pi.single i m`.
* `AnalyticAt.exists_analyticAt_eq_pow_smul`: local factorization `f z = (z i - x i) ^ m • g z`
  near `x` with `g` analytic at `x`.
* `AnalyticAt.mvTaylorCoeff_comp_update_self`: restricting `f` to the hyperplane `z i = x i`
  preserves the Taylor coefficients with `α i = 0` and kills all others.
* `TauCeti.analyticAt_dslope_update_self`: on the hyperplane `x i = ζ`, the one-coordinate divided
  difference is analytic at `x` assuming only `AnalyticAt 𝕜 f x`.
* `TauCeti.analyticAt_dslope_update`: the one-coordinate divided difference at `ζ` is analytic at
  every `x` where `f` is analytic at both `x` and `Function.update x i ζ`.

## References

Coordinate division and analyticity of `dslope` along a coordinate also appear in Michail
Karatarakis's formalization of Baker's theorem (`mkaratarakis/mathlib4`, branch `baker`, commit
`1d51891b5b`, `Mathlib/NumberTheory/Transcendental/Baker/CoordinateDivision.lean`, Apache 2.0).
-/

public section

open Filter Finset Topology
open scoped ENNReal NNReal

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {ι : Type*} [Fintype ι]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

namespace TauCeti

/-- **Coordinate division on a polydisc of normal convergence**: if the multi-index Taylor
coefficients of `f` at `x` vanish whenever `α i < m` and the expansion of `f (x + ·)` converges
normally at radius `ρ > 0`, then `f (x + z) = z i ^ m • g z` on `‖z‖ < ρ` for a function `g` with
a formal power series on `ball 0 ρ` whose multi-index coefficients are
`α ↦ mvTaylorCoeff f x (α + Pi.single i m)`. -/
theorem exists_hasFPowerSeriesOnBall_eq_pow_smul [DecidableEq ι] [CompleteSpace F]
    {f : (ι → 𝕜) → F} {x : ι → 𝕜} {ρ : ℝ≥0} (hρ : 0 < ρ)
    (hsum : Summable fun α : ι → ℕ ↦ ‖mvTaylorCoeff f x α‖ * (ρ : ℝ) ^ (∑ j, α j))
    (hexp : ∀ z : ι → 𝕜, ‖z‖ < ρ →
      HasSum (fun α : ι → ℕ ↦ (∏ j, z j ^ α j) • mvTaylorCoeff f x α) (f (x + z)))
    {i : ι} {m : ℕ} (hvan : ∀ α : ι → ℕ, α i < m → mvTaylorCoeff f x α = 0) :
    ∃ (g : (ι → 𝕜) → F) (q : FormalMultilinearSeries 𝕜 (ι → 𝕜) F),
      HasFPowerSeriesOnBall g q 0 ρ ∧
        (∀ α : ι → ℕ, q.mvCoeff α = mvTaylorCoeff f x (α + Pi.single i m)) ∧
        ∀ z : ι → 𝕜, ‖z‖ < ρ → f (x + z) = z i ^ m • g z := by
  let shift : ι → ℕ := Pi.single i m
  let d : (ι → ℕ) → F := fun β ↦ mvTaylorCoeff f x (β + shift)
  have hdeg (β : ι → ℕ) : ∑ j, (β + shift) j = (∑ j, β j) + m := by
    simp [shift, Pi.add_apply, sum_add_distrib]
  -- Shift the normal convergence bound by `Pi.single i m` and cancel `ρ ^ m > 0`.
  have hd_sum : Summable fun β : ι → ℕ ↦ ‖d β‖ * (ρ : ℝ) ^ (∑ j, β j) := by
    have hshift : Summable fun β : ι → ℕ ↦ ‖d β‖ * (ρ : ℝ) ^ (∑ j, β j) * (ρ : ℝ) ^ m := by
      convert hsum.comp_injective (add_left_injective shift) using 1
      ext β
      simp only [Function.comp_apply, d, hdeg, pow_add, mul_assoc]
    exact (summable_mul_right_iff (pow_ne_zero m (NNReal.coe_pos.mpr hρ).ne')).mp hshift
  obtain ⟨q, hq, hqd⟩ := exists_hasFPowerSeriesOnBall_tsum (𝕜 := 𝕜) d hρ hd_sum
  refine ⟨fun z ↦ ∑' β : ι → ℕ, (∏ j, z j ^ β j) • d β, q, hq, hqd, fun z hz ↦ ?_⟩
  have hg_sum : HasSum (fun β : ι → ℕ ↦ (∏ j, z j ^ β j) • d β)
      (∑' β : ι → ℕ, (∏ j, z j ^ β j) • d β) :=
    (hd_sum.norm_prod_pow_smul_of_le hz.le).of_norm.hasSum
  have hscaled : HasSum (fun β : ι → ℕ ↦
      (∏ j, z j ^ (β + shift) j) • mvTaylorCoeff f x (β + shift))
      (z i ^ m • ∑' β : ι → ℕ, (∏ j, z j ^ β j) • d β) := by
    convert hg_sum.const_smul (z i ^ m) using 1
    ext β
    rw [smul_smul]
    congr 1
    have hprod : ∏ j : ι, z j ^ shift j = z i ^ m := by
      rw [prod_eq_single i (fun j _ hji ↦ by simp [shift, hji]) (fun hi ↦ absurd (mem_univ i) hi)]
      simp [shift]
    rw [← hprod, ← prod_mul_distrib]
    exact prod_congr rfl fun j _ ↦ by rw [Pi.add_apply, pow_add, mul_comm]
  -- Extend the sum from shifted multi-indices to all multi-indices using `hvan`.
  have hfull : HasSum (fun α : ι → ℕ ↦ (∏ j, z j ^ α j) • mvTaylorCoeff f x α)
      (z i ^ m • ∑' β : ι → ℕ, (∏ j, z j ^ β j) • d β) := by
    refine ((add_left_injective shift).hasSum_iff
      (f := fun α : ι → ℕ ↦ (∏ j, z j ^ α j) • mvTaylorCoeff f x α) fun α hα ↦ ?_).mp hscaled
    have hlt : α i < m := by
      by_contra hge
      refine hα ⟨Function.update α i (α i - m), ?_⟩
      ext j
      by_cases hji : j = i
      · subst hji; simp [shift, Nat.sub_add_cancel (not_lt.mp hge)]
      · simp [shift, hji]
    rw [hvan α hlt, smul_zero]
  exact (hexp z hz).unique hfull

end TauCeti

namespace AnalyticAt

/-- **Local coordinate division**: if `f` is analytic at `x` and its multi-index Taylor
coefficients at `x` vanish whenever `α i < m`, then `f z = (z i - x i) ^ m • g z` near `x` for
some function `g` analytic at `x`. -/
theorem exists_analyticAt_eq_pow_smul [CompleteSpace F]
    {f : (ι → 𝕜) → F} {x : ι → 𝕜} (hf : AnalyticAt 𝕜 f x) {i : ι} {m : ℕ}
    (hvan : ∀ α : ι → ℕ, α i < m → TauCeti.mvTaylorCoeff f x α = 0) :
    ∃ g : (ι → 𝕜) → F, AnalyticAt 𝕜 g x ∧
      ∀ᶠ z in 𝓝 x, f z = (z i - x i) ^ m • g z := by
  classical
  obtain ⟨ρ, hρ, hsum, hexp⟩ := hf.exists_hasSum_mvTaylorCoeff
  obtain ⟨g₀, q, hq, _, hmul⟩ :=
    TauCeti.exists_hasFPowerSeriesOnBall_eq_pow_smul hρ hsum hexp hvan
  refine ⟨fun z ↦ g₀ (z - x), ?_, ?_⟩
  · have hg₀ : AnalyticAt 𝕜 g₀ (x - x) := by simpa using hq.analyticAt
    exact hg₀.comp (f := fun z ↦ z - x) (analyticAt_id.sub analyticAt_const)
  · filter_upwards [Metric.ball_mem_nhds x (NNReal.coe_pos.mpr hρ)] with z hz
    have hnorm : ‖z - x‖ < (ρ : ℝ) := by simpa [Metric.mem_ball, dist_eq_norm] using hz
    simpa [add_sub_cancel] using hmul (z - x) hnorm

/-- Restricting an analytic function `f` to the hyperplane `z i = x i` preserves the multi-index
Taylor coefficients at `x` with `α i = 0` and annihilates all coefficients with `α i ≠ 0`. -/
theorem mvTaylorCoeff_comp_update_self [DecidableEq ι] {f : (ι → 𝕜) → F} {x : ι → 𝕜}
    (hf : AnalyticAt 𝕜 f x) (i : ι) (α : ι → ℕ) :
    TauCeti.mvTaylorCoeff (fun z ↦ f (Function.update z i (x i))) x α =
      if α i = 0 then TauCeti.mvTaylorCoeff f x α else 0 := by
  obtain ⟨ρ, hρ, hsum, hexp⟩ := hf.exists_hasSum_mvTaylorCoeff
  let c : (ι → ℕ) → F := fun β ↦ if β i = 0 then TauCeti.mvTaylorCoeff f x β else 0
  have hc_sum : Summable fun β : ι → ℕ ↦ ‖c β‖ * (ρ : ℝ) ^ (∑ j, β j) := by
    refine Summable.of_nonneg_of_le (fun _ ↦ by positivity) (fun β ↦ ?_) hsum
    by_cases hβ : β i = 0
    · simp [c, hβ]
    · simp only [c, hβ, ↓reduceIte, norm_zero, zero_mul]
      positivity
  refine TauCeti.mvTaylorCoeff_eq_of_hasSum hρ hc_sum (fun y hy ↦ ?_) α
  let y' : ι → 𝕜 := Function.update y i 0
  have hy'_norm : ‖y'‖ < (ρ : ℝ) := by
    refine lt_of_le_of_lt ?_ hy
    rw [pi_norm_le_iff_of_nonneg (norm_nonneg y)]
    intro j
    by_cases hji : j = i
    · subst hji; simp [y']
    · simp [y', hji, norm_le_pi_norm]
  have hxy : Function.update (x + y) i (x i) = x + y' := by
    ext j
    by_cases hji : j = i <;> simp [y', hji]
  rw [hxy]
  convert hexp y' hy'_norm using 1
  ext β
  by_cases hβ : β i = 0
  · simp only [c, hβ, ↓reduceIte]
    congr 1
    refine prod_congr rfl fun j _ ↦ ?_
    by_cases hji : j = i
    · subst hji; simp [hβ]
    · simp [y', hji]
  · simp only [c, hβ, ↓reduceIte, smul_zero]
    have hprod0 : ∏ j : ι, y' j ^ β j = 0 :=
      prod_eq_zero (mem_univ i) (by simp [y', zero_pow hβ])
    simp [hprod0]

end AnalyticAt

namespace TauCeti

/-- On an open ball `ball x δ`, if `f w - f (Function.update w i (x i)) = (w i - x i) • g w`
with `g` continuous on the ball, then `g` agrees with the one-coordinate `dslope` throughout
the ball (including on the hyperplane `z i = x i`). -/
private theorem dslope_update_eq_of_eq_smul [DecidableEq ι] {f g : (ι → 𝕜) → F} {i : ι}
    {x z : ι → 𝕜} {δ : ℝ} (hδ_pos : 0 < δ)
    (hball : ∀ {w}, dist w x < δ →
      (f w - f (Function.update w i (x i)) = (w i - x i) • g w) ∧ ContinuousAt g w)
    (hzx : dist z x < δ) :
    g z = dslope (fun w ↦ f (Function.update z i w)) (x i) (z i) := by
  by_cases hzi : z i = x i
  · -- On the hyperplane `z i = x i`, evaluate the derivative via the slope limit.
    rw [hzi, dslope_same]
    refine (HasDerivAt.deriv ?_).symm
    rw [hasDerivAt_iff_tendsto_slope]
    have hupd_cont : ContinuousAt (fun w : 𝕜 ↦ Function.update z i w) (x i) :=
      (continuous_pi fun j ↦ by
        by_cases hji : j = i
        · subst hji; simpa using continuous_id'
        · simp [Function.update_of_ne hji, continuous_const]).continuousAt
    have hcomp_cont : ContinuousAt (fun w : 𝕜 ↦ g (Function.update z i w)) (x i) :=
      (by simpa [← hzi, Function.update_eq_self] using (hball hzx).2 :
        ContinuousAt g (Function.update z i (x i))).comp hupd_cont
    have htend : Tendsto (fun w : 𝕜 ↦ g (Function.update z i w)) (𝓝[≠] (x i)) (𝓝 (g z)) := by
      have hval : g (Function.update z i (x i)) = g z := by rw [← hzi, Function.update_eq_self]
      rw [← hval]
      exact hcomp_cont.tendsto.mono_left nhdsWithin_le_nhds
    refine htend.congr' ?_
    filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds (x i) hδ_pos),
      self_mem_nhdsWithin] with w hw hne
    have hw_ball : dist (Function.update z i w) x < δ := by
      rw [dist_pi_lt_iff hδ_pos]
      intro j
      by_cases hji : j = i
      · subst hji; simpa using Metric.mem_ball.mp hw
      · simp only [Function.update_of_ne hji]
        exact (dist_le_pi_dist z x j).trans_lt hzx
    have hfac := (hball hw_ball).1
    simp only [Function.update_idem, Function.update_self] at hfac
    rw [slope_def_module, hfac, inv_smul_smul₀ (sub_ne_zero.mpr hne)]
  · -- Off the hyperplane `z i ≠ x i`, cancel `(z i - x i)` directly.
    have hfac := (hball hzx).1
    rw [dslope_of_ne _ hzi, slope_def_module, Function.update_eq_self, hfac,
      inv_smul_smul₀ (sub_ne_zero.mpr hzi)]

/-- **Analyticity of the one-coordinate divided difference on the hyperplane**: at any point `x`
where `f` is analytic, `z ↦ dslope (fun w ↦ f (Function.update z i w)) (x i) (z i)` is analytic
at `x`. -/
theorem analyticAt_dslope_update_self [DecidableEq ι] [CompleteSpace F] {f : (ι → 𝕜) → F}
    (i : ι) {x : ι → 𝕜} (hf : AnalyticAt 𝕜 f x) :
    AnalyticAt 𝕜 (fun z : ι → 𝕜 ↦ dslope (fun w ↦ f (Function.update z i w)) (x i) (z i)) x := by
  let h : (ι → 𝕜) → F := fun z ↦ f (Function.update z i (x i))
  have hupd : AnalyticAt 𝕜 (fun z : ι → 𝕜 ↦ Function.update z i (x i)) x :=
    analyticAt_pi_iff.mpr fun j ↦ by
      by_cases hji : j = i
      · simp only [hji, Function.update_self]
        exact analyticAt_const
      · simp only [Function.update_of_ne hji]
        exact (ContinuousLinearMap.proj (R := 𝕜) j).analyticAt x
  have hh : AnalyticAt 𝕜 h x :=
    (by simpa using hf : AnalyticAt 𝕜 f (Function.update x i (x i))).comp
      (f := fun z : ι → 𝕜 ↦ Function.update z i (x i)) hupd
  have hvan : ∀ α : ι → ℕ, α i < 1 → mvTaylorCoeff (f - h) x α = 0 := fun α hα ↦ by
    have hα0 : α i = 0 := Nat.lt_one_iff.mp hα
    simp [h, hf.mvTaylorCoeff_sub hh, hf.mvTaylorCoeff_comp_update_self i α, hα0]
  obtain ⟨g, hg, hmul⟩ := (hf.sub hh).exists_analyticAt_eq_pow_smul hvan
  obtain ⟨q, r, hq⟩ := hg
  have hcont : ∀ᶠ z in 𝓝 x, ContinuousAt g z :=
    eventually_of_mem (Metric.eball_mem_nhds x hq.r_pos) fun z hz ↦
      (hq.analyticOnNhd z hz).continuousAt
  obtain ⟨δ, hδ_pos, hball⟩ := Metric.eventually_nhds_iff.mp (hmul.and hcont)
  refine hq.analyticAt.congr ?_
  filter_upwards [Metric.ball_mem_nhds x hδ_pos] with z hz
  exact dslope_update_eq_of_eq_smul hδ_pos
    (fun hw ↦ by simpa [h, pow_one] using hball hw) (Metric.mem_ball.mp hz)

/-- **Analyticity of the one-coordinate divided difference**: the map
`z ↦ dslope (fun w ↦ f (Function.update z i w)) ζ (z i)` is analytic at `x` whenever `f` is
analytic at both `x` and `Function.update x i ζ`. -/
theorem analyticAt_dslope_update [DecidableEq ι] [CompleteSpace F] {f : (ι → 𝕜) → F} (i : ι)
    (ζ : 𝕜) {x : ι → 𝕜} (hf : AnalyticAt 𝕜 f x)
    (hres : AnalyticAt 𝕜 f (Function.update x i ζ)) :
    AnalyticAt 𝕜 (fun z : ι → 𝕜 ↦ dslope (fun w ↦ f (Function.update z i w)) ζ (z i)) x := by
  rcases eq_or_ne (x i) ζ with rfl | hne
  · exact analyticAt_dslope_update_self i hf
  · have hupd : AnalyticAt 𝕜 (fun z : ι → 𝕜 ↦ Function.update z i ζ) x :=
      analyticAt_pi_iff.mpr fun j ↦ by
        by_cases hji : j = i
        · simp only [hji, Function.update_self]
          exact analyticAt_const
        · simp only [Function.update_of_ne hji]
          exact (ContinuousLinearMap.proj (R := 𝕜) j).analyticAt x
    have hnum : AnalyticAt 𝕜 (fun z : ι → 𝕜 ↦ f z - f (Function.update z i ζ)) x :=
      hf.sub (hres.comp (f := fun z : ι → 𝕜 ↦ Function.update z i ζ) hupd)
    have hinv : AnalyticAt 𝕜 (fun z : ι → 𝕜 ↦ (z i - ζ)⁻¹) x :=
      (analyticAt_inv (sub_ne_zero.mpr hne)).comp (f := fun z : ι → 𝕜 ↦ z i - ζ)
        (((ContinuousLinearMap.proj (R := 𝕜) i).analyticAt x).sub analyticAt_const)
    refine (hinv.smul hnum).congr ?_
    have hopen : IsOpen {z : ι → 𝕜 | z i ≠ ζ} := isOpen_ne.preimage (continuous_apply i)
    filter_upwards [hopen.mem_nhds hne] with z hz
    simp [dslope_of_ne _ hz, slope_def_module, Function.update_eq_self]

end TauCeti

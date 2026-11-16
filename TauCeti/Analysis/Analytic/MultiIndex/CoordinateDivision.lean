/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.DSlope
public import TauCeti.Analysis.Analytic.MultiIndex.TaylorCoeff
import Mathlib.Analysis.Analytic.Composition
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Coordinate division for multi-index power series

This file proves coordinate-wise division results for analytic functions on `ι → 𝕜` over any
nontrivially normed field `𝕜` with values in a complete normed space `F`:

* If the multi-index Taylor coefficients of `f` at `x` vanish whenever `α i < m`, then on every
  polydisc about `0` where the multi-index expansion of `f (x + ·)` converges normally, one can
  factor out `y i ^ m`, obtaining `f (x + y) = y i ^ m • g y` with `g` given by the shifted power
  series (`TauCeti.exists_hasFPowerSeriesOnBall_eq_pow_smul`).
* As a consequence, the one-coordinate divided difference
  `z ↦ dslope (fun w ↦ f (Function.update z i w)) ζ (z i)` is analytic at every point `x` where
  `f` is analytic at `x` and at `Function.update x i ζ` (`TauCeti.analyticAt_dslope_update`); on
  the hyperplane `x i = ζ`, analyticity of `f` at `x` alone suffices
  (`TauCeti.analyticAt_dslope_update_self`).

## Main results

* `TauCeti.exists_hasFPowerSeriesOnBall_eq_pow_smul`: factoring `y i ^ m` out of a normally
  convergent multi-index expansion when all coefficients with `α i < m` vanish.
* `AnalyticAt.exists_analyticAt_eq_pow_smul`: local form of coordinate division at a point.
* `TauCeti.analyticAt_dslope_update_self`: analyticity of the divided difference along the
  hyperplane `z i = x i`.
* `TauCeti.analyticAt_dslope_update`: analyticity of the divided difference in one coordinate, both
  on and off the hyperplane `z i = ζ`.

## References

Coordinate division and analyticity of divided differences in one coordinate are also part of
Michail Karatarakis's formalization of Baker's theorem (`mkaratarakis/mathlib4`, branch `baker`,
commit `1d51891b5b`, `Mathlib/NumberTheory/Transcendental/Baker/CoordinateDivision.lean`,
Apache 2.0).
-/

public section

open Filter Finset Topology
open scoped NNReal

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {ι : Type*} [Fintype ι]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

namespace TauCeti

/-- **Coordinate division on a polydisc**: if `f (x + ·)` has a normally convergent multi-index
expansion on `‖y‖ < ρ` and `mvTaylorCoeff f x α = 0` whenever `α i < m`, then there exist `g` and
a formal power series `q` on the ball of radius `ρ` about `0` with shifted multi-index coefficients
`q.mvCoeff β = mvTaylorCoeff f x (β + Pi.single i m)` and `f (x + y) = y i ^ m • g y` for all
`‖y‖ < ρ`. -/
theorem exists_hasFPowerSeriesOnBall_eq_pow_smul [DecidableEq ι] [CompleteSpace F]
    {f : (ι → 𝕜) → F} {x : ι → 𝕜} {ρ : ℝ≥0} (hρ : 0 < ρ)
    (hsum : Summable fun α : ι → ℕ ↦ ‖mvTaylorCoeff f x α‖ * (ρ : ℝ) ^ (∑ j, α j))
    (hhas : ∀ y : ι → 𝕜, ‖y‖ < ρ →
      HasSum (fun α : ι → ℕ ↦ (∏ j, y j ^ α j) • mvTaylorCoeff f x α) (f (x + y)))
    (i : ι) (m : ℕ) (hvan : ∀ α : ι → ℕ, α i < m → mvTaylorCoeff f x α = 0) :
    ∃ (g : (ι → 𝕜) → F) (q : FormalMultilinearSeries 𝕜 (ι → 𝕜) F),
      HasFPowerSeriesOnBall g q 0 ρ ∧
      (∀ β, q.mvCoeff β = mvTaylorCoeff f x (β + Pi.single i m)) ∧
      ∀ y : ι → 𝕜, ‖y‖ < ρ → f (x + y) = y i ^ m • g y := by
  let shift : (ι → ℕ) → (ι → ℕ) := fun β ↦ β + Pi.single i m
  have hshift_inj : Function.Injective shift := fun β₁ β₂ h ↦ add_right_cancel h
  let d : (ι → ℕ) → F := fun β ↦ mvTaylorCoeff f x (shift β)
  have hdeg_shift (β : ι → ℕ) : ∑ j, shift β j = (∑ j, β j) + m := by
    simp [shift, sum_add_distrib, Pi.single_apply]
  have hsum_d : Summable fun β : ι → ℕ ↦ ‖d β‖ * (ρ : ℝ) ^ (∑ j, β j) := by
    have hcomp := (hsum.comp_injective hshift_inj).mul_left ((ρ : ℝ) ^ m)⁻¹
    have hρm : (ρ : ℝ) ^ m ≠ 0 := pow_ne_zero m (NNReal.coe_pos.2 hρ).ne'
    refine hcomp.congr fun β ↦ ?_
    dsimp only [Function.comp_apply, d]
    rw [hdeg_shift, pow_add, mul_left_comm ((ρ : ℝ) ^ m)⁻¹,
      mul_comm ((ρ : ℝ) ^ (∑ j, β j)), ← mul_assoc ((ρ : ℝ) ^ m)⁻¹, inv_mul_cancel₀ hρm, one_mul]
  obtain ⟨q, hq, hqd⟩ := exists_hasFPowerSeriesOnBall_tsum (𝕜 := 𝕜) d hρ hsum_d
  refine ⟨fun z ↦ ∑' β : ι → ℕ, (∏ j, z j ^ β j) • d β, q, hq, hqd, fun y hy ↦ ?_⟩
  have hg_sum : HasSum (fun β : ι → ℕ ↦ (∏ j, y j ^ β j) • d β)
      (∑' β : ι → ℕ, (∏ j, y j ^ β j) • d β) :=
    (summable_norm_prod_pow_smul hsum_d hy.le).of_norm.hasSum
  have hg_smul : HasSum (fun β : ι → ℕ ↦ (∏ j, y j ^ shift β j) • mvTaylorCoeff f x (shift β))
      (y i ^ m • ∑' β : ι → ℕ, (∏ j, y j ^ β j) • d β) := by
    convert hg_sum.const_smul (y i ^ m) using 1
    ext β
    rw [smul_smul]
    congr 1
    have hsingle : ∏ j : ι, y j ^ (Pi.single i m : ι → ℕ) j = y i ^ m := by
      simp [Pi.single_apply]
    rw [← hsingle, mul_comm, ← prod_mul_distrib]
    exact prod_congr rfl fun j _ ↦ by rw [← pow_add]; rfl
  have hvan_range : ∀ α ∉ Set.range shift, (∏ j, y j ^ α j) • mvTaylorCoeff f x α = 0 := by
    intro α hα
    have hlt : α i < m := by
      by_contra hle
      have hle' : m ≤ α i := not_lt.1 hle
      refine hα ⟨Function.update α i (α i - m), funext fun j ↦ ?_⟩
      by_cases hji : j = i
      · subst hji; simp [shift, Nat.sub_add_cancel hle']
      · simp [shift, hji]
    rw [hvan α hlt, smul_zero]
  have hf_sum : HasSum (fun α : ι → ℕ ↦ (∏ j, y j ^ α j) • mvTaylorCoeff f x α)
      (y i ^ m • ∑' β : ι → ℕ, (∏ j, y j ^ β j) • d β) :=
    (hshift_inj.hasSum_iff hvan_range).1 hg_smul
  exact (hhas y hy).unique hf_sum

end TauCeti

namespace AnalyticAt

open TauCeti

/-- **Local coordinate division**: if `f` is analytic at `x` and `mvTaylorCoeff f x α = 0` whenever
`α i < m`, then `f (x + y) = y i ^ m • g y` near `0` for some `g` analytic at `0`. -/
theorem exists_analyticAt_eq_pow_smul [CompleteSpace F] {f : (ι → 𝕜) → F}
    {x : ι → 𝕜} (hf : AnalyticAt 𝕜 f x) (i : ι) (m : ℕ)
    (hvan : ∀ α : ι → ℕ, α i < m → mvTaylorCoeff f x α = 0) :
    ∃ g : (ι → 𝕜) → F, AnalyticAt 𝕜 g 0 ∧ (fun y ↦ f (x + y)) =ᶠ[𝓝 0] fun y ↦ y i ^ m • g y := by
  classical
  obtain ⟨ρ, hρ, hsum, hhas⟩ := hf.exists_hasSum_mvTaylorCoeff
  obtain ⟨g, q, hq, _, hfg⟩ :=
    exists_hasFPowerSeriesOnBall_eq_pow_smul hρ hsum hhas i m hvan
  refine ⟨g, hq.analyticAt, ?_⟩
  filter_upwards [Metric.ball_mem_nhds (0 : ι → 𝕜) (NNReal.coe_pos.2 hρ)] with y hy
  exact hfg y (by simpa [Metric.mem_ball, dist_zero_right] using hy)

end AnalyticAt

namespace TauCeti

/-- **Analyticity of the divided difference on the hyperplane `z i = x i`**: if `f` is analytic at
`x`, then `z ↦ dslope (fun w ↦ f (Function.update z i w)) (x i) (z i)` is analytic at `x`. -/
theorem analyticAt_dslope_update_self [DecidableEq ι] [CompleteSpace F] {f : (ι → 𝕜) → F}
    (i : ι) {x : ι → 𝕜} (hf : AnalyticAt 𝕜 f x) :
    AnalyticAt 𝕜 (fun z : ι → 𝕜 ↦ dslope (fun w ↦ f (Function.update z i w)) (x i) (z i)) x := by
  -- Factor `z i - x i` out of `F₁ z = f z - f (update z i (x i))` via local coordinate division.
  have hupd_an : AnalyticAt 𝕜 (fun z : ι → 𝕜 ↦ Function.update z i (x i)) x :=
    analyticAt_pi_iff.2 fun j ↦ by
      by_cases hji : j = i
      · subst hji; simpa using analyticAt_const
      · simp only [Function.update_of_ne hji]
        exact (ContinuousLinearMap.proj (R := 𝕜) (φ := fun _ : ι ↦ 𝕜) j).analyticAt x
  have hf_upd : AnalyticAt 𝕜 (fun z : ι → 𝕜 ↦ f (Function.update z i (x i))) x :=
    AnalyticAt.comp (g := f) (f := fun z ↦ Function.update z i (x i))
      (by simpa using hf) hupd_an
  let F₁ : (ι → 𝕜) → F := f - fun z ↦ f (Function.update z i (x i))
  have hvan : ∀ α : ι → ℕ, α i < 1 → mvTaylorCoeff F₁ x α = 0 := fun α hα ↦ by
    rw [hf.mvTaylorCoeff_sub hf_upd, hf.mvTaylorCoeff_comp_update,
      ite_eq_left (Nat.lt_one_iff.1 hα), sub_self]
  obtain ⟨g, hg, hfg⟩ := (hf.sub hf_upd).exists_analyticAt_eq_pow_smul i 1 hvan
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff.1
    (hfg.and (hg.eventually_analyticAt.mono fun _ hy ↦ hy.continuousAt))
  -- On `Metric.ball x ρ`, `g (z - x)` agrees with `dslope` both off and on `z i = x i`.
  refine (by simpa using hg.comp_sub x : AnalyticAt 𝕜 (fun z ↦ g (z - x)) x).congr ?_
  filter_upwards [Metric.ball_mem_nhds x hρ] with z hz
  have hz_norm : ‖z - x‖ < ρ := by simpa [Metric.mem_ball, dist_eq_norm] using hz
  have hline : ∀ w : 𝕜, ‖w - x i‖ < ρ →
      f (Function.update z i w) - f (Function.update z i (x i)) =
        (w - x i) • g (Function.update (z - x) i (w - x i)) := by
    intro w hw
    let y : ι → 𝕜 := Function.update (z - x) i (w - x i)
    have hy_norm : ‖y‖ < ρ := by
      rw [pi_norm_lt_iff hρ]
      intro j
      by_cases hji : j = i
      · subst hji; simpa [y] using hw
      · simpa [y, hji] using (norm_le_pi_norm (z - x) j).trans_lt hz_norm
    have hxy : x + y = Function.update z i w := by
      ext j; by_cases hji : j = i <;> simp [y, hji]
    have h := (hball (by simpa [dist_zero_right] using hy_norm)).1
    dsimp only [Pi.sub_apply] at h
    rw [hxy] at h
    simpa [y] using h
  symm
  by_cases hzi : z i = x i
  · rw [hzi, dslope_same]
    refine HasDerivAt.deriv (hasDerivAt_iff_tendsto_slope.2 ?_)
    have hcont_g : ContinuousAt g (z - x) := (hball (by simpa [dist_zero_right] using hz_norm)).2
    have hcont_upd : Continuous (fun w : 𝕜 ↦ Function.update (z - x) i (w - x i)) :=
      continuous_pi fun j ↦ by
        by_cases hji : j = i
        · subst hji; simpa using continuous_sub_right (x j)
        · simpa [hji] using continuous_const
    have hupd_at : Function.update (z - x) i (x i - x i) = z - x := by
      ext j; by_cases hji : j = i <;> simp [hji, hzi]
    have hupd_tend : Tendsto (fun w : 𝕜 ↦ Function.update (z - x) i (w - x i))
        (𝓝[≠] (x i)) (𝓝 (z - x)) := by
      have h := (hcont_upd.tendsto (x i)).mono_left (nhdsWithin_le_nhds (s := {x i}ᶜ))
      rwa [hupd_at] at h
    refine (hcont_g.tendsto.comp hupd_tend).congr' ?_
    filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds (x i) hρ),
      self_mem_nhdsWithin] with w hw hne
    have hw_norm : ‖w - x i‖ < ρ := by simpa [Metric.mem_ball, dist_eq_norm] using hw
    rw [slope_def_module, hline w hw_norm, inv_smul_smul₀ (sub_ne_zero.2 hne)]
    rfl
  · rw [dslope_of_ne _ hzi, slope_def_module, Function.update_eq_self]
    have h := hline (z i) ((norm_le_pi_norm (z - x) i).trans_lt hz_norm)
    have hupd_self : Function.update (z - x) i (z i - x i) = z - x := by
      ext j; by_cases hji : j = i <;> simp [hji]
    rw [Function.update_eq_self, hupd_self] at h
    rw [h, inv_smul_smul₀ (sub_ne_zero.2 hzi)]

/-- **Analyticity of the divided difference in one coordinate**, across the hyperplane `z i = ζ`
as well as off it. -/
theorem analyticAt_dslope_update [DecidableEq ι] [CompleteSpace F] {f : (ι → 𝕜) → F} (i : ι)
    (ζ : 𝕜) {x : ι → 𝕜} (hf : AnalyticAt 𝕜 f x) (hres : AnalyticAt 𝕜 f (Function.update x i ζ)) :
    AnalyticAt 𝕜 (fun z : ι → 𝕜 ↦ dslope (fun w ↦ f (Function.update z i w)) ζ (z i)) x := by
  by_cases hxi : x i = ζ
  · subst hxi
    exact analyticAt_dslope_update_self i hf
  · have hupd_an : AnalyticAt 𝕜 (fun z : ι → 𝕜 ↦ Function.update z i ζ) x :=
      analyticAt_pi_iff.2 fun j ↦ by
        by_cases hji : j = i
        · subst hji; simpa using analyticAt_const
        · simp only [Function.update_of_ne hji]
          exact (ContinuousLinearMap.proj (R := 𝕜) (φ := fun _ : ι ↦ 𝕜) j).analyticAt x
    have hf_upd : AnalyticAt 𝕜 (fun z : ι → 𝕜 ↦ f (Function.update z i ζ)) x :=
      AnalyticAt.comp (g := f) (f := fun z ↦ Function.update z i ζ) hres hupd_an
    have hinv : AnalyticAt 𝕜 (fun z : ι → 𝕜 ↦ (z i - ζ)⁻¹) x :=
      (((ContinuousLinearMap.proj (R := 𝕜) (φ := fun _ : ι ↦ 𝕜) i).analyticAt x).sub
        analyticAt_const).inv (sub_ne_zero.2 hxi)
    refine (hinv.smul (hf.sub hf_upd)).congr ?_
    have hne : ∀ᶠ z in 𝓝 x, z i ≠ ζ :=
      (continuous_apply i).continuousAt.eventually_ne hxi
    filter_upwards [hne] with z hz
    rw [dslope_of_ne _ hz, slope_def_module, Function.update_eq_self]
    rfl

end TauCeti

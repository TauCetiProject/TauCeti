/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Testing a continuous function against bumps composed with a reparametrization

A variant of the fundamental lemma of the calculus of variations on an interval, in which the test
functions are smooth bumps `ψ` on the real line composed with a fixed map `F` that is continuous
and strictly antitone on the interval: if `∫ₐᵀ g(σ) ψ(F σ) dσ = 0` for every bump `ψ` centred at
`F σ₀`, then `g σ₀ = 0`. Such test functions arise when a bump is pulled back along a function
that decreases strictly along a curve, for instance a Morse function along a negative-gradient
orbit.

## Main results

* `TauCeti.nonpos_of_forall_intervalIntegral_mul_contDiffBump_comp`: the one-sided version.
* `TauCeti.eq_zero_of_forall_intervalIntegral_mul_contDiffBump_comp`.
-/

public section

open Set Filter Topology

namespace TauCeti

/-- **A one-sided test against bumps composed with a monotone reparametrization.** If
`∫ₐᵀ b(σ) ψ(F σ) dσ = 0` for every smooth bump `ψ` centred at `F σ₀`, with `b` and `F` continuous
on `[a, T]` and `F` strictly antitone there, then `b σ₀ ≤ 0` for `σ₀ ∈ (a, T)`. -/
theorem nonpos_of_forall_intervalIntegral_mul_contDiffBump_comp {b F : ℝ → ℝ} {a T σ₀ : ℝ}
    (hb : ContinuousOn b (Icc a T)) (hF : ContinuousOn F (Icc a T))
    (hFa : StrictAntiOn F (Icc a T)) (hσ : σ₀ ∈ Ioo a T)
    (h : ∀ ψ : ContDiffBump (F σ₀), ∫ σ in a..T, b σ * ψ (F σ) = 0) : b σ₀ ≤ 0 := by
  by_contra hpos
  rw [not_le] at hpos
  -- `b` is positive on a neighbourhood of `σ₀` inside `(a, T)`.
  obtain ⟨ε, hε, hεb⟩ := Metric.eventually_nhds_iff.1
    ((hb.continuousAt (Icc_mem_nhds hσ.1 hσ.2)).eventually (lt_mem_nhds hpos))
  set δ := min ε (min (σ₀ - a) (T - σ₀)) with hδ
  have hδpos : 0 < δ := lt_min hε (lt_min (by linarith [hσ.1]) (by linarith [hσ.2]))
  have hδσ : δ ≤ σ₀ - a := (min_le_right _ _).trans (min_le_left _ _)
  have hδT : δ ≤ T - σ₀ := (min_le_right _ _).trans (min_le_right _ _)
  have hbpos : ∀ σ, |σ - σ₀| < δ → 0 < b σ := fun σ hσ' ↦
    hεb (by rw [Real.dist_eq]; exact hσ'.trans_le (min_le_left _ _))
  -- A bump around `F σ₀` small enough that `ψ ∘ F` lives in `(σ₀ - δ / 2, σ₀ + δ / 2)`.
  have hm : σ₀ - δ / 2 ∈ Icc a T := ⟨by linarith, by linarith [hσ.2]⟩
  have hp : σ₀ + δ / 2 ∈ Icc a T := ⟨by linarith [hσ.1], by linarith⟩
  have h0 : σ₀ ∈ Icc a T := Ioo_subset_Icc_self hσ
  set c := F σ₀
  have h1 : c < F (σ₀ - δ / 2) := hFa hm h0 (by linarith)
  have h2 : F (σ₀ + δ / 2) < c := hFa h0 hp (by linarith)
  set r := min (F (σ₀ - δ / 2) - c) (c - F (σ₀ + δ / 2)) with hr
  have hrpos : 0 < r := lt_min (by linarith) (by linarith)
  let ψ : ContDiffBump c := ⟨r / 2, r, by positivity, by linarith⟩
  have hψ0 : ∀ σ ∈ Icc a T, δ / 2 ≤ |σ - σ₀| → ψ (F σ) = 0 := fun σ hσI hσ' ↦ by
    refine ψ.zero_of_le_dist ?_
    rw [Real.dist_eq]
    rcases le_abs'.1 hσ' with h' | h'
    · have : F (σ₀ - δ / 2) ≤ F σ := hFa.antitoneOn hσI hm (by linarith)
      rw [abs_of_nonneg (by linarith)]
      exact ((min_le_left _ _).trans (by linarith) : r ≤ F σ - c)
    · have : F σ ≤ F (σ₀ + δ / 2) := hFa.antitoneOn hp hσI (by linarith)
      rw [abs_of_nonpos (by linarith)]
      exact ((min_le_right _ _).trans (by linarith) : r ≤ -(F σ - c))
  have hg : ContinuousOn (fun σ ↦ b σ * ψ (F σ)) (Icc a T) :=
    hb.mul (ψ.continuous.comp_continuousOn hF)
  have hnonneg : ∀ σ ∈ Icc a T, 0 ≤ b σ * ψ (F σ) := fun σ hσI ↦ by
    by_cases hσ' : |σ - σ₀| < δ / 2
    · exact mul_nonneg (hbpos σ (by linarith)).le ψ.nonneg
    · rw [hψ0 σ hσI (not_lt.1 hσ'), mul_zero]
  -- The integrand is nonnegative and positive at `σ₀`, so its integral is positive.
  have hψc : 0 < ψ (F σ₀) := ψ.pos_of_mem_ball (by rw [Metric.mem_ball, dist_self]; exact hrpos)
  have hT : a < T := hσ.1.trans hσ.2
  have hlt := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt hT
    continuousOn_const hg (fun σ hσI ↦ hnonneg σ (Ioc_subset_Icc_self hσI))
    ⟨σ₀, h0, mul_pos hpos hψc⟩
  rw [intervalIntegral.integral_zero, h ψ] at hlt
  exact lt_irrefl _ hlt

/-- **Testing against bumps composed with a monotone reparametrization.** If
`∫ₐᵀ g(σ) ψ(F σ) dσ = 0` for every smooth bump `ψ` centred at `F σ₀`, with `g` and `F` continuous
on `[a, T]` and `F` strictly antitone there, then `g σ₀ = 0` for `σ₀ ∈ (a, T)`. -/
theorem eq_zero_of_forall_intervalIntegral_mul_contDiffBump_comp {g F : ℝ → ℝ} {a T σ₀ : ℝ}
    (hg : ContinuousOn g (Icc a T)) (hF : ContinuousOn F (Icc a T))
    (hFa : StrictAntiOn F (Icc a T)) (hσ : σ₀ ∈ Ioo a T)
    (h : ∀ ψ : ContDiffBump (F σ₀), ∫ σ in a..T, g σ * ψ (F σ) = 0) : g σ₀ = 0 := by
  refine le_antisymm (nonpos_of_forall_intervalIntegral_mul_contDiffBump_comp hg hF hFa hσ h) ?_
  have := nonpos_of_forall_intervalIntegral_mul_contDiffBump_comp (b := fun σ ↦ -g σ) hg.neg hF hFa
    hσ fun ψ ↦ by simp only [neg_mul, intervalIntegral.integral_neg, h ψ, neg_zero]
  linarith

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-!
# Vanishing exponential damping of a half-line integral

Damping an integrand on a half-line `u ≥ a` by `exp (-u (sigma - 1))` leaves the integral of an
integrable function unchanged in the limit `sigma → 1⁺`: the damping factor is bounded on the
half-line uniformly in `sigma ∈ [1, 2]`, so dominated convergence applies.

Conversely, increasing the damping rate preserves integrability on a right half-line, and on
`(δ, ∞)` it gains the factor `e^{-(x-σ)δ}`: this bounds the tail of a Laplace integral.

This is the Abelian step of a Tauberian argument, where a Dirichlet series is tested on a vertical
line `Re s = sigma` inside its half-plane of convergence and the line is pushed to the boundary;
`TauCeti.LSeries.tsum_term_mul_fourier_sub_pole_eq_integral_boundary` uses it for the simple-pole
term of the Wiener--Ikehara identity.

## Main results

* `TauCeti.tendsto_setIntegral_exp_smul`: the damped integral converges to the undamped one as
  `sigma` decreases to `1`.
* `MeasureTheory.IntegrableOn.exp_neg_mul_smul_of_le`: if `e^{-σt} G(t)` is integrable on
  `(0, ∞)`, so is the more strongly damped `e^{-xt} G(t)` for every `x ≥ σ`.
* `TauCeti.norm_setIntegral_Ioi_exp_neg_mul_smul_le`: on `(δ, ∞)` the extra damping
  `e^{-(x-σ)t}` is at most `e^{-(x-σ)δ}`, which bounds the tail of a Laplace integral.
* `TauCeti.integrableOn_exp_neg_mul_smul_iff`: if `q(t) = O(t^{a-1})` as `t → 0+` with `a > 0`,
  then `e^{-σt} q(t)` is integrable on `(0, ∞)` exactly when `q` is locally integrable on
  `(0, ∞)` and `e^{-σt} q(t)` is integrable on `(1, ∞)`.
-/

public section

namespace TauCeti

open Asymptotics Filter MeasureTheory Set
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {μ : Measure ℝ} {f : ℝ → E}
  {a : ℝ}

/-- As `sigma` decreases to `1`, the one-sided Laplace transform
`∫ u in Ici a, exp (-u (sigma - 1)) • f u` of a function integrable on the half-line `u ≥ a`
converges to its undamped integral. -/
theorem tendsto_setIntegral_exp_smul (hf : IntegrableOn f (Ici a) μ) :
    Tendsto (fun sigma : ℝ ↦ ∫ u in Ici a, Real.exp (-u * (sigma - 1)) • f u ∂μ)
      (𝓝[≥] 1) (𝓝 (∫ u in Ici a, f u ∂μ)) := by
  refine tendsto_integral_filter_of_dominated_convergence (fun u ↦ Real.exp (max 0 (-a)) * ‖f u‖)
    (.of_forall fun sigma ↦ (Continuous.aestronglyMeasurable (by fun_prop)).smul hf.1) ?_
    (hf.norm.const_mul _) (.of_forall fun u ↦ ?_)
  · filter_upwards [Icc_mem_nhdsGE (by norm_num : (1 : ℝ) < 2)] with sigma ⟨h1, h2⟩
    filter_upwards [ae_restrict_mem measurableSet_Ici] with u (hu : a ≤ u)
    rw [norm_smul, Real.norm_eq_abs, Real.abs_exp]
    gcongr
    rcases le_total 0 u with h | h <;> nlinarith [le_max_left 0 (-a), le_max_right 0 (-a)]
  · have hexp : Tendsto (fun sigma : ℝ ↦ Real.exp (-u * (sigma - 1))) (𝓝 1) (𝓝 1) :=
      (by fun_prop : Continuous fun sigma : ℝ ↦ Real.exp (-u * (sigma - 1))).tendsto' 1 1 (by simp)
    simpa using (hexp.mono_left nhdsWithin_le_nhds).smul_const (f u)

/-- If `t ↦ e^{-σt} G(t)` is integrable on `(0, ∞)`, then so is `t ↦ e^{-xt} G(t)` for every
`x ≥ σ`. -/
theorem _root_.MeasureTheory.IntegrableOn.exp_neg_mul_smul_of_le {G : ℝ → E} {σ x : ℝ}
    (hint : IntegrableOn (fun t => Real.exp (-σ * t) • G t) (Ioi 0)) (hx : σ ≤ x) :
    IntegrableOn (fun t => Real.exp (-x * t) • G t) (Ioi 0) := by
  have h := hint.bdd_smul 1 (φ := fun t => Real.exp (-(x - σ) * t))
    (by fun_prop : Continuous fun t : ℝ => Real.exp (-(x - σ) * t)).aestronglyMeasurable
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t)
      rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_le_one_iff]
      nlinarith)
  refine IntegrableOn.congr_fun h (fun t _ => ?_) measurableSet_Ioi
  simp only [Pi.smul_apply', smul_smul, ← Real.exp_add]
  ring_nf

/-- The part of a Laplace integral beyond `δ`: if `t ↦ e^{-σt} G(t)` is integrable on `(δ, ∞)`
and `x ≥ σ`, then `‖∫_δ^∞ e^{-xt} G(t) dt‖ ≤ e^{-(x-σ)δ} ∫_δ^∞ ‖e^{-σt} G(t)‖ dt`. -/
theorem norm_setIntegral_Ioi_exp_neg_mul_smul_le {G : ℝ → E} {σ x δ : ℝ}
    (hint : IntegrableOn (fun t => Real.exp (-σ * t) • G t) (Ioi δ)) (hx : σ ≤ x) :
    ‖∫ t in Ioi δ, Real.exp (-x * t) • G t‖ ≤
      Real.exp (-(x - σ) * δ) * ∫ t in Ioi δ, ‖Real.exp (-σ * t) • G t‖ := by
  rw [← integral_const_mul]
  refine norm_integral_le_of_norm_le (hint.norm.const_mul _) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : δ < t)
  rw [norm_smul, norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le,
    Real.norm_of_nonneg (Real.exp_pos _).le, ← mul_assoc, ← Real.exp_add]
  exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by nlinarith)) (norm_nonneg _)

/-- The two forms of the integrability hypothesis of Watson's lemma. If `q(t) = O(t^{a-1})` as
`t → 0+` with `a > 0`, then `t ↦ e^{-σt} q(t)` is integrable on `(0, ∞)` if and only if `q` is
locally integrable on `(0, ∞)` and `t ↦ e^{-σt} q(t)` is integrable on `(1, ∞)`. -/
theorem integrableOn_exp_neg_mul_smul_iff {q : ℝ → E} {a σ : ℝ} (ha : 0 < a)
    (hq : q =O[𝓝[>] 0] fun t => t ^ (a - 1)) :
    IntegrableOn (fun t => Real.exp (-σ * t) • q t) (Ioi 0) ↔
      LocallyIntegrableOn q (Ioi 0) ∧ IntegrableOn (fun t => Real.exp (-σ * t) • q t) (Ioi 1) := by
  refine ⟨fun h => ⟨?_, h.mono_set (Ioi_subset_Ioi zero_le_one)⟩, fun ⟨hloc, h1⟩ => ?_⟩
  · refine (h.locallyIntegrableOn.continuousOn_smul isOpen_Ioi.isLocallyClosed
      (g := fun t => Real.exp (σ * t)) (by fun_prop)).congr (Eventually.of_forall fun t => ?_)
    simp [smul_smul, ← Real.exp_add]
  -- `q` is integrable on `(0, b]` by the bound, and on `[b, 1]` by local integrability
  obtain ⟨K, hK⟩ := hq.bound
  obtain ⟨δ, hδ0, hδ⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp hK
  set b := min δ 1
  have hb0 : 0 < b := lt_min hδ0 one_pos
  have hq0 : IntegrableOn q (Ioc 0 b) := by
    refine Integrable.mono' ((intervalIntegral.intervalIntegrable_rpow'
      (r := a - 1) (by linarith)).1.const_mul K)
      ((hloc.aestronglyMeasurable).mono_set Ioc_subset_Ioi_self) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    simpa [abs_of_nonneg (Real.rpow_nonneg ht.1.le _)] using
      hδ ⟨ht.1, ht.2.trans (min_le_left _ _)⟩
  have hq1 : IntegrableOn q (Ioc b 1) :=
    (hloc.integrableOn_compact_subset (t := Icc b 1) (fun t ht => hb0.trans_le ht.1)
      isCompact_Icc).mono_set Ioc_subset_Icc_self
  have hq01 : IntegrableOn q (Ioc 0 1) := by
    rw [← Ioc_union_Ioc_eq_Ioc hb0.le (min_le_right _ _)]
    exact hq0.union hq1
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
  exact (hq01.continuousOn_smul_of_subset (by fun_prop) isCompact_Icc measurableSet_Ioc
    Ioc_subset_Icc_self).union h1

end TauCeti

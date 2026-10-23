/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.CurveAction.Basic
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Space
import TauCeti.MeasureTheory.Function.CurveAction.Polygonal
import TauCeti.MeasureTheory.Function.Lp.LIntegralRpow
import TauCeti.MeasureTheory.OptimalTransport.Chain

/-!
# Polygonal laws on paths through an absolutely continuous curve of laws

Let `E` be a separable Banach space, `1 ≤ p < ∞`, and let `μ` be a curve in the finite-moment
Wasserstein space `P_p(E)`, absolutely continuous on `[a, b]`. For every number `N ≥ 1` of steps
this file constructs a probability measure `η` on the path space `C([a, b], E)`, concentrated on
absolutely continuous paths, such that

* at each grid time `t_k = a + k * (b - a) / N`, the law of `γ t_k` under `η` is `μ t_k`;
* the expected `p`-action of the paths is at most the `p`-action of the curve `μ`:
  `∫ A_p(γ) dη(γ) ≤ A_p(μ)`.

The construction glues optimal couplings of consecutive laws `μ t_k` and `μ t_(k+1)` into a law
on sequences (`TauCeti.Measure.chainMeasure`) and pushes it forward along the polygonal
interpolation of a sequence on the grid (`TauCeti.polygonalInterpolation`). The expected action
of the interpolated paths is the expected discrete action
`∑ k < N, W_p(μ t_k, μ t_(k+1)) ^ p * h ^ (1 - p)`, with step `h = (b - a) / N`, and Hölder's
inequality bounds each term by the action of `μ` over `[t_k, t_(k+1)]`, because
`W_p(μ t_k, μ t_(k+1)) ≤ ∫_(t_k)^(t_(k+1)) |μ'|`.

These are the approximating laws in Lisini's superposition principle: along dyadic grids their
time marginals are eventually fixed at every dyadic time and their expected actions stay bounded
by `A_p(μ)`, which for `1 < p` makes the family tight, by the tightness criterion for laws of
curves with bounded expected action.
The linear structure of `E` is used only to interpolate between consecutive points.

## Main results

* `TauCeti.exists_map_IccExtend_eq_lintegral_curveAction_le`: the polygonal law on paths with
  prescribed time marginals on the grid and expected action at most that of `μ`.

## References

* S. Lisini, *Characterization of absolutely continuous curves in Wasserstein spaces*, Calc. Var.
  Partial Differential Equations 28 (2007), 85--120, proof of Theorem 5.
* L. Ambrosio, N. Gigli and G. Savaré, *Gradient Flows in Metric Spaces and in the Space of
  Probability Measures*, 2nd ed., Birkhäuser 2008, §8.2.
-/

public section

open MeasureTheory Set
open scoped ENNReal Interval

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] [CompleteSpace E] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **Polygonal laws on paths through an absolutely continuous curve of laws.** Let `E` be a
separable Banach space, `1 ≤ p < ∞`, and let `μ` be a curve in `P_p(E)` absolutely continuous on
`[a, b]`, with `a < b`. For every `N ≠ 0` there is a probability measure `η` on `C([a, b], E)`,
concentrated on absolutely continuous paths, whose law at each grid time
`a + k * ((b - a) / N)`, `k ≤ N`, is the value of `μ` there, and whose expected `p`-action is at
most the `p`-action of `μ` over `[a, b]`. -/
theorem exists_map_IccExtend_eq_lintegral_curveAction_le (hp : p ≠ ∞)
    {μ : ℝ → WassersteinSpace p E} {a b : ℝ} (hab : a < b)
    (hμ : AbsolutelyContinuousOnInterval μ a b) {N : ℕ} (hN : N ≠ 0) :
    ∃ η : Measure C(Icc a b, E), IsProbabilityMeasure η ∧
      (∀ᵐ γ : C(Icc a b, E) ∂η, AbsolutelyContinuousOnInterval (IccExtend hab.le γ) a b) ∧
      (∀ k ≤ N, η.map (fun γ : C(Icc a b, E) ↦ IccExtend hab.le γ (a + k * ((b - a) / N))) =
        ((μ (a + k * ((b - a) / N)) : ProbabilityMeasure E) : Measure E)) ∧
      ∫⁻ γ, curveAction p.toReal (IccExtend hab.le γ) a b ∂η ≤ curveAction p.toReal μ a b := by
  have hp1 : 1 ≤ p := Fact.out
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp1).ne'
  have hr : 1 ≤ p.toReal := by simpa using ENNReal.toReal_mono hp hp1
  set h := (b - a) / N with h_def
  have hh : 0 < h := div_pos (sub_pos.2 hab) (by positivity)
  have hNh : a + N * h = b := by
    rw [h_def]
    field_simp
    ring
  -- Optimal couplings of the laws at consecutive grid times, glued into a law on sequences.
  have hcoup (k : ℕ) := exists_isCoupling_eLpNorm_eq_wassersteinEDist hp0 hp
    ((μ (a + k * h) : ProbabilityMeasure E) : Measure E)
    ((μ (a + (k + 1) * h) : ProbabilityMeasure E) : Measure E) ⟨_, isCoupling_prod _ _⟩
  choose π hπ hπW using hcoup
  have : ∀ k, IsProbabilityMeasure (π k) := fun k ↦ (hπ k).isProbabilityMeasure
  have hmatch (j : ℕ) : (π j).snd = (π (j + 1)).fst := by
    rw [(hπ j).snd_eq, (hπ (j + 1)).fst_eq, Nat.cast_succ]
  set P := Measure.chainMeasure (X := fun _ ↦ E) π
  -- The polygonal path through a sequence of points.
  let Φ : C(ℕ → E, C(Icc a b, E)) := ContinuousMap.curry
    ⟨fun q : (ℕ → E) × Icc a b ↦ polygonalInterpolation a h N q.1 q.2,
      (continuous_polygonalInterpolation a h N).comp
        (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))⟩
  have hΦ : Measurable Φ := Φ.continuous.measurable
  have hΦeq (x : ℕ → E) :
      EqOn (IccExtend hab.le (Φ x)) (polygonalInterpolation a h N x) (Icc a (a + N * h)) := by
    intro t ht
    rw [hNh] at ht
    rw [IccExtend_of_mem hab.le _ ht, ContinuousMap.curry_apply, ContinuousMap.coe_mk]
  refine ⟨P.map Φ, (Measure.isProbabilityMeasure_map_iff hΦ.aemeasurable).2 inferInstance, ?_,
    fun k hk ↦ ?_, ?_⟩
  · -- Polygonal paths are absolutely continuous.
    refine (ae_map_iff hΦ.aemeasurable
      (measurableSet_absolutelyContinuousOnInterval_IccExtend hab.le a b)).2 (ae_of_all _ ?_)
    intro x
    have := (isPolygonalOnInterval_of_eqOn_polygonalInterpolation hN hh
      (hΦeq x)).absolutelyContinuousOnInterval
    rwa [hNh] at this
  · -- At a grid time the polygonal path passes through the corresponding point.
    have heval : (fun γ : C(Icc a b, E) ↦ IccExtend hab.le γ (a + k * h)) ∘ Φ =
        fun x : ℕ → E ↦ x k := by
      funext x
      simp only [Function.comp_apply]
      rw [hΦeq x (add_natCast_mul_mem_Icc a hh.le hk), polygonalInterpolation_apply_grid x hh hk]
    rw [Measure.map_map (measurable_IccExtend_apply hab.le _) hΦ, heval,
      Measure.map_eval_chainMeasure π k fun j _ ↦ hmatch j, (hπ k).fst_eq]
  · -- The expected action is the expected discrete action, bounded cell by cell by Hölder.
    have hjump (k : ℕ) : ∫⁻ x, edist (x k) (x (k + 1)) ^ p.toReal ∂P =
        edist (μ (a + k * h)) (μ (a + (k + 1) * h)) ^ p.toReal := by
      have hk : Measurable fun x : ℕ → E ↦ (x k, x (k + 1)) :=
        (measurable_pi_apply k).prodMk (measurable_pi_apply (k + 1))
      rw [WassersteinSpace.edist_def, ← hπW k, eLpNorm_rpow_eq_lintegral hp0 hp
        measurable_edist.aemeasurable, ← Measure.map_adjacent_chainMeasure π k fun j _ ↦ hmatch j,
        lintegral_map (measurable_edist.pow_const _) hk]
    calc ∫⁻ γ, curveAction p.toReal (IccExtend hab.le γ) a b ∂P.map Φ
        = ∫⁻ x, ∑ k ∈ Finset.range N,
            edist (x k) (x (k + 1)) ^ p.toReal * ENNReal.ofReal h ^ (1 - p.toReal) ∂P := by
          rw [lintegral_map (measurable_curveAction_IccExtend hab.le _ _ _) hΦ]
          refine lintegral_congr fun x ↦ ?_
          rw [← curveAction_eq_sum_edist_rpow_mul_rpow_one_sub_of_eqOn_polygonalInterpolation hh
            (by linarith) (hΦeq x), hNh]
      _ = ∑ k ∈ Finset.range N,
            edist (μ (a + k * h)) (μ (a + (k + 1) * h)) ^ p.toReal *
              ENNReal.ofReal h ^ (1 - p.toReal) := by
          have hm (k : ℕ) : Measurable fun x : ℕ → E ↦ edist (x k) (x (k + 1)) ^ p.toReal :=
            ((measurable_pi_apply k).edist (measurable_pi_apply (k + 1))).pow_const _
          rw [lintegral_finsetSum _ fun k _ ↦ (hm k).mul_const _]
          refine Finset.sum_congr rfl fun k _ ↦ ?_
          rw [lintegral_mul_const _ (hm k), hjump]
      _ ≤ curveAction p.toReal μ a b := by
          rw [← hNh] at hμ ⊢
          exact sum_edist_rpow_mul_rpow_one_sub_le_curveAction hh hr hμ

end TauCeti

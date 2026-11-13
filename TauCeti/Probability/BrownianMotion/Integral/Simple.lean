/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Integral.L2
public import TauCeti.Probability.Finance.SimpleStrategy.Basic
import TauCeti.MeasureTheory.Function.Lp.Basic
import TauCeti.MeasureTheory.Function.Lp.DominatedConvergence
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp

/-!
# Elementary values of the completed Brownian integral

The predictable L² integral agrees with finite-grid gains for random left-endpoint-measurable
holdings. Unlike the defining rectangle formula, the holdings need not take finitely many
values or be bounded. Both results only require square integrability of the actual
predictable time-product integrand, so they also cover empty intervals and intervals beyond
the horizon without moment assumptions on their unused heights.

These identities connect completion in predictable L² with elementary stochastic integrals.
They concern terminal L² values and almost-everywhere equality at each fixed observation time,
not simultaneous equality of arbitrarily chosen representatives.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.2.B.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace TauCeti.Probability.IsFilteredPreBrownianReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {ℱ : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}

private theorem coeFn_l2Integral_simpleFunc_Ioc (hW : IsFilteredPreBrownianReal ℱ W P)
    (T s t : ℝ≥0) (g : @SimpleFunc Ω (ℱ s) ℝ)
    (hg : letI : MeasurableSpace Ω := ℱ s
      MemLp (fun p : ℝ≥0 × Ω ↦ (Ioc s t).indicator (fun _ ↦ g p.2) p.1)
        2 (ℱ.predictableMeasure P T)) :
    letI : MeasurableSpace Ω := ℱ s
    hW.l2Integral T (hg.toLp _) =ᵐ[P]
      fun ω ↦ g ω * (W (max s (min t T)) ω - W s ω) := by
  classical
  let := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
  let : MeasurableSpace Ω := ℱ s
  let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
  let R (c : ℝ) : Lp ℝ 2 (ℱ.predictableMeasure P T) :=
    indicatorConstLp 2 (measurableSet_predictable_Ioc_prod s t (g.measurableSet_fiber c))
      (measure_ne_top _ _) c
  have hin : hg.toLp _ = ∑ c ∈ g.range, R c := by
    apply Lp.ext
    filter_upwards [hg.coeFn_toLp, Lp.coeFn_fun_finsetSum g.range R,
      (ae_ball_iff g.range.countable_toSet).2 (fun c _ ↦ indicatorConstLp_coeFn (p := 2)
        (hs := measurableSet_predictable_Ioc_prod s t (g.measurableSet_fiber c))
        (hμs := measure_ne_top (ℱ.predictableMeasure P T) _) (c := c))] with p hp hsum hR
    rw [hp, hsum]
    simp only [R]
    rw [Finset.sum_congr rfl fun c hc ↦ hR c hc]
    by_cases hpt : p.1 ∈ Ioc s t
    · simp [hpt.1, hpt.2, Set.indicator, eq_comm, g.mem_range_self]
    · simp [hpt]
  rw [hin, map_sum]
  filter_upwards [Lp.coeFn_fun_finsetSum g.range (fun c ↦ hW.l2Integral T (R c)),
    (ae_ball_iff g.range.countable_toSet).2
      (fun c _ ↦ hW.coeFn_l2Integral_indicatorConstLp_Ioc_prod
        T s t (g.measurableSet_fiber c) c)] with ω hsum hR
  rw [hsum]
  simp only [R]
  rw [Finset.sum_congr rfl fun c hc ↦ hR c hc, ← Finset.sum_mul]
  simp [Set.indicator, eq_comm, g.mem_range_self]

/-- A random height known at the left endpoint integrates to that height times the clipped
Brownian increment. Square integrability is required of the interval integrand itself. -/
theorem coeFn_l2Integral_indicator_Ioc (hW : IsFilteredPreBrownianReal ℱ W P)
    (T s t : ℝ≥0) {ξ : Ω → ℝ} (hξ : StronglyMeasurable[ℱ s] ξ)
    (hH : MemLp (fun p : ℝ≥0 × Ω ↦ (Ioc s t).indicator (fun _ ↦ ξ p.2) p.1)
      2 (ℱ.predictableMeasure P T)) :
    hW.l2Integral T (hH.toLp _) =ᵐ[P]
      fun ω ↦ ξ ω * (W (max s (min t T)) ω - W s ω) := by
  classical
  let := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
  let H (a : Ω → ℝ) (p : ℝ≥0 × Ω) := (Ioc s t).indicator (fun _ ↦ a p.2) p.1
  let D (ω : Ω) := W (max s (min t T)) ω - W s ω
  let : MeasurableSpace Ω := ℱ s
  let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
  -- Approximate the height, but dominate the errors by the actual interval integrand.
  let g (n : ℕ) : SimpleFunc Ω ℝ :=
    SimpleFunc.approxOn ξ hξ.measurable univ 0 (mem_univ _) n
  have hgmem (n : ℕ) : MemLp (H (g n)) 2 (ℱ.predictableMeasure P T) :=
    ℱ.memLp_indicator_Ioc_predictableMeasure T s t (g n).stronglyMeasurable
      (memLp_of_memLp_trim (ℱ.le s) ((g n).memLp_of_isFiniteMeasure 2 (P.trim (ℱ.le s))))
  have hlim : ∀ ω, Tendsto (fun n ↦ g n ω) atTop (𝓝 (ξ ω)) := fun ω ↦
    SimpleFunc.tendsto_approxOn hξ.measurable (mem_univ _) (by simp)
  have henergy : Tendsto (fun n ↦ eLpNorm (H (g n) - H ξ) 2
      (ℱ.predictableMeasure P T)) atTop (𝓝 0) := by
    apply tendsto_eLpNorm_sub_of_ae_tendsto (C := 1) (by norm_num)
      (Eventually.of_forall fun n ↦ (hgmem n).aestronglyMeasurable) hH
    · exact Eventually.of_forall fun n ↦ Eventually.of_forall fun p ↦ by
        by_cases hp : p.1 ∈ Ioc s t
        · simp only [H, indicator_of_mem hp, ENNReal.coe_one, one_mul]
          apply eNorm_le_iff_norm_le.2
          have hn := SimpleFunc.nnNorm_approxOn_le (s := univ) (y₀ := (0 : ℝ))
            hξ.measurable (mem_univ _) p.2 n
          simp only [sub_zero] at hn
          exact_mod_cast hn
        · simp [H, hp]
    · exact Eventually.of_forall fun p ↦ by
        by_cases hp : p.1 ∈ Ioc s t
        · simpa [H, hp] using hlim p.2
        · simp [H, hp]
  have hLp : Tendsto (fun n ↦ (hgmem n).toLp _) atTop (𝓝 (hH.toLp _)) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ hgmem _ hH).2 henergy
  have hout := tendstoInMeasure_of_tendsto_Lp ((hW.l2Integral T).continuous.tendsto _ |>.comp hLp)
  have hs : ∀ n, hW.l2Integral T ((hgmem n).toLp _) =ᵐ[P] fun ω ↦ g n ω * D ω :=
    fun n ↦ hW.coeFn_l2Integral_simpleFunc_Ioc T s t (g n) (hgmem n)
  exact tendstoInMeasure_ae_unique (hout.congr_left hs)
    (tendstoInMeasure_of_tendsto_ae
      (fun n ↦ (Lp.memLp (hW.l2Integral T ((hgmem n).toLp _))).aestronglyMeasurable.congr
        (hs n))
      (Eventually.of_forall fun ω ↦ (hlim ω).mul_const (D ω)))

/-- The completed integral of a simple holding is its finite-grid gains at the observation
time. Only the actual predictable integrand must be square integrable. The grid may have
repeated dates, need not start at zero, and may extend past `T`. -/
theorem coeFn_l2Integral_simpleHolding (hW : IsFilteredPreBrownianReal ℱ W P)
    {τ : ℕ → ℝ≥0} {n : ℕ} {a : ℕ → Ω → ℝ}
    (hτ : MonotoneOn τ (Iic n))
    (ha : ∀ j < n, StronglyMeasurable[ℱ (τ j)] (a j))
    (T : ℝ≥0)
    (hH : MemLp (Function.uncurry (Finance.simpleHolding τ n a)) 2 (ℱ.predictableMeasure P T)) :
    hW.l2Integral T (hH.toLp _) =ᵐ[P]
      Finance.simpleGains τ n a W T := by
  classical
  let := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
  let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
  have hmem (j : ℕ) (hj : j ∈ Finset.range n) :
      MemLp (fun p : ℝ≥0 × Ω ↦ (Ioc (τ j) (τ (j + 1))).indicator
        (fun _ ↦ a j p.2) p.1) 2 (ℱ.predictableMeasure P T) := by
    convert hH.indicator (measurableSet_predictable_Ioc_prod (τ j) (τ (j + 1))
      (𝓕 := ℱ) MeasurableSet.univ).nullMeasurableSet using 1
    ext p
    by_cases hp : p.1 ∈ Ioc (τ j) (τ (j + 1))
    · simp [hp, Function.uncurry, Finance.simpleHolding_of_mem_Ioc hτ
        (Finset.mem_range.mp hj) hp]
    · simp [hp]
  have hin : hH.toLp _ = ∑ j : Finset.range n, (hmem j.1 j.2).toLp _ :=
    (MemLp.toLp_congr hH
      (memLp_finsetSum Finset.univ fun (j : Finset.range n) _ ↦ hmem j.1 j.2)
      (.of_forall fun (p : ℝ≥0 × Ω) ↦ by
        simpa only [Function.uncurry, Finance.simpleHolding_def] using
          (Finset.sum_coe_sort (Finset.range n)
            (fun j ↦ (Ioc (τ j) (τ (j + 1))).indicator (fun _ ↦ a j p.2) p.1)).symm)).trans
      (MemLp.toLp_finsetSum _ fun (j : Finset.range n) ↦ hmem j.1 j.2)
  rw [hin, map_sum]
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ
    (fun j : Finset.range n ↦ hW.l2Integral T ((hmem j.1 j.2).toLp _)),
    ae_all_iff.2 (fun j : Finset.range n ↦
      hW.coeFn_l2Integral_indicator_Ioc T (τ j) (τ (j + 1))
        (ha j (Finset.mem_range.mp j.2)) (hmem j j.2))] with ω hsum hj
  rw [hsum, Finance.simpleGains_def]
  conv_rhs => rw [← Finset.sum_coe_sort (Finset.range n)]
  apply Finset.sum_congr rfl
  intro j _
  rw [hj j]
  have hjn : (j : ℕ) < n := Finset.mem_range.mp j.2
  have hle : τ j ≤ τ (j + 1) := hτ (by simp; omega) (by simp; omega) (by omega)
  by_cases ht : τ j ≤ T
  · simp [min_eq_left ht, max_eq_right (le_min hle ht)]
  · have hTj : T ≤ τ j := (not_le.mp ht).le
    simp [min_eq_right hTj, min_eq_right (hTj.trans hle), max_eq_left hTj]

end TauCeti.Probability.IsFilteredPreBrownianReal

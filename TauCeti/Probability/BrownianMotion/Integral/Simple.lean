/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Integral.L2
public import TauCeti.Probability.Finance.SimpleStrategy.Energy
import TauCeti.MeasureTheory.Function.Lp.DominatedConvergence
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp

/-!
# Elementary values of the completed Brownian integral

The predictable L² integral agrees with finite-grid gains for random left-endpoint-measurable
holdings. Unlike the defining rectangle formula, the holdings need not take finitely many
values or be bounded. The one-interval result only requires square integrability of the
actual time-product integrand, so it also covers empty intervals without moment assumptions
on their unused heights.

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
  -- A one-interval simple holding supplies literal predictable measurability.
  have hpred (a : Ω → ℝ) (ha : StronglyMeasurable[ℱ s] a) :
      StronglyMeasurable[ℱ.predictable] (H a) := by
    have hm := Finance.isStronglyPredictable_simpleHolding
      (ℱ := ℱ) (τ := fun j ↦ if j = 0 then s else t) (n := 1) (a := fun _ ↦ a)
      (by
        intro j hj
        have hj0 : j = 0 := by omega
        subst j
        exact ha)
    have heq : Function.uncurry
        (Finance.simpleHolding (fun j ↦ if j = 0 then s else t) 1 (fun _ ↦ a)) = H a := by
      ext p
      simp [Function.uncurry, Finance.simpleHolding_def, H]
    rwa [IsStronglyPredictable, heq] at hm
  have hmem (a : Ω → ℝ) (ha : StronglyMeasurable[ℱ s] a) (haLp : MemLp a 2 P) :
      MemLp (H a) 2 (ℱ.predictableMeasure P T) := by
    apply (ℱ.memLp_predictableMeasure_iff P (hpred a ha) T 2).2
    convert (haLp.comp_snd (timeMeasure T)).indicator
      ((measurableSet_Ioc (a := s) (b := t)).prod MeasurableSet.univ).nullMeasurableSet
      using 1
    ext p
    by_cases hp : p.1 ∈ Ioc s t <;> simp [H, hp]
  let : MeasurableSpace Ω := ℱ s
  let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
  have hgm (g : SimpleFunc Ω ℝ) : MemLp (H g) 2 (ℱ.predictableMeasure P T) :=
    hmem g g.stronglyMeasurable
      (memLp_of_memLp_trim (ℱ.le s) (g.memLp_of_isFiniteMeasure 2 (P.trim (ℱ.le s))))
  -- Approximate the height, but dominate the errors by the actual interval integrand.
  let g (n : ℕ) : SimpleFunc Ω ℝ :=
    SimpleFunc.approxOn ξ hξ.measurable univ 0 (mem_univ _) n
  have hgmem (n : ℕ) : MemLp (H (g n)) 2 (ℱ.predictableMeasure P T) := hgm (g n)
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
time. The grid may have repeated dates, need not start at zero, and may extend past `T`. -/
theorem coeFn_l2Integral_simpleHolding (hW : IsFilteredPreBrownianReal ℱ W P)
    {τ : ℕ → ℝ≥0} {n : ℕ} {a : ℕ → Ω → ℝ}
    (hτ : MonotoneOn τ (Iic n))
    (ha : ∀ j < n, StronglyMeasurable[ℱ (τ j)] (a j))
    (haLp : ∀ j < n, MemLp (a j) 2 P) (T : ℝ≥0) :
    letI := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
    hW.l2Integral T ((Finance.memLp_simpleHolding_predictableMeasure ha haLp T).toLp _) =ᵐ[P]
      Finance.simpleGains τ n a W T := by
  classical
  let := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
  let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
  have hmem (j : ℕ) (hj : j ∈ Finset.range n) :
      MemLp (fun p : ℝ≥0 × Ω ↦ (Ioc (τ j) (τ (j + 1))).indicator
        (fun _ ↦ a j p.2) p.1) 2 (ℱ.predictableMeasure P T) := by
    have hm := Finance.memLp_simpleHolding_predictableMeasure
      (ℱ := ℱ) (τ := fun k ↦ if k = 0 then τ j else τ (j + 1)) (n := 1)
      (a := fun _ ↦ a j)
      (by
        intro k hk
        have hk0 : k = 0 := by omega
        subst k
        exact ha j (Finset.mem_range.mp hj))
      (by intro _ _; exact haLp j (Finset.mem_range.mp hj)) T
    have heq : Function.uncurry
        (Finance.simpleHolding (fun k ↦ if k = 0 then τ j else τ (j + 1)) 1 (fun _ ↦ a j)) =
        fun p : ℝ≥0 × Ω ↦ (Ioc (τ j) (τ (j + 1))).indicator (fun _ ↦ a j p.2) p.1 := by
      ext p
      simp [Function.uncurry, Finance.simpleHolding_def]
    rwa [heq] at hm
  have hin : (Finance.memLp_simpleHolding_predictableMeasure ha haLp T).toLp _ =
      ∑ j : Finset.range n, (hmem j.1 j.2).toLp _ := by
    apply Lp.ext
    filter_upwards [(Finance.memLp_simpleHolding_predictableMeasure ha haLp T).coeFn_toLp,
      Lp.coeFn_fun_finsetSum Finset.univ (fun j : Finset.range n ↦ (hmem j.1 j.2).toLp _),
      ae_all_iff.2 (fun j : Finset.range n ↦ (hmem j.1 j.2).coeFn_toLp)] with p hp hsum hj
    rw [hp, hsum]
    simp only [hj, Function.uncurry, Finance.simpleHolding_def]
    exact (Finset.sum_coe_sort (Finset.range n)
      (fun j ↦ (Ioc (τ j) (τ (j + 1))).indicator (fun _ ↦ a j p.2) p.1)).symm
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

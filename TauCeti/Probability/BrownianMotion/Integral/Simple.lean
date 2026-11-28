/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import TauCeti.Probability.BrownianMotion.Integral.Integrable
public import TauCeti.Probability.BrownianMotion.Integral.L2
public import TauCeti.Probability.Finance.SimpleStrategy.Basic
public import TauCeti.Probability.StochasticIntegral.Elementary
import TauCeti.MeasureTheory.Function.Lp.Basic
import TauCeti.MeasureTheory.Function.Lp.DominatedConvergence
import TauCeti.Probability.BrownianMotion.Integral.Energy.Basic
import TauCeti.Probability.BrownianMotion.Martingale
import TauCeti.Probability.Finance.SimpleStrategy.Approximation
import TauCeti.Probability.Finance.SimpleStrategy.Energy
import TauCeti.Probability.Martingale.LpLimit
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp

/-!
# Elementary values of the completed Brownian integral

The predictable L² integral agrees with finite-grid gains for random left-endpoint-measurable
holdings. Unlike the defining rectangle formula, the holdings need not take finitely many
values or be bounded. Both results only require square integrability of the actual
predictable time-product integrand, so they also cover empty intervals and intervals beyond
the horizon without moment assumptions on their unused heights.

For any `TauCeti.BrownianIntegrable` integrand, `TauCeti.Probability.SimpleHoldingApprox` and
`TauCeti.Probability.IsFilteredPreBrownianReal.exists_simpleHoldingApprox` bundle a sequence of
`TauCeti.ElementaryIntegrand`s on strictly increasing grids starting at zero that approximate the
integrand in `L²` and in square energy in probability while their elementary gains are true
martingales converging in `L²(P)` to the terminal `L²` integral `hW.l2Integral T`. Passing to an
`L²`-martingale limit yields `exists_simpleHolding_martingale_approx`.

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

namespace TauCeti.Probability

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {ℱ : Filtration ℝ≥0 mΩ} {W H : ℝ≥0 → Ω → ℝ}

/-- A bundled sequence of bounded elementary integrands on strictly increasing deterministic grids
starting at zero that approximates a `BrownianIntegrable` integrand `H` on every finite horizon in
`L²` while its elementary integrals form `L²`-martingales converging at every horizon to
`hW.l2Integral T`. -/
@[ext]
structure SimpleHoldingApprox {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (ℱ : Filtration ℝ≥0 mΩ) (P : Measure Ω) (W H : ℝ≥0 → Ω → ℝ)
    (hW : IsFilteredPreBrownianReal ℱ W P) (hH : BrownianIntegrable ℱ P H) where
  /-- Elementary integrand at approximation stage `m`. -/
  elem : ℕ → ElementaryIntegrand ℱ
  /-- Every approximating grid starts at time zero. -/
  grid_zero : ∀ m, (elem m).grid 0 = 0
  /-- Every approximating grid is strictly increasing. -/
  strictMono_grid : ∀ m, StrictMono (elem m).grid
  /-- The elementary integrals of each approximating stage form a martingale. -/
  martingale : ∀ m, Martingale ((elem m).integral W) ℱ P
  /-- The elementary integrals are square integrable at every time. -/
  memLp : ∀ m T, MemLp ((elem m).integral W T) 2 P
  /-- The elementary integrands converge to `H` in `L²((timeMeasure T).prod P)` at every
  horizon. -/
  tendsto_holding : ∀ T, Tendsto (fun m ↦ eLpNorm
    (fun p ↦ (elem m).toProcess p.1 p.2 - H p.1 p.2) 2
      ((timeMeasure T).prod P)) atTop (𝓝 0)
  /-- The elementary integrals converge in `L²(P)` at every horizon to `hW.l2Integral T`. -/
  tendsto_l2Integral : ∀ T, Tendsto (fun m ↦ (memLp m T).toLp
    ((elem m).integral W T)) atTop
    (𝓝 (hW.l2Integral T ((hH.memLp_predictableMeasure T).toLp (Function.uncurry H))))

namespace SimpleHoldingApprox

variable {hW : IsFilteredPreBrownianReal ℱ W P} {hH : BrownianIntegrable ℱ P H}
  (h : SimpleHoldingApprox ℱ P W H hW hH)

/-- Canonical number of grid intervals at approximation stage `m`. -/
def n (m : ℕ) : ℕ := (h.elem m).n

/-- Canonical total-index deterministic grid at stage `m`, clamped at the terminal endpoint. -/
def τ (m j : ℕ) : ℝ≥0 := (h.elem m).grid ⟨min j (h.elem m).n, by omega⟩

/-- Canonical total-index holding height at stage `m`, extended by zero beyond `h.n m`. -/
def a (m j : ℕ) : Ω → ℝ :=
  if hj : j < (h.elem m).n then (h.elem m).height ⟨j, hj⟩ else 0

/-- Canonical uniform bound on the holding heights at stage `m`. -/
def C (m : ℕ) : ℝ := ⨆ i : Fin (h.elem m).n, ⨆ ω, |(h.elem m).height i ω|

/-- Every canonical approximating grid starts at time zero. -/
theorem tau_zero (m : ℕ) : h.τ m 0 = 0 := by
  simpa [τ] using h.grid_zero m

/-- Every canonical approximating grid is strictly increasing on `Iic (h.n m)`. -/
theorem strictMonoOn (m : ℕ) : StrictMonoOn (h.τ m) (Iic (h.n m)) := by
  intro i hi j hj hij
  have hi' : i ≤ (h.elem m).n := hi
  have hj' : j ≤ (h.elem m).n := hj
  exact h.strictMono_grid m (by
    rw [Fin.lt_def]
    simpa [τ, Nat.min_eq_left hi', Nat.min_eq_left hj'] using hij)

/-- Each canonical holding height is strongly measurable at its left grid endpoint. -/
theorem stronglyMeasurable (m j : ℕ) (hj : j < h.n m) :
    StronglyMeasurable[ℱ (h.τ m j)] (h.a m j) := by
  have hj' : j < (h.elem m).n := hj
  have hτj : h.τ m j = (h.elem m).grid (⟨j, hj'⟩ : Fin (h.elem m).n).castSucc := by
    simp [τ, Nat.min_eq_left hj'.le, Fin.castSucc]
  rw [hτj]
  simpa only [a, dite_eq_left hj'] using (h.elem m).measurable_height ⟨j, hj'⟩

/-- Each canonical holding height at stage `m` is uniformly bounded by `h.C m`. -/
theorem norm_le (m j : ℕ) (hj : j < h.n m) (ω : Ω) : ‖h.a m j ω‖ ≤ h.C m := by
  have : Nonempty Ω := ⟨ω⟩
  have hj' : j < (h.elem m).n := hj
  have hbdd (i : Fin (h.elem m).n) : BddAbove (Set.range fun ω' ↦ |(h.elem m).height i ω'|) := by
    obtain ⟨B, hB⟩ := (h.elem m).bounded_height i
    exact ⟨B, Set.forall_mem_range.mpr hB⟩
  have hle_i : |(h.elem m).height ⟨j, hj'⟩ ω| ≤ ⨆ ω', |(h.elem m).height ⟨j, hj'⟩ ω'| :=
    le_ciSup (hbdd ⟨j, hj'⟩) ω
  have hle_sup : (⨆ ω', |(h.elem m).height ⟨j, hj'⟩ ω'|) ≤ h.C m :=
    le_ciSup (Set.Finite.bddAbove (Set.finite_range
      (fun i : Fin (h.elem m).n ↦ ⨆ ω', |(h.elem m).height i ω'|))) ⟨j, hj'⟩
  simpa [a, hj', Real.norm_eq_abs] using hle_i.trans hle_sup

/-- The canonical total-index `Finance.simpleHolding` equals `(h.elem m).toProcess`. -/
theorem simpleHolding_eq_toProcess (m : ℕ) :
    Finance.simpleHolding (h.τ m) (h.n m) (h.a m) = (h.elem m).toProcess := by
  ext t ω
  rw [Finance.simpleHolding_def, ElementaryIntegrand.toProcess_def]
  dsimp only [n]
  rw [← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hi : (i : ℕ) < (h.elem m).n := i.isLt
  simp [τ, a, hi, Fin.castSucc, Fin.castAdd, Fin.castLE, Fin.succ]

/-- The canonical total-index `Finance.simpleGains` equals `(h.elem m).integral W`. -/
theorem simpleGains_eq_integral (m : ℕ) :
    Finance.simpleGains (h.τ m) (h.n m) (h.a m) W = (h.elem m).integral W := by
  ext t ω
  rw [Finance.simpleGains_def, ElementaryIntegrand.integral_def]
  dsimp only [n]
  rw [← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hi : (i : ℕ) < (h.elem m).n := i.isLt
  simp [τ, a, hi, Fin.castSucc, Fin.castAdd, Fin.castLE, Fin.succ]

/-- The approximating simple holdings converge to `H` in square energy in probability on
`[0, T]`. -/
theorem tendsto_energy (T : ℝ≥0) (ε : ℝ≥0∞) (hε : 0 < ε) :
    Tendsto (fun m ↦ P {ω | ε ≤ ∫⁻ s,
      ‖(h.elem m).toProcess s ω - H s ω‖ₑ ^ 2 ∂timeMeasure T})
      atTop (𝓝 0) :=
  let := (hW.hasLaw_eval 0).isProbabilityMeasure
  IsStronglyPredictable.tendsto_measure_lintegral_enorm_sub_sq_of_tendsto_eLpNorm
    (fun m ↦ (h.elem m).isStronglyPredictable)
    (fun _ ↦ hH.isStronglyPredictable) (h.tendsto_holding T) hε

/-- The elementary gains of the approximating simple holdings converge in probability at horizon `T`
to `hW.l2Integral T`. -/
theorem tendstoInMeasure_l2Integral (T : ℝ≥0) :
    TendstoInMeasure P (fun m ↦ (h.elem m).integral W T) atTop
      (hW.l2Integral T ((hH.memLp_predictableMeasure T).toLp (Function.uncurry H))) :=
  (MeasureTheory.tendstoInMeasure_of_tendsto_Lp (h.tendsto_l2Integral T)).congr_left
    fun m ↦ (h.memLp m T).coeFn_toLp

/-- Each bounded holding height of an approximating simple holding lies in `L²(P)`. -/
theorem memLp_coeff (m j : ℕ) (hj : j < h.n m) : MemLp (h.a m j) 2 P :=
  have : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  MemLp.of_bound ((h.stronglyMeasurable m j hj).mono (ℱ.le _)).aestronglyMeasurable (h.C m)
    (.of_forall (h.norm_le m j hj))

end SimpleHoldingApprox

namespace IsFilteredPreBrownianReal

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
  have hin : hH.toLp _ = ∑ j : Finset.range n, (hmem j.val j.property).toLp _ :=
    (MemLp.toLp_congr hH
      (memLp_finsetSum Finset.univ fun (j : Finset.range n) _ ↦ hmem j.val j.property)
      (.of_forall fun (p : ℝ≥0 × Ω) ↦ by
        simpa only [Function.uncurry, Finance.simpleHolding_def] using
          (Finset.sum_coe_sort (Finset.range n)
            (fun j ↦ (Ioc (τ j) (τ (j + 1))).indicator (fun _ ↦ a j p.2) p.1)).symm)).trans
      (MemLp.toLp_finsetSum _ fun (j : Finset.range n) ↦ hmem j.val j.property)
  rw [hin, map_sum]
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ
    (fun j : Finset.range n ↦ hW.l2Integral T ((hmem j.val j.property).toLp _)),
    ae_all_iff.2 (fun j : Finset.range n ↦
      hW.coeFn_l2Integral_indicator_Ioc T (τ j) (τ (j + 1))
        (ha j (Finset.mem_range.mp j.property)) (hmem j j.property))] with ω hsum hj
  rw [hsum, Finance.simpleGains_def]
  conv_rhs => rw [← Finset.sum_coe_sort (Finset.range n)]
  apply Finset.sum_congr rfl
  intro j _
  rw [hj j]
  have hjn : (j : ℕ) < n := Finset.mem_range.mp j.property
  have hle : τ j ≤ τ (j + 1) := hτ (by simp; omega) (by simp; omega) (by omega)
  by_cases ht : τ j ≤ T
  · simp [min_eq_left ht, max_eq_right (le_min hle ht)]
  · have hTj : T ≤ τ j := (not_le.mp ht).le
    simp [min_eq_right hTj, min_eq_right (hTj.trans hle), max_eq_left hTj]

/-- `Lp` form of `coeFn_l2Integral_simpleHolding`. -/
theorem l2Integral_simpleHolding (hW : IsFilteredPreBrownianReal ℱ W P)
    {τ : ℕ → ℝ≥0} {n : ℕ} {a : ℕ → Ω → ℝ}
    (hτ : MonotoneOn τ (Iic n))
    (ha : ∀ j < n, StronglyMeasurable[ℱ (τ j)] (a j))
    (T : ℝ≥0)
    (hH : MemLp (Function.uncurry (Finance.simpleHolding τ n a)) 2 (ℱ.predictableMeasure P T))
    (hg : MemLp (Finance.simpleGains τ n a W T) 2 P) :
    hW.l2Integral T (hH.toLp (Function.uncurry (Finance.simpleHolding τ n a))) =
      hg.toLp (Finance.simpleGains τ n a W T) :=
  Lp.ext ((hW.coeFn_l2Integral_simpleHolding hτ ha T hH).trans hg.coeFn_toLp.symm)

/-- Every `BrownianIntegrable` integrand admits a `SimpleHoldingApprox` sequence of bounded
elementary integrands on strictly increasing grids starting at zero whose elementary integrals are
martingales converging in `L²(P)` at every horizon to `hW.l2Integral T`. -/
theorem exists_simpleHoldingApprox
    (hW : IsFilteredPreBrownianReal ℱ W P) (hH : BrownianIntegrable ℱ P H) :
    Nonempty (SimpleHoldingApprox ℱ P W H hW hH) := by
  have : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  obtain ⟨n, τ, a, C, hτ₀, hτ, ha, hb, herr⟩ := hH.exists_seq_simpleHolding_tendsto_eLpNorm
  have ha₂ (m j : ℕ) (hj : j < n m) : MemLp (a m j) 2 P :=
    MemLp.of_bound ((ha m j hj).mono (ℱ.le _)).aestronglyMeasurable (C m)
      (.of_forall (hb m j hj))
  let K (m : ℕ) : ElementaryIntegrand ℱ :=
    { n := n m
      grid := fun i ↦ τ m i.val
      monotone_grid := fun i j hij ↦ (hτ m).monotoneOn (Fin.is_le i) (Fin.is_le j) hij
      height := fun i ↦ a m i.val
      measurable_height := fun i ↦ ha m i.val i.isLt
      bounded_height := fun i ↦ ⟨C m, fun ω ↦ by
        simpa [Real.norm_eq_abs] using hb m i.val i.isLt ω⟩ }
  have hK_proc (m : ℕ) : (K m).toProcess = Finance.simpleHolding (τ m) (n m) (a m) := by
    ext t ω
    rw [ElementaryIntegrand.toProcess_def, Finance.simpleHolding_def, ← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp [K, Fin.castSucc, Fin.castAdd, Fin.castLE, Fin.succ]
  have hK_int (m : ℕ) : (K m).integral W = Finance.simpleGains (τ m) (n m) (a m) W := by
    ext t ω
    rw [ElementaryIntegrand.integral_def, Finance.simpleGains_def, ← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp [K, Fin.castSucc, Fin.castAdd, Fin.castLE, Fin.succ]
  refine ⟨⟨K, hτ₀, fun m _ _ hij ↦ hτ m (Fin.is_le _) (Fin.is_le _) hij,
    fun m ↦ (K m).martingale_integral hW.martingale,
    fun m T ↦ (hK_int m) ▸ hW.memLp_simpleGains (hτ m).monotoneOn (ha m) (ha₂ m) T,
    fun T ↦ by simp_rw [hK_proc]; exact herr T, fun T ↦ ?_⟩⟩
  have hu : Tendsto (fun m ↦ (Finance.memLp_simpleHolding_predictableMeasure (ha m) (ha₂ m) T).toLp
      (Function.uncurry (Finance.simpleHolding (τ m) (n m) (a m)))) atTop
      (𝓝 ((hH.memLp_predictableMeasure T).toLp (Function.uncurry H))) := by
    rw [tendsto_iff_edist_tendsto_0]
    refine (herr T).congr fun m ↦ ?_
    rw [Lp.edist_toLp_toLp, ℱ.eLpNorm_predictableMeasure P
      ((Finance.isStronglyPredictable_simpleHolding (ha m)).sub hH.isStronglyPredictable) T 2]
    simp only [Function.uncurry_def, Pi.sub_def]
  refine (((hW.l2Integral T).continuous.tendsto _).comp hu).congr fun m ↦ ?_
  dsimp only [Function.comp_apply]
  have hmem := hW.l2Integral_simpleHolding (hτ m).monotoneOn (ha m) T
    (Finance.memLp_simpleHolding_predictableMeasure (ha m) (ha₂ m) T)
    (hW.memLp_simpleGains (hτ m).monotoneOn (ha m) (ha₂ m) T)
  rw [hmem]
  exact Lp.ext ((MemLp.coeFn_toLp _).trans
    ((EventuallyEq.of_eq (congrArg (fun f ↦ f T) (hK_int m).symm)).trans
      (MemLp.coeFn_toLp _).symm))

/-- Bounded simple holdings approximating a Brownian-integrable integrand on every finite horizon
in `L²` have elementary integrals converging in `L²(P)` to a martingale that agrees almost surely
at every time with the terminal `L²` integral `hW.l2Integral t`. -/
theorem exists_simpleHolding_martingale_approx
    (hW : IsFilteredPreBrownianReal ℱ W P) (hH : BrownianIntegrable ℱ P H) :
    ∃ (n : ℕ → ℕ) (τ : ℕ → ℕ → ℝ≥0) (a : ℕ → ℕ → Ω → ℝ) (Z : ℝ≥0 → Ω → ℝ),
      (∀ k, MonotoneOn (τ k) (Iic (n k))) ∧
      (∀ k j, j < n k → StronglyMeasurable[ℱ (τ k j)] (a k j)) ∧
      (∀ k j, j < n k → MemLp (a k j) 2 P) ∧
      (∀ T, Tendsto (fun k ↦ eLpNorm (Function.uncurry (Finance.simpleHolding (τ k) (n k) (a k)) -
        Function.uncurry H) 2 ((timeMeasure T).prod P)) atTop (𝓝 0)) ∧
      Martingale Z ℱ P ∧
      (∀ t, MemLp (Z t) 2 P) ∧
      (∀ t, Tendsto (fun k ↦ eLpNorm (Finance.simpleGains (τ k) (n k) (a k) W t - Z t) 2 P)
        atTop (𝓝 0)) ∧
      (∀ t, Z t =ᵐ[P]
        hW.l2Integral t ((hH.memLp_predictableMeasure t).toLp (Function.uncurry H))) := by
  have : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  obtain ⟨h⟩ := hW.exists_simpleHoldingApprox hH
  obtain ⟨Z, hZ, hZlim⟩ := exists_martingale_of_cauchySeq_Lp h.martingale h.memLp
    fun t ↦ (h.tendsto_l2Integral t).cauchySeq
  refine ⟨h.n, h.τ, h.a, Z, fun k ↦ (h.strictMonoOn k).monotoneOn, h.stronglyMeasurable,
    h.memLp_coeff,
    fun T ↦ by simpa only [h.simpleHolding_eq_toProcess, Function.uncurry_def, Pi.sub_def] using
      h.tendsto_holding T,
    hZ, fun t ↦ (hZlim t).1,
    fun t ↦ by simpa only [h.simpleGains_eq_integral] using (hZlim t).2,
    fun t ↦ tendstoInMeasure_ae_unique
      (tendstoInMeasure_of_tendsto_eLpNorm two_ne_zero (hZlim t).2)
      (h.tendstoInMeasure_l2Integral t)⟩

end IsFilteredPreBrownianReal

end TauCeti.Probability

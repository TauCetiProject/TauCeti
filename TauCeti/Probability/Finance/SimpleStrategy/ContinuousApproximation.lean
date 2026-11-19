/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Finance.SimpleStrategy.Basic
public import TauCeti.Probability.Process.Predictable.Basic
public import TauCeti.Probability.Process.TimeMeasure
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.LpSeminorm.Prod
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Left-endpoint approximation in expected square energy

Left-endpoint samples of a left-continuous predictable process converge in expected square energy
along arbitrary deterministic vanishing-mesh grids on a fixed finite horizon. An L² random
bound on the whole path supplies domination. This identifies the particular elementary
integrands occurring in stochastic Riemann sums, rather than merely choosing some dense
sequence of elementary integrands. No stochastic integral is assumed or constructed here.

The grids may have repeated dates and need not be nested. Left continuity is needed only almost
surely, simultaneously at positive times on the horizon; fixed-time modifications alone do not
suffice. The origin, at which a simple holding vanishes, has zero time mass. Zero horizons and
empty grids are allowed. All energies use the native finite-horizon time-product measure.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.2–§3.3.
-/

public section

noncomputable section

open MeasureTheory Set Filter
open scoped Topology NNReal

namespace TauCeti.Finance

variable {Ω : Type*} {τ : ℕ → ℝ≥0} {n : ℕ} {T t : ℝ≥0} {H : ℝ≥0 → Ω → ℝ}

/-- A left-sampled holding inherits any bound on its sampled path over the horizon. -/
theorem norm_simpleHolding_le_of_bound
    (hτ : MonotoneOn τ (Iic n)) (hzero : τ 0 = 0) (hlast : τ n = T)
    (ht : t ∈ Ioc 0 T) (ω : Ω) {C : ℝ}
    (hbound : ∀ s ∈ Icc 0 T, ‖H s ω‖ ≤ C) :
    ‖simpleHolding τ n (fun j ↦ H (τ j)) t ω‖ ≤ C := by
  have ht' : t ∈ Ioc (τ 0) (τ n) := by simpa [hzero, hlast] using ht
  obtain ⟨j, hj, htj⟩ := TauCeti.exists_lt_mem_Ioc_of_mem_Ioc ht'
  rw [simpleHolding_of_mem_Ioc hτ hj htj]
  exact hbound _ ⟨bot_le, by simpa [hlast] using hτ hj.le Set.self_mem_Iic hj.le⟩

/-- The error of a left-sampled holding is bounded by twice a bound on the whole path. -/
theorem norm_simpleHolding_sub_le_of_bound
    (hτ : MonotoneOn τ (Iic n)) (hzero : τ 0 = 0) (hlast : τ n = T)
    (ht : t ∈ Ioc 0 T) (ω : Ω) {C : ℝ}
    (hbound : ∀ s ∈ Icc 0 T, ‖H s ω‖ ≤ C) :
    ‖simpleHolding τ n (fun j ↦ H (τ j)) t ω - H t ω‖ ≤ 2 * C := by
  calc
    _ ≤ ‖simpleHolding τ n (fun j ↦ H (τ j)) t ω‖ + ‖H t ω‖ := norm_sub_le _ _
    _ ≤ C + C := add_le_add (norm_simpleHolding_le_of_bound hτ hzero hlast ht ω hbound)
      (hbound _ ⟨ht.1.le, ht.2⟩)
    _ = 2 * C := by ring

/-- Left samples converge at every positive time at which the path is continuous from the
left. Only the mesh must vanish; the partitions need not be nested or strictly increasing. -/
theorem tendsto_simpleHolding_of_continuousWithinAt
    {ι : Type*} {l : Filter ι} {N : ι → ℕ} {grid : ι → ℕ → ℝ≥0}
    (hgrid : ∀ k, MonotoneOn (grid k) (Iic (N k)))
    (hzero : ∀ k, grid k 0 = 0) (hlast : ∀ k, grid k (N k) = T)
    {δ : ι → ℝ} (hmesh : ∀ k j, j < N k →
      (grid k (j + 1) : ℝ) - grid k j ≤ δ k)
    (hδ : Tendsto δ l (𝓝 0)) (ht : t ∈ Ioc 0 T) (ω : Ω)
    (hc : ContinuousWithinAt (H · ω) (Iic t) t) :
    Tendsto (fun k ↦ simpleHolding (grid k) (N k) (fun j ↦ H (grid k j)) t ω)
      l (𝓝 (H t ω)) := by
  classical
  have ht' k : t ∈ Ioc (grid k 0) (grid k (N k)) := by simpa [hzero k, hlast k] using ht
  have hex k := TauCeti.exists_lt_mem_Ioc_of_mem_Ioc (ht' k)
  let j k := (hex k).choose
  have hj k : j k < N k := (hex k).choose_spec.1
  have htj k : t ∈ Ioc (grid k (j k)) (grid k (j k + 1)) := (hex k).choose_spec.2
  have hsample : Tendsto (fun k ↦ grid k (j k)) l (𝓝 t) := by
    apply NNReal.tendsto_coe.mp
    have hlo : Tendsto (fun k ↦ (t : ℝ) - δ k) l (𝓝 (t : ℝ)) := by
      simpa using tendsto_const_nhds.sub hδ
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlo tendsto_const_nhds
      (fun k ↦ ?_) (fun k ↦ by exact_mod_cast (htj k).1.le)
    have hm := hmesh k (j k) (hj k)
    have hu : (t : ℝ) ≤ grid k (j k + 1) := by exact_mod_cast (htj k).2
    linarith
  have hlim := hc.tendsto.comp (tendsto_nhdsWithin_iff.mpr
    ⟨hsample, .of_forall fun k ↦ (htj k).1.le⟩)
  exact hlim.congr fun k ↦ (simpleHolding_of_mem_Ioc (hgrid k) (hj k) (htj k) ω).symm

end TauCeti.Finance

namespace MeasureTheory.IsStronglyPredictable

open TauCeti.Finance TauCeti.Probability

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [SFinite P]
  {ℱ : Filtration ℝ≥0 mΩ} {H : ℝ≥0 → Ω → ℝ} {T : ℝ≥0}

/-- Under an L² path bound, left-sampled holdings and the original predictable process
have square-integrable differences on the finite time-product space. -/
theorem memLp_simpleHolding_sub_of_bound (hH : IsStronglyPredictable ℱ H)
    {τ : ℕ → ℝ≥0} {n : ℕ} (hτ : MonotoneOn τ (Iic n))
    (hzero : τ 0 = 0) (hlast : τ n = T) {C : Ω → ℝ} (hC : MemLp C 2 P)
    (hbound : ∀ᵐ ω ∂P, ∀ t ∈ Icc 0 T, ‖H t ω‖ ≤ C ω) :
    MemLp (fun p : ℝ≥0 × Ω ↦
      simpleHolding τ n (fun j ↦ H (τ j)) p.1 p.2 - H p.1 p.2) 2
      ((timeMeasure T).prod P) := by
  have hK := isStronglyPredictable_simpleHolding
    (fun j (_ : j < n) ↦ hH.stronglyAdapted (τ j))
  have hm := (hK.sub hH).mono ℱ.predictable_le_prod
  have hdom : MemLp (fun p : ℝ≥0 × Ω ↦ 2 * C p.2) 2 ((timeMeasure T).prod P) :=
    (hC.comp_snd (timeMeasure T)).const_mul 2
  apply hdom.mono' hm.aestronglyMeasurable
  have htime : ∀ᵐ t ∂timeMeasure T, t ∈ Ioc 0 T := by
    rw [timeMeasure_def]
    exact ae_restrict_mem measurableSet_Ioc
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae htime,
    Measure.quasiMeasurePreserving_snd.ae hbound] with p ht hb
  exact norm_simpleHolding_sub_le_of_bound hτ hzero hlast ht p.2 hb

/-- Left-endpoint samples converge in expected square energy for an almost surely left-continuous
predictable process dominated on the horizon by an L² random variable. This applies on raw
filtrations and to arbitrary vanishing-mesh families with a countably generated index filter.
The preceding membership theorem ensures that these are genuine finite energies. -/
theorem tendsto_integral_sq_simpleHolding_sub (hH : IsStronglyPredictable ℱ H)
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {N : ι → ℕ} {grid : ι → ℕ → ℝ≥0}
    (hgrid : ∀ k, MonotoneOn (grid k) (Iic (N k)))
    (hzero : ∀ k, grid k 0 = 0) (hlast : ∀ k, grid k (N k) = T)
    {δ : ι → ℝ} (hmesh : ∀ k j, j < N k →
      (grid k (j + 1) : ℝ) - grid k j ≤ δ k) (hδ : Tendsto δ l (𝓝 0))
    (hcont : ∀ᵐ ω ∂P, ∀ t ∈ Ioc 0 T, ContinuousWithinAt (H · ω) (Iic t) t)
    {C : Ω → ℝ} (hC : MemLp C 2 P)
    (hbound : ∀ᵐ ω ∂P, ∀ t ∈ Icc 0 T, ‖H t ω‖ ≤ C ω) :
    Tendsto (fun k ↦ ∫ p : ℝ≥0 × Ω,
      (simpleHolding (grid k) (N k) (fun j ↦ H (grid k j)) p.1 p.2 - H p.1 p.2) ^ 2
        ∂(timeMeasure T).prod P) l (𝓝 0) := by
  have htime : ∀ᵐ t ∂timeMeasure T, t ∈ Ioc 0 T := by
    rw [timeMeasure_def]
    exact ae_restrict_mem measurableSet_Ioc
  have hmem k := hH.memLp_simpleHolding_sub_of_bound
    (hgrid k) (hzero k) (hlast k) hC hbound
  have hdom : Integrable (fun p : ℝ≥0 × Ω ↦ (2 * C p.2) ^ 2) ((timeMeasure T).prod P) :=
    (((hC.comp_snd (timeMeasure T)).const_mul 2).integrable_sq)
  have hlim := tendsto_integral_filter_of_dominated_convergence (l := l)
    (f := fun _ : ℝ≥0 × Ω ↦ (0 : ℝ)) (fun p : ℝ≥0 × Ω ↦ (2 * C p.2) ^ 2)
    (.of_forall fun k ↦ (hmem k).integrable_sq.aestronglyMeasurable) ?_ hdom ?_
  · simpa using hlim
  · apply Eventually.of_forall
    intro k
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae htime,
      Measure.quasiMeasurePreserving_snd.ae hbound] with p ht hb
    have hnorm := norm_simpleHolding_sub_le_of_bound
      (hgrid k) (hzero k) (hlast k) ht p.2 hb
    simpa only [Real.norm_eq_abs, abs_pow, sq_abs] using
      pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  · filter_upwards [Measure.quasiMeasurePreserving_fst.ae htime,
      Measure.quasiMeasurePreserving_snd.ae hcont] with p ht hc
    have h := tendsto_simpleHolding_of_continuousWithinAt
      hgrid hzero hlast hmesh hδ ht p.2 (hc p.1 ht)
    simpa using (h.sub (tendsto_const_nhds (x := H p.1 p.2) (f := l))).pow 2

/-- Native L²-seminorm convergence of the left-endpoint integrands. This is the form used
with the Itô isometry to identify stochastic Riemann-sum limits. -/
theorem tendsto_eLpNorm_simpleHolding_sub (hH : IsStronglyPredictable ℱ H)
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {N : ι → ℕ} {grid : ι → ℕ → ℝ≥0}
    (hgrid : ∀ k, MonotoneOn (grid k) (Iic (N k)))
    (hzero : ∀ k, grid k 0 = 0) (hlast : ∀ k, grid k (N k) = T)
    {δ : ι → ℝ} (hmesh : ∀ k j, j < N k →
      (grid k (j + 1) : ℝ) - grid k j ≤ δ k) (hδ : Tendsto δ l (𝓝 0))
    (hcont : ∀ᵐ ω ∂P, ∀ t ∈ Ioc 0 T, ContinuousWithinAt (H · ω) (Iic t) t)
    {C : Ω → ℝ} (hC : MemLp C 2 P)
    (hbound : ∀ᵐ ω ∂P, ∀ t ∈ Icc 0 T, ‖H t ω‖ ≤ C ω) :
    Tendsto (fun k ↦ eLpNorm (fun p : ℝ≥0 × Ω ↦
      simpleHolding (grid k) (N k) (fun j ↦ H (grid k j)) p.1 p.2 - H p.1 p.2)
        2 ((timeMeasure T).prod P)) l (𝓝 0) := by
  have h := hH.tendsto_integral_sq_simpleHolding_sub hgrid hzero hlast hmesh hδ hcont hC hbound
  have hlim := ENNReal.continuous_ofReal.continuousAt.tendsto.comp h.sqrt
  simp only [Real.sqrt_zero, ENNReal.ofReal_zero] at hlim
  convert hlim using 1
  ext k
  have hm := hH.memLp_simpleHolding_sub_of_bound (hgrid k) (hzero k) (hlast k) hC hbound
  rw [hm.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top]
  simp [Real.sqrt_eq_rpow, Real.norm_eq_abs]

end MeasureTheory.IsStronglyPredictable

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
public import TauCeti.MeasureTheory.OptimalTransport.Cost.WeakConvergence
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.KantorovichRubinstein
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Bounded-Lipschitz transport and weak convergence

Transport with cost `min (dist x y) (2 * R)`, for `R > 0`, detects weak convergence of
probability measures without a moment assumption. On Polish spaces, bounded-Lipschitz
Kantorovich--Rubinstein duality identifies this cost with the uniform integral discrepancy
over all `1`-Lipschitz real functions bounded in absolute value by `R`.

The comparison theorem bounds the Lévy--Prokhorov extended distance by `ε` whenever
the truncated transport cost is below `ε²` and `ε` does not exceed the cap. Together with
the convergence theorem for bounded costs vanishing near the diagonal, it proves that
truncated transport, uniform bounded-Lipschitz testing, and Mathlib's weak topology give
the same convergence. The cap must be positive: a zero cap discards all information.

## Main statements

* `TauCeti.levyProkhorovEDist_le_of_transportCost_truncated_dist_lt_mul_self`
* `TauCeti.tendsto_probabilityMeasure_iff_transportCost_truncated_dist`
* `TauCeti.tendsto_probabilityMeasure_iff_iSup_abs_integral_sub_integral_boundedLipschitz`

## References

* R. M. Dudley, *Real Analysis and Probability*, Cambridge University Press, 2002,
  Section 11.3 (bounded-Lipschitz metrics and weak convergence).
* C. Villani, *Optimal Transport: Old and New*, Springer, 2009, Particular Case 5.16
  (Kantorovich--Rubinstein duality for a truncated ground metric).
-/

public section

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace TauCeti

variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]

/-- A small truncated transport cost bounds the Lévy--Prokhorov extended distance.
The comparison radius must not exceed the truncation cap. No separability or moment
assumption is needed. -/
theorem levyProkhorovEDist_le_of_transportCost_truncated_dist_lt_mul_self
    (hd : Measurable fun z : X × X ↦ dist z.1 z.2)
    {μ ν : Measure X} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {R : ℝ}
    {ε : ℝ≥0∞} (hεR : ε ≤ ENNReal.ofReal (2 * R))
    (h : transportCost (fun z : X × X ↦ ENNReal.ofReal (min (dist z.1 z.2) (2 * R)))
      μ ν < ε * ε) :
    levyProkhorovEDist μ ν ≤ ε := by
  have hε0 : ε ≠ 0 := by rintro rfl; simp at h
  have hεtop : ε ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hεR
  obtain ⟨π, hπ, hπε⟩ := transportCost_lt_iff.1 h
  have hc : Measurable fun z : X × X ↦
      ENNReal.ofReal (min (dist z.1 z.2) (2 * R)) :=
    (hd.min measurable_const).ennreal_ofReal
  have hbad : π {z : X × X | ε ≤ edist z.1 z.2} ≤ ε := by
    have heq : {z : X × X | ε ≤ edist z.1 z.2} =
        {z | ε ≤ ENNReal.ofReal (min (dist z.1 z.2) (2 * R))} := by
      ext z
      simp only [ENNReal.ofReal_min, edist_dist, le_min_iff, and_iff_left hεR]
    rw [heq]
    exact (meas_ge_le_lintegral_div hc.aemeasurable hε0 hεtop).trans
      ((ENNReal.div_lt_iff (Or.inl hε0) (Or.inl hεtop)).2 hπε).le
  refine levyProkhorovEDist_le_of_forall_le μ ν ε fun δ B hεδ hδtop hB ↦ ?_
  refine (hπ.measure_le_of_measure_setOf_le hbad hB).trans (add_le_add ?_ hεδ.le)
  apply measure_mono
  rintro y ⟨x, hx, hxy⟩
  rw [Metric.mem_thickening_iff_exists_edist_lt]
  exact ⟨x, hx, by simpa [edist_comm, ENNReal.ofReal_toReal hδtop.ne] using hxy.trans hεδ⟩

section Convergence

variable [TopologicalSpace.SeparableSpace X]
  {ι : Type*} {l : Filter ι} {μs : ι → ProbabilityMeasure X} {μ : ProbabilityMeasure X}
  {R : ℝ}

/-- Weak convergence is equivalent to convergence to zero of transport with any fixed
positive cap on the ground distance. This holds for arbitrary filters, without completeness,
separation of points, or finite moments. -/
theorem tendsto_probabilityMeasure_iff_transportCost_truncated_dist (hR : 0 < R) :
    Tendsto μs l (𝓝 μ) ↔
      Tendsto (fun i ↦ transportCost
        (fun z : X × X ↦ ENNReal.ofReal (min (dist z.1 z.2) (2 * R)))
        (μs i : Measure X) (μ : Measure X)) l (𝓝 0) := by
  constructor
  · refine tendsto_transportCost_of_tendsto_probabilityMeasure ENNReal.ofReal_ne_top
      (fun z ↦ ENNReal.ofReal_le_ofReal (min_le_right _ _)) ?_
    intro ε hε
    refine ⟨ε, hε, fun x y hxy ↦ ?_⟩
    exact (ENNReal.ofReal_le_ofReal (min_le_left _ _)).trans (by simpa [edist_dist] using hxy.le)
  · intro h
    have hLP : Tendsto (fun i ↦ LevyProkhorov.ofMeasure (μs i)) l
        (𝓝 (LevyProkhorov.ofMeasure μ)) := by
      refine Metric.tendsto_nhds.2 fun ε hε ↦ ?_
      let δ : ℝ := min (ε / 2) R
      have hδ : 0 < δ := lt_min (half_pos hε) hR
      have hδR : ENNReal.ofReal δ ≤ ENNReal.ofReal (2 * R) :=
        ENNReal.ofReal_le_ofReal (by dsimp [δ]; linarith [min_le_right (ε / 2) R])
      have hδsq : 0 < ENNReal.ofReal δ * ENNReal.ofReal δ :=
        ENNReal.mul_pos (ENNReal.ofReal_pos.2 hδ).ne' (ENNReal.ofReal_pos.2 hδ).ne'
      filter_upwards [h.eventually (gt_mem_nhds hδsq)] with i hi
      have hbound := levyProkhorovEDist_le_of_transportCost_truncated_dist_lt_mul_self
        measurable_dist hδR hi
      rw [LevyProkhorov.dist_probabilityMeasure_def, levyProkhorovDist]
      refine (ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound).trans_lt ?_
      rw [ENNReal.toReal_ofReal hδ.le]
      exact (min_le_left (ε / 2) R).trans_lt (half_lt_self hε)
    exact (LevyProkhorov.continuous_toMeasure_probabilityMeasure.tendsto _).comp hLP

end Convergence

section Polish

variable [PolishSpace X] [BorelSpace X]
  {ι : Type*} {l : Filter ι} {μs : ι → ProbabilityMeasure X} {μ : ProbabilityMeasure X}
  {R : ℝ}

/-- On a Polish space, weak convergence is equivalent to uniform convergence of the
integrals over all `1`-Lipschitz real test functions bounded in absolute value by a fixed
positive `R`. The supremum is taken in `ℝ≥0∞`; no moments are assumed. -/
theorem tendsto_probabilityMeasure_iff_iSup_abs_integral_sub_integral_boundedLipschitz
    (hR : 0 < R) :
    Tendsto μs l (𝓝 μ) ↔
      Tendsto (fun i ↦ ⨆ (f : X → ℝ) (_ : LipschitzWith 1 f) (_ : ∀ x, ‖f x‖ ≤ R),
        ENNReal.ofReal |∫ x, f x ∂(μs i : Measure X) - ∫ x, f x ∂(μ : Measure X)|)
        l (𝓝 0) := by
  have heq (i : ι) := transportCost_truncated_dist_eq_iSup_abs
    (μ := (μs i : Measure X)) (ν := (μ : Measure X)) hR.le (by simp)
  simp_rw [← heq]
  exact tendsto_probabilityMeasure_iff_transportCost_truncated_dist hR

end Polish

end TauCeti

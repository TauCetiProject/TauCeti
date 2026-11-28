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
import TauCeti.Analysis.Normed.Field.Lipschitz

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

* `TauCeti.ofReal_abs_integral_sub_integral_le_transportCost_truncated_dist` and
  `TauCeti.abs_integral_sub_integral_le_add_one_mul_toReal_transportCost_truncated_dist`
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
open scoped ENNReal NNReal Topology

namespace TauCeti

variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]

/-- Absolute-value form of bounded-Lipschitz weak duality: for finite measures `μ` and `ν`, the
difference of expectations of any `1`-Lipschitz function bounded in norm by `R` is bounded by the
transport cost with ground distance truncated at `2 * R`. -/
theorem ofReal_abs_integral_sub_integral_le_transportCost_truncated_dist
    {μ ν : Measure X} [IsFiniteMeasure μ] [IsFiniteMeasure ν] {R : ℝ} {f : X → ℝ}
    (hf : LipschitzWith 1 f) (hfb : ∀ x, ‖f x‖ ≤ R) :
    ENNReal.ofReal |∫ x, f x ∂μ - ∫ x, f x ∂ν| ≤
      transportCost (fun z : X × X ↦ ENNReal.ofReal (min (dist z.1 z.2) (2 * R))) μ ν := by
  rcases le_total (∫ x, f x ∂ν) (∫ x, f x ∂μ) with h | h
  · rw [abs_of_nonneg (sub_nonneg.2 h)]
    exact ofReal_integral_sub_integral_le_transportCost_truncated_dist hf hfb
  · rw [abs_of_nonpos (sub_nonpos.2 h), neg_sub]
    have hneg := ofReal_integral_sub_integral_le_transportCost_truncated_dist
      (μ := μ) (ν := ν) hf.neg (fun x ↦ by simpa using hfb x)
    simpa only [Pi.neg_apply, integral_neg, sub_neg_eq_add, neg_add_eq_sub] using hneg

/-- Rescaled real-valued bounded-Lipschitz inequality: for any `K`-Lipschitz real function `f`
within `R` of a constant `a` and any two probability measures `μ` and `ν`, `|∫ f dμ - ∫ f dν|` is
bounded by `(K + 1)` times the truncated optimal transport cost with cap `2 * R / (K + 1)`. -/
theorem abs_integral_sub_integral_le_add_one_mul_toReal_transportCost_truncated_dist
    {μ ν : Measure X} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {K : ℝ≥0} {a R : ℝ} {f : X → ℝ} (hf : LipschitzWith K f) (hfb : ∀ x, ‖f x - a‖ ≤ R) :
    |∫ x, f x ∂μ - ∫ x, f x ∂ν| ≤
      (K + 1 : ℝ) * (transportCost (fun z : X × X ↦
        ENNReal.ofReal (min (dist z.1 z.2) (2 * R / (K + 1)))) μ ν).toReal := by
  set K' : ℝ≥0 := K + 1
  have hK'0 : K' ≠ 0 := by simp [K']
  have hK'pos : (0 : ℝ) < K' := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hK'0)
  set R' : ℝ := R / K'
  have h2R' : 2 * R' = 2 * R / (K + 1 : ℝ) := by
    simp [R', K', NNReal.coe_add, NNReal.coe_one, mul_div_assoc]
  have htfin : transportCost (fun z : X × X ↦ ENNReal.ofReal (min (dist z.1 z.2) (2 * R')))
      μ ν ≠ ∞ :=
    ne_top_of_le_ne_top (ne_top_of_le_ne_top (b := ENNReal.ofReal (2 * R')) ENNReal.ofReal_ne_top <|
      (lintegral_mono fun z : X × X ↦ ENNReal.ofReal_le_ofReal (min_le_right _ _)).trans_eq
        (by simp)) (transportCost_le_lintegral (isCoupling_prod μ ν) _)
  have hKK' : K ≤ K' := le_self_add
  have hnorm : ‖(K' : ℝ)‖₊ = K' := NNReal.eq (Real.norm_of_nonneg K'.coe_nonneg)
  have hgL : LipschitzWith 1 (fun x ↦ (f x - a) / K') := by
    simpa only [add_zero, hnorm, div_self hK'0] using
      (((hf.weaken hKK').sub (LipschitzWith.const a)).div_const (K' : ℝ))
  have hgB : ∀ x, ‖(f x - a) / K'‖ ≤ R' := fun x ↦ by
    rw [norm_div, Real.norm_of_nonneg K'.coe_nonneg]
    exact div_le_div_of_nonneg_right (hfb x) hK'pos.le
  have hfi (ρ : Measure X) [IsFiniteMeasure ρ] : Integrable f ρ := by
    have hsub : Integrable (fun x ↦ f x - a) ρ :=
      .of_bound (hf.continuous.sub continuous_const).aestronglyMeasurable R (ae_of_all _ hfb)
    exact (hsub.add (integrable_const a)).congr (ae_of_all _ fun x ↦ sub_add_cancel (f x) a)
  have hshift : |∫ x, f x ∂μ - ∫ x, f x ∂ν| =
      (K' : ℝ) * |∫ x, (f x - a) / K' ∂μ - ∫ x, (f x - a) / K' ∂ν| := by
    have heq : ∫ x, f x ∂μ - ∫ x, f x ∂ν =
        (K' : ℝ) * (∫ x, (f x - a) / K' ∂μ - ∫ x, (f x - a) / K' ∂ν) := by
      rw [integral_div, integral_div, integral_sub (hfi μ) (integrable_const _),
        integral_sub (hfi ν) (integrable_const _)]
      simp only [integral_const, probReal_univ, one_smul]
      field_simp
      ring
    rw [heq, abs_mul, abs_of_pos hK'pos]
  have htr := (ENNReal.ofReal_le_iff_le_toReal htfin).1
    (ofReal_abs_integral_sub_integral_le_transportCost_truncated_dist hgL hgB)
  rw [hshift, ← h2R']
  simpa only [K', NNReal.coe_add, NNReal.coe_one] using mul_le_mul_of_nonneg_left htr hK'pos.le

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
    (μ := (μs i : Measure X)) (ν := (μ : Measure X)) (R := R) (by simp)
  simp_rw [← heq]
  exact tendsto_probabilityMeasure_iff_transportCost_truncated_dist hR

end Polish

end TauCeti

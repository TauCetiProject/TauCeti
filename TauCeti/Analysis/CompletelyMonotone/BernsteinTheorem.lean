/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.CompletelyMonotone.LaplaceRepresentation
public import Mathlib.MeasureTheory.Measure.FiniteMeasureExt
public import Mathlib.MeasureTheory.Measure.TightNormed
public import Mathlib.RingTheory.Adjoin.Polynomial.Basic
public import TauCeti.MeasureTheory.Measure.Prokhorov

/-!
# Hausdorff--Bernstein--Widder theorem

This file proves the finite-measure form of the Hausdorff--Bernstein--Widder theorem for
completely monotone functions on the closed half-line. It imports the Laplace-transform helper
API and proves the Chafaï extraction, uniqueness, and headline existence and unique-existence
statements.

## Main declarations

* `TauCeti.exists_representsLaplace_of_isCompletelyMonotone`
* `TauCeti.exists_representsLaplace_of_isClosedCompletelyMonotone`
* `TauCeti.laplaceTransform_ext`, `TauCeti.laplaceTransform_unique`
* `TauCeti.hausdorff_bernstein_widder`, `TauCeti.hausdorff_bernstein_widder_unique`
* `TauCeti.existsUnique_representsLaplace_of_isCompletelyMonotone`

## References

The finite-measure representation is the Hausdorff--Bernstein--Widder theorem, after
S. Bernstein (1928) and D. V. Widder, *The Laplace Transform*, Chapter IV. The extraction
argument follows the Bernstein-kernel proof described by D. Chafaï (2013). The Lean proofs of
`chafai_identity` and the Bernstein-to-Laplace kernel convergence were adapted from Tau Ceti's
Hille--Yosida formalization in `HilleYosida/BernsteinChafai.lean` and completed here; in
particular, the `chafai_identity` that was `sorry` there is now proved.
-/

public section

open MeasureTheory Set Filter
open scoped BoundedContinuousFunction ContDiff ENNReal NNReal Pointwise Polynomial Topology

namespace TauCeti

/-! ## Hard direction: extraction from the Chafaï measures -/

/-- A finite family of finite measures is tight. -/
private lemma isTightMeasureSet_range_finite
    {ι : Type*} [Finite ι] (μ : ι → Measure ℝ≥0)
    (hfin : ∀ i, IsFiniteMeasure (μ i)) :
    IsTightMeasureSet (Set.range μ) := by
  classical
  letI := Fintype.ofFinite ι
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  have hchoose : ∀ i, ∃ K : Set ℝ≥0, IsCompact K ∧ (μ i) Kᶜ ≤ ε := by
    intro i
    haveI : IsFiniteMeasure (μ i) := hfin i
    have htight : IsTightMeasureSet ({μ i} : Set (Measure ℝ≥0)) :=
      isTightMeasureSet_singleton
    obtain ⟨K, hKc, hKtail⟩ :=
      isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp htight ε hε
    exact ⟨K, hKc, hKtail (μ i) (by simp)⟩
  choose K hK_comp hK_tail using hchoose
  refine ⟨⋃ i, K i, isCompact_iUnion hK_comp, ?_⟩
  intro ν hν
  rcases hν with ⟨i, rfl⟩
  exact (measure_mono (compl_subset_compl.mpr (subset_iUnion K i))).trans (hK_tail i)

/-- A Laplace-representing measure for a positive shift has exponentially controlled tails.

The estimate uses Markov's inequality on the bounded coordinate
`p ↦ 1 - exp (-x * p)`. It is the tightness input for shifting the existing strong Chafaï
existence theorem back to the closed-half-line theorem. -/
private lemma shiftedMeasure_closedBall_compl_le
    {f : ℝ → ℝ} {μ : Measure ℝ≥0} [IsFiniteMeasure μ]
    {δ x R : ℝ} (hμ : RepresentsLaplace (fun t : ℝ => f (t + δ)) μ)
    (hx : 0 < x) (hR : 0 < R) :
    μ (Metric.closedBall (0 : ℝ≥0) R)ᶜ ≤
      ENNReal.ofReal ((f δ - f (x + δ)) / (1 - Real.exp (-(x * R)))) := by
  let coord : ℝ≥0 → ENNReal := fun p => ENNReal.ofReal (1 - Real.exp (-(x * (p : ℝ))))
  let c : ℝ := 1 - Real.exp (-(x * R))
  have hc_pos : 0 < c := by
    have hxR : 0 < x * R := mul_pos hx hR
    have hexp_lt : Real.exp (-(x * R)) < 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.mpr (by linarith)
    dsimp [c]
    linarith
  have hc_ne_zero : ENNReal.ofReal c ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hc_pos
  have hc_ne_top : ENNReal.ofReal c ≠ (∞ : ENNReal) := ENNReal.ofReal_ne_top
  have hcoord_meas : AEMeasurable coord μ :=
    (ENNReal.measurable_ofReal.comp
      (by fun_prop : Measurable fun p : ℝ≥0 => 1 - Real.exp (-(x * (p : ℝ)))))
        |>.aemeasurable
  have hmarkov : μ {p : ℝ≥0 | ENNReal.ofReal c ≤ coord p} ≤
      (∫⁻ p : ℝ≥0, coord p ∂μ) / ENNReal.ofReal c :=
    meas_ge_le_lintegral_div hcoord_meas hc_ne_zero hc_ne_top
  have hsubset : (Metric.closedBall (0 : ℝ≥0) R)ᶜ ⊆
      {p : ℝ≥0 | ENNReal.ofReal c ≤ coord p} := by
    intro p hp
    have hpdist : R < dist p (0 : ℝ≥0) := by
      simpa [Metric.mem_closedBall, not_le] using hp
    have hdist : dist p (0 : ℝ≥0) = (p : ℝ) := by
      simp [NNReal.dist_eq]
    have hRp : R ≤ (p : ℝ) := by linarith
    have hxp : x * R ≤ x * (p : ℝ) := mul_le_mul_of_nonneg_left hRp hx.le
    have hexp_le : Real.exp (-(x * (p : ℝ))) ≤ Real.exp (-(x * R)) :=
      Real.exp_le_exp.mpr (neg_le_neg hxp)
    have hreal : c ≤ 1 - Real.exp (-(x * (p : ℝ))) := by
      dsimp [c]
      linarith
    exact ENNReal.ofReal_le_ofReal hreal
  have hlintegral :
      ∫⁻ p : ℝ≥0, coord p ∂μ = ENNReal.ofReal (f δ - f (x + δ)) := by
    have h_one : Integrable (fun _ : ℝ≥0 => (1 : ℝ)) μ := integrable_const 1
    have h_exp : Integrable (fun p : ℝ≥0 => Real.exp (-(x * (p : ℝ)))) μ :=
      integrable_laplaceKernel_of_nonneg μ hx.le
    have h_nonneg : 0 ≤ᵐ[μ] fun p : ℝ≥0 => 1 - Real.exp (-(x * (p : ℝ))) := by
      refine Filter.Eventually.of_forall fun p => ?_
      have hxp_nonneg : 0 ≤ x * (p : ℝ) := mul_nonneg hx.le p.2
      have hexp_le : Real.exp (-(x * (p : ℝ))) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        exact neg_nonpos.mpr hxp_nonneg
      exact sub_nonneg.mpr hexp_le
    have hint : Integrable (fun p : ℝ≥0 => 1 - Real.exp (-(x * (p : ℝ)))) μ :=
      h_one.sub h_exp
    have h_int :
        ∫ p : ℝ≥0, (1 - Real.exp (-(x * (p : ℝ)))) ∂μ = f δ - f (x + δ) := by
      calc
        ∫ p : ℝ≥0, (1 - Real.exp (-(x * (p : ℝ)))) ∂μ
            = (∫ _p : ℝ≥0, (1 : ℝ) ∂μ) -
                ∫ p : ℝ≥0, Real.exp (-(x * (p : ℝ))) ∂μ := by
              rw [integral_sub h_one h_exp]
        _ = μ.real univ - laplaceTransform μ x := by
              simp [laplaceTransform]
        _ = f δ - f (x + δ) := by
              have h0 := hμ.eq_laplaceTransform (t := 0) le_rfl
              have hxrep := hμ.eq_laplaceTransform (t := x) hx.le
              have h0' : f δ = μ.real univ := by
                simpa [laplaceTransform_zero] using h0
              rw [← h0', ← hxrep]
    calc
      ∫⁻ p : ℝ≥0, coord p ∂μ
          = ∫⁻ p : ℝ≥0, ENNReal.ofReal (1 - Real.exp (-(x * (p : ℝ)))) ∂μ := rfl
      _ = ENNReal.ofReal
            (∫ p : ℝ≥0, (1 - Real.exp (-(x * (p : ℝ)))) ∂μ) := by
            rw [ofReal_integral_eq_lintegral_ofReal hint h_nonneg]
      _ = ENNReal.ofReal (f δ - f (x + δ)) := by rw [h_int]
  calc
    μ (Metric.closedBall (0 : ℝ≥0) R)ᶜ
        ≤ μ {p : ℝ≥0 | ENNReal.ofReal c ≤ coord p} := measure_mono hsubset
    _ ≤ (∫⁻ p : ℝ≥0, coord p ∂μ) / ENNReal.ofReal c := hmarkov
    _ = ENNReal.ofReal (f δ - f (x + δ)) / ENNReal.ofReal c := by rw [hlintegral]
    _ = ENNReal.ofReal ((f δ - f (x + δ)) / c) := by
          rw [ENNReal.ofReal_div_of_pos hc_pos]

private lemma chafaiRescaled_closedBall_compl_le
    {f : ℝ → ℝ} (hcm : IsCompletelyMonotone f) {r : ℝ} (hr : 0 < r) (n : ℕ) :
    (chafaiRescaled f n) (Metric.closedBall (0 : ℝ≥0) r)ᶜ ≤
      ENNReal.ofReal (-derivWithin f (Ici 0) 0 / r) := by
  let coord : ℝ≥0 → ENNReal := fun p => ENNReal.ofReal (p : ℝ)
  have hcoord_meas : AEMeasurable coord (chafaiRescaled f n) :=
    (ENNReal.measurable_ofReal.comp (by fun_prop : Measurable fun p : ℝ≥0 => (p : ℝ)))
      |>.aemeasurable
  have hε0 : ENNReal.ofReal r ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hr
  have hεtop : ENNReal.ofReal r ≠ (∞ : ENNReal) := ENNReal.ofReal_ne_top
  have hmarkov : (chafaiRescaled f n) {p : ℝ≥0 | ENNReal.ofReal r ≤ coord p} ≤
      (∫⁻ p : ℝ≥0, coord p ∂(chafaiRescaled f n)) / ENNReal.ofReal r :=
    meas_ge_le_lintegral_div hcoord_meas hε0 hεtop
  have hsubset :
      (Metric.closedBall (0 : ℝ≥0) r)ᶜ ⊆ {p : ℝ≥0 | ENNReal.ofReal r ≤ coord p} := by
    intro p hp
    have hpdist : r < dist p (0 : ℝ≥0) := by
      simpa [Metric.mem_closedBall, not_le] using hp
    have hdist : dist p (0 : ℝ≥0) = (p : ℝ) := by
      simp [NNReal.dist_eq]
    have hle : r ≤ (p : ℝ) := by linarith
    exact ENNReal.ofReal_le_ofReal hle
  calc
    (chafaiRescaled f n) (Metric.closedBall (0 : ℝ≥0) r)ᶜ
        ≤ (chafaiRescaled f n) {p : ℝ≥0 | ENNReal.ofReal r ≤ coord p} :=
          measure_mono hsubset
    _ ≤ (∫⁻ p : ℝ≥0, coord p ∂(chafaiRescaled f n)) / ENNReal.ofReal r := hmarkov
    _ ≤ ENNReal.ofReal (-derivWithin f (Ici 0) 0) / ENNReal.ofReal r :=
          ENNReal.div_le_div_right (chafaiRescaled_lintegral_coe_le f hcm n) _
    _ = ENNReal.ofReal (-derivWithin f (Ici 0) 0 / r) := by
          rw [ENNReal.ofReal_div_of_pos hr]

/-- Completely monotone functions give a tight family of rescaled Chafaï measures.

The proof uses the Chafaï first-moment bound from `BernsteinMeasures` and Markov's inequality.
Since the measure space is `ℝ≥0` rather than a normed additive group, it applies Mathlib's
closed-ball tightness criterion. -/
private theorem chafaiRescaled_tight {f : ℝ → ℝ} (hcm : IsCompletelyMonotone f) :
    IsTightMeasureSet (Set.range (chafaiRescaled f)) := by
  refine isTightMeasureSet_of_tendsto_measure_compl_closedBall
    (S := Set.range (chafaiRescaled f)) (x := (0 : ℝ≥0)) ?_
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hreal : Tendsto (fun r : ℝ => -derivWithin f (Ici 0) 0 / r) atTop (nhds 0) :=
    Filter.Tendsto.const_div_atTop tendsto_id _
  have henn : Tendsto (fun r : ℝ => ENNReal.ofReal (-derivWithin f (Ici 0) 0 / r))
      atTop (nhds (0 : ENNReal)) := by
    simpa using ENNReal.tendsto_ofReal hreal
  have hsmall := (ENNReal.tendsto_nhds_zero.mp henn) ε hε
  filter_upwards [eventually_gt_atTop (0 : ℝ), hsmall] with r hr hsmallr
  have hbound :
      (⨆ μ ∈ Set.range (chafaiRescaled f), μ (Metric.closedBall (0 : ℝ≥0) r)ᶜ) ≤
        ENNReal.ofReal (-derivWithin f (Ici 0) 0 / r) := by
    rw [iSup₂_le_iff]
    intro μ hμ
    rcases hμ with ⟨n, rfl⟩
    exact chafaiRescaled_closedBall_compl_le hcm hr n
  exact hbound.trans hsmallr

/-- Analytic Chafaï convergence in its correct nonconstant-part form.

If `f(t) → L` at infinity, the Chafaï densities have total mass `f 0 - L`; their Laplace
integrals should converge to `f t - L`. The extraction proof below adds the missing atom
`L δ₀`, whose Laplace transform is the constant `L`. -/
private def ChafaiRescaledLaplaceConvergenceToNonconstantPart (f : ℝ → ℝ) : Prop :=
  ∃ L : ℝ, Tendsto f atTop (nhds L) ∧ 0 ≤ L ∧
    ∀ {l : Filter ℕ}, l ≤ atTop → ∀ {t : ℝ}, 0 ≤ t →
      Tendsto (fun n => ∫ p, Real.exp (-(t * (p : ℝ))) ∂(chafaiRescaled f n)) l
        (nhds (f t - L))

/-- Bernstein-kernel approximation step for the Chafaï measures.

This is the analytic core behind
`ChafaiRescaledLaplaceConvergenceToNonconstantPart`: prove that the Bernstein kernels
reconstruct the nonconstant part `f t - L`, and that replacing those kernels by the Laplace
kernels costs `o(1)` against the varying rescaled Chafaï measures. -/
private def ChafaiRescaledBernsteinApproximationToNonconstantPart (f : ℝ → ℝ) : Prop :=
  ∃ L : ℝ, Tendsto f atTop (nhds L) ∧ 0 ≤ L ∧
    ∀ {t : ℝ}, (ht : 0 ≤ t) →
      Tendsto (fun n =>
        ∫ p, (bernsteinKernelBoundedContinuous n ht) p ∂(chafaiRescaled f n)) atTop
          (nhds (f t - L)) ∧
      Tendsto (fun n =>
        ∫ p, (Real.exp (-(t * (p : ℝ))) - (bernsteinKernelBoundedContinuous n ht) p)
          ∂(chafaiRescaled f n)) atTop (nhds 0)

/-- The Chafaï Bernstein-kernel approximation reconstructs the nonconstant part of a completely
monotone function, and the Bernstein kernels may be replaced by Laplace kernels at `o(1)` cost. -/
private theorem chafaiRescaledBernsteinApproximationToNonconstantPart
    {f : ℝ → ℝ} (hcm : IsCompletelyMonotone f) :
    ChafaiRescaledBernsteinApproximationToNonconstantPart f := by
  obtain ⟨L, hL, hL_nonneg, hfinite⟩ := chafaiRescaled_finite_mass f hcm
  refine ⟨L, hL, hL_nonneg, fun {t} ht => ?_⟩
  constructor
  · have hconst : ∀ᶠ n in atTop,
        (∫ p, (bernsteinKernelBoundedContinuous n ht) p ∂(chafaiRescaled f n)) =
          f t - L := by
      filter_upwards [eventually_ge_atTop 2] with n hn
      simpa using
        chafaiRescaled_integral_bernsteinKernel_eq_sub_tendsto_atTop f hcm n hn t ht L hL
    exact Tendsto.congr' (EventuallyEq.symm hconst) tendsto_const_nhds
  · have hkernel :
        Tendsto (fun n => ∫ p : ℝ≥0,
          (bernsteinKernel n t (p : ℝ) - Real.exp (-(t * (p : ℝ))))
            ∂(chafaiRescaled f n)) atTop (nhds 0) :=
      integral_bernsteinKernel_sub_laplaceKernel_tendsto_zero_of_mass_bound
        (σ := chafaiRescaled f) (C := f 0 - L)
        (Filter.Eventually.of_forall (fun n => (hfinite n).2)) t ht
    have hneg :
        Tendsto (fun n => -∫ p : ℝ≥0,
          (bernsteinKernel n t (p : ℝ) - Real.exp (-(t * (p : ℝ))))
            ∂(chafaiRescaled f n)) atTop (nhds 0) := by
      simpa using hkernel.neg
    refine Tendsto.congr' ?_ hneg
    filter_upwards with n
    letI := (hfinite n).1
    have h_exp : Integrable (fun p : ℝ≥0 => Real.exp (-(t * (p : ℝ))))
        (chafaiRescaled f n) :=
      integrable_laplaceKernel_of_nonneg _ ht
    have h_bernstein : Integrable (fun p : ℝ≥0 =>
        (bernsteinKernelBoundedContinuous n ht) p) (chafaiRescaled f n) :=
      (bernsteinKernelBoundedContinuous n ht).integrable (chafaiRescaled f n)
    calc
      -∫ p : ℝ≥0,
          (bernsteinKernel n t (p : ℝ) - Real.exp (-(t * (p : ℝ))))
            ∂(chafaiRescaled f n)
          = ∫ p : ℝ≥0,
              -(bernsteinKernel n t (p : ℝ) - Real.exp (-(t * (p : ℝ))))
                ∂(chafaiRescaled f n) := by
            simpa using (integral_neg
              (f := fun p : ℝ≥0 =>
                bernsteinKernel n t (p : ℝ) - Real.exp (-(t * (p : ℝ))))
              (μ := chafaiRescaled f n)).symm
      _ = ∫ p : ℝ≥0,
          (Real.exp (-(t * (p : ℝ))) - (bernsteinKernelBoundedContinuous n ht) p)
            ∂(chafaiRescaled f n) := by
            refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
            simp

/-- The filter-general Chafaï Laplace convergence follows formally from the at-top
Bernstein-kernel approximation step.

All substantive analysis is isolated in
`ChafaiRescaledBernsteinApproximationToNonconstantPart`: after that, this proof only splits the
Laplace kernel as the Bernstein kernel plus the replacement error, and weakens `atTop` to any
smaller filter. -/
private theorem chafaiRescaledLaplaceConvergenceToNonconstantPart_of_bernsteinApprox
    {f : ℝ → ℝ} (hcm : IsCompletelyMonotone f)
    (happrox : ChafaiRescaledBernsteinApproximationToNonconstantPart f) :
    ChafaiRescaledLaplaceConvergenceToNonconstantPart f := by
  obtain ⟨L, hL, hL_nonneg, happrox⟩ := happrox
  obtain ⟨_L₀, _hL₀, _hL₀_nonneg, hfinite⟩ := chafaiRescaled_finite_mass f hcm
  refine ⟨L, hL, hL_nonneg, fun {l} hl {t} ht => ?_⟩
  obtain ⟨hbernstein, herr⟩ := happrox ht
  let laplacePart := fun n : ℕ =>
    ∫ p, Real.exp (-(t * (p : ℝ))) ∂(chafaiRescaled f n)
  let bernsteinPart := fun n : ℕ =>
    ∫ p, (bernsteinKernelBoundedContinuous n ht) p ∂(chafaiRescaled f n)
  let errorPart := fun n : ℕ =>
    ∫ p, (Real.exp (-(t * (p : ℝ))) - (bernsteinKernelBoundedContinuous n ht) p)
      ∂(chafaiRescaled f n)
  have hsplit : ∀ n, laplacePart n = bernsteinPart n + errorPart n := by
    intro n
    letI := (hfinite n).1
    have h_exp : Integrable (fun p : ℝ≥0 => Real.exp (-(t * (p : ℝ))))
        (chafaiRescaled f n) :=
      integrable_laplaceKernel_of_nonneg _ ht
    have h_bernstein : Integrable (fun p : ℝ≥0 => (bernsteinKernelBoundedContinuous n ht) p)
        (chafaiRescaled f n) :=
      (bernsteinKernelBoundedContinuous n ht).integrable (chafaiRescaled f n)
    have h_error : Integrable (fun p : ℝ≥0 =>
        Real.exp (-(t * (p : ℝ))) - (bernsteinKernelBoundedContinuous n ht) p)
        (chafaiRescaled f n) :=
      h_exp.sub h_bernstein
    dsimp [laplacePart, bernsteinPart, errorPart]
    calc
      ∫ p : ℝ≥0, Real.exp (-(t * (p : ℝ))) ∂(chafaiRescaled f n)
          = ∫ p : ℝ≥0,
              (bernsteinKernelBoundedContinuous n ht) p +
                (Real.exp (-(t * (p : ℝ))) - (bernsteinKernelBoundedContinuous n ht) p)
              ∂(chafaiRescaled f n) := by
            refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
            ring
      _ = (∫ p : ℝ≥0, (bernsteinKernelBoundedContinuous n ht) p ∂(chafaiRescaled f n)) +
            ∫ p : ℝ≥0,
              (Real.exp (-(t * (p : ℝ))) - (bernsteinKernelBoundedContinuous n ht) p)
              ∂(chafaiRescaled f n) := by
            rw [integral_add h_bernstein h_error]
  have hsum :
      Tendsto (fun n => bernsteinPart n + errorPart n) atTop (nhds (f t - L)) := by
    simpa [bernsteinPart, errorPart] using hbernstein.add herr
  exact (Tendsto.congr' (Filter.Eventually.of_forall fun n => (hsplit n).symm) hsum).mono_left hl

/-- Chafaï Laplace convergence for a completely monotone function, with the constant limit split
off as the missing atom at zero. -/
private theorem chafaiRescaledLaplaceConvergenceToNonconstantPart
    {f : ℝ → ℝ} (hcm : IsCompletelyMonotone f) :
    ChafaiRescaledLaplaceConvergenceToNonconstantPart f :=
  chafaiRescaledLaplaceConvergenceToNonconstantPart_of_bernsteinApprox hcm
    (chafaiRescaledBernsteinApproximationToNonconstantPart hcm)

/-- Existence of a finite representing measure for a function satisfying the existing strong
`IsCompletelyMonotone` predicate.

This is the part of the hard direction that the Part-1 Chafaï infrastructure is designed to feed:
use the mass bound, prove tightness, extract a weak cluster point, and identify the Laplace
integrals of the limit. -/
theorem exists_representsLaplace_of_isCompletelyMonotone
    {f : ℝ → ℝ} (hcm : IsCompletelyMonotone f) :
    ∃ μ : Measure ℝ≥0, RepresentsLaplace f μ := by
  have hconv : ChafaiRescaledLaplaceConvergenceToNonconstantPart f :=
    chafaiRescaledLaplaceConvergenceToNonconstantPart hcm
  obtain ⟨L, _hL, hL_nonneg, hconv⟩ := hconv
  obtain ⟨_L, C, _hL, _hL_nonneg, _hC, hmass⟩ :=
    chafaiRescaled_prokhorov_mass_bound f hcm
  obtain ⟨μ, U, hUle, hμ_fin, _hμ_mass, hweak⟩ :=
    finite_measure_cluster_limit (σ := chafaiRescaled f) C
      (fun n => (hmass n).2) (chafaiRescaled_tight hcm)
  let ν : Measure ℝ≥0 := μ + ENNReal.ofReal L • Measure.dirac (0 : ℝ≥0)
  have hatom_fin : IsFiniteMeasure (ENNReal.ofReal L • Measure.dirac (0 : ℝ≥0)) := by
    refine ⟨?_⟩
    simp
  letI := hatom_fin
  have hν_fin : IsFiniteMeasure ν := by
    dsimp [ν]
    infer_instance
  refine ⟨ν, representsLaplace_iff.mpr ⟨hν_fin, fun t ht => ?_⟩⟩
  letI := hν_fin
  have hweak_laplace :
      Tendsto (fun n => ∫ p, Real.exp (-(t * (p : ℝ))) ∂(chafaiRescaled f n))
        (U : Filter ℕ)
        (nhds (∫ p, Real.exp (-(t * (p : ℝ))) ∂μ)) :=
    chafaiRescaled_tendsto_laplace_integral_of_weak
      (μ₀ := μ) (l := (U : Filter ℕ)) hweak ht
  have hchafai :
      Tendsto (fun n => ∫ p, Real.exp (-(t * (p : ℝ))) ∂(chafaiRescaled f n))
        (U : Filter ℕ) (nhds (f t - L)) :=
    hconv hUle ht
  have hμ_laplace :
      f t - L = ∫ p, Real.exp (-(t * (p : ℝ))) ∂μ :=
    tendsto_nhds_unique hchafai hweak_laplace
  have hν_laplace :
      laplaceTransform ν t = (∫ p, Real.exp (-(t * (p : ℝ))) ∂μ) + L := by
    have hμ_int : Integrable (fun p : ℝ≥0 => Real.exp (-(t * (p : ℝ)))) μ :=
      integrable_laplaceKernel_of_nonneg μ ht
    have hatom_int : Integrable (fun p : ℝ≥0 => Real.exp (-(t * (p : ℝ))))
        (ENNReal.ofReal L • Measure.dirac (0 : ℝ≥0)) := by
      letI := hatom_fin
      exact integrable_laplaceKernel_of_nonneg _ ht
    calc
      laplaceTransform ν t
          = ∫ p, Real.exp (-(t * (p : ℝ))) ∂ν := rfl
      _ = (∫ p, Real.exp (-(t * (p : ℝ))) ∂μ) +
            ∫ p, Real.exp (-(t * (p : ℝ))) ∂(ENNReal.ofReal L •
              Measure.dirac (0 : ℝ≥0)) := by
            dsimp [ν]
            rw [integral_add_measure hμ_int hatom_int]
      _ = (∫ p, Real.exp (-(t * (p : ℝ))) ∂μ) + L := by
            rw [integral_smul_measure, integral_dirac]
            simp [hL_nonneg]
  calc
    f t = (f t - L) + L := by ring
    _ = (∫ p, Real.exp (-(t * (p : ℝ))) ∂μ) + L := by rw [hμ_laplace]
    _ = laplaceTransform ν t := hν_laplace.symm

/-- Existence of a finite representing measure for the closed-half-line predicate.

The existing Chafaï construction is applied to the positive shifts `t ↦ f (t + a)`, which satisfy
the stronger Tau Ceti predicate. As `a ↓ 0`, the representing measures are uniformly tight by an
elementary Laplace-kernel tail estimate and hence have a weak cluster point. Continuity at `0`
then identifies that cluster point as a representing measure for the original closed-half-line
function. -/
theorem exists_representsLaplace_of_isClosedCompletelyMonotone
    {f : ℝ → ℝ} (hf : IsClosedCompletelyMonotone f) :
    ∃ μ : Measure ℝ≥0, RepresentsLaplace f μ := by
  classical
  let a : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have ha_pos : ∀ n, 0 < a n := by
    intro n
    dsimp [a]
    positivity
  have ha_tendsto_nhds : Tendsto a atTop (nhds 0) := by
    have hden : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop := by
      exact Filter.tendsto_atTop_add_const_right atTop 1
        (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa [a] using Filter.Tendsto.const_div_atTop hden (1 : ℝ)
  have ha_mem : ∀ᶠ n : ℕ in atTop, a n ∈ Ici (0 : ℝ) := by
    filter_upwards with n
    exact mem_Ici.mpr (ha_pos n).le
  have ha_tendsto_Ici : Tendsto a atTop (𝓝[Ici (0 : ℝ)] 0) := by
    rw [nhdsWithin]
    exact tendsto_inf.2 ⟨ha_tendsto_nhds, tendsto_principal.mpr ha_mem⟩
  have hshift_cm : ∀ n, IsCompletelyMonotone (fun t : ℝ => f (t + a n)) :=
    fun n => hf.shift_pos (ha_pos n)
  choose μ hμ using fun n =>
    exists_representsLaplace_of_isCompletelyMonotone (hshift_cm n)
  have hμ_fin : ∀ n, IsFiniteMeasure (μ n) := fun n => (hμ n).isFiniteMeasure
  let C : ℝ≥0 := ⟨f 0, hf.nonneg_zero⟩
  have hmass : ∀ n, (μ n) univ ≤ (C : ENNReal) := by
    intro n
    haveI : IsFiniteMeasure (μ n) := hμ_fin n
    have h0 := (hμ n).eq_laplaceTransform (t := 0) le_rfl
    have hreal : (μ n).real univ = f (a n) := by
      simpa [laplaceTransform_zero] using h0.symm
    have hle : (μ n).real univ ≤ f 0 := by
      rw [hreal]
      exact hf.le_zero (ha_pos n).le
    calc
      (μ n) univ = ENNReal.ofReal ((μ n).real univ) := by
        rw [ofReal_measureReal]
      _ ≤ ENNReal.ofReal (f 0) := ENNReal.ofReal_le_ofReal hle
      _ = (C : ENNReal) := by
            have hC : f 0 = (C : ℝ) := rfl
            rw [hC]
            exact ENNReal.ofReal_coe_nnreal
  have hf_tendsto0 : Tendsto (fun n => f (a n)) atTop (nhds (f 0)) :=
    (hf.continuousOn.continuousWithinAt (mem_Ici.mpr le_rfl)).tendsto.comp
      ha_tendsto_Ici
  have htight : IsTightMeasureSet (Set.range μ) := by
    rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
    intro ε hε
    by_cases hε_top : ε = (∞ : ENNReal)
    · refine ⟨∅, isCompact_empty, ?_⟩
      intro ν _hν
      rw [hε_top]
      exact le_top
    have hε_real_pos : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hε_top
    let c0 : ℝ := 1 - Real.exp (-1)
    have hc0_pos : 0 < c0 := by
      have hexp_lt : Real.exp (-1) < 1 := by
        rw [← Real.exp_zero]
        exact Real.exp_lt_exp.mpr (by norm_num)
      dsimp [c0]
      linarith
    have heta_pos : 0 < ε.toReal * c0 / 2 := by
      positivity
    have hnear := (Metric.tendsto_nhds.mp hf_tendsto0)
      (ε.toReal * c0 / 2) heta_pos
    obtain ⟨m, hm⟩ := eventually_atTop.1 hnear
    let x : ℝ := a m
    have hx_pos : 0 < x := ha_pos m
    have hx_mem : x ∈ Ici (0 : ℝ) := mem_Ici.mpr hx_pos.le
    have hx_close : dist (f x) (f 0) < ε.toReal * c0 / 2 := by
      exact hm m le_rfl
    have hgap_limit_lt : f 0 - f x < ε.toReal * c0 / 2 := by
      rw [Real.dist_eq] at hx_close
      have hx_abs := abs_lt.mp hx_close
      linarith
    have hx_a_tendsto_nhds : Tendsto (fun n => x + a n) atTop (nhds x) := by
      simpa [add_zero] using tendsto_const_nhds.add ha_tendsto_nhds
    have hx_a_mem : ∀ᶠ n : ℕ in atTop, x + a n ∈ Ici (0 : ℝ) := by
      filter_upwards with n
      exact mem_Ici.mpr (add_nonneg hx_pos.le (ha_pos n).le)
    have hx_a_tendsto_Ici : Tendsto (fun n => x + a n) atTop (𝓝[Ici (0 : ℝ)] x) := by
      rw [nhdsWithin]
      exact tendsto_inf.2 ⟨hx_a_tendsto_nhds, tendsto_principal.mpr hx_a_mem⟩
    have hfx_tendsto : Tendsto (fun n => f (x + a n)) atTop (nhds (f x)) :=
      (hf.continuousOn.continuousWithinAt hx_mem).tendsto.comp hx_a_tendsto_Ici
    have hgap_tendsto :
        Tendsto (fun n => f (a n) - f (x + a n)) atTop (nhds (f 0 - f x)) :=
      hf_tendsto0.sub hfx_tendsto
    have hlim_lt : f 0 - f x < ε.toReal * c0 := by
      nlinarith [hgap_limit_lt, hε_real_pos, hc0_pos]
    have hgap_event :
        ∀ᶠ n : ℕ in atTop, (f (a n) - f (x + a n)) / c0 ≤ ε.toReal := by
      filter_upwards [hgap_tendsto.eventually_lt_const hlim_lt] with n hn
      rw [div_le_iff₀ hc0_pos]
      exact le_of_lt hn
    obtain ⟨N, hN⟩ := eventually_atTop.1 hgap_event
    let μfin : {n // n < N} → Measure ℝ≥0 := fun n => μ n
    have hfin_tight : IsTightMeasureSet (Set.range μfin) :=
      isTightMeasureSet_range_finite μfin (fun n => hμ_fin n)
    obtain ⟨Kfin, hKfin_comp, hKfin_tail⟩ :=
      isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp hfin_tight ε hε
    let R : ℝ := x⁻¹
    have hR_pos : 0 < R := inv_pos.mpr hx_pos
    refine ⟨Kfin ∪ Metric.closedBall (0 : ℝ≥0) R,
      hKfin_comp.union (isCompact_closedBall _ _), ?_⟩
    intro ν hν
    rcases hν with ⟨n, rfl⟩
    by_cases hnlt : n < N
    · have hmem_fin : μ n ∈ Set.range μfin := ⟨⟨n, hnlt⟩, rfl⟩
      have hsubset : (Kfin ∪ Metric.closedBall (0 : ℝ≥0) R)ᶜ ⊆ Kfinᶜ :=
        compl_subset_compl.mpr (subset_union_left)
      exact (measure_mono hsubset).trans (hKfin_tail (μ n) hmem_fin)
    · have hNn : N ≤ n := le_of_not_gt hnlt
      have hball_subset :
          (Kfin ∪ Metric.closedBall (0 : ℝ≥0) R)ᶜ ⊆
            (Metric.closedBall (0 : ℝ≥0) R)ᶜ :=
        compl_subset_compl.mpr (subset_union_right)
      have htail :=
        shiftedMeasure_closedBall_compl_le (hμ n) hx_pos hR_pos
      have hden : 1 - Real.exp (-(x * R)) = c0 := by
        dsimp [R, c0]
        rw [mul_inv_cancel₀ hx_pos.ne']
      have hquot :
          ENNReal.ofReal
            ((f (a n) - f (x + a n)) / (1 - Real.exp (-(x * R)))) ≤ ε := by
        rw [hden]
        exact ENNReal.ofReal_le_of_le_toReal (hN n hNn)
      calc
        μ n (Kfin ∪ Metric.closedBall (0 : ℝ≥0) R)ᶜ
            ≤ μ n (Metric.closedBall (0 : ℝ≥0) R)ᶜ := measure_mono hball_subset
        _ ≤ ENNReal.ofReal
              ((f (a n) - f (x + a n)) / (1 - Real.exp (-(x * R)))) := htail
        _ ≤ ε := hquot
  obtain ⟨μ₀, U, hUle, hμ₀_fin, _hmass₀, hweak⟩ :=
    finite_measure_cluster_limit (σ := μ) C hmass htight
  refine ⟨μ₀, representsLaplace_iff.mpr ⟨hμ₀_fin, fun t ht => ?_⟩⟩
  have ht_a_tendsto_nhds : Tendsto (fun n => t + a n) atTop (nhds t) := by
    simpa [add_zero] using tendsto_const_nhds.add ha_tendsto_nhds
  have ht_a_mem : ∀ᶠ n : ℕ in atTop, t + a n ∈ Ici (0 : ℝ) := by
    filter_upwards with n
    exact mem_Ici.mpr (add_nonneg ht (ha_pos n).le)
  have ht_a_tendsto_Ici : Tendsto (fun n => t + a n) atTop (𝓝[Ici (0 : ℝ)] t) := by
    rw [nhdsWithin]
    exact tendsto_inf.2 ⟨ht_a_tendsto_nhds, tendsto_principal.mpr ht_a_mem⟩
  have hf_arg_atTop : Tendsto (fun n => f (t + a n)) atTop (nhds (f t)) :=
    (hf.continuousOn.continuousWithinAt (mem_Ici.mpr ht)).tendsto.comp ht_a_tendsto_Ici
  have hf_arg_U : Tendsto (fun n => f (t + a n)) (U : Filter ℕ) (nhds (f t)) :=
    hf_arg_atTop.mono_left hUle
  have hlaplace_U :
      Tendsto (fun n => laplaceTransform (μ n) t) (U : Filter ℕ) (nhds (f t)) := by
    exact Tendsto.congr'
      (Filter.Eventually.of_forall fun n => (hμ n).eq_laplaceTransform (t := t) ht)
      hf_arg_U
  have hshift_laplace :
      Tendsto (fun n => ∫ p, Real.exp (-(t * (p : ℝ))) ∂(μ n)) (U : Filter ℕ)
        (nhds (f t)) := by
    simpa [laplaceTransform] using hlaplace_U
  have hweak_laplace :
      Tendsto (fun n => ∫ p, Real.exp (-(t * (p : ℝ))) ∂(μ n)) (U : Filter ℕ)
        (nhds (∫ p, Real.exp (-(t * (p : ℝ))) ∂μ₀)) := by
    simpa using hweak (laplaceKernelBoundedContinuous ht)
  exact tendsto_nhds_unique hshift_laplace hweak_laplace

/-! ## Uniqueness -/

private noncomputable def laplaceExpGenerator : ℝ≥0 →ᵇ ℝ :=
  laplaceKernelBoundedContinuous (show 0 ≤ (1 : ℝ) by norm_num)

private lemma laplaceExpGenerator_pow (n : ℕ) (x : ℝ≥0) :
    (laplaceExpGenerator x) ^ n = Real.exp (-((n : ℝ) * (x : ℝ))) := by
  rw [laplaceExpGenerator, laplaceKernelBoundedContinuous_apply]
  simp [← Real.exp_nat_mul]

private lemma integral_laplaceExpGenerator_pow_eq
    {μ ν : Measure ℝ≥0} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ t : ℝ, 0 ≤ t → laplaceTransform μ t = laplaceTransform ν t) (n : ℕ) :
    ∫ x, (laplaceExpGenerator x) ^ n ∂μ =
      ∫ x, (laplaceExpGenerator x) ^ n ∂ν := by
  have hn : 0 ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
  simpa [laplaceTransform, laplaceExpGenerator_pow] using h (n : ℝ) hn

private lemma integral_aeval_laplaceExpGenerator_eq
    {μ ν : Measure ℝ≥0} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ t : ℝ, 0 ≤ t → laplaceTransform μ t = laplaceTransform ν t) (p : ℝ[X]) :
    ∫ x, ((Polynomial.aeval laplaceExpGenerator) p : ℝ≥0 →ᵇ ℝ) x ∂μ =
      ∫ x, ((Polynomial.aeval laplaceExpGenerator) p : ℝ≥0 →ᵇ ℝ) x ∂ν := by
  rw [Polynomial.aeval_eq_sum_range laplaceExpGenerator]
  simp only [BoundedContinuousFunction.coe_sum, Finset.sum_apply]
  rw [integral_finsetSum _ (fun i _ =>
    BoundedContinuousFunction.integrable μ ((p.coeff i) • laplaceExpGenerator ^ i))]
  rw [integral_finsetSum _ (fun i _ =>
    BoundedContinuousFunction.integrable ν ((p.coeff i) • laplaceExpGenerator ^ i))]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  simp only [BoundedContinuousFunction.coe_smul, BoundedContinuousFunction.coe_pow, Pi.pow_apply,
    smul_eq_mul]
  rw [integral_const_mul, integral_const_mul, integral_laplaceExpGenerator_pow_eq h i]

private lemma laplaceExpGenerator_star : star laplaceExpGenerator = laplaceExpGenerator := by
  ext x
  rw [laplaceExpGenerator, laplaceKernelBoundedContinuous_apply]
  simp

private lemma mem_laplaceExpGenerator_adjoin_exists_aeval
    {g : ℝ≥0 →ᵇ ℝ}
    (hg : g ∈ StarAlgebra.adjoin ℝ ({laplaceExpGenerator} : Set (ℝ≥0 →ᵇ ℝ))) :
    ∃ p : ℝ[X], (Polynomial.aeval laplaceExpGenerator) p = g := by
  have hg' : g ∈
      (StarAlgebra.adjoin ℝ ({laplaceExpGenerator} : Set (ℝ≥0 →ᵇ ℝ))).toSubalgebra := hg
  rw [StarAlgebra.adjoin_toSubalgebra] at hg'
  rw [Set.star_singleton, laplaceExpGenerator_star, Set.union_self] at hg'
  exact Algebra.adjoin_mem_exists_aeval ℝ laplaceExpGenerator hg'

private lemma laplaceExpGenerator_adjoin_separatesPoints :
    ((StarAlgebra.adjoin ℝ ({laplaceExpGenerator} : Set (ℝ≥0 →ᵇ ℝ))).map
      (BoundedContinuousFunction.toContinuousMapStarₐ ℝ)).SeparatesPoints := by
  intro x y hxy
  refine ⟨(laplaceExpGenerator : ℝ≥0 → ℝ), ?_, ?_⟩
  · -- Coerce the bounded continuous generator to the plain function used by `SeparatesPoints`.
    refine ⟨BoundedContinuousFunction.toContinuousMap laplaceExpGenerator, ?_, rfl⟩
    -- The mapped star subalgebra contains the continuous-map coercion of the generator.
    exact StarSubalgebra.mem_map.mpr
      ⟨laplaceExpGenerator, StarAlgebra.self_mem_adjoin_singleton ℝ laplaceExpGenerator, rfl⟩
  · intro h
    apply hxy
    have hlog := congrArg Real.log h
    simpa [laplaceExpGenerator, laplaceKernelBoundedContinuous_apply] using hlog

/-- Finite measures on `ℝ≥0` are determined by their Laplace transforms on `[0, ∞)`.

This applies Mathlib's finite-measure extensionality theorem for point-separating star
subalgebras of bounded continuous functions to the star subalgebra generated by
`x ↦ exp (-x)`. Its powers are the Laplace kernels at natural parameters. -/
theorem laplaceTransform_ext
    {μ ν : Measure ℝ≥0} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ t : ℝ, 0 ≤ t → laplaceTransform μ t = laplaceTransform ν t) :
    μ = ν := by
  exact MeasureTheory.ext_of_forall_mem_subalgebra_integral_eq_of_polish
    (P := μ) (P' := ν)
    (A := StarAlgebra.adjoin ℝ ({laplaceExpGenerator} : Set (ℝ≥0 →ᵇ ℝ)))
    laplaceExpGenerator_adjoin_separatesPoints
    (fun g hg => by
      obtain ⟨p, rfl⟩ := mem_laplaceExpGenerator_adjoin_exists_aeval hg
      exact integral_aeval_laplaceExpGenerator_eq h p)

/-- A function has at most one finite representing measure. -/
theorem laplaceTransform_unique
    {f : ℝ → ℝ} {μ ν : Measure ℝ≥0}
    (hμ : RepresentsLaplace f μ) (hν : RepresentsLaplace f ν) :
    μ = ν := by
  letI := hμ.isFiniteMeasure
  letI := hν.isFiniteMeasure
  exact laplaceTransform_ext fun t ht => by
    rw [← hμ.eq_laplaceTransform ht, ← hν.eq_laplaceTransform ht]

/-! ## Headline theorem -/

/-- Internal proposition form of the **Hausdorff--Bernstein--Widder theorem**, finite-measure
version on `ℝ≥0`.

A function is continuous on `[0, ∞)` and completely monotone on `(0, ∞)` if and only if it is the
Laplace transform of a finite positive measure on `ℝ≥0`, on the nonnegative half-line. -/
private def HausdorffBernsteinWidderTheorem : Prop :=
  ∀ f : ℝ → ℝ,
    IsClosedCompletelyMonotone f ↔ ∃ μ : Measure ℝ≥0, RepresentsLaplace f μ

/-- Internal proposition form of the unique-existence statement of the
Hausdorff--Bernstein--Widder theorem. -/
private def HausdorffBernsteinWidderUniqueTheorem : Prop :=
  ∀ f : ℝ → ℝ,
    IsClosedCompletelyMonotone f ↔ ∃! μ : Measure ℝ≥0, RepresentsLaplace f μ

/-- Assemble the non-unique Hausdorff--Bernstein--Widder theorem from separately supplied
existence and easy directions. -/
private theorem hausdorff_bernstein_widder_of_exists_of_laplaceTransform
    (hexists :
      ∀ f : ℝ → ℝ, IsClosedCompletelyMonotone f →
        ∃ μ : Measure ℝ≥0, RepresentsLaplace f μ)
    (hlaplace :
      ∀ μ : Measure ℝ≥0, IsFiniteMeasure μ →
        IsClosedCompletelyMonotone (laplaceTransform μ)) :
    HausdorffBernsteinWidderTheorem := by
  intro f
  constructor
  · exact hexists f
  · rintro ⟨μ, hμ⟩
    exact (hlaplace μ hμ.isFiniteMeasure).congr fun t ht =>
      hμ.eq_laplaceTransform ht

/-- Assemble the unique-existence Hausdorff--Bernstein--Widder theorem from the non-unique
theorem. -/
private theorem hausdorff_bernstein_widder_unique_of_hausdorff_bernstein_widder
    (hhbw : HausdorffBernsteinWidderTheorem) :
    HausdorffBernsteinWidderUniqueTheorem := by
  intro f
  constructor
  · intro hf
    obtain ⟨μ, hμ⟩ := (hhbw f).mp hf
    exact ⟨μ, hμ, fun ν hν =>
      (laplaceTransform_unique (f := f) (μ := μ) (ν := ν) hμ hν).symm⟩
  · rintro ⟨μ, hμ, _huniq⟩
    exact (hhbw f).mpr ⟨μ, hμ⟩

/-- Hausdorff--Bernstein--Widder theorem, finite-measure version on `ℝ≥0`.

A function is continuous on `[0, ∞)` and completely monotone on `(0, ∞)` if and only if it is
the Laplace transform of a finite positive measure on `ℝ≥0`. -/
theorem hausdorff_bernstein_widder (f : ℝ → ℝ) :
    IsClosedCompletelyMonotone f ↔ ∃ μ : Measure ℝ≥0, RepresentsLaplace f μ :=
  hausdorff_bernstein_widder_of_exists_of_laplaceTransform
    (fun _f hf => exists_representsLaplace_of_isClosedCompletelyMonotone hf)
    (fun μ hμ => by
      letI := hμ
      exact laplaceTransform_isClosedCompletelyMonotone μ) f

/-- Unique-existence form of the Hausdorff--Bernstein--Widder theorem. -/
theorem hausdorff_bernstein_widder_unique (f : ℝ → ℝ) :
    IsClosedCompletelyMonotone f ↔ ∃! μ : Measure ℝ≥0, RepresentsLaplace f μ :=
  hausdorff_bernstein_widder_unique_of_hausdorff_bernstein_widder
    (hausdorff_bernstein_widder_of_exists_of_laplaceTransform
      (fun _f hf => exists_representsLaplace_of_isClosedCompletelyMonotone hf)
      (fun μ hμ => by
        letI := hμ
        exact laplaceTransform_isClosedCompletelyMonotone μ)) f

/-- Strong-predicate unique-existence corollary of the Bernstein theorem. -/
theorem existsUnique_representsLaplace_of_isCompletelyMonotone
    {f : ℝ → ℝ} (hcm : IsCompletelyMonotone f) :
    ∃! μ : Measure ℝ≥0, RepresentsLaplace f μ := by
  obtain ⟨μ, hμ⟩ :=
    exists_representsLaplace_of_isCompletelyMonotone hcm
  exact ⟨μ, hμ, fun ν hν =>
    (laplaceTransform_unique (f := f) (μ := μ) (ν := ν) hμ hν).symm⟩


end TauCeti

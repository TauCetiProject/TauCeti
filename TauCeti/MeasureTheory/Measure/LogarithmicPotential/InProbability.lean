/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.LogarithmicPotential.Convergence
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

import Mathlib.MeasureTheory.Measure.WithDensityFinite
import Mathlib.Probability.Kernel.MeasurableIntegral
import TauCeti.MeasureTheory.Function.ConvergenceInMeasure
import TauCeti.MeasureTheory.Measure.Measurability

/-!
# Random logarithmic potentials

Convergence in probability at Lebesgue-almost every observation point implies convergence
in probability of every bounded continuous spectral statistic. The analogous almost-sure
statement gives almost-sure weak convergence of the random probability measures.

The passage from observation-point convergence in probability to the deterministic continuity
theorem uses convergence in measure on a product and subsequence extraction. A finite measure
equivalent to Lebesgue measure provides a common subsequence for the entire plane.
These are the probabilistic forms of T. Tao, *Topics in Random Matrix Theory*, Theorem 2.8.3.

The same passage gives the probabilistic forms of the replacement principle, which compares two
sequences of random probability measures through the differences of their potentials. Almost
surely, or in probability, their integrals against continuous compactly supported functions
become asymptotically equal (T. Tao, V. Vu, *Random matrices: universality of ESDs and the
circular law*, Ann. Probab. 38 (2010); arXiv:0807.4898, Theorem 2.1). Almost surely, a weak limit
of one sequence is then a weak limit of the other.
-/

public section

open Filter MeasureTheory Set Topology
open scoped BoundedContinuousFunction ENNReal

namespace MeasureTheory

namespace ProbabilityMeasure

/-- Evaluation of the logarithmic potential is jointly measurable in the measure and the point. -/
@[fun_prop]
theorem measurable_logarithmicPotential :
    Measurable fun p : ProbabilityMeasure ℂ × ℂ ↦ (p.1 : Measure ℂ).logarithmicPotential p.2 := by
  let κ : ProbabilityTheory.Kernel (ProbabilityMeasure ℂ × ℂ) ℂ :=
    ⟨fun p ↦ p.1, measurable_subtypeVal.comp measurable_fst⟩
  have hκ (p : ProbabilityMeasure ℂ × ℂ) : κ p = p.1 := (rfl)
  have : ProbabilityTheory.IsMarkovKernel κ := ⟨fun p ↦ hκ p ▸ inferInstance⟩
  have h : Measurable fun q : (ProbabilityMeasure ℂ × ℂ) × ℂ ↦ Real.log ‖q.1.2 - q.2‖ := by
    fun_prop
  simpa only [Measure.logarithmicPotential_def, hκ] using
    (h.stronglyMeasurable.integral_kernel_prod_right' (κ := κ)).measurable

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {X Y : ℕ → Ω → ProbabilityMeasure ℂ} {μ : ProbabilityMeasure ℂ}

private theorem measurable_logarithmicPotential_sub (hX : ∀ n, Measurable (X n))
    (hY : ∀ n, Measurable (Y n)) (n : ℕ) :
    Measurable fun p : Ω × ℂ ↦ (X n p.1 : Measure ℂ).logarithmicPotential p.2 -
      (Y n p.1 : Measure ℂ).logarithmicPotential p.2 :=
  (measurable_logarithmicPotential.comp (((hX n).comp measurable_fst).prodMk measurable_snd)).sub
    (measurable_logarithmicPotential.comp (((hY n).comp measurable_fst).prodMk measurable_snd))

/-- The almost-sure hypothesis at almost every point can be read pathwise: almost surely the
potential differences converge at almost every point. -/
private theorem ae_ae_tendsto_logarithmicPotential_sub [SFinite P]
    (hX : ∀ n, AEMeasurable (X n) P) (hY : ∀ n, AEMeasurable (Y n) P)
    (h : ∀ᵐ z ∂volume, ∀ᵐ ω ∂P, Tendsto (fun n ↦ (X n ω : Measure ℂ).logarithmicPotential z -
      (Y n ω : Measure ℂ).logarithmicPotential z) atTop (𝓝 0)) :
    ∀ᵐ ω ∂P, ∀ᵐ z ∂volume, Tendsto (fun n ↦ (X n ω : Measure ℂ).logarithmicPotential z -
      (Y n ω : Measure ℂ).logarithmicPotential z) atTop (𝓝 0) := by
  let X' (n : ℕ) := (hX n).mk (X n)
  let Y' (n : ℕ) := (hY n).mk (Y n)
  have hXX : ∀ᵐ ω ∂P, ∀ n, X n ω = X' n ω := ae_all_iff.2 fun n ↦ (hX n).ae_eq_mk
  have hYY : ∀ᵐ ω ∂P, ∀ n, Y n ω = Y' n ω := ae_all_iff.2 fun n ↦ (hY n).ae_eq_mk
  have hs : MeasurableSet {p : Ω × ℂ | Tendsto (fun n ↦
      (X' n p.1 : Measure ℂ).logarithmicPotential p.2 -
        (Y' n p.1 : Measure ℂ).logarithmicPotential p.2) atTop (𝓝 0)} :=
    measurableSet_tendsto (𝓝 0) (measurable_logarithmicPotential_sub
      (fun n ↦ (hX n).measurable_mk) (fun n ↦ (hY n).measurable_mk))
  have h' : ∀ᵐ z ∂volume, ∀ᵐ ω ∂P, Tendsto (fun n ↦
      (X' n ω : Measure ℂ).logarithmicPotential z -
        (Y' n ω : Measure ℂ).logarithmicPotential z) atTop (𝓝 0) := by
    filter_upwards [h] with z hz
    filter_upwards [hz, hXX, hYY] with ω hω hx hy
    simpa only [hx, hy] using hω
  filter_upwards [(Measure.ae_ae_comm hs).2 h', hXX, hYY] with ω hω hx hy
  simpa only [hx, hy] using hω

/-- Convergence in probability at almost every point gives, along a subsequence of any given
subsequence, almost-sure convergence of the potential differences at almost every point. -/
private theorem exists_subseq_ae_ae_tendsto_logarithmicPotential_sub [IsFiniteMeasure P]
    (hX : ∀ n, Measurable (X n)) (hY : ∀ n, Measurable (Y n))
    (h : ∀ᵐ z ∂volume, TendstoInMeasure P (fun n ω ↦ (X n ω : Measure ℂ).logarithmicPotential z -
      (Y n ω : Measure ℂ).logarithmicPotential z) atTop 0)
    {ns : ℕ → ℕ} (hns : StrictMono ns) :
    ∃ ms : ℕ → ℕ, StrictMono ms ∧ ∀ᵐ ω ∂P, ∀ᵐ z ∂volume, Tendsto (fun k ↦
      (X (ns (ms k)) ω : Measure ℂ).logarithmicPotential z -
        (Y (ns (ms k)) ω : Measure ℂ).logarithmicPotential z) atTop (𝓝 0) := by
  let ν := (volume : Measure ℂ).toFinite
  let u (n : ℕ) (p : ℂ × Ω) := (X n p.2 : Measure ℂ).logarithmicPotential p.1 -
    (Y n p.2 : Measure ℂ).logarithmicPotential p.1
  have hu (n : ℕ) : Measurable (u n) :=
    (measurable_logarithmicPotential_sub hX hY n).comp measurable_swap
  have hprod : TendstoInMeasure (ν.prod P) u atTop 0 :=
    tendstoInMeasure_prod_of_ae_tendstoInMeasure
      (Eventually.of_forall fun n ↦ (hu n).edist measurable_const)
      ((toFinite_absolutelyContinuous _).ae_le h)
  obtain ⟨ms, hms, hconv⟩ := (hprod.comp hns.tendsto_atTop).exists_seq_tendsto_ae
  refine ⟨ms, hms, ?_⟩
  have hswap : ∀ᵐ p ∂P.prod ν, Tendsto (fun k ↦
      (X (ns (ms k)) p.1 : Measure ℂ).logarithmicPotential p.2 -
        (Y (ns (ms k)) p.1 : Measure ℂ).logarithmicPotential p.2) atTop (𝓝 0) :=
    (Measure.measurePreserving_swap (μ := P) (ν := ν)).quasiMeasurePreserving.ae hconv
  filter_upwards [Measure.ae_ae_of_ae_prod hswap] with ω hω
  exact (absolutelyContinuous_toFinite (volume : Measure ℂ)).ae_le hω

/-- **Replacement principle, almost-sure form.** If, at almost every point, the logarithmic
potentials of the random probability measures `X n` and `Y n` almost surely become asymptotically
equal, then almost surely `X n - Y n` tends to zero vaguely: the integrals of every continuous
compactly supported function against `X n` and `Y n` become asymptotically equal. The logarithmic
moments may be random and need only be finite almost surely. -/
theorem ae_tendsto_integral_sub_integral_of_ae_ae_tendsto_logarithmicPotential_sub [SFinite P]
    (hX : ∀ n, AEMeasurable (X n) P) (hY : ∀ n, AEMeasurable (Y n) P)
    (hmX : ∀ᵐ ω ∂P, ∀ n, Integrable (fun w : ℂ ↦ Real.posLog ‖w‖) (X n ω : Measure ℂ))
    (hmY : ∀ᵐ ω ∂P, ∀ n, Integrable (fun w : ℂ ↦ Real.posLog ‖w‖) (Y n ω : Measure ℂ))
    (h : ∀ᵐ z ∂volume, ∀ᵐ ω ∂P, Tendsto (fun n ↦ (X n ω : Measure ℂ).logarithmicPotential z -
      (Y n ω : Measure ℂ).logarithmicPotential z) atTop (𝓝 0)) :
    ∀ᵐ ω ∂P, ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f →
      Tendsto (fun n ↦ ∫ z, f z ∂(X n ω : Measure ℂ) - ∫ z, f z ∂(Y n ω : Measure ℂ)) atTop
        (𝓝 0) := by
  filter_upwards [ae_ae_tendsto_logarithmicPotential_sub hX hY h, hmX, hmY] with ω hω hx hy f hf
    hc
  exact tendsto_integral_sub_integral_of_ae_tendsto_logarithmicPotential_sub hx hy hω hf hc

/-- **Replacement principle with a limit, almost-sure form.** If almost surely `Y n` converges
weakly to a probability measure `μ`, and at almost every point the logarithmic potentials of `X n`
and `Y n` almost surely become asymptotically equal, then almost surely `X n` converges weakly to
`μ`. -/
theorem ae_tendsto_of_ae_tendsto_of_ae_ae_tendsto_logarithmicPotential_sub [SFinite P]
    (hX : ∀ n, AEMeasurable (X n) P) (hY : ∀ n, AEMeasurable (Y n) P)
    (hmX : ∀ᵐ ω ∂P, ∀ n, Integrable (fun w : ℂ ↦ Real.posLog ‖w‖) (X n ω : Measure ℂ))
    (hmY : ∀ᵐ ω ∂P, ∀ n, Integrable (fun w : ℂ ↦ Real.posLog ‖w‖) (Y n ω : Measure ℂ))
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n ↦ Y n ω) atTop (𝓝 μ))
    (h : ∀ᵐ z ∂volume, ∀ᵐ ω ∂P, Tendsto (fun n ↦ (X n ω : Measure ℂ).logarithmicPotential z -
      (Y n ω : Measure ℂ).logarithmicPotential z) atTop (𝓝 0)) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦ X n ω) atTop (𝓝 μ) := by
  filter_upwards [ae_ae_tendsto_logarithmicPotential_sub hX hY h, hmX, hmY, hlim] with ω hω hx hy
    hl
  exact tendsto_of_tendsto_of_ae_tendsto_logarithmicPotential_sub hx hy hl hω

/-- **Replacement principle, in-probability form.** If, at almost every point, the difference of
the logarithmic potentials of the random probability measures `X n` and `Y n` converges to zero in
probability, then for every continuous compactly supported `f` the difference of the integrals of
`f` against `X n` and `Y n` converges to zero in probability. -/
theorem tendstoInMeasure_integral_sub_integral_of_ae_tendstoInMeasure_logarithmicPotential_sub
    [IsFiniteMeasure P] (hX : ∀ n, AEMeasurable (X n) P) (hY : ∀ n, AEMeasurable (Y n) P)
    (hmX : ∀ᵐ ω ∂P, ∀ n, Integrable (fun w : ℂ ↦ Real.posLog ‖w‖) (X n ω : Measure ℂ))
    (hmY : ∀ᵐ ω ∂P, ∀ n, Integrable (fun w : ℂ ↦ Real.posLog ‖w‖) (Y n ω : Measure ℂ))
    (h : ∀ᵐ z ∂volume, TendstoInMeasure P (fun n ω ↦ (X n ω : Measure ℂ).logarithmicPotential z -
      (Y n ω : Measure ℂ).logarithmicPotential z) atTop 0)
    {f : ℂ → ℝ} (hf : Continuous f) (hc : HasCompactSupport f) :
    TendstoInMeasure P (fun n ω ↦ ∫ z, f z ∂(X n ω : Measure ℂ) - ∫ z, f z ∂(Y n ω : Measure ℂ))
      atTop 0 := by
  let X' (n : ℕ) := (hX n).mk (X n)
  let Y' (n : ℕ) := (hY n).mk (Y n)
  have hXX : ∀ᵐ ω ∂P, ∀ n, X n ω = X' n ω := ae_all_iff.2 fun n ↦ (hX n).ae_eq_mk
  have hYY : ∀ᵐ ω ∂P, ∀ n, Y n ω = Y' n ω := ae_all_iff.2 fun n ↦ (hY n).ae_eq_mk
  have hF : Measurable fun σ : ProbabilityMeasure ℂ ↦ ∫ z, f z ∂(σ : Measure ℂ) :=
    hf.stronglyMeasurable.integral_probabilityMeasure.measurable
  have hconv : ∀ ns : ℕ → ℕ, StrictMono ns → ∃ ms : ℕ → ℕ, StrictMono ms ∧ ∀ᵐ ω ∂P,
      Tendsto (fun k ↦ ∫ z, f z ∂(X (ns (ms k)) ω : Measure ℂ) -
        ∫ z, f z ∂(Y (ns (ms k)) ω : Measure ℂ)) atTop (𝓝 0) := by
    intro ns hns
    have h' : ∀ᵐ z ∂volume, TendstoInMeasure P (fun n ω ↦
        (X' n ω : Measure ℂ).logarithmicPotential z -
          (Y' n ω : Measure ℂ).logarithmicPotential z) atTop 0 := by
      filter_upwards [h] with z hz
      refine TendstoInMeasure.congr_left (fun n ↦ ?_) hz
      filter_upwards [hXX, hYY] with ω hx hy
      rw [hx n, hy n]
    obtain ⟨ms, hms, hpath⟩ := exists_subseq_ae_ae_tendsto_logarithmicPotential_sub (X := X')
      (Y := Y') (fun n ↦ (hX n).measurable_mk) (fun n ↦ (hY n).measurable_mk) h' hns
    refine ⟨ms, hms, ?_⟩
    filter_upwards [hpath, hmX, hmY, hXX, hYY] with ω hω hx hy hxx hyy
    simp only [hxx, hyy] at hx hy ⊢
    exact tendsto_integral_sub_integral_of_ae_tendsto_logarithmicPotential_sub (fun k ↦ hx _)
      (fun k ↦ hy _) hω hf hc
  exact (exists_seq_tendstoInMeasure_atTop_iff fun n ↦ ((hF.comp_aemeasurable (hX n)).sub
    (hF.comp_aemeasurable (hY n))).aestronglyMeasurable).2 hconv

/-- Almost-sure convergence of the potentials at Lebesgue-almost every point implies almost-sure
weak convergence of the random measures. The logarithmic moments may be random and need
only be finite almost surely. -/
theorem ae_tendsto_of_ae_ae_tendsto_logarithmicPotential [SFinite P]
    (hX : ∀ n, AEMeasurable (X n) P)
    (hm : ∀ᵐ ω ∂P, ∀ n, Integrable (fun w : ℂ ↦ Real.posLog ‖w‖) (X n ω : Measure ℂ))
    (hμ : Integrable (fun w : ℂ ↦ Real.posLog ‖w‖) (μ : Measure ℂ))
    (h : ∀ᵐ z ∂volume, ∀ᵐ ω ∂P, Tendsto (fun n ↦ (X n ω : Measure ℂ).logarithmicPotential z)
      atTop (𝓝 ((μ : Measure ℂ).logarithmicPotential z))) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦ X n ω) atTop (𝓝 μ) := by
  refine ae_tendsto_of_ae_tendsto_of_ae_ae_tendsto_logarithmicPotential_sub (Y := fun _ _ ↦ μ) hX
    (fun _ ↦ aemeasurable_const) hm (ae_of_all _ fun _ _ ↦ hμ) (ae_of_all _ fun _ ↦
      tendsto_const_nhds) ?_
  filter_upwards [h] with z hz
  filter_upwards [hz] with ω hω
  exact tendsto_sub_nhds_zero_iff.2 hω

/-- Pointwise convergence in probability of the potentials for almost every observation point
implies convergence in probability of every bounded continuous test integral. -/
theorem tendstoInMeasure_integral_of_ae_tendstoInMeasure_logarithmicPotential [IsFiniteMeasure P]
    (hX : ∀ n, AEMeasurable (X n) P)
    (hm : ∀ᵐ ω ∂P, ∀ n, Integrable (fun w : ℂ ↦ Real.posLog ‖w‖) (X n ω : Measure ℂ))
    (hμ : Integrable (fun w : ℂ ↦ Real.posLog ‖w‖) (μ : Measure ℂ))
    (h : ∀ᵐ z ∂volume, TendstoInMeasure P (fun n ω ↦ (X n ω : Measure ℂ).logarithmicPotential z)
      atTop (fun _ ↦ (μ : Measure ℂ).logarithmicPotential z))
    (f : ℂ →ᵇ ℝ) :
    TendstoInMeasure P (fun n ω ↦ ∫ z, f z ∂(X n ω : Measure ℂ))
      atTop (fun _ ↦ ∫ z, f z ∂(μ : Measure ℂ)) := by
  let X' (n : ℕ) := (hX n).mk (X n)
  have hXX : ∀ᵐ ω ∂P, ∀ n, X n ω = X' n ω := ae_all_iff.2 fun n ↦ (hX n).ae_eq_mk
  have hF : Continuous fun σ : ProbabilityMeasure ℂ ↦ ∫ z, f z ∂(σ : Measure ℂ) :=
    continuous_integral_boundedContinuousFunction f
  have h' : ∀ᵐ z ∂volume, TendstoInMeasure P (fun n ω ↦
      (X' n ω : Measure ℂ).logarithmicPotential z - (μ : Measure ℂ).logarithmicPotential z)
      atTop 0 := by
    filter_upwards [h] with z hz
    rw [tendstoInMeasure_iff_norm] at hz ⊢
    intro ε hε
    refine (hz ε hε).congr' (.of_forall fun n ↦ measure_congr ?_)
    filter_upwards [hXX] with ω hx
    simp only [hx n, Pi.zero_apply, sub_zero]
  refine (exists_seq_tendstoInMeasure_atTop_iff fun n ↦
    (f.continuous.stronglyMeasurable.integral_probabilityMeasure.measurable.comp_aemeasurable
      (hX n)).aestronglyMeasurable).2
    fun ns hns ↦ ?_
  obtain ⟨ms, hms, hpath⟩ := exists_subseq_ae_ae_tendsto_logarithmicPotential_sub (X := X')
    (Y := fun _ _ ↦ μ) (fun n ↦ (hX n).measurable_mk) (fun _ ↦ measurable_const) h' hns
  refine ⟨ms, hms, ?_⟩
  filter_upwards [hpath, hm, hXX] with ω hω hx hxx
  simp only [← hxx] at hω
  exact hF.continuousAt.tendsto.comp (tendsto_of_ae_tendsto_logarithmicPotential (fun k ↦ hx _) hμ
    (hω.mono fun z hz ↦ tendsto_sub_nhds_zero_iff.1 hz))

end ProbabilityMeasure
end MeasureTheory

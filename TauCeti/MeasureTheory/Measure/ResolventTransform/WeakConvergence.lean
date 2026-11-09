/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.ResolventTransform.Basic
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Measure.Tight
import TauCeti.MeasureTheory.Measure.ResolventTransform.Atoms
import TauCeti.MeasureTheory.Measure.ResolventTransform.Expansion
import TauCeti.MeasureTheory.Measure.ResolventTransform.Inversion
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.TightNormed
import Mathlib.Topology.MetricSpace.Equicontinuity
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Tactic.Positivity

/-!
# Weak convergence and the resolvent transform

Probability measures `μᵢ` on `ℝ` converge weakly to a probability measure `μ` if and only if
their resolvent transforms `m_{μᵢ}(z) = ∫ (x - z)⁻¹ dμᵢ(x)` converge to `m_μ(z)` at every point
`z` of the upper half-plane. This is the analytic route to the global laws of random matrix
theory: the resolvent transform of an empirical spectral measure is a normalized trace of a
resolvent matrix, and the limit is identified by an equation that the limiting transform solves.

One direction is immediate, since off the real axis the kernel `x ↦ (x - z)⁻¹` is bounded and
continuous. For the converse, the transform on the imaginary axis controls the tails,

`μ {x | y ≤ |x|} ≤ 2 (μ(ℝ) - y Im m_μ(iy))` for `y > 0`,

and the right-hand side tends to `0` as `y → ∞` (`tendsto_mul_I_mul_resolventTransform`). So
pointwise convergence of the transforms on the imaginary axis to a function `g` with
`iy g(iy) → -1` makes a sequence tight. By Prokhorov's theorem every cluster point of the
sequence is a probability measure, whose transform is the limit of the transforms; Stieltjes
inversion (`Measure.ext_of_resolventTransform`) then identifies it with `μ`.

The transforms of probability measures are uniformly Lipschitz on each half-plane
`Im z ≥ c > 0`, so convergence on any subset `D` whose closure contains the upper half-plane
already suffices; `D` can be taken countable. Through this countable determining set, convergence
of the transforms almost surely at each fixed point gives almost sure weak convergence of random
probability measures, the form in which the almost sure semicircle and Marchenko–Pastur laws
are proved.

## Main results

* `MeasureTheory.measureReal_le_abs_le_two_mul_sub_mul_im_resolventTransform`: the tail bound.
* `MeasureTheory.isTightMeasureSet_range_of_tendsto_resolventTransform`: tightness from
  convergence of the transforms on the imaginary axis.
* `MeasureTheory.ProbabilityMeasure.tendsto_iff_tendsto_resolventTransform`: weak convergence is
  convergence of the transforms on the upper half-plane.
* `MeasureTheory.ProbabilityMeasure.tendsto_of_tendsto_resolventTransform_of_subset_closure`:
  convergence on a set whose closure contains the upper half-plane suffices.
* `MeasureTheory.ProbabilityMeasure.ae_tendsto_of_ae_tendsto_resolventTransform`: the almost
  sure version for random probability measures.

## Implementation notes

The identification of cluster points follows the ultrafilter argument of Mathlib's
`MeasureTheory.ProbabilityMeasure.tendsto_of_tight_of_separatesPoints`, with Stieltjes inversion
in place of a separating algebra of test functions. Tightness of a range is only available for
sequences, so the general statements assume a countably generated filter and reduce to sequences.

## References

* G. W. Anderson, A. Guionnet and O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press (2010), Theorem 2.4.4.
* T. Tao, *Topics in Random Matrix Theory*, American Mathematical Society (2012), §2.4.3.
-/

public section

open Filter Complex Set
open scoped Topology ENNReal

namespace MeasureTheory

variable {ι : Type*} {l : Filter ι}

/-- **Tail bound from the resolvent transform.** For a finite measure `ν` on `ℝ` and `y > 0`,
`ν {x | y ≤ |x|} ≤ 2 (ν(ℝ) - y Im m_ν(iy))`. -/
theorem measureReal_le_abs_le_two_mul_sub_mul_im_resolventTransform {ν : Measure ℝ}
    [IsFiniteMeasure ν] {y : ℝ} (hy : 0 < y) :
    ν.real {x | y ≤ |x|} ≤ 2 * (ν.real univ - y * (resolventTransform ν (y * I)).im) := by
  have hpos (x : ℝ) : 0 < x ^ 2 + y ^ 2 := by positivity
  have hx : Integrable (fun x : ℝ ↦ x ^ 2 / (x ^ 2 + y ^ 2)) ν := by
    refine (integrable_const (1 : ℝ)).mono' (by fun_prop : Measurable _).aestronglyMeasurable
      (ae_of_all _ fun x ↦ ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), div_le_one (hpos x)]
    nlinarith
  have hy' : Integrable (fun x : ℝ ↦ y ^ 2 / (x ^ 2 + y ^ 2)) ν := by
    refine (integrable_const (1 : ℝ)).mono' (by fun_prop : Measurable _).aestronglyMeasurable
      (ae_of_all _ fun x ↦ ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), div_le_one (hpos x)]
    nlinarith
  -- `y Im m_ν(iy) = ∫ y² / (x² + y²) dν`, and the two kernels add up to `1`.
  have him : y * (resolventTransform ν (y * I)).im = ∫ x, y ^ 2 / (x ^ 2 + y ^ 2) ∂ν := by
    simpa using mul_im_resolventTransform (μ := ν) (a := 0) (η := y)
  have htot : ∫ x, x ^ 2 / (x ^ 2 + y ^ 2) ∂ν + ∫ x, y ^ 2 / (x ^ 2 + y ^ 2) ∂ν =
      ν.real univ := by
    have h1 : (fun x : ℝ ↦ x ^ 2 / (x ^ 2 + y ^ 2) + y ^ 2 / (x ^ 2 + y ^ 2)) = fun _ ↦ 1 := by
      ext1 x
      rw [← add_div, div_self (hpos x).ne']
    rw [← integral_add hx hy', h1, integral_const, smul_eq_mul, mul_one]
  -- Markov's inequality at level `1 / 2`, since `x² / (x² + y²) ≥ 1 / 2` when `y ≤ |x|`.
  have hmarkov := mul_meas_ge_le_integral_of_nonneg (ae_of_all _ fun x ↦ by positivity) hx
    (1 / 2)
  have hsub : {x : ℝ | y ≤ |x|} ⊆ {x | 1 / 2 ≤ x ^ 2 / (x ^ 2 + y ^ 2)} := by
    intro x hxy
    simp only [mem_ofPred_eq] at hxy ⊢
    rw [le_div_iff₀ (hpos x)]
    nlinarith [mul_le_mul hxy hxy hy.le (abs_nonneg x), sq_abs x]
  linarith [measureReal_mono hsub (μ := ν)]

/-- **Tightness from resolvent transforms.** If the resolvent transforms of a sequence of
probability measures on `ℝ` converge on the positive imaginary axis to a function `g` with
`iy g(iy) → -1` as `y → ∞`, then the sequence is tight. -/
theorem isTightMeasureSet_range_of_tendsto_resolventTransform {μ : ℕ → Measure ℝ}
    [∀ n, IsProbabilityMeasure (μ n)] {g : ℂ → ℂ}
    (hg : Tendsto (fun y : ℝ ↦ y * I * g (y * I)) atTop (𝓝 (-1)))
    (h : ∀ y : ℝ, 0 < y →
      Tendsto (fun n ↦ resolventTransform (μ n) (y * I)) atTop (𝓝 (g (y * I)))) :
    IsTightMeasureSet (range μ) := by
  -- `y Im g(iy) → 1`, since it is minus the real part of `iy g(iy)`.
  have hgim : Tendsto (fun y : ℝ ↦ y * (g (y * I)).im) atTop (𝓝 1) := by
    have := ((continuous_re.tendsto _).comp hg).neg
    simpa [Function.comp_def] using this
  -- For `y > 0`, the tail bound passes to the limit.
  have hbound (y : ℝ) (hy : 0 < y) : limsup (fun n ↦ μ n {x | y < ‖x‖}) atTop ≤
      ENNReal.ofReal (2 * (1 - y * (g (y * I)).im)) := by
    have hlim : Tendsto (fun n ↦ ENNReal.ofReal
        (2 * (1 - y * (resolventTransform (μ n) (y * I)).im))) atTop
        (𝓝 (ENNReal.ofReal (2 * (1 - y * (g (y * I)).im)))) :=
      ENNReal.tendsto_ofReal
        ((((continuous_im.tendsto _).comp (h y hy)).const_mul y).const_sub 1 |>.const_mul 2)
    rw [← hlim.limsup_eq]
    refine limsup_le_limsup (Eventually.of_forall fun n ↦ ?_)
    rw [← ofReal_measureReal]
    gcongr
    calc (μ n).real {x | y < ‖x‖} ≤ (μ n).real {x | y ≤ |x|} :=
          measureReal_mono fun x hx ↦ le_of_lt (by simpa using hx)
      _ ≤ 2 * ((μ n).real univ - y * (resolventTransform (μ n) (y * I)).im) :=
          measureReal_le_abs_le_two_mul_sub_mul_im_resolventTransform hy
      _ = 2 * (1 - y * (resolventTransform (μ n) (y * I)).im) := by simp
  refine isTightMeasureSet_range_of_tendsto_limsup_measure_norm_gt ?_
  have hR : Tendsto (fun y : ℝ ↦ ENNReal.ofReal (2 * (1 - y * (g (y * I)).im))) atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal ((hgim.const_sub 1).const_mul 2)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hR
    (Eventually.of_forall fun _ ↦ zero_le) ((eventually_gt_atTop 0).mono hbound)

/-- If the resolvent transforms of probability measures `μᵢ` converge to those of a probability
measure `ν` on a set `D` whose closure contains the upper half-plane, then they converge at every
point of the upper half-plane. The transforms are uniformly Lipschitz on each half-plane
`Im z ≥ c > 0`. -/
theorem tendsto_resolventTransform_of_subset_closure {μ : ι → Measure ℝ}
    [∀ i, IsProbabilityMeasure (μ i)] {ν : Measure ℝ} [IsProbabilityMeasure ν] {D : Set ℂ}
    (hD : {z : ℂ | 0 < z.im} ⊆ closure D)
    (h : ∀ w ∈ D, Tendsto (fun i ↦ resolventTransform (μ i) w) l (𝓝 (resolventTransform ν w)))
    {z : ℂ} (hz : 0 < z.im) :
    Tendsto (fun i ↦ resolventTransform (μ i) z) l (𝓝 (resolventTransform ν z)) := by
  -- The transforms of all probability measures are equicontinuous at `z`.
  have hF : EquicontinuousAt
      (fun ρ : ProbabilityMeasure ℝ ↦ resolventTransform (ρ : Measure ℝ)) z := by
    refine Metric.equicontinuousAt_of_continuity_modulus
      (fun w ↦ ‖z - w‖ / (|z.im| * |w.im|)) ?_ _ ?_
    · have : Tendsto (fun w : ℂ ↦ ‖z - w‖ / (|z.im| * |w.im|)) (𝓝 z)
          (𝓝 (‖z - z‖ / (|z.im| * |z.im|))) :=
        ((tendsto_const_nhds.sub tendsto_id).norm.div
          (tendsto_const_nhds.mul (continuous_im.tendsto z).abs)
          (mul_ne_zero (abs_ne_zero.2 hz.ne') (abs_ne_zero.2 hz.ne')))
      simpa using this
    · filter_upwards [(continuous_im.tendsto z).eventually (lt_mem_nhds hz)] with w hw ρ
      simpa [dist_eq_norm] using
        norm_resolventTransform_sub_le (μ := (ρ : Measure ℝ)) hz.ne' hw.ne'
  exact (hF.comp fun i ↦ ⟨μ i, inferInstance⟩).tendsto_of_mem_closure
    ((hF.continuousAt ⟨ν, inferInstance⟩).mono_left nhdsWithin_le_nhds) h (hD hz)

namespace ProbabilityMeasure

/-- Weak convergence of probability measures on `ℝ` gives convergence of their resolvent
transforms at every point off the real axis. -/
theorem tendsto_resolventTransform_of_tendsto {μs : ι → ProbabilityMeasure ℝ}
    {μ : ProbabilityMeasure ℝ} (h : Tendsto μs l (𝓝 μ)) {z : ℂ} (hz : z.im ≠ 0) :
    Tendsto (fun i ↦ resolventTransform (μs i : Measure ℝ) z) l
      (𝓝 (resolventTransform (μ : Measure ℝ) z)) := by
  rw [tendsto_iff_forall_integral_rclike_tendsto ℂ] at h
  simpa only [resolventTransform_apply, BoundedContinuousFunction.coe_ofNormedAddCommGroup] using
    h (BoundedContinuousFunction.ofNormedAddCommGroup _ (Complex.continuous_resolvent_real hz) _
      (Complex.norm_resolvent_real_le z · hz))

/-- A tight family of probability measures on `ℝ` whose resolvent transforms converge on the
upper half-plane to the transform of a probability measure `μ` converges weakly to `μ`. -/
theorem tendsto_of_isTightMeasureSet_of_tendsto_resolventTransform
    {μs : ι → ProbabilityMeasure ℝ} {μ : ProbabilityMeasure ℝ}
    (h_tight : IsTightMeasureSet {(μs i : Measure ℝ) | i})
    (h : ∀ z : ℂ, 0 < z.im → Tendsto (fun i ↦ resolventTransform (μs i : Measure ℝ) z) l
      (𝓝 (resolventTransform (μ : Measure ℝ) z))) :
    Tendsto μs l (𝓝 μ) := by
  refine (tendsto_iff_ultrafilter _ _ _).2 fun U hU ↦ ?_
  have h_compact : IsCompact (closure {μs i | i}) :=
    isCompact_closure_of_isTightMeasureSet (by simpa using h_tight)
  obtain ⟨μ', -, hμ' : Tendsto _ _ _⟩ := h_compact.ultrafilter_le_nhds (U.map μs)
    (.trans (by simp) (monotone_principal subset_closure))
  -- The cluster point `μ'` has the limiting transforms, so it is `μ` by Stieltjes inversion.
  obtain rfl : μ' = μ := toMeasure_injective <| Measure.ext_of_resolventTransform fun z hz ↦
    tendsto_nhds_unique (tendsto_resolventTransform_of_tendsto hμ' hz.ne') ((h z hz).comp hU)
  exact hμ'

/-- **Weak convergence from resolvent transforms on a determining set.** Along a countably
generated filter, if the resolvent transforms of probability measures `μᵢ` on `ℝ` converge to
that of a probability measure `μ` on a set `D` whose closure contains the upper half-plane, then
`μᵢ → μ` weakly. -/
theorem tendsto_of_tendsto_resolventTransform_of_subset_closure [l.IsCountablyGenerated]
    {μs : ι → ProbabilityMeasure ℝ} {μ : ProbabilityMeasure ℝ} {D : Set ℂ}
    (hD : {z : ℂ | 0 < z.im} ⊆ closure D)
    (h : ∀ z ∈ D, Tendsto (fun i ↦ resolventTransform (μs i : Measure ℝ) z) l
      (𝓝 (resolventTransform (μ : Measure ℝ) z))) :
    Tendsto μs l (𝓝 μ) := by
  have h' (z : ℂ) (hz : 0 < z.im) := tendsto_resolventTransform_of_subset_closure hD h hz
  refine tendsto_of_seq_tendsto fun x hx ↦
    tendsto_of_isTightMeasureSet_of_tendsto_resolventTransform ?_ fun z hz ↦ (h' z hz).comp hx
  refine isTightMeasureSet_range_of_tendsto_resolventTransform
    (μ := fun n ↦ (μs (x n) : Measure ℝ)) (g := resolventTransform (μ : Measure ℝ)) ?_
    fun y hy ↦ (h' _ (by simpa using hy)).comp hx
  simpa using tendsto_mul_I_mul_resolventTransform (μ := (μ : Measure ℝ))

/-- **Weak convergence and resolvent transforms.** Along a countably generated filter,
probability measures on `ℝ` converge weakly if and only if their resolvent transforms converge
at every point of the upper half-plane to the transform of the limit. -/
theorem tendsto_iff_tendsto_resolventTransform [l.IsCountablyGenerated]
    {μs : ι → ProbabilityMeasure ℝ} {μ : ProbabilityMeasure ℝ} :
    Tendsto μs l (𝓝 μ) ↔ ∀ z : ℂ, 0 < z.im →
      Tendsto (fun i ↦ resolventTransform (μs i : Measure ℝ) z) l
        (𝓝 (resolventTransform (μ : Measure ℝ) z)) :=
  ⟨fun h _ hz ↦ tendsto_resolventTransform_of_tendsto h hz.ne',
    tendsto_of_tendsto_resolventTransform_of_subset_closure subset_closure⟩

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- **Almost sure weak convergence on a countable determining set.** Along a countably generated
filter, if for each `z` in a countable set `D` whose closure contains the upper half-plane the
resolvent transforms of random probability measures `μᵢ ω` converge almost surely to that of a
probability measure `μ`, then almost surely `μᵢ ω → μ` weakly. -/
theorem ae_tendsto_of_ae_tendsto_resolventTransform_of_subset_closure [l.IsCountablyGenerated]
    {μs : ι → Ω → ProbabilityMeasure ℝ} {μ : ProbabilityMeasure ℝ} {D : Set ℂ}
    (hDc : D.Countable) (hD : {z : ℂ | 0 < z.im} ⊆ closure D)
    (h : ∀ z ∈ D, ∀ᵐ ω ∂P, Tendsto (fun i ↦ resolventTransform (μs i ω : Measure ℝ) z) l
      (𝓝 (resolventTransform (μ : Measure ℝ) z))) :
    ∀ᵐ ω ∂P, Tendsto (fun i ↦ μs i ω) l (𝓝 μ) := by
  filter_upwards [(ae_ball_iff hDc).2 h] with ω hω
  exact tendsto_of_tendsto_resolventTransform_of_subset_closure hD hω

/-- **Almost sure weak convergence from resolvent transforms.** Along a countably generated
filter, if for each `z` in the upper half-plane the resolvent transforms of random probability
measures `μᵢ ω` converge almost surely to that of a probability measure `μ`, then almost surely
`μᵢ ω → μ` weakly. The exceptional null set may depend on `z`. -/
theorem ae_tendsto_of_ae_tendsto_resolventTransform [l.IsCountablyGenerated]
    {μs : ι → Ω → ProbabilityMeasure ℝ} {μ : ProbabilityMeasure ℝ}
    (h : ∀ z : ℂ, 0 < z.im → ∀ᵐ ω ∂P, Tendsto (fun i ↦ resolventTransform (μs i ω : Measure ℝ) z)
      l (𝓝 (resolventTransform (μ : Measure ℝ) z))) :
    ∀ᵐ ω ∂P, Tendsto (fun i ↦ μs i ω) l (𝓝 μ) := by
  obtain ⟨D, hDsub, hDc, hD⟩ := (TopologicalSpace.IsSeparable.of_separableSpace
    {z : ℂ | 0 < z.im}).exists_countable_dense_subset
  exact ae_tendsto_of_ae_tendsto_resolventTransform_of_subset_closure hDc hD
    fun z hz ↦ h z (hDsub hz)

end ProbabilityMeasure

end MeasureTheory

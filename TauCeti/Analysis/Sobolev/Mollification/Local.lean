/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.Convolution
public import Mathlib.Topology.UniformSpace.UniformConvergence
public import TauCeti.Analysis.Sobolev.WeakDeriv.Basic

import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Group.Integral
import TauCeti.Analysis.Calculus.BumpFunction.Convolution
import TauCeti.Analysis.Sobolev.Mollification.Interior
import TauCeti.Analysis.Sobolev.WeakDeriv.Lipschitz
import TauCeti.MeasureTheory.Function.Lp.ApproximateIdentity

/-!
# Local smooth approximation of weakly differentiable functions by mollification

Let `Ω` be an open subset of a finite-dimensional real normed space `E` with an additive Haar
measure `μ`, and let `u : E → F` have weak Fréchet derivative `Du` on `Ω`, with values in a real
Banach space `F`. Extending `u` by zero outside an open subset `V` with compact closure in `Ω` and
convolving with a normalized smooth bump `φ.normed μ` produces a globally smooth function whose
Fréchet derivative agrees with `φ.normed μ ⋆ V.indicator Du` at every point whose `φ.rOut`-closed
ball lies in `V`, and whose `Lᵖ` seminorm on any measurable subset of such points is at most
`‖Du‖_{Lᵖ(V)}`.

As the outer radii of the bumps shrink to zero, these mollifications converge to `u` and their
derivatives converge to `Du` in `Lᵖ(U)` for every `1 ≤ p < ∞` and every open `U` with compact
closure inside `V ≤ Ω` (provided `u` and `Du` lie in `Lᵖ(V)`). If `u` is continuous on `Ω`, the
mollifications also converge uniformly to `u` on `closure U`.

The absolute value `x ↦ |x|` on `ℝ` illustrates the endpoint behaviour: its mollifications are
smooth, agree identically with `|x|` for `|x| ≥ φ.rOut` by symmetry of the bump, and have
derivatives converging to `sign` in `Lᵖ(K)` for every `1 ≤ p < ∞` and compact `K`, while any
function continuous at `0` — in particular the derivative of any mollification — stays at
`L^∞(B(0, r))` distance at least `1` from `sign`.

## Main declarations

* `TauCeti.HasWeakFDerivOn.contDiff_normed_convolution_indicator`: smoothness of the zero-extended
  mollification.
* `TauCeti.HasWeakFDerivOn.hasFDerivAt_normed_convolution_indicator` and
  `TauCeti.HasWeakFDerivOn.fderiv_normed_convolution_indicator`: the derivative of the
  mollification is the mollification of the weak derivative where the ball fits in `V`.
* `TauCeti.HasWeakFDerivOn.eLpNorm_fderiv_normed_convolution_indicator_le`: `Lᵖ` gradient bound
  `‖D(φ ⋆ V.indicator u)‖_{Lᵖ(s)} ≤ ‖Du‖_{Lᵖ(V)}` for `1 ≤ p < ∞`.
* `TauCeti.HasWeakFDerivOn.tendsto_eLpNorm_fderiv_normed_convolution_indicator_sub`: `Lᵖ`
  convergence of the derivatives of the mollifications for `1 ≤ p < ∞`.
* `TauCeti.HasWeakFDerivOn.exists_smooth_approx_memLp` and
  `TauCeti.HasWeakFDerivOn.exists_smooth_approx_continuousOn`: packaged local smooth
  approximations on a relatively compact open subdomain.
* `TauCeti.hasWeakFDerivOn_abs`, `TauCeti.normed_convolution_abs_eq_of_le_abs`,
  `TauCeti.fderiv_normed_convolution_abs_apply`,
  `TauCeti.tendsto_eLpNorm_fderiv_normed_convolution_abs_sub`,
  `TauCeti.one_le_eLpNorm_top_sub_sign_of_continuousAt`, and
  `TauCeti.one_le_eLpNorm_top_fderiv_normed_convolution_abs_sub`: the `|x|` example on `ℝ`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Chapter 5, §5.3.1, Theorem 1.
* W. Arendt and M. Kreuter, *Mapping theorems for Sobolev spaces of vector-valued functions*,
  Studia Math. **240** (2018), §2.
-/

public section

noncomputable section

open ContinuousLinearMap Filter MeasureTheory Metric Set TopologicalSpace
open scoped ContDiff Convolution ENNReal Topology

namespace TauCeti

section LocalMollification

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {Ω : Opens E} {u : E → F} {Du : E → E →L[ℝ] F}

/-- **Smoothness of the interior mollification.** If `u` has a weak Fréchet derivative on `Ω` and
`V` is an open set with compact closure in `Ω`, then convolving the zero extension of `u` from `V`
with a normalized smooth bump yields a globally smooth function. -/
theorem HasWeakFDerivOn.contDiff_normed_convolution_indicator (hu : HasWeakFDerivOn μ Ω u Du)
    {V : Opens E} (hVc : IsCompact (closure (V : Set E))) (hVΩ : closure (V : Set E) ⊆ Ω)
    (φ : ContDiffBump (0 : E)) :
    ContDiff ℝ ∞ (φ.normed μ ⋆[lsmul ℝ ℝ, μ] (V : Set E).indicator u) := by
  have : CompleteSpace F := hu.completeSpace
  have huV : Integrable ((V : Set E).indicator u) μ :=
    ((hu.locallyIntegrableOn.integrableOn_compact_subset hVΩ hVc).mono_set
      subset_closure).integrable_indicator V.isOpen.measurableSet
  exact φ.hasCompactSupport_normed.contDiff_convolution_left (lsmul ℝ ℝ) φ.contDiff_normed
    huV.locallyIntegrable

/-- **Derivative of the interior mollification.** On an open set `V` with compact closure in `Ω`,
the Fréchet derivative of `φ.normed μ ⋆ V.indicator u` at any point `x` with
`closedBall x φ.rOut ⊆ V` is `(φ.normed μ ⋆ V.indicator Du) x`. -/
theorem HasWeakFDerivOn.hasFDerivAt_normed_convolution_indicator (hu : HasWeakFDerivOn μ Ω u Du)
    {V : Opens E} (hVc : IsCompact (closure (V : Set E))) (hVΩ : closure (V : Set E) ⊆ Ω)
    (φ : ContDiffBump (0 : E)) {x : E} (hx : closedBall x φ.rOut ⊆ V) :
    HasFDerivAt (φ.normed μ ⋆[lsmul ℝ ℝ, μ] (V : Set E).indicator u)
      ((φ.normed μ ⋆[lsmul ℝ ℝ, μ] (V : Set E).indicator Du) x) x := by
  have huV : MemLp u 1 (μ.restrict V) := memLp_one_iff_integrable.2 <|
    (hu.locallyIntegrableOn.integrableOn_compact_subset hVΩ hVc).mono_set subset_closure
  have hDuV : MemLp Du 1 (μ.restrict V) := memLp_one_iff_integrable.2 <|
    (hu.locallyIntegrableOn_deriv.integrableOn_compact_subset hVΩ hVc).mono_set subset_closure
  have h := (hu.mono (subset_closure.trans hVΩ)).hasFDerivAt_indicator_convolution_normed
    huV hDuV le_rfl le_rfl φ x hx
  simpa only [convolution_flip] using h

/-- **Fréchet derivative equation for the interior mollification.** At any point `x` with
`closedBall x φ.rOut ⊆ V`, the Fréchet derivative of `φ.normed μ ⋆ V.indicator u` equals
`(φ.normed μ ⋆ V.indicator Du) x`. -/
theorem HasWeakFDerivOn.fderiv_normed_convolution_indicator (hu : HasWeakFDerivOn μ Ω u Du)
    {V : Opens E} (hVc : IsCompact (closure (V : Set E))) (hVΩ : closure (V : Set E) ⊆ Ω)
    (φ : ContDiffBump (0 : E)) {x : E} (hx : closedBall x φ.rOut ⊆ V) :
    fderiv ℝ (φ.normed μ ⋆[lsmul ℝ ℝ, μ] (V : Set E).indicator u) x =
      (φ.normed μ ⋆[lsmul ℝ ℝ, μ] (V : Set E).indicator Du) x :=
  (hu.hasFDerivAt_normed_convolution_indicator hVc hVΩ φ hx).fderiv

/-- **`Lᵖ` gradient bound for interior mollifications.** If `V` has compact closure in `Ω`,
`Du ∈ Lᵖ(V)` for `1 ≤ p < ∞`, and every point of a measurable set `s` has `closedBall x φ.rOut ⊆ V`,
then `‖D(φ.normed μ ⋆ V.indicator u)‖_{Lᵖ(s)} ≤ ‖Du‖_{Lᵖ(V)}`. -/
theorem HasWeakFDerivOn.eLpNorm_fderiv_normed_convolution_indicator_le
    (hu : HasWeakFDerivOn μ Ω u Du) {V : Opens E} (hVc : IsCompact (closure (V : Set E)))
    (hVΩ : closure (V : Set E) ⊆ Ω) {s : Set E} (hs : MeasurableSet s)
    (φ : ContDiffBump (0 : E)) (hball : ∀ x ∈ s, closedBall x φ.rOut ⊆ V) {p : ℝ≥0∞}
    (hp1 : 1 ≤ p) (hp : p ≠ (∞ : ℝ≥0∞)) (hDu : MemLp Du p (μ.restrict V)) :
    eLpNorm (fderiv ℝ (φ.normed μ ⋆[lsmul ℝ ℝ, μ] (V : Set E).indicator u)) p (μ.restrict s) ≤
      eLpNorm Du p (μ.restrict V) := by
  have : CompleteSpace F := hu.completeSpace
  have : Fact (1 ≤ p) := ⟨hp1⟩
  have hDext : MemLp ((V : Set E).indicator Du) p μ :=
    (memLp_indicator_iff_restrict (f := Du) V.isOpen.measurableSet.nullMeasurableSet).2 hDu
  have heq : fderiv ℝ (φ.normed μ ⋆[lsmul ℝ ℝ, μ] (V : Set E).indicator u) =ᵐ[μ.restrict s]
      φ.normed μ ⋆[lsmul ℝ ℝ, μ] (V : Set E).indicator Du :=
    (ae_restrict_mem hs).mono fun x hx =>
      hu.fderiv_normed_convolution_indicator hVc hVΩ φ (hball x hx)
  calc eLpNorm (fderiv ℝ (φ.normed μ ⋆[lsmul ℝ ℝ, μ] (V : Set E).indicator u)) p (μ.restrict s)
      = eLpNorm (φ.normed μ ⋆[lsmul ℝ ℝ, μ] (V : Set E).indicator Du) p (μ.restrict s) :=
        eLpNorm_congr_ae heq
    _ ≤ eLpNorm (φ.normed μ ⋆[lsmul ℝ ℝ, μ] (V : Set E).indicator Du) p μ :=
        eLpNorm_mono_measure _ Measure.restrict_le_self
    _ ≤ eLpNorm ((V : Set E).indicator Du) p μ := eLpNorm_normed_convolution_le hp φ hDext
    _ = eLpNorm Du p (μ.restrict V) :=
        eLpNorm_indicator_eq_eLpNorm_restrict (f := Du) V.isOpen.measurableSet.nullMeasurableSet

/-- **`Lᵖ` convergence of the derivatives of interior mollifications.** For `1 ≤ p < ∞`, if
`thickening δ s ⊆ V` where `V` has compact closure in `Ω` and `Du ∈ Lᵖ(V)`, then the derivatives
of `φᵢ.normed μ ⋆ V.indicator u` converge to `Du` in `Lᵖ(s)` as `(φᵢ).rOut → 0`. -/
theorem HasWeakFDerivOn.tendsto_eLpNorm_fderiv_normed_convolution_indicator_sub
    (hu : HasWeakFDerivOn μ Ω u Du) {V : Opens E} (hVc : IsCompact (closure (V : Set E)))
    (hVΩ : closure (V : Set E) ⊆ Ω) {s : Set E} {δ : ℝ} (hδ : 0 < δ)
    (hsV : thickening δ s ⊆ V) {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ (∞ : ℝ≥0∞))
    (hDu : MemLp Du p (μ.restrict V)) {ι : Type*} {l : Filter ι}
    {φ : ι → ContDiffBump (0 : E)} (hφ : Tendsto (fun i => (φ i).rOut) l (𝓝 0)) :
    Tendsto (fun i => eLpNorm
      (fderiv ℝ ((φ i).normed μ ⋆[lsmul ℝ ℝ, μ] (V : Set E).indicator u) - Du) p
      (μ.restrict s)) l (𝓝 0) := by
  have : CompleteSpace F := hu.completeSpace
  have : Fact (1 ≤ p) := ⟨hp1⟩
  have hDext : MemLp ((V : Set E).indicator Du) p μ :=
    (memLp_indicator_iff_restrict (f := Du) V.isOpen.measurableSet.nullMeasurableSet).2 hDu
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (tendsto_eLpNorm_normed_convolution_sub hp hφ hDext) (.of_forall fun _ => zero_le) ?_
  filter_upwards [hφ.eventually (gt_mem_nhds hδ)] with i hi
  have heq : fderiv ℝ ((φ i).normed μ ⋆[lsmul ℝ ℝ, μ] (V : Set E).indicator u) - Du
      =ᵐ[μ.restrict s]
      (φ i).normed μ ⋆[lsmul ℝ ℝ, μ] (V : Set E).indicator Du - (V : Set E).indicator Du := by
    filter_upwards [(ae_restrict_mem isClosed_closure.measurableSet).filter_mono
      (ae_mono (Measure.restrict_mono_set μ subset_closure))] with x hx
    have hxV : x ∈ (V : Set E) := hsV (thickening_closure (δ := δ) (s := s) ▸
      self_subset_thickening hδ (closure s) hx)
    have hball : closedBall x (φ i).rOut ⊆ V := fun y hy => hsV <| by
      rw [← thickening_closure]
      exact mem_thickening_iff.2 ⟨x, hx, (mem_closedBall.1 hy).trans_lt hi⟩
    simp only [Pi.sub_apply, indicator_of_mem hxV,
      hu.fderiv_normed_convolution_indicator hVc hVΩ (φ i) hball]
  exact (eLpNorm_congr_ae heq).trans_le (eLpNorm_mono_measure _ Measure.restrict_le_self)

/-- **Local smooth approximation in `W^{1,p}`.** Let `u` have weak Fréchet derivative `Du` on `Ω`,
let `U` be an open set with compact closure inside an open `V ≤ Ω`, and let `u, Du ∈ Lᵖ(V)` for
`1 ≤ p < ∞`. Then there is a sequence of globally smooth functions `uₙ` converging to `u` in
`Lᵖ(U)` whose derivatives converge to `Du` in `Lᵖ(U)` and satisfy `‖Duₙ‖_{Lᵖ(U)} ≤ ‖Du‖_{Lᵖ(V)}`. -/
theorem HasWeakFDerivOn.exists_smooth_approx_memLp (hu : HasWeakFDerivOn μ Ω u Du)
    {U V : Opens E} (hUc : IsCompact (closure (U : Set E))) (hUV : closure (U : Set E) ⊆ V)
    (hVΩ : V ≤ Ω) {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ (∞ : ℝ≥0∞))
    (hup : MemLp u p (μ.restrict V)) (hDup : MemLp Du p (μ.restrict V)) :
    ∃ un : ℕ → E → F, (∀ n, ContDiff ℝ ∞ (un n)) ∧
      (∀ n, eLpNorm (fderiv ℝ (un n)) p (μ.restrict U) ≤ eLpNorm Du p (μ.restrict V)) ∧
      Tendsto (fun n => eLpNorm (un n - u) p (μ.restrict U)) atTop (𝓝 0) ∧
      Tendsto (fun n => eLpNorm (fderiv ℝ (un n) - Du) p (μ.restrict U)) atTop (𝓝 0) := by
  have : CompleteSpace F := hu.completeSpace
  have : Fact (1 ≤ p) := ⟨hp1⟩
  obtain ⟨δ, hδ, hδV⟩ := hUc.exists_cthickening_subset_open V.isOpen hUV
  let W : Opens E := ⟨thickening δ (closure (U : Set E)), isOpen_thickening⟩
  have hclW : closure (W : Set E) ⊆ V :=
    (closure_thickening_subset_cthickening _ _).trans hδV
  have hWc : IsCompact (closure (W : Set E)) := hUc.isBounded.thickening.isCompact_closure
  have hWΩ : closure (W : Set E) ⊆ Ω := hclW.trans hVΩ
  have hUW : thickening δ (U : Set E) ⊆ W := (thickening_closure (δ := δ) (s := (U : Set E))).ge
  let φ : ℕ → ContDiffBump (0 : E) := ContDiffBump.shrinking (half_pos hδ)
  have hφ : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0) :=
    ContDiffBump.tendsto_rOut_shrinking (half_pos hδ)
  have hDuW : MemLp Du p (μ.restrict W) :=
    hDup.mono_measure (Measure.restrict_mono (subset_closure.trans hclW) le_rfl)
  have huW : MemLp u p (μ.restrict W) :=
    hup.mono_measure (Measure.restrict_mono (subset_closure.trans hclW) le_rfl)
  refine ⟨fun n => (φ n).normed μ ⋆[lsmul ℝ ℝ, μ] (W : Set E).indicator u,
    fun n => hu.contDiff_normed_convolution_indicator hWc hWΩ (φ n), fun n => ?_,
    tendsto_eLpNorm_normed_convolution_indicator_sub hp hφ W.isOpen.measurableSet
      ((self_subset_thickening hδ _).trans hUW) huW,
    hu.tendsto_eLpNorm_fderiv_normed_convolution_indicator_sub hWc hWΩ hδ hUW hp1 hp hDuW hφ⟩
  have hball : ∀ x ∈ (U : Set E), closedBall x (φ n).rOut ⊆ W := fun x hx y hy =>
    mem_thickening_iff.2 ⟨x, subset_closure hx, (mem_closedBall.1 hy).trans_lt <| by
      simp only [φ, ContDiffBump.rOut_shrinking]
      exact (div_le_self (half_pos hδ).le (by linarith [n.cast_nonneg' (α := ℝ)])).trans_lt
        (half_lt_self hδ)⟩
  exact (hu.eLpNorm_fderiv_normed_convolution_indicator_le hWc hWΩ U.isOpen.measurableSet (φ n)
    hball hp1 hp hDuW).trans
    (eLpNorm_mono_measure _ (Measure.restrict_mono (subset_closure.trans hclW) le_rfl))

/-- **Local smooth approximation in `W^{1,p}` and uniformly on `closure U` for continuous `u`.** -/
theorem HasWeakFDerivOn.exists_smooth_approx_continuousOn (hu : HasWeakFDerivOn μ Ω u Du)
    (huc : ContinuousOn u Ω) {U V : Opens E} (hUc : IsCompact (closure (U : Set E)))
    (hUV : closure (U : Set E) ⊆ V) (hVΩ : V ≤ Ω) {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ (∞ : ℝ≥0∞))
    (hDup : MemLp Du p (μ.restrict V)) :
    ∃ un : ℕ → E → F, (∀ n, ContDiff ℝ ∞ (un n)) ∧
      TendstoUniformlyOn un u atTop (closure (U : Set E)) ∧
      (∀ n, eLpNorm (fderiv ℝ (un n)) p (μ.restrict U) ≤ eLpNorm Du p (μ.restrict V)) ∧
      Tendsto (fun n => eLpNorm (un n - u) p (μ.restrict U)) atTop (𝓝 0) ∧
      Tendsto (fun n => eLpNorm (fderiv ℝ (un n) - Du) p (μ.restrict U)) atTop (𝓝 0) := by
  have : CompleteSpace F := hu.completeSpace
  have : Fact (1 ≤ p) := ⟨hp1⟩
  obtain ⟨δ, hδ, hδV⟩ := hUc.exists_cthickening_subset_open V.isOpen hUV
  let W : Opens E := ⟨thickening δ (closure (U : Set E)), isOpen_thickening⟩
  have hclW : closure (W : Set E) ⊆ V :=
    (closure_thickening_subset_cthickening _ _).trans hδV
  have hWc : IsCompact (closure (W : Set E)) := hUc.isBounded.thickening.isCompact_closure
  have hWΩ : closure (W : Set E) ⊆ Ω := hclW.trans hVΩ
  have hUW : thickening δ (U : Set E) ⊆ W := (thickening_closure (δ := δ) (s := (U : Set E))).ge
  let φ : ℕ → ContDiffBump (0 : E) := ContDiffBump.shrinking (half_pos hδ)
  have hφ : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0) :=
    ContDiffBump.tendsto_rOut_shrinking (half_pos hδ)
  have huW : MemLp u p (μ.restrict W) := by
    obtain ⟨C, hC⟩ := hWc.exists_bound_of_continuousOn (huc.mono hWΩ)
    have : IsFiniteMeasure (μ.restrict (closure (W : Set E))) :=
      isFiniteMeasure_restrict.2 hWc.measure_lt_top.ne
    have hmem : MemLp u ∞ (μ.restrict (closure (W : Set E))) :=
      memLp_top_of_bound ((huc.mono hWΩ).aestronglyMeasurable isClosed_closure.measurableSet) C
        ((ae_restrict_mem isClosed_closure.measurableSet).mono hC)
    exact (hmem.mono_exponent le_top).mono_measure (Measure.restrict_mono subset_closure le_rfl)
  have hDuW : MemLp Du p (μ.restrict W) :=
    hDup.mono_measure (Measure.restrict_mono (subset_closure.trans hclW) le_rfl)
  refine ⟨fun n => (φ n).normed μ ⋆[lsmul ℝ ℝ, μ] (W : Set E).indicator u,
    fun n => hu.contDiff_normed_convolution_indicator hWc hWΩ (φ n),
    ContDiffBump.tendstoUniformlyOn_normed_convolution_indicator W.isOpen.measurableSet hWc
      (huc.mono hWΩ) hδ subset_rfl hφ,
    fun n => ?_,
    tendsto_eLpNorm_normed_convolution_indicator_sub hp hφ W.isOpen.measurableSet
      ((self_subset_thickening hδ _).trans hUW) huW,
    hu.tendsto_eLpNorm_fderiv_normed_convolution_indicator_sub hWc hWΩ hδ hUW hp1 hp hDuW hφ⟩
  have hball : ∀ x ∈ (U : Set E), closedBall x (φ n).rOut ⊆ W := fun x hx y hy =>
    mem_thickening_iff.2 ⟨x, subset_closure hx, (mem_closedBall.1 hy).trans_lt <| by
      simp only [φ, ContDiffBump.rOut_shrinking]
      exact (div_le_self (half_pos hδ).le (by linarith [n.cast_nonneg' (α := ℝ)])).trans_lt
        (half_lt_self hδ)⟩
  exact (hu.eLpNorm_fderiv_normed_convolution_indicator_le hWc hWΩ U.isOpen.measurableSet (φ n)
    hball hp1 hp hDuW).trans
    (eLpNorm_mono_measure _ (Measure.restrict_mono (subset_closure.trans hclW) le_rfl))

end LocalMollification

/-! ### Check: mollification of `|x|` on `ℝ` -/

section AbsCheck

/-- The absolute value on `ℝ` has weak Fréchet derivative `x ↦ (SignType.sign x : ℝ) • id`. -/
theorem hasWeakFDerivOn_abs :
    HasWeakFDerivOn (volume : Measure ℝ) ⊤ (abs : ℝ → ℝ)
      fun x => (SignType.sign x : ℝ) • ContinuousLinearMap.id ℝ ℝ := by
  have hlip : LocallyLipschitzOn (⊤ : Opens ℝ) (abs : ℝ → ℝ) :=
    (LipschitzWith.of_dist_le_mul (K := 1) fun x y => by
      simpa [Real.dist_eq] using abs_abs_sub_abs_le x y).locallyLipschitz.locallyLipschitzOn
  refine hlip.hasWeakFDerivOn ?_
  have hne : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := by rw [ae_iff]; simp
  filter_upwards [hne] with x hx _
  exact (hasFDerivAt_id x).abs hx

/-- Away from the origin (`φ.rOut ≤ |x|`), convolving `|·|` with a normalized smooth bump centred
at `0` reproduces `|x|` identically, because the bump is symmetric and `|·|` is affine on each
half-line. -/
theorem normed_convolution_abs_eq_of_le_abs {φ : ContDiffBump (0 : ℝ)} {x : ℝ}
    (hx : φ.rOut ≤ |x|) :
    (φ.normed volume ⋆[lsmul ℝ ℝ, volume] (abs : ℝ → ℝ)) x = |x| := by
  have hodd : ∫ y : ℝ, φ.normed volume y * y ∂volume = 0 := by
    have hneg := integral_neg_eq_self (fun y : ℝ => φ.normed volume y * y) (volume : Measure ℝ)
    simp only [φ.normed_neg, mul_neg, integral_neg] at hneg
    linarith
  have hint_id : Integrable (fun y : ℝ => φ.normed volume y * y) volume :=
    (φ.continuous_normed.mul continuous_id).integrable_of_hasCompactSupport
      φ.hasCompactSupport_normed.mul_right
  have hint_const : Integrable (fun y : ℝ => φ.normed volume y * x) volume :=
    φ.integrable_normed.mul_const x
  rcases le_or_gt 0 x with hx0 | hx0
  · rw [abs_of_nonneg hx0] at hx ⊢
    have hcongr : ∀ y : ℝ, φ.normed volume y * |x - y| =
        φ.normed volume y * x - φ.normed volume y * y := fun y => by
      by_cases hy : y ∈ ball (0 : ℝ) φ.rOut
      · rw [mem_ball_zero_iff, Real.norm_eq_abs] at hy
        rw [abs_of_nonneg (by linarith [(abs_le.1 hy.le).2]), mul_sub]
      · rw [← φ.support_normed_eq (μ := volume), Function.notMem_support] at hy
        simp [hy]
    simp only [convolution_def, lsmul_apply, smul_eq_mul, hcongr]
    rw [integral_sub hint_const hint_id, integral_mul_const, φ.integral_normed, one_mul, hodd,
      sub_zero]
  · rw [abs_of_neg hx0] at hx ⊢
    have hcongr : ∀ y : ℝ, φ.normed volume y * |x - y| =
        φ.normed volume y * y - φ.normed volume y * x := fun y => by
      by_cases hy : y ∈ ball (0 : ℝ) φ.rOut
      · rw [mem_ball_zero_iff, Real.norm_eq_abs] at hy
        rw [abs_of_nonpos (by linarith [(abs_le.1 hy.le).1])]
        ring
      · rw [← φ.support_normed_eq (μ := volume), Function.notMem_support] at hy
        simp [hy]
    simp only [convolution_def, lsmul_apply, smul_eq_mul, hcongr]
    rw [integral_sub hint_id hint_const, hodd, integral_mul_const, φ.integral_normed, one_mul,
      zero_sub]

/-- The derivative of `φ.normed volume ⋆ |·|` is `φ.normed volume ⋆ sign`. -/
theorem fderiv_normed_convolution_abs_apply (φ : ContDiffBump (0 : ℝ)) (x : ℝ) :
    fderiv ℝ (φ.normed volume ⋆[lsmul ℝ ℝ, volume] (abs : ℝ → ℝ)) x 1 =
      (φ.normed volume ⋆[lsmul ℝ ℝ, volume] fun y : ℝ => (SignType.sign y : ℝ)) x := by
  have hmeas : Measurable fun y : ℝ => (SignType.sign y : ℝ) := by
    simpa only [← deriv_abs] using measurable_deriv (abs : ℝ → ℝ)
  have hDu_loc : LocallyIntegrable
      (fun y : ℝ => (SignType.sign y : ℝ) • ContinuousLinearMap.id ℝ ℝ) volume :=
    (memLp_top_of_bound (hmeas.aestronglyMeasurable.smul aestronglyMeasurable_const) 1
      (.of_forall fun y => by
        change ‖(SignType.sign y : ℝ) • ContinuousLinearMap.id ℝ ℝ‖ ≤ 1
        rw [norm_smul, ContinuousLinearMap.norm_id, mul_one, Real.norm_eq_abs]
        cases SignType.sign y <;> norm_num)).locallyIntegrable le_top
  have h := hasWeakFDerivOn_abs.fderiv_convolution_right continuous_abs.locallyIntegrable hDu_loc
    (φ.normed volume) φ.contDiff_normed φ.hasCompactSupport_normed x (fun _ _ => trivial)
  rw [convolution_flip, convolution_flip] at h
  rw [h]
  have hint : Integrable (fun t : ℝ => φ.normed volume t •
      ((SignType.sign (x - t) : ℝ) • ContinuousLinearMap.id ℝ ℝ)) volume :=
    φ.hasCompactSupport_normed.convolutionExists_left (lsmul ℝ ℝ) φ.continuous_normed hDu_loc x
  simp only [convolution_def, lsmul_apply]
  rw [ContinuousLinearMap.integral_apply hint]
  simp only [smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul, mul_one]

/-- On every compact set `K ⊆ ℝ` and for every `1 ≤ p < ∞`, the derivatives of the mollifications
of `|·|` converge to `sign` in `Lᵖ(K)`. -/
theorem tendsto_eLpNorm_fderiv_normed_convolution_abs_sub {K : Set ℝ} (hK : IsCompact K)
    {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ (∞ : ℝ≥0∞)) {ι : Type*} {l : Filter ι}
    {φ : ι → ContDiffBump (0 : ℝ)} (hφ : Tendsto (fun i => (φ i).rOut) l (𝓝 0)) :
    Tendsto (fun i => eLpNorm
      (fun x => fderiv ℝ ((φ i).normed volume ⋆[lsmul ℝ ℝ, volume] (abs : ℝ → ℝ)) x 1 -
        (SignType.sign x : ℝ)) p (volume.restrict K)) l (𝓝 0) := by
  have : Fact (1 ≤ p) := ⟨hp1⟩
  have hmeas : Measurable fun y : ℝ => (SignType.sign y : ℝ) := by
    simpa only [← deriv_abs] using measurable_deriv (abs : ℝ → ℝ)
  have hmem : MemLp (fun y : ℝ => (SignType.sign y : ℝ)) p
      (volume.restrict (thickening 1 K)) := by
    have : IsFiniteMeasure (volume.restrict (thickening 1 K)) :=
      isFiniteMeasure_restrict.2
        ((measure_mono (thickening_subset_cthickening 1 K)).trans_lt
          hK.cthickening.measure_lt_top).ne
    exact (memLp_top_of_bound hmeas.aestronglyMeasurable 1 (.of_forall fun y => by
      rw [Real.norm_eq_abs]
      cases SignType.sign y <;> norm_num)).mono_exponent le_top
  refine (tendsto_eLpNorm_normed_convolution_sub_restrict hp hφ one_pos hmem).congr fun i => ?_
  congr 1
  ext x
  exact (fderiv_normed_convolution_abs_apply (φ i) x).symm ▸ rfl

/-- Any real function continuous at `0` stays at `L^∞(B(0, r))` distance at least `1` from `sign`
for every `r > 0`. -/
theorem one_le_eLpNorm_top_sub_sign_of_continuousAt {g : ℝ → ℝ} (hg : ContinuousAt g 0)
    {r : ℝ} (hr : 0 < r) :
    1 ≤ eLpNorm (fun x : ℝ => g x - (SignType.sign x : ℝ)) ∞ (volume.restrict (ball 0 r)) := by
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hε0 : 0 < (ε : ℝ) := NNReal.coe_pos.2 hε
  obtain ⟨δ, hδ, hδg⟩ := Metric.continuousAt_iff.1 hg (ε : ℝ) hε0
  set η := min δ r
  have hη : 0 < η := lt_min hδ hr
  set c : ℝ≥0∞ := eLpNorm (fun x => g x - (SignType.sign x : ℝ)) ∞ (volume.restrict (ball 0 r))
  have hae : ∀ᵐ x ∂volume.restrict (ball (0 : ℝ) r), ‖g x - (SignType.sign x : ℝ)‖ₑ ≤ c :=
    ae_le_eLpNormEssSup.mono fun x hx => hx.trans eLpNormEssSup_le_eLpNorm_top
  have hstep {a b s : ℝ} (hab : a < b) (hsub : Ioo a b ⊆ ball (0 : ℝ) r)
      (hsign : ∀ x ∈ Ioo a b, (SignType.sign x : ℝ) = s)
      (hclose : ∀ x ∈ Ioo a b, |g x - g 0| < ε) (hgap : (1 : ℝ) ≤ |g 0 - s|) :
      (1 : ℝ≥0∞) ≤ c + ε := by
    have hpos : volume (Ioo a b) ≠ 0 := by simp [Real.volume_Ioo, hab]
    obtain ⟨x, hxIoo, hxc⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hpos
      (ae_restrict_of_ae_restrict_of_subset hsub hae)
    have h1 : (1 : ℝ) ≤ |g x - (SignType.sign x : ℝ)| + ε := by
      have htri : |g 0 - s| ≤ |g 0 - g x| + |g x - s| := abs_sub_le _ _ _
      rw [abs_sub_comm (g 0) (g x)] at htri
      rw [hsign x hxIoo]
      linarith [hclose x hxIoo]
    calc (1 : ℝ≥0∞) = ENNReal.ofReal 1 := by simp
      _ ≤ ENNReal.ofReal (|g x - (SignType.sign x : ℝ)| + ε) := ENNReal.ofReal_le_ofReal h1
      _ = ‖g x - (SignType.sign x : ℝ)‖ₑ + ε := by
          rw [ENNReal.ofReal_add (abs_nonneg _) hε0.le, ← Real.norm_eq_abs, ofReal_norm,
            ENNReal.ofReal_coe_nnreal]
      _ ≤ c + ε := by gcongr
  rcases le_or_gt (g 0) 0 with hg0 | hg0
  · refine hstep hη (fun x hx => by
        rw [mem_ball_zero_iff, Real.norm_eq_abs, abs_of_pos hx.1]
        exact hx.2.trans_le (min_le_right _ _))
      (fun x hx => by rw [sign_pos hx.1, SignType.coe_one])
      (fun x hx => hδg <| by
        rw [Real.dist_eq, sub_zero, abs_of_pos hx.1]
        exact hx.2.trans_le (min_le_left _ _))
      (by linarith [neg_le_abs (g 0 - 1)])
  · refine hstep (neg_lt_zero.2 hη) (fun x hx => by
        rw [mem_ball_zero_iff, Real.norm_eq_abs, abs_of_neg hx.2]
        linarith [hx.1, min_le_right δ r])
      (fun x hx => by rw [sign_neg hx.2, SignType.coe_neg, SignType.coe_one])
      (fun x hx => hδg <| by
        rw [Real.dist_eq, sub_zero, abs_of_neg hx.2]
        linarith [hx.1, min_le_left δ r])
      (by linarith [le_abs_self (g 0 - (-1))])

/-- The derivatives of the mollifications of `|·|` do not converge to `sign` in `L^∞` near `0`:
they stay at `L^∞(B(0, r))` distance at least `1` from `sign` for every `r > 0`. -/
theorem one_le_eLpNorm_top_fderiv_normed_convolution_abs_sub {r : ℝ} (hr : 0 < r)
    (φ : ContDiffBump (0 : ℝ)) :
    1 ≤ eLpNorm (fun x : ℝ => fderiv ℝ (φ.normed volume ⋆[lsmul ℝ ℝ, volume] (abs : ℝ → ℝ)) x 1 -
      (SignType.sign x : ℝ)) ∞ (volume.restrict (ball 0 r)) := by
  have hsm : ContDiff ℝ ∞ (φ.normed volume ⋆[lsmul ℝ ℝ, volume] (abs : ℝ → ℝ)) :=
    φ.hasCompactSupport_normed.contDiff_convolution_left (lsmul ℝ ℝ) φ.contDiff_normed
      continuous_abs.locallyIntegrable
  exact one_le_eLpNorm_top_sub_sign_of_continuousAt
    ((hsm.continuous_fderiv (by simp)).clm_apply continuous_const).continuousAt hr

end AbsCheck

end TauCeti

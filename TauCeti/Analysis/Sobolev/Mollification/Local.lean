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
public import TauCeti.MeasureTheory.Function.MemLpLoc

import TauCeti.Analysis.Calculus.BumpFunction.Convolution
import TauCeti.Analysis.Sobolev.Mollification.Interior
import TauCeti.MeasureTheory.Function.LocallyIntegrable
import TauCeti.MeasureTheory.Function.Lp.ApproximateIdentity
import TauCeti.MeasureTheory.Function.LpSeminorm.ContinuousOn

/-!
# Local smooth approximation of weakly differentiable functions by mollification

Let `Ω` be an open subset of a finite-dimensional real normed space `E` with an additive Haar
measure `μ`, and let `u : E → F` have weak Fréchet derivative `Du` on `Ω`, with values in a real
Banach space `F`. Extending `u` by zero outside an open subset `V` with compact closure in `Ω` and
convolving with a normalized smooth bump `φ.normed μ` produces a globally smooth function whose
Fréchet derivative agrees with `φ.normed μ ⋆ V.indicator Du` at every point whose `φ.rOut`-closed
ball lies in `V`, and whose `Lᵖ` seminorm on any null-measurable subset of such points is at most
`‖Du‖_{Lᵖ(V)}` for every `1 ≤ p ≤ ∞`.

As the outer radii of the bumps shrink to zero, these mollifications converge to `u` in `L^q(U)`
and their derivatives converge to `Du` in `Lᵖ(U)` for finite exponents `1 ≤ q, p < ∞` and every
open `U` with compact closure inside `Ω` (provided `u` is locally `L^q` on `Ω` and `Du` is
locally `Lᵖ` on `Ω`). If `u` is continuous on `Ω`, the mollifications also converge uniformly to
`u` on `closure U`.

## Main declarations

* `TauCeti.HasWeakFDerivOn.eLpNorm_fderiv_normed_convolution_indicator_le`: `Lᵖ` gradient bound
  `‖D(φ ⋆ V.indicator u)‖_{Lᵖ(s)} ≤ ‖Du‖_{Lᵖ(V)}` for `1 ≤ p ≤ ∞`.
* `TauCeti.HasWeakFDerivOn.tendsto_eLpNorm_fderiv_normed_convolution_indicator_sub`: `Lᵖ`
  convergence of the derivatives of the mollifications for `1 ≤ p < ∞`.
* `TauCeti.HasWeakFDerivOn.exists_contDiff_tendsto_eLpNorm` and
  `TauCeti.HasWeakFDerivOn.exists_contDiff_tendstoUniformlyOn`: packaged local smooth
  approximations on a relatively compact open subdomain.

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

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {Ω : Opens E} {u : E → F} {Du : E → E →L[ℝ] F}

/-- **`Lᵖ` gradient bound for interior mollifications.** If `V` has compact closure in `Ω`,
`1 ≤ p ≤ ∞`, and every point of a null-measurable set `s` has `closedBall x φ.rOut ⊆ V`, then
`‖D(φ.normed μ ⋆ V.indicator u)‖_{Lᵖ(s)} ≤ ‖Du‖_{Lᵖ(V)}`. -/
theorem HasWeakFDerivOn.eLpNorm_fderiv_normed_convolution_indicator_le
    (hu : HasWeakFDerivOn μ Ω u Du) {V : Opens E} (hVc : IsCompact (closure (V : Set E)))
    (hVΩ : closure (V : Set E) ⊆ Ω) {s : Set E} (hs : NullMeasurableSet s μ)
    (φ : ContDiffBump (0 : E)) (hball : ∀ x ∈ s, closedBall x φ.rOut ⊆ V) {p : ℝ≥0∞}
    (hp1 : 1 ≤ p) :
    eLpNorm (fderiv ℝ (φ.normed μ ⋆[lsmul ℝ ℝ, μ] (V : Set E).indicator u)) p (μ.restrict s) ≤
      eLpNorm Du p (μ.restrict V) := by
  have : CompleteSpace F := hu.completeSpace
  have : Fact (1 ≤ p) := ⟨hp1⟩
  have hDm_V : AEStronglyMeasurable Du (μ.restrict V) :=
    (hu.locallyIntegrableOn_deriv.integrableOn_of_isCompact_closure hVc hVΩ).aestronglyMeasurable
  have hDext : AEStronglyMeasurable ((V : Set E).indicator Du) μ :=
    (aestronglyMeasurable_indicator_iff V.isOpen.measurableSet).2 hDm_V
  have heq : fderiv ℝ (φ.normed μ ⋆[lsmul ℝ ℝ, μ] (V : Set E).indicator u) =ᵐ[μ.restrict s]
      φ.normed μ ⋆[lsmul ℝ ℝ, μ] (V : Set E).indicator Du :=
    (ae_restrict_mem₀ hs).mono fun x hx =>
      hu.fderiv_normed_convolution_indicator hVc hVΩ φ (hball x hx)
  calc eLpNorm (fderiv ℝ (φ.normed μ ⋆[lsmul ℝ ℝ, μ] (V : Set E).indicator u)) p (μ.restrict s)
      = eLpNorm (φ.normed μ ⋆[lsmul ℝ ℝ, μ] (V : Set E).indicator Du) p (μ.restrict s) :=
        eLpNorm_congr_ae heq
    _ ≤ eLpNorm (φ.normed μ ⋆[lsmul ℝ ℝ, μ] (V : Set E).indicator Du) p μ :=
        eLpNorm_mono_measure _ Measure.restrict_le_self
    _ ≤ eLpNorm ((V : Set E).indicator Du) p μ := φ.eLpNorm_normed_convolution_le hDext
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
  refine (tendsto_eLpNorm_normed_convolution_indicator_sub hp hφ
    V.isOpen.measurableSet.nullMeasurableSet ((self_subset_thickening hδ s).trans hsV) hDu).congr'
    ?_
  filter_upwards [hφ.eventually (gt_mem_nhds hδ)] with i hi
  refine eLpNorm_congr_ae ?_
  filter_upwards [(ae_restrict_mem isClosed_closure.measurableSet).filter_mono
    (ae_mono (Measure.restrict_mono_set μ subset_closure))] with x hx
  have hball : closedBall x (φ i).rOut ⊆ V :=
    (closedBall_subset_ball hi).trans <|
      (ball_subset_thickening hx δ).trans (thickening_closure.subset.trans hsV)
  simp only [Pi.sub_apply, hu.fderiv_normed_convolution_indicator hVc hVΩ (φ i) hball]

/-- Shared interior mollification construction with separate finite exponents `q` (for `u`) and
`p` (for `Du`), and an optional uniform convergence conclusion when `u` is continuous on `Ω`. -/
private theorem exists_interior_mollification (hu : HasWeakFDerivOn μ Ω u Du)
    {U : Opens E} (hUc : IsCompact (closure (U : Set E))) (hUΩ : closure (U : Set E) ⊆ Ω)
    {q p : ℝ≥0∞} (hq1 : 1 ≤ q) (hq : q ≠ (∞ : ℝ≥0∞))
    (huW : ∀ W : Opens E, IsCompact (closure (W : Set E)) → closure (W : Set E) ⊆ Ω →
      MemLp u q (μ.restrict W))
    (hp1 : 1 ≤ p) (hp : p ≠ (∞ : ℝ≥0∞)) (hDup : MemLpLoc p Ω Du μ) :
    ∃ un : ℕ → E → F, (∀ n, ContDiff ℝ ∞ (un n)) ∧
      (∀ n, eLpNorm (fderiv ℝ (un n)) p (μ.restrict U) ≤ eLpNorm Du p (μ.restrict Ω)) ∧
      (ContinuousOn u Ω → TendstoUniformlyOn un u atTop (closure (U : Set E))) ∧
      Tendsto (fun n => eLpNorm (un n - u) q (μ.restrict U)) atTop (𝓝 0) ∧
      Tendsto (fun n => eLpNorm (fderiv ℝ (un n) - Du) p (μ.restrict U)) atTop (𝓝 0) := by
  have : CompleteSpace F := hu.completeSpace
  have : Fact (1 ≤ q) := ⟨hq1⟩
  have : Fact (1 ≤ p) := ⟨hp1⟩
  obtain ⟨δ, hδ, hδΩ⟩ := hUc.exists_cthickening_subset_open Ω.isOpen hUΩ
  let W : Opens E := ⟨thickening δ (closure (U : Set E)), isOpen_thickening⟩
  have hWΩ : closure (W : Set E) ⊆ Ω := (closure_thickening_subset_cthickening _ _).trans hδΩ
  have hWc : IsCompact (closure (W : Set E)) := hUc.isBounded.thickening.isCompact_closure
  have hUW : thickening δ (U : Set E) ⊆ W := (thickening_closure (δ := δ) (s := (U : Set E))).ge
  have hδ2 : 0 < δ / 2 := half_pos hδ
  let φ : ℕ → ContDiffBump (0 : E) := ContDiffBump.shrinking hδ2
  have hφ : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0) :=
    ContDiffBump.tendsto_rOut_shrinking hδ2
  have hDuW : MemLp Du p (μ.restrict W) := hDup.memLp_restrict_of_isCompact_closure hWc hWΩ
  have hball (n : ℕ) : ∀ x ∈ (U : Set E), closedBall x (φ n).rOut ⊆ W := fun x hx =>
    (closedBall_subset_ball
      ((ContDiffBump.rOut_shrinking_le hδ2 n).trans_lt (half_lt_self hδ))).trans
      (ball_subset_thickening (subset_closure hx) δ)
  refine ⟨fun n => (φ n).normed μ ⋆[lsmul ℝ ℝ, μ] (W : Set E).indicator u,
    fun n => hu.locallyIntegrableOn.contDiff_normed_convolution_indicator
      W.isOpen.measurableSet.nullMeasurableSet hWc hWΩ (φ n),
    fun n => (hu.eLpNorm_fderiv_normed_convolution_indicator_le hWc hWΩ
      U.isOpen.measurableSet.nullMeasurableSet (φ n) (hball n) hp1).trans
      (eLpNorm_mono_measure _ (Measure.restrict_mono (subset_closure.trans hWΩ) le_rfl)),
    fun huc => ContDiffBump.tendstoUniformlyOn_normed_convolution_indicator
      W.isOpen.measurableSet.nullMeasurableSet hWc (huc.mono hWΩ) hδ subset_rfl hφ,
    tendsto_eLpNorm_normed_convolution_indicator_sub hq hφ
      W.isOpen.measurableSet.nullMeasurableSet ((self_subset_thickening hδ _).trans hUW)
      (huW W hWc hWΩ),
    hu.tendsto_eLpNorm_fderiv_normed_convolution_indicator_sub hWc hWΩ hδ hUW hp1 hp hDuW hφ⟩

/-- **Local smooth approximation in `W^{1,p}` (with separate value and derivative exponents).**
Let `u` have weak Fréchet derivative `Du` on `Ω`, let `U` be an open set with compact closure
inside `Ω`, and let `u` be locally `L^q` on `Ω` and `Du` be locally `Lᵖ` on `Ω` for
`1 ≤ q, p < ∞`. Then there is a sequence of globally smooth functions `uₙ` converging to `u` in
`L^q(U)` whose derivatives converge to `Du` in `Lᵖ(U)` and satisfy
`‖Duₙ‖_{Lᵖ(U)} ≤ ‖Du‖_{Lᵖ(Ω)}`. -/
theorem HasWeakFDerivOn.exists_contDiff_tendsto_eLpNorm (hu : HasWeakFDerivOn μ Ω u Du)
    {U : Opens E} (hUc : IsCompact (closure (U : Set E))) (hUΩ : closure (U : Set E) ⊆ Ω)
    {q p : ℝ≥0∞} (hq1 : 1 ≤ q) (hq : q ≠ (∞ : ℝ≥0∞))
    (huq : MemLpLoc q Ω u μ) (hp1 : 1 ≤ p) (hp : p ≠ (∞ : ℝ≥0∞))
    (hDup : MemLpLoc p Ω Du μ) :
    ∃ un : ℕ → E → F, (∀ n, ContDiff ℝ ∞ (un n)) ∧
      (∀ n, eLpNorm (fderiv ℝ (un n)) p (μ.restrict U) ≤ eLpNorm Du p (μ.restrict Ω)) ∧
      Tendsto (fun n => eLpNorm (un n - u) q (μ.restrict U)) atTop (𝓝 0) ∧
      Tendsto (fun n => eLpNorm (fderiv ℝ (un n) - Du) p (μ.restrict U)) atTop (𝓝 0) := by
  obtain ⟨un, hcd, hbound, -, hu_conv, hDu_conv⟩ := exists_interior_mollification hu hUc hUΩ
    hq1 hq (fun _ hWc hWΩ => huq.memLp_restrict_of_isCompact_closure hWc hWΩ) hp1 hp hDup
  exact ⟨un, hcd, hbound, hu_conv, hDu_conv⟩

/-- **Local smooth approximation in `W^{1,p}` and uniformly on `closure U` for continuous `u`.**
For `u` continuous on `Ω` and `Du` locally `Lᵖ` on `Ω`, the mollifications converge uniformly to
`u` on `closure U`, to `u` in `L^q(U)`, and their derivatives converge to `Du` in `Lᵖ(U)` for all
finite exponents `1 ≤ q, p < ∞`. -/
theorem HasWeakFDerivOn.exists_contDiff_tendstoUniformlyOn (hu : HasWeakFDerivOn μ Ω u Du)
    {U : Opens E} (huc : ContinuousOn u Ω) (hUc : IsCompact (closure (U : Set E)))
    (hUΩ : closure (U : Set E) ⊆ Ω) {q p : ℝ≥0∞} (hq1 : 1 ≤ q)
    (hq : q ≠ (∞ : ℝ≥0∞)) (hp1 : 1 ≤ p) (hp : p ≠ (∞ : ℝ≥0∞)) (hDup : MemLpLoc p Ω Du μ) :
    ∃ un : ℕ → E → F, (∀ n, ContDiff ℝ ∞ (un n)) ∧
      TendstoUniformlyOn un u atTop (closure (U : Set E)) ∧
      (∀ n, eLpNorm (fderiv ℝ (un n)) p (μ.restrict U) ≤ eLpNorm Du p (μ.restrict Ω)) ∧
      Tendsto (fun n => eLpNorm (un n - u) q (μ.restrict U)) atTop (𝓝 0) ∧
      Tendsto (fun n => eLpNorm (fderiv ℝ (un n) - Du) p (μ.restrict U)) atTop (𝓝 0) := by
  have huW (W : Opens E) (hWc : IsCompact (closure (W : Set E)))
      (hWΩ : closure (W : Set E) ⊆ Ω) : MemLp u q (μ.restrict W) := by
    have : IsFiniteMeasure (μ.restrict (W : Set E)) :=
      isFiniteMeasure_restrict.2 ((measure_mono subset_closure).trans_lt hWc.measure_lt_top).ne
    exact ((huc.mono hWΩ).memLp_top_restrict_of_subset_isCompact hWc
      W.isOpen.measurableSet subset_closure).mono_exponent le_top
  obtain ⟨un, hcd, hbound, hunif, hu_conv, hDu_conv⟩ :=
    exists_interior_mollification hu hUc hUΩ hq1 hq huW hp1 hp hDup
  exact ⟨un, hcd, hunif huc, hbound, hu_conv, hDu_conv⟩

end TauCeti

end

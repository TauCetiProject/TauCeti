/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Laplacian
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Basic
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Coordinate.Frame
import TauCeti.Geometry.Manifold.VectorBundle.LocalFrame

/-!
# The divergence in a chart

Let `ρ = √det (gᵢⱼ)` be the Riemannian volume density in the chart frame `e₁, …, eₙ` at `α`, and
write `Xᵏ` for the coefficients of a vector field `X` in that frame. This file proves the classical
coordinate formula for the Riemannian divergence

`ρ div X = ∑ₖ ∂ₖ (ρ Xᵏ)`,

where `∂ₖ` is differentiation along `eₖ`. Thus `ρ div X` is a flat divergence in the chart, which
is what lets the integral of a divergence against the Riemannian volume be computed by the flat
divergence theorem in coordinates. No orientation is involved, and the formulas hold at every
point of the chart domain, including boundary and corner points.

The formula rests on the derivative of the volume density. For any connection compatible with
the metric, differentiating the Gram matrix gives `dG = Pᵀ G + G P`, where `P` is the matrix of the
connection form in the chart frame, and Jacobi's formula `d (det G) = det G * trace (G⁻¹ dG)` turns
this into `dρ = ρ trace P`; these general identities are
`Riemannian.Tensor.mvfderiv_det_chartGramMatrix` and `TauCeti.mvfderiv_chartVolumeDensity`. For the
Levi-Civita connection, torsion-freeness identifies `trace P (eⱼ)` with the contracted Christoffel
symbol `∑ₖ Γᵏₖⱼ`, which appears when the trace of `∇X` is expanded in the frame.

## Main definitions and results

* `TauCeti.mvfderiv_chartVolumeDensity_chartLocalFrame`: `∂ⱼ log ρ = ∑ₖ Γᵏₖⱼ` for the
  Levi-Civita connection.
* `TauCeti.divergence_eq_sum_christoffelSymbol`: `div X = ∑ₖ (∂ₖ Xᵏ + ∑ⱼ Xʲ Γᵏₖⱼ)`.
* `TauCeti.chartVolumeDensity_mul_divergence`: the coordinate formula `ρ div X = ∑ₖ ∂ₖ (ρ Xᵏ)`.
* `TauCeti.chartFlux`, `TauCeti.chartFlux_eq_zero`, `TauCeti.chartFlux_eventuallyEq_zero`,
  `TauCeti.contMDiffOn_mul_localFrameCoeff`, and `TauCeti.contDiffOn_chartFlux`: the
  density-weighted chart-frame fluxes of a vector field in coordinates, extended by zero off the
  chart target, together with their vanishing and `C^k` regularity properties on manifolds with or
  without boundary.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapter 2 (the divergence and the Riemannian density) and Chapter 5 (the Levi-Civita
  connection and its Christoffel symbols in coordinates).
-/

public section

open Bundle FiberBundle Riemannian.Tensor Set TauCeti.Manifold
open scoped ContDiff Manifold Matrix Topology

namespace TauCeti

section Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]

/-- **The divergence in a chart frame.** In the chart frame `e₁, …, eₙ` at `α`, the divergence of a
vector field `X` with coefficients `Xᵏ` is `div X = ∑ₖ (∂ₖ Xᵏ + ∑ⱼ Xʲ Γᵏₖⱼ)` at every point of the
chart domain where `X` is differentiable, where `∂ₖ` is the derivative along `eₖ` and `Γᵏᵢⱼ` are the
Christoffel symbols of the Levi-Civita connection in that frame. -/
theorem divergence_eq_sum_christoffelSymbol (α : M) {y : M}
    (hy : y ∈ (trivializationAt E (TangentSpace I) α).baseSet) {X : Π x : M, TangentSpace I x}
    (hX : MDiffAt (T% X) y) :
    divergence I X y = ∑ k,
      (mvfderiv I (fun z ↦ (trivializationAt E (TangentSpace I) α).localFrameCoeff I
          (Module.finBasis ℝ E) k z (X z)) y (chartLocalFrame (I := I) α k y) +
        ∑ j, (trivializationAt E (TangentSpace I) α).localFrameCoeff I (Module.finBasis ℝ E) j y
            (X y) *
          christoffelSymbol I (Module.finBasis ℝ E) (trivializationAt E (TangentSpace I) α)
            (CovariantDerivative.leviCivitaConnection I M) k j k y) := by
  classical
  let e := trivializationAt E (TangentSpace I) α
  let b := Module.finBasis ℝ E
  have : IsManifold I (1 + 1) M := by norm_num; infer_instance
  -- Trace `∇X` in the frame, and expand `∇_{eₖ} X` by the frame formula.
  rw [divergence_def, trace_eq_sum_localFrameCoeff I b hy]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [ContinuousLinearMap.coe_coe, covariantDerivative_apply_localFrame_eq_sum b
      ((CovariantDerivative.leviCivitaConnection I M).isCovariantDerivativeOn (s := e.baseSet))
      hy hX k, map_sum]
  simp [localFrameCoeff_localFrame b hy, chartLocalFrame_def, e, b]

/-- **The contracted Christoffel symbols.** In the chart frame `e₁, …, eₙ` at `α`, the derivative of
the volume density `ρ` along `eⱼ` is `ρ ∑ₖ Γᵏₖⱼ`, where `Γᵏᵢⱼ` are the Christoffel symbols of the
Levi-Civita connection in that frame; that is, `∂ⱼ log ρ = ∑ₖ Γᵏₖⱼ`. -/
theorem mvfderiv_chartVolumeDensity_chartLocalFrame (α : M) {y : M}
    (hy : y ∈ (trivializationAt E (TangentSpace I) α).baseSet) (j : Fin (Module.finrank ℝ E)) :
    mvfderiv I (chartVolumeDensity (I := I) α) y (chartLocalFrame (I := I) α j y) =
      chartVolumeDensity (I := I) α y *
        ∑ k, christoffelSymbol I (Module.finBasis ℝ E) (trivializationAt E (TangentSpace I) α)
          (CovariantDerivative.leviCivitaConnection I M) k j k y := by
  have : IsManifold I (minSmoothness ℝ 2) M := by
    rw [minSmoothness_of_isRCLikeNormedField]; infer_instance
  have ht : (CovariantDerivative.leviCivitaConnection I M).IsTorsionFree :=
    (CovariantDerivative.isTorsionFree_iff_torsion_eq_zero _).2
      (CovariantDerivative.isLeviCivitaConnection_leviCivitaConnection I).torsion
  rw [mvfderiv_chartVolumeDensity
    (CovariantDerivative.isLeviCivitaConnection_leviCivitaConnection I).isMetricCompatible α hy]
  congr 1
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  -- By torsion-freeness `Γᵏₖⱼ = Γᵏⱼₖ = (∇_{eⱼ} eₖ)ᵏ`.
  rw [christoffelSymbol_comm ht _ α (by simpa using hy) k j k, christoffelSymbol_apply,
    chartLocalFrame_def]

/-- **The divergence in a chart.** Let `ρ` be the volume density in the chart frame `e₁, …, eₙ`
at `α`, and let `Xᵏ` be the coefficients of the vector field `X` in that frame. At every point `y`
of the chart domain where `X` is differentiable, `ρ div X = ∑ₖ ∂ₖ (ρ Xᵏ)`, where `∂ₖ` is the
derivative along `eₖ`. -/
theorem chartVolumeDensity_mul_divergence (α : M) {y : M}
    (hy : y ∈ (trivializationAt E (TangentSpace I) α).baseSet) {X : Π x : M, TangentSpace I x}
    (hX : MDiffAt (T% X) y) :
    chartVolumeDensity (I := I) α y * divergence I X y =
      ∑ k, mvfderiv I (fun z ↦ chartVolumeDensity (I := I) α z *
        (trivializationAt E (TangentSpace I) α).localFrameCoeff I (Module.finBasis ℝ E) k z (X z))
          y (chartLocalFrame (I := I) α k y) := by
  have : IsManifold I (1 + 1) M := by norm_num; infer_instance
  have hρ : MDiffAt (chartVolumeDensity (I := I) α) y :=
    ((contMDiffOn_chartVolumeDensity (n := 1) α).contMDiffAt
      ((trivializationAt E (TangentSpace I) α).open_baseSet.mem_nhds hy)).mdifferentiableAt
        one_ne_zero
  -- Expand `∂ₖ (ρ Xᵏ) = ρ ∂ₖ Xᵏ + Xᵏ ∂ₖ ρ`; the terms `Xᵏ ∂ₖ ρ = ρ ∑ⱼ Xᵏ Γʲⱼₖ` are the
  -- Christoffel terms of `ρ div X`.
  have hprod (k : Fin (Module.finrank ℝ E)) (w : TangentSpace I y) :
      mvfderiv I (fun z ↦ chartVolumeDensity (I := I) α z *
        (trivializationAt E (TangentSpace I) α).localFrameCoeff I (Module.finBasis ℝ E) k z (X z))
          y w =
        chartVolumeDensity (I := I) α y * mvfderiv I (fun z ↦
          (trivializationAt E (TangentSpace I) α).localFrameCoeff I (Module.finBasis ℝ E) k z
            (X z)) y w +
          (trivializationAt E (TangentSpace I) α).localFrameCoeff I (Module.finBasis ℝ E) k y
            (X y) * mvfderiv I (chartVolumeDensity (I := I) α) y w :=
    congrArg (fun L ↦ L w)
      (mvfderiv_mul hρ (mdifferentiableAt_localFrameCoeff (Module.finBasis ℝ E) hy hX k))
  simp only [divergence_eq_sum_christoffelSymbol α hy hX, hprod,
    mvfderiv_chartVolumeDensity_chartLocalFrame α hy, mul_add, Finset.mul_sum,
    Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun k _ ↦ ?_
  ring

end Riemannian

/-! ### Density-weighted chart fluxes -/

section ChartFlux

variable {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]

/-- The `i`-th density-weighted flux of a vector field `X` in the extended chart at `α` relative to
a basis `b` of the model space and a scalar density `ρ`, extended by zero off the chart target. -/
noncomputable def chartFlux (b : Module.Basis ι ℝ E) (ρ : M → ℝ) (α : M)
    (X : (x : M) → TangentSpace I x) (i : ι) : E → ℝ :=
  (extChartAt I α).target.indicator fun z ↦ ρ ((extChartAt I α).symm z) *
    (trivializationAt E (TangentSpace I) α).localFrameCoeff I b i
      ((extChartAt I α).symm z) (X ((extChartAt I α).symm z))

variable {α : M} {X : (x : M) → TangentSpace I x}

/-- On the extended chart target at `α`, `chartFlux` evaluates to the density times the local-frame
coefficient of `X` at `(extChartAt I α).symm z`. -/
theorem chartFlux_apply_of_mem (b : Module.Basis ι ℝ E) (ρ : M → ℝ) (i : ι) {z : E}
    (hz : z ∈ (extChartAt I α).target) :
    chartFlux b ρ α X i z = ρ ((extChartAt I α).symm z) *
      (trivializationAt E (TangentSpace I) α).localFrameCoeff I b i
        ((extChartAt I α).symm z) (X ((extChartAt I α).symm z)) :=
  indicator_of_mem hz _

/-- Outside the extended chart target at `α`, `chartFlux` vanishes. -/
theorem chartFlux_apply_of_notMem (b : Module.Basis ι ℝ E) (ρ : M → ℝ) (i : ι) {z : E}
    (hz : z ∉ (extChartAt I α).target) : chartFlux b ρ α X i z = 0 :=
  indicator_of_notMem hz _

/-- The chart flux vanishes outside the chart image of `tsupport X`. -/
theorem chartFlux_eq_zero (b : Module.Basis ι ℝ E) (ρ : M → ℝ) (i : ι) {z : E}
    (hz : z ∉ extChartAt I α '' tsupport (α := E) X) : chartFlux b ρ α X i z = 0 := by
  by_cases ht : z ∈ (extChartAt I α).target
  · have hX0 : X ((extChartAt I α).symm z) = 0 :=
      image_eq_zero_of_notMem_tsupport (α := E) fun h ↦ hz ⟨_, h, (extChartAt I α).right_inv ht⟩
    rw [chartFlux_apply_of_mem b ρ i ht, hX0, map_zero, mul_zero]
  · exact chartFlux_apply_of_notMem b ρ i ht

/-- When the chart image of `tsupport X` is compact, the chart flux vanishes near any point outside
it. -/
theorem chartFlux_eventuallyEq_zero (b : Module.Basis ι ℝ E) (ρ : M → ℝ)
    (hKc : IsCompact (extChartAt I α '' tsupport (α := E) X)) (i : ι) {z : E}
    (hz : z ∉ extChartAt I α '' tsupport (α := E) X) : chartFlux b ρ α X i =ᶠ[𝓝 z] 0 :=
  Filter.eventually_of_mem (hKc.isClosed.isOpen_compl.mem_nhds hz) fun _ h ↦
    chartFlux_eq_zero b ρ i h

/-- On the chart source at `α`, the product of a `C^k` scalar density `ρ` and a local-frame
coefficient of a `C^k` vector field `X` is `C^k`. -/
theorem contMDiffOn_mul_localFrameCoeff [FiniteDimensional ℝ E] {k : ℕ∞ω} [IsManifold I (k + 1) M]
    (b : Module.Basis ι ℝ E) {ρ : M → ℝ} (hρ : ContMDiffOn I 𝓘(ℝ) k ρ (chartAt H α).source)
    (hX : ContMDiffOn I I.tangent k (T% X) (chartAt H α).source) (i : ι) :
    ContMDiffOn I 𝓘(ℝ) k (fun y ↦ ρ y *
      (trivializationAt E (TangentSpace I) α).localFrameCoeff I b i y (X y))
      (chartAt H α).source := by
  let _ : ContMDiffVectorBundle k E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  rw [← TangentBundle.trivializationAt_baseSet (I := I) (x := α)] at hρ hX ⊢
  exact hρ.mul (contMDiffOn_baseSet_localFrameCoeff (I := I)
    (e := trivializationAt E (TangentSpace I) α) b (k := k) hX i)

/-- When the chart image of `tsupport X` is compact and contained in the chart target, each chart
flux is `C^k` on `range I`. -/
theorem contDiffOn_chartFlux [FiniteDimensional ℝ E] {k : ℕ∞ω} [IsManifold I (k + 1) M]
    (b : Module.Basis ι ℝ E) {ρ : M → ℝ} (hρ : ContMDiffOn I 𝓘(ℝ) k ρ (chartAt H α).source)
    (hX : ContMDiffOn I I.tangent k (T% X) (chartAt H α).source)
    (hKc : IsCompact (extChartAt I α '' tsupport (α := E) X))
    (himage : extChartAt I α '' tsupport (α := E) X ⊆ (extChartAt I α).target) (i : ι) :
    ContDiffOn ℝ k (chartFlux b ρ α X i) (range I) := by
  have : IsManifold I k M := IsManifold.of_le (n := k + 1) le_self_add
  intro z _
  by_cases hz : z ∈ (extChartAt I α).target
  · have hy : (extChartAt I α).symm z ∈ (chartAt H α).source := by
      rw [← extChartAt_source (I := I)]; exact (extChartAt I α).map_target hz
    have hg : ContDiffWithinAt ℝ k _ (range I) z :=
      contMDiffWithinAt_iff_contDiffWithinAt.1
        (((contMDiffOn_mul_localFrameCoeff b hρ hX i).contMDiffAt
          ((chartAt H α).open_source.mem_nhds hy)).comp_contMDiffWithinAt z
            (contMDiffWithinAt_extChartAt_symm_range (n := k) α hz))
    exact hg.congr_of_eventuallyEq
      (Filter.eventually_of_mem (extChartAt_target_mem_nhdsWithin_of_mem hz) fun _ h ↦
        chartFlux_apply_of_mem b ρ i h) (chartFlux_apply_of_mem b ρ i hz)
  · exact (contDiffAt_const.congr_of_eventuallyEq
      (chartFlux_eventuallyEq_zero b ρ hKc i fun h ↦ hz (himage h))).contDiffWithinAt

end ChartFlux

end TauCeti

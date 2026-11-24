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
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric.Basic
import TauCeti.Geometry.Manifold.VectorBundle.LocalFrame

/-!
# The divergence and coordinate Piola identity in a chart

Let `ρ = √det (gᵢⱼ)` be the Riemannian volume density in the chart frame `e₁, …, eₙ` at `α`, and
write `Xᵏ` for the coefficients of a vector field `X` in that frame. This file proves the classical
coordinate formula for the Riemannian divergence

`ρ div X = ∑ₖ ∂ₖ (ρ Xᵏ)`,

where `∂ₖ` is differentiation along `eₖ`, together with the **coordinate Piola identity**
`∑ₖ ∇^{LC}_{eₖ}(ρ • eₖ♯) = 0` for the weighted metric-dual frame `ρ • eₖ♯`. Thus `ρ div X` is a
flat divergence in the chart, and covariant codifferentials and rough Laplacians take divergence
form `ρ (∇* η) = -∑ₖ ∇_{eₖ}(ρ • η(eₖ♯))` without connection terms on `TM`. No orientation is
involved, and the formulas hold at every point of the chart domain, including boundary and corner
points.

The formula rests on the derivative of the volume density. For any connection compatible with
the metric, differentiating the Gram matrix gives `dG = Pᵀ G + G P`, where `P` is the matrix of the
connection form in the chart frame, and Jacobi's formula `d (det G) = det G * trace (G⁻¹ dG)` turns
this into `dρ = ρ trace P`; these general identities are
`Riemannian.Tensor.mvfderiv_det_chartGramMatrix` and `TauCeti.mvfderiv_chartVolumeDensity`. For the
Levi-Civita connection, torsion-freeness identifies `trace P (eⱼ)` with the contracted Christoffel
symbol `∑ₖ Γᵏₖⱼ`, which appears when the trace of `∇X` is expanded in the frame.

## Main results

* `TauCeti.mvfderiv_chartVolumeDensity_chartLocalFrame`: `∂ⱼ log ρ = ∑ₖ Γᵏₖⱼ` for the
  Levi-Civita connection.
* `TauCeti.divergence_eq_sum_christoffelSymbol`: `div X = ∑ₖ (∂ₖ Xᵏ + ∑ⱼ Xʲ Γᵏₖⱼ)`.
* `TauCeti.chartVolumeDensity_mul_divergence`: the coordinate formula `ρ div X = ∑ₖ ∂ₖ (ρ Xᵏ)`.
* `TauCeti.inner_leviCivitaConnection_chartDualFrame` and
  `TauCeti.sum_leviCivitaConnection_chartVolumeDensity_smul_chartDualFrame`: the coordinate Piola
  identity `∑ₖ ∇^{LC}_{eₖ}(ρ • eₖ♯) = 0`.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapter 2 (the divergence and the Riemannian density) and Chapter 5 (the Levi-Civita
  connection and its Christoffel symbols in coordinates).
-/

public section

open Bundle FiberBundle Riemannian.Tensor TauCeti.Manifold
open scoped ContDiff Manifold Matrix RealInnerProductSpace Topology

namespace TauCeti

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
    (contMDiffAt_chartVolumeDensity (n := 1) α
      (by simpa only [TangentBundle.trivializationAt_baseSet] using hy)).mdifferentiableAt
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

/-- Differentiating the locally constant Kronecker delta `⟪eₖ♯, eⱼ⟫ = δₖⱼ` expresses
`⟪∇^{LC}_{eₖ} eₖ♯, eⱼ⟫` as minus the `k`-th local-frame coefficient of `∇^{LC}_{eₖ} eⱼ`. -/
theorem inner_leviCivitaConnection_chartDualFrame
    (α : M) {y : M} (hy : y ∈ (chartAt H α).source) (k j : Fin (Module.finrank ℝ E)) :
    ⟪CovariantDerivative.leviCivitaConnection I M (chartDualFrame (I := I) α k) y
        (chartLocalFrame (I := I) α k y), chartLocalFrame (I := I) α j y⟫ =
      -(trivializationAt E (TangentSpace I) α).localFrameCoeff I (Module.finBasis ℝ E) k y
        (CovariantDerivative.leviCivitaConnection I M (chartLocalFrame (I := I) α k) y
          (chartLocalFrame (I := I) α j y)) := by
  have : IsManifold I (minSmoothness ℝ 2) M := by
    rw [minSmoothness_of_isRCLikeNormedField]; infer_instance
  have hy' : y ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    simpa only [TangentBundle.trivializationAt_baseSet] using hy
  have hy_ext : y ∈ (extChartAt I α).source := by rwa [extChartAt_source]
  have hLC := CovariantDerivative.isLeviCivitaConnection_leviCivitaConnection (I := I) (M := M)
  have ht : (CovariantDerivative.leviCivitaConnection I M).IsTorsionFree :=
    (CovariantDerivative.isTorsionFree_iff_torsion_eq_zero _).2 hLC.torsion
  have hconst : (fun z ↦ ⟪chartDualFrame (I := I) α k z, chartLocalFrame (I := I) α j z⟫) =ᶠ[𝓝 y]
      fun _ ↦ if k = j then (1 : ℝ) else 0 := by
    filter_upwards [(chartAt H α).open_source.mem_nhds hy] with z hz
    exact inner_chartDualFrame α hz k j
  have hm := hLC.isMetricCompatible.inner_apply_add_inner_apply_eq_zero_of_eventuallyEq_const
    (mdifferentiableAt_chartDualFrame α hy' k) (mdifferentiableAt_chartLocalFrame α hy' j)
    hconst (chartLocalFrame (I := I) α k y)
  have hcomm : CovariantDerivative.leviCivitaConnection I M (chartLocalFrame (I := I) α j) y
        (chartLocalFrame (I := I) α k y) =
      CovariantDerivative.leviCivitaConnection I M (chartLocalFrame (I := I) α k) y
        (chartLocalFrame (I := I) α j y) := by
    simpa only [chartLocalFrame_def] using
      covariantDerivative_localFrame_comm ht (Module.finBasis ℝ E) α hy_ext k j
  rw [hcomm, inner_chartDualFrame_eq_localFrameCoeff α hy k] at hm
  linarith

/-- **Coordinate Piola identity for the Levi-Civita connection.** On a chart domain, the weighted
dual frame `ρ • eₖ♯` (with `ρ = chartVolumeDensity α`) satisfies `∑ₖ ∇^{LC}_{eₖ}(ρ • eₖ♯) = 0`.
This cancels the connection terms on `TM` when `∇*` and `∇*∇` are written in divergence form. -/
theorem sum_leviCivitaConnection_chartVolumeDensity_smul_chartDualFrame
    (α : M) {y : M} (hy : y ∈ (chartAt H α).source) :
    ∑ k, CovariantDerivative.leviCivitaConnection I M
      (fun z ↦ chartVolumeDensity (I := I) α z • chartDualFrame (I := I) α k z) y
      (chartLocalFrame (I := I) α k y) = 0 := by
  have : IsManifold I (1 + 1) M := by norm_num; infer_instance
  have hy' : y ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    simpa only [TangentBundle.trivializationAt_baseSet] using hy
  let b := (trivializationAt E (TangentSpace I) α).basisAt (Module.finBasis ℝ E) hy'
  have hb (j) : b j = chartLocalFrame (I := I) α j y :=
    (chartLocalFrame_apply_of_mem_chart_source (I := I) α hy j).symm
  have hLC := CovariantDerivative.isLeviCivitaConnection_leviCivitaConnection (I := I) (M := M)
  have hρ : MDiffAt (chartVolumeDensity (I := I) α) y :=
    (contMDiffAt_chartVolumeDensity (I := I) (n := 1) α hy).mdifferentiableAt one_ne_zero
  refine InnerProductSpace.ext_inner_right_basis b fun j ↦ ?_
  rw [inner_zero_left, hb, sum_inner]
  have hterm (k : Fin (Module.finrank ℝ E)) :
      ⟪CovariantDerivative.leviCivitaConnection I M
          (chartVolumeDensity (I := I) α • chartDualFrame (I := I) α k) y
          (chartLocalFrame (I := I) α k y), chartLocalFrame (I := I) α j y⟫ =
        chartVolumeDensity (I := I) α y *
            (-(trivializationAt E (TangentSpace I) α).localFrameCoeff I (Module.finBasis ℝ E) k y
              (CovariantDerivative.leviCivitaConnection I M (chartLocalFrame (I := I) α k) y
                (chartLocalFrame (I := I) α j y))) +
          mvfderiv I (chartVolumeDensity (I := I) α) y (chartLocalFrame (I := I) α k y) *
            if k = j then 1 else 0 := by
    rw [(CovariantDerivative.leviCivitaConnection I M).isCovariantDerivativeOnUniv.leibniz_apply
      (mdifferentiableAt_chartDualFrame α hy' k) hρ, inner_add_left, real_inner_smul_left,
      real_inner_smul_left, inner_leviCivitaConnection_chartDualFrame α hy,
      inner_chartDualFrame α hy]
  have hsmul (k) : (fun z ↦ chartVolumeDensity (I := I) α z • chartDualFrame (I := I) α k z) =
      chartVolumeDensity (I := I) α • chartDualFrame (I := I) α k :=
    funext fun _ ↦ rfl
  simp_rw [hsmul, hterm]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
    Finset.sum_neg_distrib, mvfderiv_chartVolumeDensity hLC.isMetricCompatible α hy']
  ring

end TauCeti

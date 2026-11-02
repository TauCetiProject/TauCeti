/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
public import TauCeti.Geometry.Manifold.VectorBundle.NondegenerateMetric.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Tangent

/-!
# Composing a metric on `M × ℝ` with a map of the time coordinate

For a smooth metric `G` on `M × ℝ` and a smooth `φ : ℝ → ℝ`, this file constructs the metric whose
value at `(x, t)` is the value of `G` at `(x, φ t)`, on the same tangent vectors. For the cylinder
metric `g t + dt²` of a smooth path `t ↦ g t` of metrics on `M`, this is the cylinder metric of the
reparametrised path `t ↦ g (φ t)`. Unlike a pullback along `(x, t) ↦ (x, φ t)`, it does not
multiply the `ℝ`-components of tangent vectors by `φ'`. It is smooth because the tangent-bundle
trivializations of `M × ℝ` do not depend on the `ℝ`-coordinate
(`TauCeti.Manifold.symmL_trivializationAt_prod_model_space`).

## Main definitions

* `Bundle.ContMDiffRiemannianMetric.compTime`: the metric `(x, t) ↦ G (x, φ t)` on `M × ℝ`.

## Main results

* `Bundle.ContMDiffRiemannianMetric.compTime_inner`: the value of `compTime` at `(x, t)`.
* `Bundle.ContMDiffRiemannianMetric.chartMetric_compTime`: in charts, `compTime` reads the chart
  metric of `G` along `(z, τ) ↦ (z, φ τ)`.
-/

public section

open Bundle Set
open TauCeti.Manifold (symmL_trivializationAt_prod_model_space)
open scoped ContDiff Manifold

noncomputable section

namespace Bundle.ContMDiffRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable (G : ContMDiffRiemannianMetric (I.prod 𝓘(ℝ)) ∞ (E × ℝ)
    (fun p : M × ℝ ↦ TangentSpace (I.prod 𝓘(ℝ)) p)) {φ : ℝ → ℝ}

/-- The metric on `M × ℝ` whose value at `(x, t)` is the value of `G` at `(x, φ t)`, on the same
tangent vectors. For a cylinder metric `G = g t + dt²` of a path `g` of metrics, this is the
cylinder metric `g (φ t) + dt²` of the reparametrised path. Unlike
`Bundle.ContMDiffRiemannianMetric.reparamTime`, the `ℝ`-components of tangent vectors are not
multiplied by `φ'`. -/
def compTime (hφ : ContDiff ℝ ∞ φ) :
    ContMDiffRiemannianMetric (I.prod 𝓘(ℝ)) ∞ (E × ℝ)
      (fun p : M × ℝ ↦ TangentSpace (I.prod 𝓘(ℝ)) p) where
  inner p := G.inner (p.1, φ p.2)
  symm p := G.symm (p.1, φ p.2)
  pos p := G.pos (p.1, φ p.2)
  isVonNBounded p := G.isVonNBounded (p.1, φ p.2)
  contMDiff p₀ := by
    refine (contMDiffAt_section (F := E × ℝ →L[ℝ] E × ℝ →L[ℝ] ℝ)
      (E := fun p : M × ℝ ↦
        TangentSpace (I.prod 𝓘(ℝ)) p →L[ℝ] TangentSpace (I.prod 𝓘(ℝ)) p →L[ℝ] ℝ)
      (s := fun p ↦ G.inner (p.1, φ p.2)) p₀).2 ?_
    -- In the trivializations at `p₀` and at `(p₀.1, φ p₀.2)`, which agree over points with the
    -- same `M`-coordinate, the metric reads as the coordinate expression of `G` along
    -- `(x, t) ↦ (x, φ t)`.
    have hΦ : ContMDiffAt (I.prod 𝓘(ℝ)) (I.prod 𝓘(ℝ)) ∞ (Prod.map id φ) p₀ :=
      contMDiffAt_id.prodMap (hφ.contMDiff.contMDiffAt)
    have hG := G.contMDiff (p₀.1, φ p₀.2)
    rw [contMDiffAt_section] at hG
    apply (hG.comp p₀ hΦ).congr_of_eventuallyEq
    filter_upwards [(trivializationAt (E × ℝ) (TangentSpace (I.prod 𝓘(ℝ)) : M × ℝ → Type _)
      p₀).open_baseSet.mem_nhds (mem_baseSet_trivializationAt (E × ℝ)
        (TangentSpace (I.prod 𝓘(ℝ)) : M × ℝ → Type _) p₀)] with q hq
    have hq' : (q.1, φ q.2) ∈ (trivializationAt (E × ℝ)
        (TangentSpace (I.prod 𝓘(ℝ)) : M × ℝ → Type _) (p₀.1, φ p₀.2)).baseSet := by
      simp only [TangentBundle.trivializationAt_baseSet] at hq ⊢
      simpa using hq
    have hq₁ : q.1 ∈ (chartAt H p₀.1).source := by
      simp only [TangentBundle.trivializationAt_baseSet] at hq
      simpa using hq
    have hsymm (u : E × ℝ) :
        (trivializationAt (E × ℝ) (TangentSpace (I.prod 𝓘(ℝ))) p₀).symm q u =
          (trivializationAt (E × ℝ) (TangentSpace (I.prod 𝓘(ℝ))) (p₀.1, φ p₀.2)).symm
            (q.1, φ q.2) u := by
      rw [← Trivialization.symmL_apply (R := ℝ) _ hq, ← Trivialization.symmL_apply (R := ℝ) _ hq']
      exact symmL_trivializationAt_prod_model_space hq₁ _ _ u
    refine ContinuousLinearMap.ext fun v ↦ ContinuousLinearMap.ext fun w ↦ ?_
    simp only [hom_trivializationAt_apply, Function.comp_apply]
    refine (inCoordinates_apply_eq₂ (𝕜 := ℝ) (F₃ := ℝ) (E₃ := fun _ : M × ℝ ↦ ℝ) (x := q)
      (ϕ := G.inner (q.1, φ q.2)) hq hq (by simp)).trans ?_
    refine Eq.trans ?_ (inCoordinates_apply_eq₂ hq' hq' (by simp)).symm
    simp only [Trivial.fiberBundle_trivializationAt', Trivial.linearMapAt_trivialization,
      LinearMap.id_apply]
    rw [hsymm, hsymm]
    -- `Prod.map id φ q` is `(q.1, φ q.2)` by definition.
    rfl

variable {G}

/-- The metric `compTime` at `(x, t)` is `G` at `(x, φ t)`. -/
@[simp]
theorem compTime_inner (hφ : ContDiff ℝ ∞ φ) (p : M × ℝ) :
    (G.compTime hφ).inner p = G.inner (p.1, φ p.2) :=
  (rfl)

/-- In the chart at `(x₀, t₀)`, the metric `compTime` reads as the chart metric of `G` at
`(x₀, s)`, for any `s`, along the map `(z, τ) ↦ (z, φ τ)`. -/
theorem chartMetric_compTime (hφ : ContDiff ℝ ∞ φ) (x₀ : M) (t₀ s : ℝ) {z : E}
    (hz : z ∈ (extChartAt I x₀).target) (τ : ℝ) :
    (G.compTime hφ).toNondegenerateMetric.chartMetric (x₀, t₀) (z, τ) =
      G.toNondegenerateMetric.chartMetric (x₀, s) (z, φ τ) := by
  have hz₁ : (z, τ) ∈ (extChartAt (I.prod 𝓘(ℝ)) (x₀, t₀)).target := by
    rw [extChartAt_prod, PartialEquiv.prod_target]
    exact ⟨hz, by simp⟩
  have hz₂ : (z, φ τ) ∈ (extChartAt (I.prod 𝓘(ℝ)) (x₀, s)).target := by
    rw [extChartAt_prod, PartialEquiv.prod_target]
    exact ⟨hz, by simp⟩
  set y := (extChartAt (I.prod 𝓘(ℝ)) (x₀, t₀)).symm (z, τ)
  have hy : y = ((extChartAt I x₀).symm z, τ) := by
    simp only [y, extChartAt_prod, PartialEquiv.prod_symm, PartialEquiv.prod_coe,
      extChartAt_model_space_eq_id, PartialEquiv.refl_symm, PartialEquiv.refl_coe, id_eq]
  have hy₁ : y.1 ∈ (chartAt H x₀).source := by
    simpa [hy] using (extChartAt I x₀).map_target hz
  have hpt : (extChartAt (I.prod 𝓘(ℝ)) (x₀, s)).symm (z, φ τ) = (y.1, φ y.2) := by
    simp only [hy, extChartAt_prod, PartialEquiv.prod_symm, PartialEquiv.prod_coe,
      extChartAt_model_space_eq_id, PartialEquiv.refl_symm, PartialEquiv.refl_coe, id_eq]
  have hbase₁ :
      y ∈ (trivializationAt (E × ℝ) (TangentSpace (I.prod 𝓘(ℝ))) (x₀, t₀)).baseSet := by
    simpa using hy₁
  have hbase₂ : (y.1, φ y.2) ∈
      (trivializationAt (E × ℝ) (TangentSpace (I.prod 𝓘(ℝ))) (x₀, s)).baseSet := by
    simpa using hy₁
  have hsymm (v : E × ℝ) :
      (trivializationAt (E × ℝ) (TangentSpace (I.prod 𝓘(ℝ))) (x₀, t₀)).symm y v =
        (trivializationAt (E × ℝ) (TangentSpace (I.prod 𝓘(ℝ))) (x₀, s)).symm (y.1, φ y.2) v := by
    rw [← Trivialization.symmL_apply (R := ℝ) _ hbase₁,
      ← Trivialization.symmL_apply (R := ℝ) _ hbase₂]
    exact symmL_trivializationAt_prod_model_space hy₁ _ _ v
  refine ContinuousLinearMap.ext fun u ↦ ContinuousLinearMap.ext fun w ↦ ?_
  rw [TauCeti.Manifold.ContMDiffNondegenerateMetric.chartMetric_apply _ hz₁,
    TauCeti.Manifold.ContMDiffNondegenerateMetric.chartMetric_apply _ hz₂, hpt]
  simp only [toNondegenerateMetric_apply, compTime_inner]
  rw [hsymm, hsymm]
  -- `y` abbreviates the point `(extChartAt (I.prod 𝓘(ℝ)) (x₀, t₀)).symm (z, τ)`.
  rfl

end Bundle.ContMDiffRiemannianMetric

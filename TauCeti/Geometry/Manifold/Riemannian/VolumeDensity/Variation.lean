/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Trace.Basic
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Scalar
import Mathlib.Analysis.SpecialFunctions.Sqrt
import TauCeti.Analysis.Calculus.Deriv.Matrix

/-!
# The first variation of the Riemannian volume density

Let `g_τ` be a one-parameter family of Riemannian metrics on `M`, and suppose that at a point `x`
the metrics have parameter derivative `h = ∂_τ g_τ` at `τ = t`, a bilinear form on `T_x M`. In the
frame of a chart, the volume density of `g_τ` is `ρ_τ = √(det G_τ)`, where `G_τ` is the Gram
matrix of `g_τ` in that frame. Jacobi's formula gives `∂_τ det G = det G * trace (G⁻¹ ∂_τ G)`,
and the trace of `G⁻¹ ∂_τ G` is the metric trace `tr_g h = gⁱʲ hᵢⱼ`, so

`∂_τ ρ = ½ tr_g(h) ρ`.

That is, the Riemannian volume form varies by `∂_τ dμ_g = ½ tr_g(h) dμ_g`. No orientation is
involved, and the identity holds in every chart containing `x`. Since `TauCeti.riemannianVolume`
is the coordinate Haar measure weighted by `TauCeti.chartVolumeDensity` on each chart, this is
the pointwise form of the variation of the Riemannian volume measure.

Each metric `g_τ` is installed in turn as the `RiemannianBundle` instance of the tangent bundle,
so that `TauCeti.chartVolumeDensity` and `TauCeti.bilinFormTrace` are computed for it. Only the
inner products at the single point `x` need to be differentiable in the parameter, and
derivatives within a set of parameters cover one-sided derivatives at the ends of an interval.

For a conformal variation `h = μ g` this gives `∂_τ ρ = (n μ / 2) ρ` in real dimension `n`. Along
a Ricci flow, `h = -2 Ric(g)` and `tr_g Ric = Scal`, so the volume form evolves by
`∂_τ dμ_g = -Scal(g) dμ_g`.

## Main results

* `TauCeti.hasDerivWithinAt_chartVolumeDensity`, `TauCeti.hasDerivAt_chartVolumeDensity`: the
  variation `∂_τ ρ = ½ tr_g(h) ρ` of the chart volume density.
* `TauCeti.hasDerivWithinAt_chartVolumeDensity_of_conformal`: under `∂_τ g = μ g` the density
  varies by `(n μ / 2) ρ`.
* `TauCeti.hasDerivWithinAt_chartVolumeDensity_of_ricciFlow`: under `∂_τ g = -2 Ric(g)` the
  density varies by `-Scal(g) ρ`.

## References

* P. Topping, *Lectures on the Ricci Flow*, LMS Lecture Note Series 325, Cambridge University
  Press (2006), Section 2.3 (variations of geometric quantities, including the volume form).
* A. L. Besse, *Einstein Manifolds*, Springer (1987), Section 1.K.
-/

public section

open Bundle Riemannian.Tensor
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {s : Set ℝ} {t : ℝ} {x : M}

section Variation

variable [IsManifold I 1 M] {g : ℝ → RiemannianMetric (fun x : M ↦ TangentSpace I x)}

/-- **The variation of the volume density.** If the metrics `g_τ` have parameter derivative `h`
at `x` at `τ = t` within `s`, then in every chart containing `x` the volume density
`ρ_τ = √(det G_τ)` has derivative `½ tr_g(h) ρ` there, with the trace and the density computed
for `g_t`. -/
theorem hasDerivWithinAt_chartVolumeDensity (α : M) (hx : x ∈ (chartAt H α).source)
    {h : LinearMap.BilinForm ℝ (TangentSpace I x)}
    (hg : ∀ v w, HasDerivWithinAt (fun τ ↦ (g τ).inner x v w) (h v w) s t) :
    HasDerivWithinAt
      (fun τ ↦ letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g τ⟩;
        chartVolumeDensity (I := I) α x)
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g t⟩;
        2⁻¹ * bilinFormTrace h * chartVolumeDensity (I := I) α x) s t := by
  have hx' : x ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    simpa only [TangentBundle.trivializationAt_baseSet] using hx
  -- `G τ` is the Gram matrix of `g τ` in the chart frame `e`, and `G'` that of `h`.
  let e := fun i ↦ chartLocalFrame (I := I) α i x
  let G : ℝ → Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    fun τ ↦ Matrix.of fun i j ↦ (g τ).inner x (e i) (e j)
  let G' : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    Matrix.of fun i j ↦ h (e i) (e j)
  have hG (τ : ℝ) : (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g τ⟩;
      chartGramMatrix (I := I) α x) = G τ := by
    let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g τ⟩
    ext i j
    -- The inner product installed by `⟨g τ⟩` is `(g τ).inner` by definition of the instance.
    exact chartGramMatrix_apply α x i j
  have hρ (τ : ℝ) : (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g τ⟩;
      chartVolumeDensity (I := I) α x) = √(G τ).det := by
    let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g τ⟩
    rw [chartVolumeDensity_def, hG τ]
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g t⟩
  have hGt : G t = chartGramMatrix (I := I) α x := (hG t).symm
  have hdet : 0 < (G t).det := hGt ▸ chartGramMatrix_det_pos α hx'
  have hsqrt := HasDerivWithinAt.sqrt (Matrix.hasDerivWithinAt_det_of_entries (A := G)
    (A' := G') (fun i j ↦ hg _ _) hdet.ne'.isUnit) hdet.ne'
  -- The trace of `G⁻¹ G'` is the metric trace of `h`, since `G⁻¹` is symmetric.
  have htr : ((G t)⁻¹ * G').trace = bilinFormTrace h := by
    have hsymm := (posDef_chartGramMatrix (I := I) α hx').inv.isHermitian
    rw [← hGt] at hsymm
    rw [bilinFormTrace_eq_sum_chartInvGramMatrix α hx, chartInvGramMatrix_def, ← hGt,
      Matrix.trace_mul_comm]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, G', Matrix.of_apply]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    rw [show (G t)⁻¹ j i = (G t)⁻¹ i j by simpa using hsymm.apply i j]
    ring
  convert hsqrt using 1
  · exact funext hρ
  rw [htr, hρ t]
  field_simp [(Real.sqrt_pos.2 hdet).ne']
  rw [Real.sq_sqrt hdet.le]

/-- **The variation of the volume density.** If the metrics `g_τ` have parameter derivative `h`
at `x` at `τ = t`, then in every chart containing `x` the volume density `ρ_τ = √(det G_τ)` has
derivative `½ tr_g(h) ρ` at `t`, with the trace and the density computed for `g_t`. -/
theorem hasDerivAt_chartVolumeDensity (α : M) (hx : x ∈ (chartAt H α).source)
    {h : LinearMap.BilinForm ℝ (TangentSpace I x)}
    (hg : ∀ v w, HasDerivAt (fun τ ↦ (g τ).inner x v w) (h v w) t) :
    HasDerivAt
      (fun τ ↦ letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g τ⟩;
        chartVolumeDensity (I := I) α x)
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g t⟩;
        2⁻¹ * bilinFormTrace h * chartVolumeDensity (I := I) α x) t :=
  hasDerivWithinAt_univ.1 <|
    hasDerivWithinAt_chartVolumeDensity α hx fun v w ↦ (hg v w).hasDerivWithinAt

/-- **The volume density under a conformal variation.** If `∂_τ g = μ g` at `x` at `τ = t`
within `s`, then in real dimension `n` the chart volume density has derivative `(n μ / 2) ρ`
there. -/
theorem hasDerivWithinAt_chartVolumeDensity_of_conformal (α : M)
    (hx : x ∈ (chartAt H α).source) {μ : ℝ}
    (hg : ∀ v w, HasDerivWithinAt (fun τ ↦ (g τ).inner x v w) (μ * (g t).inner x v w) s t) :
    HasDerivWithinAt
      (fun τ ↦ letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g τ⟩;
        chartVolumeDensity (I := I) α x)
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g t⟩;
        Module.finrank ℝ E * μ / 2 * chartVolumeDensity (I := I) α x) s t := by
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g t⟩
  convert hasDerivWithinAt_chartVolumeDensity α hx (h := μ • innerₗ (TangentSpace I x)) hg
    using 1
  -- The tangent space `T_x M` is the model space `E` by definition.
  have hn : Module.finrank ℝ (TangentSpace I x) = Module.finrank ℝ E := (rfl)
  rw [map_smul, bilinFormTrace_inner, smul_eq_mul, hn]
  ring

end Variation

section RicciFlow

variable [T2Space M] [IsManifold I ∞ M]
  {g : ℝ → ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}

/-- **The volume density along a Ricci flow.** If the metrics satisfy the Ricci flow equation
`∂_τ g = -2 Ric(g)` at `x` at `τ = t` within `s`, then in every chart containing `x` the volume
density has derivative `-Scal(g_t)(x) ρ` there; that is, `∂_τ dμ_g = -Scal(g) dμ_g`. -/
theorem hasDerivWithinAt_chartVolumeDensity_of_ricciFlow (α : M)
    (hx : x ∈ (chartAt H α).source)
    (hg : ∀ v w, HasDerivWithinAt (fun τ ↦ (g τ).inner x v w)
      (-2 * (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
          ⟨(g t).toRiemannianMetric⟩;
        (CovariantDerivative.leviCivitaConnection I M).ricciTensor x v w)) s t) :
    HasDerivWithinAt
      (fun τ ↦ letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
          ⟨(g τ).toRiemannianMetric⟩;
        chartVolumeDensity (I := I) α x)
      (-(g t).scalarCurvature x *
        letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g t).toRiemannianMetric⟩;
        chartVolumeDensity (I := I) α x) s t := by
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g t).toRiemannianMetric⟩
  convert hasDerivWithinAt_chartVolumeDensity (g := fun τ ↦ (g τ).toRiemannianMetric) α hx
    (h := (-2 : ℝ) • (CovariantDerivative.leviCivitaConnection I M).ricciTensor x) hg using 1
  rw [map_smul, ContMDiffRiemannianMetric.scalarCurvature_def,
    CovariantDerivative.scalarCurvature_apply, smul_eq_mul]
  ring

end RicciFlow

end TauCeti

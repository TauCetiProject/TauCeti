/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Pullback
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Jet
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.CompTime

/-!
# Scalar curvature of a metric composed with a map of the time coordinate

For a smooth metric `G` on `M × ℝ` and a smooth `φ : ℝ → ℝ`,
`Bundle.ContMDiffRiemannianMetric.compTime` is the metric whose value at `(x, t)` is the value of
`G` at `(x, φ t)`. This file records two properties of its scalar curvature.

Translating the time coordinate is a pullback along `(x, t) ↦ (x, t + c)`, whose differential is
the identity, so the scalar curvature of `compTime` along `τ ↦ φ (τ + c)` at `(x, t)` is that of
`compTime` along `φ` at `(x, t + c)`.

For the affine maps `τ ↦ s + c τ`, the metrics `compTime` read, in the chart at `(x, 0)`, the
chart metric of `G` along the affine map `(z, τ) ↦ (z, s + c τ)`. Their coordinate `2`-jets
therefore depend continuously on `(c, s)` and the chart point, and since scalar curvature is a
continuous function of the coordinate `2`-jet
(`TauCeti.Manifold.continuousAt_scalarCurvature_of_continuousAt_chartMetric`), so does their scalar
curvature at `(x, 0)`.

## Main results

* `Bundle.ContMDiffRiemannianMetric.scalarCurvature_compTime_of_eq_add`: translation invariance of
  the scalar curvature of `compTime`.
* `Bundle.ContMDiffRiemannianMetric.continuousAt_scalarCurvature_compTime_affine`: the scalar
  curvature at `(x, 0)` of `compTime` along `τ ↦ s + c τ` is jointly continuous in `(c, s)` and
  `x`.
-/

public section

open Bundle Set Topology Filter
open TauCeti.Manifold (tangentSpaceProdEquiv tangentSpaceProdEquiv_apply)
open scoped ContDiff Manifold

noncomputable section

namespace Bundle.ContMDiffRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

variable {G : ContMDiffRiemannianMetric (I.prod 𝓘(ℝ)) ∞ (E × ℝ)
    (fun p : M × ℝ ↦ TangentSpace (I.prod 𝓘(ℝ)) p)} {φ : ℝ → ℝ}

/-- **Translation invariance.** If `ψ τ = φ (τ + c)`, then the scalar curvature of the metric
`compTime` along `ψ` at `(x, t)` is that of the metric `compTime` along `φ` at `(x, t + c)`. -/
theorem scalarCurvature_compTime_of_eq_add {ψ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hψ : ContDiff ℝ ∞ ψ) {c : ℝ} (h : ∀ τ, ψ τ = φ (τ + c)) (p : M × ℝ) :
    (G.compTime hψ).scalarCurvature p = (G.compTime hφ).scalarCurvature (p.1, p.2 + c) := by
  have hc : ContMDiff (I.prod 𝓘(ℝ)) (I.prod 𝓘(ℝ)) (∞ + 1) (Prod.map id (· + c) : M × ℝ → M × ℝ) :=
    contMDiff_id.prodMap (contDiff_id.add contDiff_const).contMDiff
  have hinv (q : M × ℝ) :
      (mfderiv (I.prod 𝓘(ℝ)) (I.prod 𝓘(ℝ)) (Prod.map id (· + c) : M × ℝ → M × ℝ) q).IsInvertible :=
    TauCeti.Manifold.isInvertible_mfderiv_prodMap_id (by fun_prop) (by simp)
  have heq : G.compTime hψ = (G.compTime hφ).pullback _ hc fun q ↦ (hinv q).injective := by
    ext q v w
    have hd (u : TangentSpace (I.prod 𝓘(ℝ)) q) :
        mfderiv (I.prod 𝓘(ℝ)) (I.prod 𝓘(ℝ)) (Prod.map id (· + c)) q u = u := by
      have := TauCeti.Manifold.tangentSpaceProdEquiv_mfderiv_prodMap_id (I := I)
        (φ := (· + c)) (p := q) (by fun_prop) u
      apply (tangentSpaceProdEquiv (I := I) (J := 𝓘(ℝ)) (q.1, q.2 + c)).injective
      rw [this, tangentSpaceProdEquiv_apply]
      simp only [deriv_add_const, deriv_id'', one_mul]
      exact (tangentSpaceProdEquiv_apply (I := I) (J := 𝓘(ℝ))
        (q.1, q.2 + c) u).symm
    rw [pullback_inner, hd, hd]
    simp only [compTime_inner]
    exact congrArg (fun y ↦ G.inner (q.1, y) v w) (h q.2)
  rw [heq]
  exact scalarCurvature_pullback_of_isInvertible _ hc hinv p

/-- The scalar curvature at `(x, 0)` of `τ ↦ G (x, s + c τ)` is jointly continuous in `(c, s)`
and `x`. -/
theorem continuousAt_scalarCurvature_compTime_affine [I.Boundaryless] (q₀ : ℝ × ℝ) (x₀ : M) :
    ContinuousAt (fun r : (ℝ × ℝ) × M ↦
      (G.compTime (φ := fun τ ↦ r.1.2 + r.1.1 * τ)
        (contDiff_const.add (contDiff_const.mul contDiff_id))).scalarCurvature (r.2, 0))
      (q₀, x₀) := by
  have hφ (q : ℝ × ℝ) : ContDiff ℝ ∞ (fun τ : ℝ ↦ q.2 + q.1 * τ) := by fun_prop
  let b := Module.finBasis ℝ (E × ℝ)
  let C := G.toNondegenerateMetric.chartMetric (x₀, (0 : ℝ))
  set T := (extChartAt I x₀).target
  have hT : IsOpen T := isOpen_extChartAt_target x₀
  have htarget : (extChartAt (I.prod 𝓘(ℝ)) (x₀, (0 : ℝ))).target = T ×ˢ univ := by
    rw [extChartAt_prod, PartialEquiv.prod_target, extChartAt_model_space_eq_id,
      PartialEquiv.refl_target]
  have hC : ContDiffOn ℝ ∞ C (T ×ˢ univ) :=
    htarget ▸ G.toNondegenerateMetric.contDiffOn_chartMetric (x₀, (0 : ℝ))
  -- In the chart at `(x₀, 0)`, the metrics `compTime` read `C` along the affine maps `A`.
  let A : (ℝ × ℝ) × (E × ℝ) → E × ℝ := fun r ↦ (r.2.1, r.1.2 + r.1.1 * r.2.2)
  have hA : ContDiff ℝ ∞ A := by fun_prop
  let V : Set ((ℝ × ℝ) × (E × ℝ)) := univ ×ˢ (T ×ˢ univ)
  have hV : IsOpen V := isOpen_univ.prod (hT.prod isOpen_univ)
  have hK (q : ℝ × ℝ) {w : E × ℝ} (hw : w ∈ T ×ˢ univ) :
      (G.compTime (hφ q)).toNondegenerateMetric.chartMetric (x₀, 0) w =
        C (A (q, w)) :=
    chartMetric_compTime _ x₀ 0 0 hw.1 w.2
  let F (i j : Fin (Module.finrank ℝ (E × ℝ))) : (ℝ × ℝ) × (E × ℝ) → ℝ :=
    fun r ↦ C (A r) (b i) (b j)
  have hF (i j) : ContDiffOn ℝ ∞ (F i j) V :=
    ((hC.comp hA.contDiffOn fun r (hr : r ∈ V) ↦
      (⟨hr.2.1, trivial⟩ : A r ∈ T ×ˢ univ)).clm_apply contDiffOn_const).clm_apply
      contDiffOn_const
  -- The first derivatives of the coefficients in the chart variable, and their equality with
  -- those of the metrics `compTime`.
  let D (i j k) : (ℝ × ℝ) × (E × ℝ) → ℝ := fun r ↦ fderiv ℝ (fun z ↦ F i j (r.1, z)) r.2 (b k)
  have hD (i j k) {r} (hr : r ∈ V) : ContDiffAt ℝ 1 (D i j k) r := by
    refine (ContDiffAt.fderiv (f := fun (r : (ℝ × ℝ) × (E × ℝ)) z ↦ F i j (r.1, z))
      (g := Prod.snd) ?_ contDiffAt_snd (m := 1) (n := ∞) (by norm_cast)).clm_apply
      contDiffAt_const
    exact ((hF i j).contDiffAt (hV.mem_nhds hr)).comp _ (by fun_prop)
  have hd₁ (i j) {r : (ℝ × ℝ) × (E × ℝ)} (hr : r ∈ V) :
      fderiv ℝ (fun z ↦ (G.compTime (hφ r.1)).toNondegenerateMetric.chartMetric
        (x₀, 0) z (b i) (b j)) r.2 = fderiv ℝ (fun z ↦ F i j (r.1, z)) r.2 := by
    refine Filter.EventuallyEq.fderiv_eq ?_
    filter_upwards [(hT.prod isOpen_univ).mem_nhds hr.2] with z hz
    rw [hK r.1 hz]
  have hd₂ (i j k) {r : (ℝ × ℝ) × (E × ℝ)} (hr : r ∈ V) :
      fderiv ℝ (fun z ↦ fderiv ℝ (fun z' ↦
        (G.compTime (hφ r.1)).toNondegenerateMetric.chartMetric (x₀, 0) z' (b i) (b j))
        z (b k)) r.2 = fderiv ℝ (fun z ↦ D i j k (r.1, z)) r.2 := by
    refine Filter.EventuallyEq.fderiv_eq ?_
    filter_upwards [(hT.prod isOpen_univ).mem_nhds hr.2] with z hz
    rw [hd₁ i j (r := (r.1, z)) ⟨trivial, hz⟩]
  have hw₀ : (q₀, extChartAt (I.prod 𝓘(ℝ)) (x₀, (0 : ℝ)) (x₀, 0)) ∈ V :=
    ⟨trivial, htarget ▸ mem_extChartAt_target (x₀, (0 : ℝ))⟩
  have hint :
      extChartAt (I.prod 𝓘(ℝ)) (x₀, (0 : ℝ)) (x₀, 0) ∈ interior (range (I.prod 𝓘(ℝ))) := by
    rw [ModelWithCorners.range_prod, ModelWithCorners.Boundaryless.range_eq_univ,
      ModelWithCorners.Boundaryless.range_eq_univ, univ_prod_univ, interior_univ]
    trivial
  -- It remains to check the continuity of the Gram matrix and of its first and second
  -- derivatives, which near `(q₀, (x₀, 0))` are those of the coefficients `F i j`.
  have hcont := TauCeti.Manifold.continuousAt_scalarCurvature_of_continuousAt_chartMetric b
    (fun q ↦ G.compTime (hφ q)) (p₀ := q₀) hint ?_ ?_ ?_
  · exact ContinuousAt.comp (f := fun r : (ℝ × ℝ) × M ↦ (r.1, (r.2, (0 : ℝ)))) (x := (q₀, x₀))
      hcont (by fun_prop)
  · refine ContinuousAt.congr (f := fun r ↦ Matrix.of fun i j ↦ F i j r) ?_
      (Filter.eventually_of_mem (hV.mem_nhds hw₀) fun r hr ↦ ?_)
    · refine continuousAt_pi.2 fun i ↦ continuousAt_pi.2 fun j ↦ ?_
      exact (hF i j).continuousOn.continuousAt (hV.mem_nhds hw₀)
    · ext i j
      simp [LinearMap.toMatrix₂_apply, hK r.1 hr.2, F]
  · refine ContinuousAt.congr (f := fun r k i j ↦ D i j k r) ?_
      (Filter.eventually_of_mem (hV.mem_nhds hw₀) fun r hr ↦ ?_)
    · refine continuousAt_pi.2 fun k ↦ continuousAt_pi.2 fun i ↦ continuousAt_pi.2 fun j ↦ ?_
      exact (hD i j k hw₀).continuousAt
    · funext k i j
      simp only [D, hd₁ i j hr]
  · refine ContinuousAt.congr
      (f := fun r m k i j ↦ fderiv ℝ (fun z ↦ D i j k (r.1, z)) r.2 (b m)) ?_
      (Filter.eventually_of_mem (hV.mem_nhds hw₀) fun r hr ↦ ?_)
    · refine continuousAt_pi.2 fun m ↦ continuousAt_pi.2 fun k ↦ continuousAt_pi.2 fun i ↦
        continuousAt_pi.2 fun j ↦ ?_
      refine (ContDiffAt.fderiv (f := fun (r : (ℝ × ℝ) × (E × ℝ)) z ↦ D i j k (r.1, z))
        (g := Prod.snd) ?_ contDiffAt_snd (m := 0) (n := 1) (by norm_num)).continuousAt.clm_apply
        continuousAt_const
      exact (hD i j k hw₀).comp
        (f := fun rz : ((ℝ × ℝ) × (E × ℝ)) × (E × ℝ) ↦ (rz.1.1, rz.2)) _ (by fun_prop)
    · funext m k i j
      simp only [hd₂ i j k hr]

end Bundle.ContMDiffRiemannianMetric

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.PositiveScalarCurvature.Concordance
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.CylinderJet
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.CompTime
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import TauCeti.Analysis.Calculus.FDeriv.Prod

/-!
# The scalar curvature of a cylinder over a path of metrics

A smooth path `s ↦ g s` of metrics on `M` is recorded by a metric `G` on `M × ℝ` which is the
cylinder metric `g τ + dτ²` at every point `(y, τ)`. In a basis of the model space let `A` be the
Gram matrix of `g t` at `x`, and `A'`, `A''` the first and second derivatives at `t` of the Gram
matrix of `g s` at `x`. The scalar curvature of `G` at `(x, t)` is
`Scal(g t)(x) - tr (A⁻¹ A'') + (3 / 4) tr ((A⁻¹ A')²) - (1 / 4) (tr (A⁻¹ A'))²`
(`Bundle.ContMDiffRiemannianMetric.scalarCurvature_eq_of_forall_inner_eq_cylinder`). In a product
chart `G` has the block Gram matrix `fromBlocks A 0 0 1`, and the formula is the jet computation
`TauCeti.Manifold.scalarCurvatureOfJet_fromBlocks_one`.

Reparametrising the path by a smooth `φ : ℝ → ℝ` gives the metric `G.compTime hφ`, the cylinder
metric `g (φ τ) + dτ²`. Its time derivatives pick up the factors `φ'` and `φ''`, and its scalar
curvature at `(x, t)` is
`φ'² Scal(G)(x, φ t) + (1 - φ'²) Scal(g (φ t))(x) - φ'' tr (A⁻¹ A')`, with `A` and `A'` taken at
`φ t` (`Bundle.ContMDiffRiemannianMetric.scalarCurvature_compTime_of_forall_inner_eq_cylinder`).
Here `tr (A⁻¹ A') / 2` is the mean curvature, the trace of the shape operator, of the slice
`M × {φ t}`.

This is the scalar curvature of the bent metric in the Gromov–Lawson surgery construction. Near a
sphere along which surgery is done, write the metric as `dr² + g r` in the distance `r` to the
sphere and the coordinates of the distance tubes. A unit speed curve `σ ↦ (r σ, h σ)` in the
`(r, h)` half-plane, whose tangent makes the angle `θ` with the `-r` direction as in
`TauCeti.IsGromovLawsonBendingCurve`, and with curvature `k`, sweeps out a hypersurface of `M × ℝ`
whose induced metric is
`dσ² + g (r σ)`: the reparametrised cylinder along `φ = r`. Since `r' = -cos θ` and
`r'' = k sin θ`, its scalar curvature is
`cos² θ Scal(M) + sin² θ Scal(g r) - k sin θ tr (A⁻¹ A')`. For the distance tubes around a point of
an `n`-manifold, `Scal(g r) = (n - 1) (n - 2) / r² + O(1)` and `tr (A⁻¹ A') = 2 (n - 1) / r + O(r)`,
which turns this into the bending term `(n - 1) (n - 2) sin² θ / r² - 2 (n - 1) k sin θ / r` up to
bounded errors. Those tube estimates are not part of this file.

## Main results

* `Bundle.ContMDiffRiemannianMetric.scalarCurvature_eq_of_forall_inner_eq_cylinder`: the scalar
  curvature of the cylinder metric `g t + dt²` of a path of metrics.
* `Bundle.ContMDiffRiemannianMetric.scalarCurvature_compTime_of_forall_inner_eq_cylinder`: the
  scalar curvature of the reparametrised cylinder metric `g (φ t) + dt²`.
* `Bundle.ContMDiffRiemannianMetric.chartMetric_apply_of_forall_inner_eq_cylinder`: the cylinder
  metric in a product chart.
* `Bundle.ContMDiffRiemannianMetric.contDiff_inner_of_forall_inner_eq_cylinder`: the path of
  metrics recorded by a cylinder metric is smooth.

## References

* P. Petersen, *Riemannian Geometry*, 3rd ed., Springer GTM 171 (2016), Chapter 3, §3.2 (metrics
  `dr² + g r` and their radial and tangential curvature equations).
* M. Gromov, H. B. Lawson, *The classification of simply connected manifolds of positive scalar
  curvature*, Ann. of Math. 111 (1980), 423–434, proof of Theorem A.
* J. Rosenberg, S. Stolz, *Metrics of positive scalar curvature and connections with surgery*,
  Surveys on surgery theory, Vol. 2, Ann. of Math. Stud. 149 (2001), 353–386, Section 3.
-/

public section

open Bundle Filter Matrix Set Topology TauCeti.Manifold
open scoped ContDiff Manifold

noncomputable section

namespace Bundle.ContMDiffRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {G : ContMDiffRiemannianMetric (I.prod 𝓘(ℝ)) ∞ (E × ℝ)
    (fun p : M × ℝ ↦ TangentSpace (I.prod 𝓘(ℝ)) p)}
  {g : ℝ → ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}

/-- In the product chart at `(x, t)`, a metric which is the cylinder metric `g τ + dτ²` at every
point `(y, τ)` pairs two vectors as the chart metric of `g τ` at `x` pairs their `E`-components,
plus the product of their `ℝ`-components. -/
theorem chartMetric_apply_of_forall_inner_eq_cylinder
    (hG : ∀ p : M × ℝ, G.inner p = (g p.2).cylinder.inner p) (x : M) (t : ℝ) {z : E}
    (hz : z ∈ (extChartAt I x).target) (τ : ℝ) (v w : E × ℝ) :
    G.toNondegenerateMetric.chartMetric (x, t) (z, τ) v w =
      (g τ).toNondegenerateMetric.chartMetric x z v.1 w.1 + v.2 * w.2 := by
  have hz₁ : (z, τ) ∈ (extChartAt (I.prod 𝓘(ℝ)) (x, t)).target := by
    rw [TauCeti.extChartAt_prod_target]
    exact ⟨hz, by simp⟩
  have hy : (extChartAt (I.prod 𝓘(ℝ)) (x, t)).symm (z, τ) = ((extChartAt I x).symm z, τ) := by
    simp only [extChartAt_prod, PartialEquiv.prod_symm, PartialEquiv.prod_coe,
      extChartAt_model_space_eq_id, PartialEquiv.refl_symm, PartialEquiv.refl_coe, id_eq]
  have hy₁ : (extChartAt I x).symm z ∈ (chartAt H x).source := by
    simpa using (extChartAt I x).map_target hz
  have hq : ((extChartAt I x).symm z, τ) ∈ (chartAt (ModelProd H ℝ) (x, t)).source := by
    simpa using hy₁
  have hbase : ((extChartAt I x).symm z, τ) ∈
      (trivializationAt (E × ℝ) (TangentSpace (I.prod 𝓘(ℝ))) (x, t)).baseSet := by
    simpa using hy₁
  have hbase₁ : (extChartAt I x).symm z ∈ (trivializationAt E (TangentSpace I) x).baseSet := by
    simpa using hy₁
  rw [ContMDiffNondegenerateMetric.chartMetric_apply _ hz₁,
    ContMDiffNondegenerateMetric.chartMetric_apply _ hz, hy]
  simp only [toNondegenerateMetric_apply, hG, cylinder_inner]
  simp only [← Trivialization.symmL_apply (R := ℝ) _ hbase,
    ← Trivialization.symmL_apply (R := ℝ) _ hbase₁, tangentSpaceProdEquiv_symmL_trivializationAt hq,
    TangentBundle.symmL_model_space]
  rfl

/-- At the centre of its chart, the chart metric of a Riemannian metric is the metric itself. -/
private theorem chartMetric_extChartAt_self_apply
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) (x : M) (v w : E) :
    g.toNondegenerateMetric.chartMetric x (extChartAt I x x) v w = g.inner x v w := by
  have hbase : x ∈ (trivializationAt E (TangentSpace I) x).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' x
  rw [ContMDiffNondegenerateMetric.chartMetric_extChartAt_apply _ (mem_extChartAt_source x),
    ← Trivialization.symmL_apply (R := ℝ) _ hbase, ← Trivialization.symmL_apply (R := ℝ) _ hbase,
    symmL_trivializationAt_self, symmL_trivializationAt_self]
  exact g.toNondegenerateMetric_apply x v w

/-- In the product chart at `(x, t)`, a metric which is the cylinder metric `g τ + dτ²` at every
point `(y, τ)` reads at `(extChartAt I x x, s)` as `g s` at `x` on `E`-vectors. -/
private theorem chartMetric_extChartAt_self_apply_of_forall_inner_eq_cylinder
    (hG : ∀ p : M × ℝ, G.inner p = (g p.2).cylinder.inner p) (x : M) (t s : ℝ) (v w : E) :
    G.toNondegenerateMetric.chartMetric (x, t) (extChartAt I x x, s) (v, 0) (w, 0) =
      (g s).inner x v w := by
  rw [chartMetric_apply_of_forall_inner_eq_cylinder hG x t (mem_extChartAt_target x),
    chartMetric_extChartAt_self_apply, mul_zero, add_zero]

/-- A metric on `M × ℝ` which is the cylinder metric `g τ + dτ²` at every point `(y, τ)` records a
smooth path of metrics: the inner product of two fixed tangent vectors at `x` under `g s` is a
smooth function of `s`. -/
theorem contDiff_inner_of_forall_inner_eq_cylinder
    (hG : ∀ p : M × ℝ, G.inner p = (g p.2).cylinder.inner p) (x : M) (v w : E) :
    ContDiff ℝ ∞ fun s ↦ (g s).inner x v w := by
  have hC := G.toNondegenerateMetric.contDiffOn_chartMetric (x, (0 : ℝ))
  rw [TauCeti.extChartAt_prod_target] at hC
  have hline : ContDiff ℝ ∞ fun s : ℝ ↦ (extChartAt I x x, s) := by fun_prop
  have := ((hC.comp (hline.contDiffOn (s := univ)) fun s _ ↦
    (⟨mem_extChartAt_target x, by simp⟩ : (extChartAt I x x, s) ∈ _ ×ˢ _)).clm_apply
      (contDiffOn_const (c := ((v, 0) : E × ℝ)))).clm_apply
        (contDiffOn_const (c := ((w, 0) : E × ℝ)))
  rw [show (fun s ↦ (g s).inner x v w) = fun s ↦
      G.toNondegenerateMetric.chartMetric (x, 0) (extChartAt I x x, s) (v, 0) (w, 0) from
    funext fun s ↦
      (chartMetric_extChartAt_self_apply_of_forall_inner_eq_cylinder hG x 0 s v w).symm]
  exact contDiffOn_univ.1 this

/-! ### The coordinate jet of a cylinder over a path of metrics -/

/-- A function which is constant on an open set has vanishing first and second derivatives
there. -/
private theorem fderiv_eq_zero_of_eqOn_const {φ : E × ℝ → ℝ} {U : Set (E × ℝ)} (hU : IsOpen U)
    {c : ℝ} (h : EqOn φ (fun _ ↦ c) U) {w : E × ℝ} (hw : w ∈ U) (u v : E × ℝ) :
    fderiv ℝ φ w u = 0 ∧ fderiv ℝ (fun w' ↦ fderiv ℝ φ w' u) w v = 0 := by
  have h₁ {w' : E × ℝ} (hw' : w' ∈ U) : fderiv ℝ φ w' = 0 := by
    rw [Filter.EventuallyEq.fderiv_eq (Filter.eventuallyEq_of_mem (hU.mem_nhds hw') h),
      fderiv_const_apply]
  refine ⟨by simp [h₁ hw], ?_⟩
  have h₂ : (fun w' ↦ fderiv ℝ φ w' u) =ᶠ[𝓝 w] fun _ ↦ 0 := by
    filter_upwards [hU.mem_nhds hw] with w' hw'
    simp [h₁ hw']
  simp [h₂.fderiv_eq]

section Jet

variable [I.Boundaryless] (hG : ∀ p : M × ℝ, G.inner p = (g p.2).cylinder.inner p) (x : M)
  (t : ℝ)
include hG

omit [I.Boundaryless] in
/-- On the chart target, a coefficient of the chart metric of a cylinder metric involving the
`ℝ`-direction `(0, 1)` is constant. -/
private theorem eqOn_chartMetric_apply_of_forall_inner_eq_cylinder (u w : E × ℝ)
    (hu : u.1 = 0 ∨ w.1 = 0) :
    EqOn (fun q ↦ G.toNondegenerateMetric.chartMetric (x, t) q u w) (fun _ ↦ u.2 * w.2)
      ((extChartAt I x).target ×ˢ univ) := by
  rintro ⟨z, τ⟩ ⟨hz, -⟩
  dsimp only
  rw [chartMetric_apply_of_forall_inner_eq_cylinder hG x t hz]
  rcases hu with hu | hu <;> simp [hu]

omit [I.Boundaryless] hG in
/-- The coefficient of the chart metric of a cylinder metric on two `E`-vectors is smooth on the
chart target. -/
private theorem contDiffOn_chartMetric_apply_of_forall_inner_eq_cylinder (v w : E) :
    ContDiffOn ℝ ∞ (fun q ↦ G.toNondegenerateMetric.chartMetric (x, t) q (v, 0) (w, 0))
      ((extChartAt I x).target ×ˢ univ) := by
  have hC := G.toNondegenerateMetric.contDiffOn_chartMetric (x, t)
  rw [TauCeti.extChartAt_prod_target, extChartAt_model_space_eq_id,
    PartialEquiv.refl_target] at hC
  exact (hC.clm_apply contDiffOn_const).clm_apply contDiffOn_const

/-- The first and second derivatives in the `E`-directions of a coefficient of the chart metric of
a cylinder metric at `(z, t)` are those of the chart metric of `g t` at `z`. -/
private theorem fderiv_chartMetric_apply_of_forall_inner_eq_cylinder {z : E}
    (hz : z ∈ (extChartAt I x).target) (u u' v w : E) :
    fderiv ℝ (fun q ↦ G.toNondegenerateMetric.chartMetric (x, t) q (v, 0) (w, 0)) (z, t) (u, 0) =
      fderiv ℝ (fun z ↦ (g t).toNondegenerateMetric.chartMetric x z v w) z u ∧
    fderiv ℝ (fun q ↦ fderiv ℝ (fun q ↦ G.toNondegenerateMetric.chartMetric (x, t) q (v, 0)
        (w, 0)) q (u, 0)) (z, t) (u', 0) =
      fderiv ℝ (fun z ↦ fderiv ℝ (fun z ↦ (g t).toNondegenerateMetric.chartMetric x z v w) z u)
        z u' := by
  set T := (extChartAt I x).target
  have hT : IsOpen T := isOpen_extChartAt_target x
  have hU : IsOpen (T ×ˢ (univ : Set ℝ)) := hT.prod isOpen_univ
  set F := fun q ↦ G.toNondegenerateMetric.chartMetric (x, t) q (v, 0) (w, 0)
  have hF := contDiffOn_chartMetric_apply_of_forall_inner_eq_cylinder (G := G) x t v w
  -- On the slice through `t`, the coefficient is that of the chart metric of `g t`.
  have h₁ {z : E} (hz : z ∈ T) :
      fderiv ℝ F (z, t) (u, 0) = fderiv ℝ (fun z ↦ (g t).toNondegenerateMetric.chartMetric x z v w)
        z u := by
    have hd : DifferentiableAt ℝ F (z, t) :=
      (hF.contDiffAt (hU.mem_nhds ⟨hz, trivial⟩)).differentiableAt (by simp)
    rw [show fderiv ℝ F (z, t) (u, 0) = fderiv ℝ (fun z ↦ F (z, t)) z u by
      simp [TauCeti.fderiv_slice_left hd]]
    refine congrArg (fun L : E →L[ℝ] ℝ ↦ L u) (Filter.EventuallyEq.fderiv_eq ?_)
    filter_upwards [hT.mem_nhds hz] with z' hz'
    simp [F, chartMetric_apply_of_forall_inner_eq_cylinder hG x t hz']
  refine ⟨h₁ hz, ?_⟩
  have hD : DifferentiableAt ℝ (fun q ↦ fderiv ℝ F q (u, 0)) (z, t) :=
    (((hF.fderiv_of_isOpen hU (m := 1) (by simp)).clm_apply contDiffOn_const).contDiffAt
      (hU.mem_nhds ⟨hz, trivial⟩)).differentiableAt (by simp)
  rw [show fderiv ℝ (fun q ↦ fderiv ℝ F q (u, 0)) (z, t) (u', 0) =
      fderiv ℝ (fun z ↦ fderiv ℝ F (z, t) (u, 0)) z u' by simp [TauCeti.fderiv_slice_left hD]]
  refine congrArg (fun L : E →L[ℝ] ℝ ↦ L u') (Filter.EventuallyEq.fderiv_eq ?_)
  filter_upwards [hT.mem_nhds hz] with z' hz'
  exact h₁ hz'

/-- The first and second derivatives in the `ℝ`-direction of a coefficient of the chart metric
of a cylinder metric at the centre of the chart are those of the path `s ↦ g s` at `x`. -/
private theorem deriv_chartMetric_apply_of_forall_inner_eq_cylinder (v w : E) (s : ℝ) :
    fderiv ℝ (fun q ↦ G.toNondegenerateMetric.chartMetric (x, t) q (v, 0) (w, 0))
        (extChartAt I x x, s) (0, 1) = deriv (fun s ↦ (g s).inner x v w) s ∧
    fderiv ℝ (fun q ↦ fderiv ℝ (fun q ↦ G.toNondegenerateMetric.chartMetric (x, t) q (v, 0)
        (w, 0)) q (0, 1)) (extChartAt I x x, s) (0, 1) =
      deriv (deriv fun s ↦ (g s).inner x v w) s := by
  have hU : IsOpen ((extChartAt I x).target ×ˢ (univ : Set ℝ)) :=
    (isOpen_extChartAt_target x).prod isOpen_univ
  have hmem (s : ℝ) : (extChartAt I x x, s) ∈ (extChartAt I x).target ×ˢ (univ : Set ℝ) :=
    ⟨mem_extChartAt_target x, trivial⟩
  set F := fun q ↦ G.toNondegenerateMetric.chartMetric (x, t) q (v, 0) (w, 0)
  have hF := contDiffOn_chartMetric_apply_of_forall_inner_eq_cylinder (G := G) x t v w
  -- Along the line through the centre of the chart, the coefficient is the path `s ↦ g s`.
  have h₁ (s : ℝ) :
      fderiv ℝ F (extChartAt I x x, s) (0, 1) = deriv (fun s ↦ (g s).inner x v w) s := by
    have hd : DifferentiableAt ℝ F (extChartAt I x x, s) :=
      (hF.contDiffAt (hU.mem_nhds (hmem s))).differentiableAt (by simp)
    rw [← (TauCeti.hasDerivAt_slice_right hd).deriv]
    exact congrArg (deriv · s) (funext fun s' ↦
      chartMetric_extChartAt_self_apply_of_forall_inner_eq_cylinder hG x t s' v w)
  refine ⟨h₁ s, ?_⟩
  have hD : DifferentiableAt ℝ (fun q ↦ fderiv ℝ F q (0, 1)) (extChartAt I x x, s) :=
    (((hF.fderiv_of_isOpen hU (m := 1) (by simp)).clm_apply contDiffOn_const).contDiffAt
      (hU.mem_nhds (hmem s))).differentiableAt (by simp)
  rw [← (TauCeti.hasDerivAt_slice_right hD).deriv]
  exact congrArg (deriv · s) (funext h₁)

end Jet

/-- The Gram matrix of the chart metric at the centre of the chart is that of the metric. -/
private theorem toMatrix₂_chartMetric_extChartAt_self
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) (x : M) {ι : Type*}
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E) :
    LinearMap.toMatrix₂ b b (g.toNondegenerateMetric.chartMetric x (extChartAt I x x)).toBilinForm =
      of fun i j ↦ g.inner x (b i) (b j) := by
  ext i j
  rw [LinearMap.toMatrix₂_apply, ContinuousLinearMap.toBilinForm_apply, of_apply,
    chartMetric_extChartAt_self_apply]

/-- In the product chart at `(x, t)`, the Gram matrix of a cylinder metric at
`(extChartAt I x x, t)` in the basis `b.prod (Module.Basis.singleton Unit ℝ)` is block diagonal,
with the Gram matrix of the chart metric of `g t` and the `1 × 1` identity on the diagonal. -/
private theorem toMatrix₂_chartMetric_of_forall_inner_eq_cylinder
    (hG : ∀ p : M × ℝ, G.inner p = (g p.2).cylinder.inner p) (x : M) (t : ℝ) {ι : Type*}
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E) :
    LinearMap.toMatrix₂ (b.prod (Module.Basis.singleton Unit ℝ))
        (b.prod (Module.Basis.singleton Unit ℝ))
        (G.toNondegenerateMetric.chartMetric (x, t) (extChartAt I x x, t)).toBilinForm =
      fromBlocks (LinearMap.toMatrix₂ b b
        ((g t).toNondegenerateMetric.chartMetric x (extChartAt I x x)).toBilinForm) 0 0 1 := by
  ext (i | u) (j | u') <;>
    simp only [LinearMap.toMatrix₂_apply, ContinuousLinearMap.toBilinForm_apply,
      Module.Basis.prod_apply, Sum.elim_inl, Sum.elim_inr, Function.comp_apply,
      LinearMap.inl_apply, LinearMap.inr_apply, fromBlocks_apply₁₁, fromBlocks_apply₁₂,
      fromBlocks_apply₂₁, fromBlocks_apply₂₂,
      chartMetric_apply_of_forall_inner_eq_cylinder hG x t (mem_extChartAt_target x)] <;>
    simp

/-- **The scalar curvature of a cylinder over a path of metrics.** Let `G` be a metric on `M × ℝ`
which is the cylinder metric `g τ + dτ²` at every point `(y, τ)`. In a basis `b` of the model space,
let `A` be the Gram matrix of `g t` at `x`, and `A'`, `A''` the entrywise first and second
derivatives at `t` of the Gram matrix of `g s` at `x`. Then the scalar curvature of `G` at `(x, t)`
is `Scal(g t)(x) - tr (A⁻¹ A'') + (3 / 4) tr ((A⁻¹ A')²) - (1 / 4) (tr (A⁻¹ A'))²`. -/
theorem scalarCurvature_eq_of_forall_inner_eq_cylinder [I.Boundaryless] [FiniteDimensional ℝ E]
    [T2Space M] (hG : ∀ p : M × ℝ, G.inner p = (g p.2).cylinder.inner p) {ι : Type*}
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E) (x : M) (t : ℝ) :
    G.scalarCurvature (x, t) = (g t).scalarCurvature x -
        ((of fun i j ↦ (g t).inner x (b i) (b j))⁻¹ *
          of fun i j ↦ iteratedDeriv 2 (fun s ↦ (g s).inner x (b i) (b j)) t).trace +
      3 / 4 * (((of fun i j ↦ (g t).inner x (b i) (b j))⁻¹ *
          of fun i j ↦ deriv (fun s ↦ (g s).inner x (b i) (b j)) t) *
        ((of fun i j ↦ (g t).inner x (b i) (b j))⁻¹ *
          of fun i j ↦ deriv (fun s ↦ (g s).inner x (b i) (b j)) t)).trace -
      1 / 4 * ((of fun i j ↦ (g t).inner x (b i) (b j))⁻¹ *
          of fun i j ↦ deriv (fun s ↦ (g s).inner x (b i) (b j)) t).trace ^ 2 := by
  set bb := b.prod (Module.Basis.singleton Unit ℝ)
  have hbl (i : ι) : bb (.inl i) = (b i, 0) := by simp [bb]
  have hbr (u : Unit) : bb (.inr u) = (0, 1) := by simp [bb]
  have hz₀ : extChartAt I x x ∈ (extChartAt I x).target := mem_extChartAt_target x
  have hU : IsOpen ((extChartAt I x).target ×ˢ (univ : Set ℝ)) :=
    (isOpen_extChartAt_target x).prod isOpen_univ
  have hw₀ : extChartAt (I.prod 𝓘(ℝ)) (x, t) (x, t) = (extChartAt I x x, t) := by simp
  have hint₁ : extChartAt (I.prod 𝓘(ℝ)) (x, t) (x, t) ∈ interior (range (I.prod 𝓘(ℝ))) := by
    rw [ModelWithCorners.range_prod, ModelWithCorners.Boundaryless.range_eq_univ,
      ModelWithCorners.Boundaryless.range_eq_univ, univ_prod_univ, interior_univ]
    trivial
  have hint₂ : extChartAt I x x ∈ interior (range I) := by
    rw [ModelWithCorners.Boundaryless.range_eq_univ, interior_univ]
    trivial
  rw [G.scalarCurvature_eq_scalarCurvatureOfJet bb (mem_extChartAt_source (x, t)) hint₁,
    (g t).scalarCurvature_eq_scalarCurvatureOfJet b (mem_extChartAt_source x) hint₂, hw₀]
  have hAeq := toMatrix₂_chartMetric_extChartAt_self (g t) x b
  have hgram := toMatrix₂_chartMetric_of_forall_inner_eq_cylinder hG x t b
  generalize hA' : LinearMap.toMatrix₂ b b
    ((g t).toNondegenerateMetric.chartMetric x (extChartAt I x x)).toBilinForm = A at hAeq hgram ⊢
  have hA : IsUnit A := by
    rw [Matrix.isUnit_iff_isUnit_det, ← hA']
    exact ((LinearMap.nondegenerate_iff_det_ne_zero b).1
      ((g t).toNondegenerateMetric.nondegenerate_chartMetric hz₀)).isUnit
  have hAs : A.IsSymm := by
    rw [hAeq]
    exact IsSymm.ext fun i j ↦ by simp [(g t).symm x (b i) (b j)]
  -- The coefficients involving the `ℝ`-direction are constant near the centre of the chart.
  have hz (a a' : ι ⊕ Unit) (h : (bb a).1 = 0 ∨ (bb a').1 = 0) (u v : E × ℝ) :=
    fderiv_eq_zero_of_eqOn_const hU
      (eqOn_chartMetric_apply_of_forall_inner_eq_cylinder hG x t (bb a) (bb a') h)
      (⟨hz₀, trivial⟩ : (extChartAt I x x, t) ∈ (extChartAt I x).target ×ˢ (univ : Set ℝ)) u v
  have e₁ (u v w : E) := (fderiv_chartMetric_apply_of_forall_inner_eq_cylinder hG x t hz₀ u 0 v w).1
  have e₂ (u u' v w : E) :=
    (fderiv_chartMetric_apply_of_forall_inner_eq_cylinder hG x t hz₀ u u' v w).2
  have e₃ (v w : E) := (deriv_chartMetric_apply_of_forall_inner_eq_cylinder hG x t v w t).1
  have e₄ (v w : E) := (deriv_chartMetric_apply_of_forall_inner_eq_cylinder hG x t v w t).2
  have hsymm (v w : E) : (fun s ↦ (g s).inner x v w) = fun s ↦ (g s).inner x w v :=
    funext fun s ↦ (g s).symm x v w
  rw [hgram, scalarCurvatureOfJet_fromBlocks_one hA (fun k i ↦ (hz _ _ (by simp [hbr]) _ 0).1)
    (fun k j ↦ (hz _ _ (by simp [hbr]) _ 0).1) (fun k ↦ (hz _ _ (by simp [hbr]) _ 0).1)
    (fun m k i ↦ (hz _ _ (by simp [hbr]) _ _).2) (fun m k j ↦ (hz _ _ (by simp [hbr]) _ _).2)
    (fun m k ↦ (hz _ _ (by simp [hbr]) _ _).2) (fun i j ↦ by simp only [hbl, hbr, e₃, hsymm])
    hAs (fun i j ↦ by simp only [hbl, hbr, e₄, hsymm])]
  have h₂ (f : ℝ → ℝ) : iteratedDeriv 2 f = deriv (deriv f) := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  simp only [hbl, hbr, e₁, e₂, e₃, e₄, hAeq, h₂]

/-- **The scalar curvature of a reparametrised cylinder.** Let `G` be a metric on `M × ℝ` which is
the cylinder metric `g τ + dτ²` at every point `(y, τ)`, and `φ : ℝ → ℝ` smooth, so that
`G.compTime hφ` is the cylinder metric `g (φ τ) + dτ²` of the reparametrised path. With `A` the Gram
matrix of `g (φ t)` at `x` in a basis `b`, and `A'` the entrywise derivative at `φ t` of the Gram
matrix of `g s` at `x`, its scalar curvature at `(x, t)` is
`φ'(t)² Scal(G)(x, φ t) + (1 - φ'(t)²) Scal(g (φ t))(x) - φ''(t) tr (A⁻¹ A')`.

Here `tr (A⁻¹ A') / 2` is the mean curvature, the trace of the shape operator, of the slice
`M × {φ t}` in `G`. If `t ↦ (φ t, h t)` is a unit speed curve in the plane whose tangent makes the
angle `θ` with the `-τ` direction, with curvature `k`, then `φ' = -cos θ` and `φ'' = k sin θ`, and
this is the scalar curvature of the hypersurface `{(y, φ t, h t)}` of `M × ℝ × ℝ` with the metric
`G + dh²`. In the Gromov–Lawson construction it yields the bending term. -/
theorem scalarCurvature_compTime_of_forall_inner_eq_cylinder [I.Boundaryless]
    [FiniteDimensional ℝ E] [T2Space M] (hG : ∀ p : M × ℝ, G.inner p = (g p.2).cylinder.inner p)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ E) (x : M) (t : ℝ) :
    (G.compTime hφ).scalarCurvature (x, t) =
      deriv φ t ^ 2 * G.scalarCurvature (x, φ t) +
        (1 - deriv φ t ^ 2) * (g (φ t)).scalarCurvature x -
        iteratedDeriv 2 φ t * ((of fun i j ↦ (g (φ t)).inner x (b i) (b j))⁻¹ *
          of fun i j ↦ deriv (fun s ↦ (g s).inner x (b i) (b j)) (φ t)).trace := by
  have hG' (p : M × ℝ) : (G.compTime hφ).inner p = (g (φ p.2)).cylinder.inner p := by
    rw [compTime_inner, hG]
    exact cylinder_inner_mk _ _ _ _
  rw [scalarCurvature_eq_of_forall_inner_eq_cylinder (g := fun s ↦ g (φ s)) hG' b x t,
    scalarCurvature_eq_of_forall_inner_eq_cylinder hG b x (φ t)]
  -- The chain rule for the reparametrised Gram matrix.
  have hψ (i j : ι) := contDiff_inner_of_forall_inner_eq_cylinder hG x (b i) (b j)
  have h₁ (i j : ι) : deriv (fun s ↦ (g (φ s)).inner x (b i) (b j)) t =
      deriv φ t * deriv (fun s ↦ (g s).inner x (b i) (b j)) (φ t) := by
    rw [mul_comm]
    exact deriv_comp (h₂ := fun s ↦ (g s).inner x (b i) (b j)) t
      ((hψ i j).differentiable (by simp) _) (hφ.differentiable (by simp) _)
  have h₂ (i j : ι) : iteratedDeriv 2 (fun s ↦ (g (φ s)).inner x (b i) (b j)) t =
      deriv φ t ^ 2 * iteratedDeriv 2 (fun s ↦ (g s).inner x (b i) (b j)) (φ t) +
        iteratedDeriv 2 φ t * deriv (fun s ↦ (g s).inner x (b i) (b j)) (φ t) := by
    rw [show (fun s ↦ (g (φ s)).inner x (b i) (b j)) =
      (fun s ↦ (g s).inner x (b i) (b j)) ∘ φ from rfl,
      iteratedDeriv_comp_two ((hψ i j).contDiffAt.of_le (by simp)) (hφ.contDiffAt.of_le (by simp))]
    ring
  set A := of fun i j ↦ (g (φ t)).inner x (b i) (b j)
  set D₁ := of fun i j ↦ deriv (fun s ↦ (g s).inner x (b i) (b j)) (φ t)
  set D₂ := of fun i j ↦ iteratedDeriv 2 (fun s ↦ (g s).inner x (b i) (b j)) (φ t)
  have hd₁ : (of fun i j ↦ deriv (fun s ↦ (g (φ s)).inner x (b i) (b j)) t) = deriv φ t • D₁ := by
    ext i j
    simp [D₁, h₁]
  have hd₂ : (of fun i j ↦ iteratedDeriv 2 (fun s ↦ (g (φ s)).inner x (b i) (b j)) t) =
      deriv φ t ^ 2 • D₂ + iteratedDeriv 2 φ t • D₁ := by
    ext i j
    simp [D₁, D₂, h₂]
  rw [hd₁, hd₂]
  simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.smul_mul, trace_add, trace_smul, smul_eq_mul]
  ring

end Bundle.ContMDiffRiemannianMetric

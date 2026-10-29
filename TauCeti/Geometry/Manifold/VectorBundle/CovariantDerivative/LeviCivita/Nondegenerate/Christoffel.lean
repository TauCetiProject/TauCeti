/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Coordinate.Frame
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Christoffel.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Nondegenerate.Basic
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import TauCeti.LinearAlgebra.Matrix.BilinearForm

/-!
# Christoffel symbols of a nondegenerate Levi-Civita connection in a chart

Let `g` be a smooth symmetric nondegenerate metric on `M`, of any signature. Read in the chart at
`x₀`, it becomes a field `chartMetric g x₀ : E → E →L[ℝ] E →L[ℝ] ℝ` of symmetric nondegenerate
bilinear forms on the chart target. This file identifies the Christoffel map of a Levi-Civita
connection of `g`, read in the canonical tangent-bundle trivialization at `x₀`, with the
Christoffel symbols of the second kind `christoffelSecondKind` of the chart metric. In particular
the scalar Christoffel symbols of the connection are given on the chart domain by the classical
index formula

`Γᵏᵢⱼ = (1/2) Σ_l g^(kl) (∂ᵢ g_jl + ∂ⱼ g_il - ∂_l g_ij)`.

The index formula using derivatives within the chart target holds throughout the chart domain,
including boundary and corner points. At interior chart points it also holds with unrestricted
Fréchet derivatives, giving the comparison with `christoffelSecondKind`. Its metric input is
the coordinate form `Dg(u)(v, w) = g(Γ(u, v), w) + g(v, Γ(u, w))` of metric compatibility, valid
for every compatible connection. No extension of the chart metric to an open model domain is
assumed in the within-derivative formula.

## Main definitions and results

In the namespace `TauCeti.Manifold.ContMDiffNondegenerateMetric`:

* `IsMetricCompatible.fderivWithin_chartMetric_apply`: metric compatibility throughout a chart
  target, using within derivatives; `fderiv_chartMetric_apply` is its interior form.
* `IsLeviCivitaConnection.christoffelMap_apply_eq_christoffelSecondKind`: the Christoffel map of a
  Levi-Civita connection is given by the Christoffel symbols of the second kind of the chart
  metric.
* `IsLeviCivitaConnection.christoffelSymbol_eq_fderivWithin`: the inverse-matrix index formula
  throughout the chart domain; `christoffelSymbol_eq` is its interior form.
* `IsLeviCivitaConnection.christoffelSymbol_eventuallyEq`: near a point, the scalar Christoffel
  symbols are the coordinates of the Christoffel symbols of the second kind of the chart metric.

## References

* B. O'Neill, *Semi-Riemannian Geometry with Applications to Relativity*, Academic Press, 1983,
  Ch. 3, the Christoffel symbols of the Levi-Civita connection in a coordinate system.
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Ch. 5,
  the formula for the Christoffel symbols of the Levi-Civita connection in coordinates.
-/

public section

noncomputable section

open Bundle FiberBundle Filter Module Set
open scoped ContDiff Manifold Topology

namespace TauCeti.Manifold.ContMDiffNondegenerateMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  (g : ContMDiffNondegenerateMetric (I := I) (M := M)) {x₀ y : M}

/-! ### Metric compatibility in coordinates -/

section Coordinates

variable [FiniteDimensional ℝ E] {g} {ι : Type*} [Fintype ι] (b : Basis ι ℝ E)
  {cov : CovariantDerivative I E (fun x : M ↦ TangentSpace I x)}

/-- **Metric compatibility in coordinates.** Let `∇` be compatible with the nondegenerate metric
`g`, and let `y` be any point of the chart domain at `x₀`, including a boundary or corner point.
Writing `G` for the chart metric and `Γ(u, v) = christoffelMap b _ y v u` for the
Christoffel map of `∇` in the trivialization at `x₀`, applied to the field value `v` and the
direction `u`, the derivative within the chart target is
`DG(u)(v, w) = G(Γ(u, v), w) + G(v, Γ(u, w))`.
-/
theorem IsMetricCompatible.fderivWithin_chartMetric_apply (h : g.IsMetricCompatible cov)
    (hy : y ∈ (extChartAt I x₀).source)
    (u v w : E) :
    fderivWithin ℝ (g.chartMetric x₀) (extChartAt I x₀).target (extChartAt I x₀ y) u v w =
      g.chartMetric x₀ (extChartAt I x₀ y)
          (christoffelMap b (cov.isCovariantDerivativeOn
            (s := (trivializationAt E (TangentSpace I) x₀).baseSet)) y v u) w +
        g.chartMetric x₀ (extChartAt I x₀ y) v
          (christoffelMap b (cov.isCovariantDerivativeOn
            (s := (trivializationAt E (TangentSpace I) x₀).baseSet)) y w u) := by
  set e := trivializationAt E (TangentSpace I) x₀
  have hbase : y ∈ e.baseSet := by simpa [e] using hy
  have hcov := cov.isCovariantDerivativeOn (s := e.baseSet)
  have hd := ((g.contDiffOn_chartMetric x₀) _ ((extChartAt I x₀).map_source hy))
    |>.differentiableWithinAt (by simp)
  have hV (v : E) : MDiffAt (T% (fun y' ↦ e.symm y' v)) y :=
    ((contMDiffOn_symm_baseSet (n := 1) v).mdifferentiableOn one_ne_zero).mdifferentiableAt
      (e.open_baseSet.mem_nhds hbase)
  -- The pairing of the fields with constant coordinates `v` and `w` is, near `y`, the chart
  -- metric evaluated on `v` and `w`, composed with the chart.
  have hloc : (fun y' ↦ g y' (e.symm y' v) (e.symm y' w)) =ᶠ[𝓝 y]
      (fun z ↦ g.chartMetric x₀ z v w) ∘ extChartAt I x₀ :=
    eventually_of_mem ((isOpen_extChartAt_source x₀).mem_nhds hy) fun y' hy' ↦
      (g.chartMetric_extChartAt_apply hy' v w).symm
  have hF : HasMFDerivWithinAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ)
      (fun z ↦ g.chartMetric x₀ z v w) (extChartAt I x₀).target (extChartAt I x₀ y)
      (((fderivWithin ℝ (g.chartMetric x₀) (extChartAt I x₀).target
        (extChartAt I x₀ y)).flip v).flip w) := by
    simpa only [ContinuousLinearMap.comp_zero, zero_add] using
      ((hd.hasFDerivWithinAt.clm_apply
        (hasFDerivWithinAt_const v (extChartAt I x₀ y) (extChartAt I x₀).target)).clm_apply
          (hasFDerivWithinAt_const w (extChartAt I x₀ y) (extChartAt I x₀).target))
        |>.hasMFDerivWithinAt
  have hderiv := (((hF.comp y
      (mdifferentiableAt_extChartAt (by simpa using hy)).hasMFDerivAt.hasMFDerivWithinAt
      (fun _ hz ↦ (extChartAt I x₀).map_source hz)).hasMFDerivAt
        ((isOpen_extChartAt_source x₀).mem_nhds hy))
      |>.congr_of_eventuallyEq hloc).mfderiv
  have hcomp : mvfderiv I (fun y' ↦ g y' (e.symm y' v) (e.symm y' w)) y (e.symm y u) =
      g y (cov (fun y' ↦ e.symm y' v) y (e.symm y u)) (e.symm y w) +
        g y (e.symm y v) (cov (fun y' ↦ e.symm y' w) y (e.symm y u)) :=
    h.mvfderiv_eq (hV v) (hV w) (e.symm y u)
  rw [covariantDerivative_symm_apply_symm b hcov hbase,
    covariantDerivative_symm_apply_symm b hcov hbase,
    ← g.chartMetric_extChartAt_apply hy, ← g.chartMetric_extChartAt_apply hy] at hcomp
  rw [← hcomp]
  have hφ : mfderiv% (extChartAt I x₀) y (e.symm y u) = u := by
    rw [← TangentBundle.continuousLinearMapAt_trivializationAt (by simpa using hy),
      ← e.symmL_apply (R := ℝ) hbase]
    exact e.continuousLinearMapAt_symmL hbase u
  simp only [mvfderiv, hderiv, ContinuousLinearMap.comp_apply]
  -- The tangent identifications for the scalar model space are definitionally identities.
  change _ = fderivWithin ℝ (g.chartMetric x₀) (extChartAt I x₀).target
    (extChartAt I x₀ y) (mfderiv% (extChartAt I x₀) y (e.symm y u)) v w
  rw [hφ]

/-- **Metric compatibility in coordinates.** Let `∇` be compatible with the nondegenerate metric
`g`, and let `y` be a point of the chart domain at `x₀` whose chart image lies in the interior of
the model. Writing `G` for the chart metric and `Γ(u, v) = christoffelMap b _ y v u` for the
Christoffel map of `∇` in the trivialization at `x₀`, applied to the field value `v` and the
direction `u`, the derivative of the chart metric is `DG(u)(v, w) = G(Γ(u, v), w) + G(v, Γ(u, w))`.
-/
theorem IsMetricCompatible.fderiv_chartMetric_apply (h : g.IsMetricCompatible cov)
    (hy : y ∈ (extChartAt I x₀).source) (hint : extChartAt I x₀ y ∈ interior (range I))
    (u v w : E) :
    fderiv ℝ (g.chartMetric x₀) (extChartAt I x₀ y) u v w =
      g.chartMetric x₀ (extChartAt I x₀ y)
          (christoffelMap b (cov.isCovariantDerivativeOn
            (s := (trivializationAt E (TangentSpace I) x₀).baseSet)) y v u) w +
        g.chartMetric x₀ (extChartAt I x₀ y) v
          (christoffelMap b (cov.isCovariantDerivativeOn
            (s := (trivializationAt E (TangentSpace I) x₀).baseSet)) y w u) := by
  have htarget : (extChartAt I x₀).target ∈ 𝓝 (extChartAt I x₀ y) := by
    rw [← nhdsWithin_eq_nhds.2 (mem_interior_iff_mem_nhds.1 hint)]
    exact extChartAt_target_mem_nhdsWithin' hy
  simpa only [fderivWithin_of_mem_nhds (f := g.chartMetric x₀) htarget] using
    h.fderivWithin_chartMetric_apply b hy u v w

/-! ### The Christoffel symbols of a Levi-Civita connection -/

/-- **The Christoffel map of a Levi-Civita connection in a chart.** Let `∇` be a Levi-Civita
connection of the nondegenerate metric `g`, and let `y` be a point of the chart domain at `x₀`
whose chart image lies in the interior of the model. The Christoffel map of `∇` in the
trivialization at `x₀`, applied to the field value `v` and the direction `u`, is the Christoffel
symbol of the second kind `christoffelSecondKind` of the chart metric at the chart image of `y`,
applied to `u` and `v`. -/
theorem IsLeviCivitaConnection.christoffelMap_apply_eq_christoffelSecondKind
    (h : g.IsLeviCivitaConnection cov) (hy : y ∈ (extChartAt I x₀).source)
    (hint : extChartAt I x₀ y ∈ interior (range I)) (v u : E) :
    christoffelMap b (cov.isCovariantDerivativeOn
        (s := (trivializationAt E (TangentSpace I) x₀).baseSet)) y v u =
      christoffelSecondKind (g.chartMetric x₀) (extChartAt I x₀ y) u v := by
  have : IsManifold I (minSmoothness ℝ 2) M := by
    rw [minSmoothness_of_isRCLikeNormedField]; infer_instance
  have ht : cov.IsTorsionFree :=
    (CovariantDerivative.isTorsionFree_iff_torsion_eq_zero cov).2 h.torsion
  have hA := eq_christoffelSecondKind_of_fderiv_apply_eq (g := g.chartMetric x₀)
    (x := extChartAt I x₀ y) (g.isSymm_chartMetric ((extChartAt I x₀).map_source hy))
    (g.nondegenerate_chartMetric ((extChartAt I x₀).map_source hy))
    (A := (christoffelMap b (cov.isCovariantDerivativeOn
      (s := (trivializationAt E (TangentSpace I) x₀).baseSet)) y).flip)
    (fun u v ↦ by simp only [ContinuousLinearMap.flip_apply, christoffelMap_comm ht b x₀ hy])
    (fun u v w ↦ by
      simpa only [ContinuousLinearMap.flip_apply] using
        h.isMetricCompatible.fderiv_chartMetric_apply b hy hint u v w)
  rw [← hA, ContinuousLinearMap.flip_apply]

/-- **The index formula on the whole chart domain.** The coordinate partial derivatives are
Fréchet derivatives within the chart target, so the formula includes boundary and corner points
and requires no extension of the metric to an open subset of the model space. -/
theorem IsLeviCivitaConnection.christoffelSymbol_eq_fderivWithin [DecidableEq ι]
    (h : g.IsLeviCivitaConnection cov) (hy : y ∈ (extChartAt I x₀).source)
    (i j k : ι) :
    christoffelSymbol I b (trivializationAt E (TangentSpace I) x₀) cov i j k y =
      2⁻¹ * ∑ l, (LinearMap.toMatrix₂ b b
          (g.chartMetric x₀ (extChartAt I x₀ y)).toBilinForm)⁻¹ k l *
        (fderivWithin ℝ (g.chartMetric x₀) (extChartAt I x₀).target
            (extChartAt I x₀ y) (b i) (b j) (b l) +
          fderivWithin ℝ (g.chartMetric x₀) (extChartAt I x₀).target
            (extChartAt I x₀ y) (b j) (b i) (b l) -
          fderivWithin ℝ (g.chartMetric x₀) (extChartAt I x₀).target
            (extChartAt I x₀ y) (b l) (b i) (b j)) := by
  let A := christoffelMap b (cov.isCovariantDerivativeOn
    (s := (trivializationAt E (TangentSpace I) x₀).baseSet)) y
  let G := g.chartMetric x₀ (extChartAt I x₀ y)
  let D := fderivWithin ℝ (g.chartMetric x₀) (extChartAt I x₀).target (extChartAt I x₀ y)
  have hg (v w : E) : G v w = G w v :=
    (g.isSymm_chartMetric ((extChartAt I x₀).map_source hy)).eq v w
  have : IsManifold I (minSmoothness ℝ 2) M := by
    rw [minSmoothness_of_isRCLikeNormedField]; infer_instance
  have ht : cov.IsTorsionFree :=
    (CovariantDerivative.isTorsionFree_iff_torsion_eq_zero cov).2 h.torsion
  have hA (u v : E) : A u v = A v u := christoffelMap_comm ht b x₀ hy u v
  have hcomp (u v w : E) : D u v w = G (A v u) w + G v (A w u) :=
    h.isMetricCompatible.fderivWithin_chartMetric_apply b hy u v w
  have hpair (u v w : E) : 2 * G (A v u) w = D u v w + D v u w - D w u v := by
    have h₁ := hcomp u v w
    have h₂ := hcomp v u w
    have h₃ := hcomp w u v
    rw [hg v (A w u)] at h₁
    rw [hg u (A w v), hA u v] at h₂
    rw [hg u (A v w), hA u w, hA v w] at h₃
    linarith
  have hbase : y ∈ (trivializationAt E (TangentSpace I) x₀).baseSet := by simpa using hy
  rw [← coord_christoffelMap_apply_basis b (cov.isCovariantDerivativeOn (s := _)) hbase i j k,
    Basis.coord_apply,
    LinearMap.BilinForm.Nondegenerate.repr_eq_sum_inv_toMatrix₂_mul_apply
      (g.nondegenerate_chartMetric ((extChartAt I x₀).map_source hy)), Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  rw [ContinuousLinearMap.toBilinForm_apply, hg]
  -- Read the summand through the coordinate metric and its within derivative.
  change _ * G (A (b j) (b i)) (b l) = 2⁻¹ * (_ * (D _ _ _ + D _ _ _ - D _ _ _))
  rw [← hpair]
  ring

/-- **The index formula for the Christoffel symbols of a Levi-Civita connection.** Let `∇` be a
Levi-Civita connection of the nondegenerate metric `g`, and `b` a basis of the model space. At a
point `y` of the chart domain at `x₀` whose chart image lies in the interior of the model, the
Christoffel symbols of `∇` in the coordinate frame of `b` are
`Γᵏᵢⱼ = (1/2) Σ_l g^(kl) (∂ᵢ g_jl + ∂ⱼ g_il - ∂_l g_ij)`, where `g_ij` is the Gram matrix of the
chart metric in the basis `b`, `g^(kl)` its inverse, and `∂ᵢ` the derivative in the direction
`b i`. -/
theorem IsLeviCivitaConnection.christoffelSymbol_eq [DecidableEq ι]
    (h : g.IsLeviCivitaConnection cov) (hy : y ∈ (extChartAt I x₀).source)
    (hint : extChartAt I x₀ y ∈ interior (range I)) (i j k : ι) :
    christoffelSymbol I b (trivializationAt E (TangentSpace I) x₀) cov i j k y =
      2⁻¹ * ∑ l, (LinearMap.toMatrix₂ b b
          (g.chartMetric x₀ (extChartAt I x₀ y)).toBilinForm)⁻¹ k l *
        (fderiv ℝ (g.chartMetric x₀) (extChartAt I x₀ y) (b i) (b j) (b l) +
          fderiv ℝ (g.chartMetric x₀) (extChartAt I x₀ y) (b j) (b i) (b l) -
          fderiv ℝ (g.chartMetric x₀) (extChartAt I x₀ y) (b l) (b i) (b j)) := by
  have htarget : (extChartAt I x₀).target ∈ 𝓝 (extChartAt I x₀ y) := by
    rw [← nhdsWithin_eq_nhds.2 (mem_interior_iff_mem_nhds.1 hint)]
    exact extChartAt_target_mem_nhdsWithin' hy
  simpa only [fderivWithin_of_mem_nhds (f := g.chartMetric x₀) htarget] using
    h.christoffelSymbol_eq_fderivWithin b hy i j k

omit [Fintype ι] in
/-- Near a point of the chart domain at `x₀` whose chart image is interior, the Christoffel
symbols of a Levi-Civita connection of `g`, in the frame of `b`, are the coordinates of the
Christoffel symbols of the second kind of the chart metric. -/
theorem IsLeviCivitaConnection.christoffelSymbol_eventuallyEq [Finite ι]
    (h : g.IsLeviCivitaConnection cov) (hy : y ∈ (extChartAt I x₀).source)
    (hint : extChartAt I x₀ y ∈ interior (range I)) (i j k : ι) :
    christoffelSymbol I b (trivializationAt E (TangentSpace I) x₀) cov i j k =ᶠ[𝓝 y]
      fun y' ↦ b.repr
        (christoffelSecondKind (g.chartMetric x₀) (extChartAt I x₀ y') (b i) (b j)) k := by
  filter_upwards [(isOpen_extChartAt_source x₀).mem_nhds hy,
    (continuousAt_extChartAt' hy).preimage_mem_nhds (isOpen_interior.mem_nhds hint)]
    with y' hy' hint'
  have := Fintype.ofFinite ι
  rw [← coord_christoffelMap_apply_basis b (cov.isCovariantDerivativeOn (s := _))
    (by simpa using hy') i j k, h.christoffelMap_apply_eq_christoffelSecondKind b hy' hint',
    Basis.coord_apply]

end Coordinates

end TauCeti.Manifold.ContMDiffNondegenerateMetric

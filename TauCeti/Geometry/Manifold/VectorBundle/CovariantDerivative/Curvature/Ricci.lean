/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Bianchi
public import Mathlib.Analysis.InnerProductSpace.Trace
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.ChartGram
import Mathlib.Geometry.Manifold.BumpFunction
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import TauCeti.Geometry.Manifold.IsManifold.Basic

/-!
# Ricci curvature of a smooth connection

The Ricci tensor of a connection on the tangent bundle is the bilinear form
`Ric(u,v) = trace (w ↦ R(w,u)v)`. The trace makes this definition independent of a choice
of basis. Applying it to the Levi-Civita connection gives Riemannian Ricci curvature.
A general connection need not have symmetric Ricci curvature.

We work with a `RiemannianBundle` on the tangent bundle for the orthonormal-basis formulas.
The connection need not preserve this metric or be torsion free,
and the metric need not vary smoothly. Compactness and absence of boundary are not required.

We give the coordinate formula in any basis and the inner-product formula in an
orthonormal basis. The constant-curvature calculation fixes the sign convention:
`R(w,u)v = κ (⟪u,v⟫ w - ⟪w,v⟫ u)` gives `Ric = (dim - 1) κ g`.
The calculation is stated for any bilinear form in place of `κ g`, and then specialised
to `κ g`.

The Ricci coefficients of a smooth connection in a chart-local frame are smooth on the chart, so
the Ricci tensor pairs vector fields differentiable at a point to a function differentiable there.

The convention follows J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed.,
Springer GTM 176 (2018), Chapter 7. The curvature tensor being contracted is
`CovariantDerivative.curvatureTensor`, with convention
`R(X,Y)Z = ∇_X ∇_Y Z - ∇_Y ∇_X Z - ∇_[X,Y] Z`.
-/

public section

open Bundle
open scoped ContDiff Manifold Topology

noncomputable section

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
  [ContMDiffCovariantDerivative cov ∞]

local notation "curvature" => cov.curvatureTensor (I := I) (M := M) (F := E)
  (V := TangentSpace I)

/-- The Ricci tensor of a smooth connection on the tangent bundle, defined by
`Ric(u,v) = trace (w ↦ R(w,u)v)`. Metric compatibility and vanishing torsion are not
assumed; symmetry is not asserted for an arbitrary connection. -/
def ricciTensor (x : M) : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ :=
  (LinearMap.lflip.toLinearMap.comp (curvature x).flip).compr₂
    (LinearMap.trace ℝ (TangentSpace I x))

/-- The defining trace formula for Ricci curvature. The two flips leave the first
curvature argument free, so it is this argument that is traced against the output. -/
@[simp]
theorem ricciTensor_apply (x : M) (u v : TangentSpace I x) :
    cov.ricciTensor x u v =
      LinearMap.trace ℝ (TangentSpace I x) (((curvature x).flip u).flip v) :=
  (rfl)

/-- Ricci curvature in an arbitrary basis: sum the diagonal coefficients of
`w ↦ R(w,u)v`. The basis need not be orthogonal. -/
theorem ricciTensor_eq_sum {ι : Type*} [Fintype ι] (x : M)
    (b : Module.Basis ι ℝ (TangentSpace I x)) (u v : TangentSpace I x) :
    cov.ricciTensor x u v = ∑ i, b.repr (curvature x (b i) u v) i := by
  classical
  rw [ricciTensor_apply, LinearMap.trace_eq_matrix_trace ℝ b]
  simp [Matrix.trace, LinearMap.toMatrix_apply]

/-- In an orthonormal basis, Ricci curvature is the sum of the corresponding inner
products for the given fibre metric. -/
theorem ricciTensor_eq_sum_inner {ι : Type*} [Fintype ι]
    [RiemannianBundle (TangentSpace I : M → Type _)] (x : M)
    (b : OrthonormalBasis ι ℝ (TangentSpace I x)) (u v : TangentSpace I x) :
    cov.ricciTensor x u v = ∑ i, inner ℝ (b i) (curvature x (b i) u v) := by
  rw [ricciTensor_apply, LinearMap.trace_eq_sum_inner _ b]
  rfl

/-- The Ricci tensor of a metric-compatible torsion-free connection is symmetric. -/
theorem IsMetricCompatible.ricciTensor_comm
    [RiemannianBundle (TangentSpace I : M → Type _)]
    [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)]
    (hcov : CovariantDerivative.IsMetricCompatible
      (V := fun y : M ↦ TangentSpace I y) cov) (ht : cov.torsion = 0)
    (x : M) (u v : TangentSpace I x) :
    cov.ricciTensor x u v = cov.ricciTensor x v u := by
  let b := stdOrthonormalBasis ℝ (TangentSpace I x)
  rw [cov.ricciTensor_eq_sum_inner x b u v, cov.ricciTensor_eq_sum_inner x b v u]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  calc
    inner ℝ (b i) (curvature x (b i) u v) =
        inner ℝ (curvature x (b i) u v) (b i) := real_inner_comm _ _
    _ = inner ℝ (curvature x v (b i) (b i)) u :=
      hcov.inner_curvatureTensor_swap_pairs ht x (b i) u v (b i)
    _ = -inner ℝ (curvature x (b i) v (b i)) u := by
      rw [cov.curvatureTensor_antisymm x v (b i), LinearMap.neg_apply, inner_neg_left]
    _ = inner ℝ (b i) (curvature x (b i) v u) := by
      rw [hcov.inner_curvatureTensor_eq_neg x (b i) v (b i) u]
      ring

/-- The Ricci tensor of a metric-compatible torsion-free connection is a symmetric bilinear
form. -/
theorem IsMetricCompatible.ricciTensor_isSymm
    [RiemannianBundle (TangentSpace I : M → Type _)]
    [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)]
    (hcov : CovariantDerivative.IsMetricCompatible
      (V := fun y : M ↦ TangentSpace I y) cov) (ht : cov.torsion = 0) (x : M) :
    (cov.ricciTensor x).IsSymm :=
  ⟨IsMetricCompatible.ricciTensor_comm (cov := cov) hcov ht x⟩

/-- A point with zero curvature tensor has zero Ricci tensor. -/
@[simp]
theorem ricciTensor_eq_zero_of_curvatureTensor_eq_zero (x : M)
    (h : curvature x = 0) : cov.ricciTensor x = 0 := by
  ext u v
  have hz : ((curvature x).flip u).flip v = 0 := by
    ext w
    simp [h]
  rw [ricciTensor_apply, hz, map_zero]
  rfl

/-- A smooth connection on a manifold of dimension at most one has zero Ricci tensor. -/
@[simp]
theorem ricciTensor_eq_zero_of_finrank_le_one (x : M)
    (h : Module.finrank ℝ E ≤ 1) : cov.ricciTensor x = 0 :=
  cov.ricciTensor_eq_zero_of_curvatureTensor_eq_zero x
    (cov.curvatureTensor_eq_zero_of_finrank_le_one x
      (by simpa only [TauCeti.finrank_tangentSpace] using h))

/-- Contracting curvature of the form `R(w,u)v = B(u,v)w - B(w,v)u` gives
`Ric = (dim - 1) B`. In particular, the constant-curvature model with `B = κ g`
has Ricci tensor `(dim - 1) κ g`, with the sign fixed by the curvature convention. -/
theorem ricciTensor_eq_of_curvatureTensor_eq_smul_sub (x : M)
    (B : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (h : ∀ w u v, curvature x w u v = B u v • w - B w v • u) :
    cov.ricciTensor x = (Module.finrank ℝ (TangentSpace I x) - 1 : ℝ) • B := by
  ext u v
  have hmap : ((curvature x).flip u).flip v =
      B u v • LinearMap.id - (B.flip v).smulRight u := by
    ext w
    exact h w u v
  rw [ricciTensor_apply, hmap, map_sub, map_smul, LinearMap.trace_id,
    LinearMap.trace_smulRight]
  simp only [LinearMap.smul_apply, LinearMap.flip_apply, smul_eq_mul]
  ring

/-- The Ricci tensor of the constant-curvature model `R(w,u)v = κ (⟪u,v⟫ w - ⟪w,v⟫ u)` is
`(dim - 1) κ g`. -/
theorem ricciTensor_eq_of_curvatureTensor_eq_smul_inner_sub
    [RiemannianBundle (TangentSpace I : M → Type _)] (x : M) (k : ℝ)
    (h : ∀ w u v, curvature x w u v =
      k • (inner ℝ u v • w - inner ℝ w v • u)) :
    cov.ricciTensor x =
      ((Module.finrank ℝ (TangentSpace I x) - 1 : ℝ) * k) • innerₗ (TangentSpace I x) := by
  rw [cov.ricciTensor_eq_of_curvatureTensor_eq_smul_sub x (k • innerₗ (TangentSpace I x)),
    smul_smul]
  intro w u v
  rw [h w u v]
  simp only [LinearMap.smul_apply, innerₗ_apply_apply, smul_sub, smul_smul, smul_eq_mul]

open Riemannian.Tensor in
/-- The Ricci coefficients `Ric(eᵢ, eⱼ)` of a smooth connection on the tangent bundle in the
chart-local frame at `a` are smooth on the chart source. No metric is involved. -/
theorem contMDiffOn_ricciTensor_chartLocalFrame (a : M) (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun x ↦ cov.ricciTensor x (chartLocalFrame (I := I) a i x)
        (chartLocalFrame (I := I) a j x))
      (chartAt H a).source := by
  let _ : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  let e := trivializationAt E (TangentSpace I : M → Type _) a
  let b := Module.finBasis ℝ E
  have hsource : (chartAt H a).source = e.baseSet :=
    (TangentBundle.trivializationAt_baseSet (I := I) a).symm
  intro x₀ hx₀
  rw [hsource] at hx₀
  refine ContMDiffAt.contMDiffWithinAt ?_
  -- Cut off the frame by a bump function equal to one near `x₀`. This gives globally smooth
  -- vector fields, to which the curvature operator applies, agreeing with the frame near `x₀`.
  have hnhds : e.baseSet ∈ 𝓝 x₀ := e.open_baseSet.mem_nhds hx₀
  obtain ⟨ρ, hρ, -⟩ := (SmoothBumpFunction.nhds_basis_support (I := I) hnhds).mem_iff.mp hnhds
  let X (k : Fin (Module.finrank ℝ E)) : Π y : M, TangentSpace I y :=
    (ρ : M → ℝ) • chartLocalFrame (I := I) a k
  have hX (k : Fin (Module.finrank ℝ E)) : CMDiff ∞ (T% (X k)) :=
    ρ.contMDiff.contMDiffOn.smul_section_of_tsupport e.open_baseSet hρ
      (contMDiffOn_chartLocalFrame (I := I) a k)
  have hsum : ContMDiffAt I 𝓘(ℝ) ∞
      (fun y ↦ ∑ k, e.localFrameCoeff I b k y (cov.curvatureOperator (X k) (X i) (X j) y)) x₀ :=
    contMDiffAt_finsetSum fun k _ ↦ contMDiffAt_localFrameCoeff b hx₀
      (cov.contMDiff_curvatureOperator (hX k) (hX i) (hX j) x₀) k
  refine hsum.congr_of_eventuallyEq ?_
  filter_upwards [ρ.eventuallyEq_one, hnhds] with y hρy hy
  have hXy (k : Fin (Module.finrank ℝ E)) : X k y = chartLocalFrame (I := I) a k y := by
    simp only [X, Pi.smul_apply', hρy, Pi.one_apply, one_smul]
  -- Trace `w ↦ R(w, eᵢ)eⱼ` in the trivialization basis, which is the chart-local frame.
  have hb (k : Fin (Module.finrank ℝ E)) : e.basisAt b hy k = chartLocalFrame (I := I) a k y :=
    (chartLocalFrame_apply_of_mem_chart_source (I := I) a (hsource ▸ hy) k).symm
  rw [cov.ricciTensor_eq_sum y (e.basisAt b hy)]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [e.localFrameCoeff_apply_of_mem_baseSet b hy (cov.curvatureOperator (X k) (X i) (X j)) k,
    ← curvatureTensor_apply cov y (hX k) (hX i) (hX j), hXy, hXy, hXy, hb]

open Riemannian.Tensor in
/-- The Ricci tensor of a smooth connection pairs two vector fields differentiable at `x` to a
function differentiable at `x`. No metric is involved. -/
theorem mdifferentiableAt_ricciTensor_apply {σ τ : Π x : M, TangentSpace I x} {x : M}
    (hσ : MDiffAt (T% σ) x) (hτ : MDiffAt (T% τ) x) :
    MDiffAt (fun y ↦ cov.ricciTensor y (σ y) (τ y)) x := by
  let e := trivializationAt E (TangentSpace I : M → Type _) x
  let b := Module.finBasis ℝ E
  have hx : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  have hfin {f : Fin (Module.finrank ℝ E) → M → ℝ} (hf : ∀ i, MDiffAt (f i) x) :
      MDiffAt (fun y ↦ ∑ i, f i y) x := by
    simpa only [Finset.sum_fn] using MDifferentiableAt.sum (t := Finset.univ) fun i _ ↦ hf i
  -- Expand both fields in the chart-local frame at `x`, whose Ricci coefficients are smooth.
  have hsum : MDiffAt (fun y ↦ ∑ i, ∑ j, e.localFrameCoeff I b i y (σ y) *
      e.localFrameCoeff I b j y (τ y) *
        cov.ricciTensor y (chartLocalFrame (I := I) x i y) (chartLocalFrame (I := I) x j y)) x :=
    hfin fun i ↦ hfin fun j ↦
      ((mdifferentiableAt_localFrameCoeff b hx hσ i).mul
        (mdifferentiableAt_localFrameCoeff b hx hτ j)).mul
      (((cov.contMDiffOn_ricciTensor_chartLocalFrame x i j).contMDiffAt
        ((chartAt H x).open_source.mem_nhds (mem_chart_source H x))).mdifferentiableAt
          (by simp))
  refine hsum.congr_of_eventuallyEq ?_
  filter_upwards [e.eventually_eq_localFrame_sum_coeff_smul (I := I) b (s := σ) hx,
    e.eventually_eq_localFrame_sum_coeff_smul (I := I) b (s := τ) hx] with y hσy hτy
  conv_lhs => rw [hσy, hτy]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    chartLocalFrame_def, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  ring

end CovariantDerivative

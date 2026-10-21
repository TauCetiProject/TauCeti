/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Trace.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Ricci
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Regularity
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.ChartGram
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Conformal

/-!
# Scalar curvature of a smooth connection

The scalar curvature of a connection on a Riemannian tangent bundle is the metric trace of its
Ricci tensor. The definition is basis-free; in an orthonormal basis it is the sum of the diagonal
Ricci curvatures. In the chart-local frame of a tangent trivialization it is the classical
contraction `gⁱʲ Rᵢⱼ` of the Ricci coefficients against the inverse Gram matrix. Applying it to
the Levi-Civita connection gives the scalar curvature of a Riemannian manifold; for a smooth
metric `g`, `Bundle.ContMDiffRiemannianMetric.scalarCurvature` records it as a function of `g`, so
that several metrics on one manifold can be compared. For a metric `f g` rescaled by a positive
function, `Bundle.ContMDiffRiemannianMetric.scalarCurvature_rescale_eq_sum` computes its scalar
curvature in an orthonormal basis for `g`.

As for `CovariantDerivative.ricciTensor`, the connection need not preserve the metric or be torsion
free. The pointwise formulas do not need the metric to vary smoothly; for a smooth metric, the
chart formula shows that scalar curvature is a smooth function. Compactness and absence of
boundary are not required.

For the convention
`R(w,u)v = κ (⟨u,v⟩ w - ⟨w,v⟩ u)`, the scalar curvature is `n (n - 1) κ` in
real dimension `n`.

The definition and convention follow J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed.,
Springer GTM 176 (2018), Chapter 7.
-/

public section

open Bundle
open scoped ContDiff Manifold

noncomputable section

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
  [ContMDiffCovariantDerivative cov ∞]

local notation "curvature" => cov.curvatureTensor (I := I) (M := M) (F := E)
  (V := TangentSpace I)

/-- The scalar curvature of a smooth connection on the tangent bundle, defined as the metric
trace of its Ricci tensor. -/
def scalarCurvature (x : M) : ℝ :=
  TauCeti.bilinFormTrace (cov.ricciTensor x)

/-- Scalar curvature is the metric trace of Ricci curvature. -/
theorem scalarCurvature_apply (x : M) :
    cov.scalarCurvature x = TauCeti.bilinFormTrace (cov.ricciTensor x) :=
  (rfl)

/-- In an orthonormal basis, scalar curvature is the sum of the diagonal Ricci curvatures. -/
theorem scalarCurvature_eq_sum {i : Type*} [Fintype i] (x : M)
    (b : OrthonormalBasis i ℝ (TangentSpace I x)) :
    cov.scalarCurvature x = ∑ j, cov.ricciTensor x (b j) (b j) := by
  rw [scalarCurvature_apply]
  exact TauCeti.bilinFormTrace_eq_sum _ b

open Riemannian.Tensor in
/-- In the chart-local frame `eᵢ` at `a`, scalar curvature is the contraction `gⁱʲ Ric(eᵢ, eⱼ)`
of the Ricci coefficients against the inverse Gram matrix of the frame. This holds at every point
of the chart source; the frame need not be orthonormal. -/
theorem scalarCurvature_eq_sum_chartInvGramMatrix (a : M) {x : M}
    (hx : x ∈ (chartAt H a).source) :
    cov.scalarCurvature x = ∑ i, ∑ j, chartInvGramMatrix (I := I) a x i j *
      cov.ricciTensor x (chartLocalFrame (I := I) a i x) (chartLocalFrame (I := I) a j x) := by
  have hx' : x ∈ (trivializationAt E (TangentSpace I) a).baseSet := by
    simpa only [TangentBundle.trivializationAt_baseSet] using hx
  let b := (trivializationAt E (TangentSpace I) a).basisAt (Module.finBasis ℝ E) hx'
  have hb : ⇑b = fun i ↦ chartLocalFrame (I := I) a i x :=
    funext fun i ↦ (chartLocalFrame_apply_of_mem_chart_source (I := I) a hx i).symm
  have hgram : Matrix.gram ℝ b = chartGramMatrix (I := I) a x := by
    ext i j
    rw [Matrix.gram_apply, chartGramMatrix_apply, hb]
  have hinv : (Matrix.gram ℝ b)⁻¹ = chartInvGramMatrix (I := I) a x :=
    Matrix.inv_eq_left_inv (hgram ▸ chartInvGramMatrix_mul_chartGramMatrix (I := I) a hx)
  rw [scalarCurvature_apply, TauCeti.bilinFormTrace_eq_sum_inv_gram _ b, hinv, hb]

open Riemannian.Tensor in
/-- The scalar curvature of a smooth connection on the tangent bundle is smooth when the metric is
smooth. Neither metric compatibility nor vanishing torsion is required, so this applies in
particular to the Levi-Civita connection of a smooth metric. -/
theorem contMDiff_scalarCurvature
    [IsContMDiffRiemannianBundle I ∞ E (TangentSpace I : M → Type _)] :
    ContMDiff I 𝓘(ℝ) ∞ cov.scalarCurvature := by
  let _ : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  intro a
  have hGinv (i j : Fin (Module.finrank ℝ E)) :
      ContMDiffOn I 𝓘(ℝ) ∞ (fun x ↦ chartInvGramMatrix (I := I) a x i j)
        (chartAt H a).source := by
    simpa only [TangentBundle.trivializationAt_baseSet] using
      contMDiffOn_chartInvGramMatrix_entry (I := I) (n := ∞) a i j
  have hsum : ContMDiffOn I 𝓘(ℝ) ∞
      (fun x ↦ ∑ i, ∑ j, chartInvGramMatrix (I := I) a x i j *
        cov.ricciTensor x (chartLocalFrame (I := I) a i x) (chartLocalFrame (I := I) a j x))
      (chartAt H a).source :=
    contMDiffOn_finsetSum fun i _ ↦ contMDiffOn_finsetSum fun j _ ↦
      (hGinv i j).mul (cov.contMDiffOn_ricciTensor_chartLocalFrame a i j)
  exact (hsum.congr fun x hx ↦ cov.scalarCurvature_eq_sum_chartInvGramMatrix a hx).contMDiffAt
    ((chartAt H a).open_source.mem_nhds (mem_chart_source H a))

/-- The scalar curvature of a smooth connection on the tangent bundle is continuous when the
metric is smooth. -/
theorem continuous_scalarCurvature
    [IsContMDiffRiemannianBundle I ∞ E (TangentSpace I : M → Type _)] :
    Continuous cov.scalarCurvature :=
  cov.contMDiff_scalarCurvature.continuous

/-- In an orthonormal basis, scalar curvature is the double contraction of the curvature
tensor. The inner sum contracts the curvature output against its first argument; the outer sum
contracts the two Ricci arguments. -/
theorem scalarCurvature_eq_sum_inner_curvatureTensor {i : Type*} [Fintype i] (x : M)
    (b : OrthonormalBasis i ℝ (TangentSpace I x)) :
    cov.scalarCurvature x =
      ∑ j, ∑ k, inner ℝ (b k) (curvature x (b k) (b j) (b j)) := by
  rw [scalarCurvature_eq_sum cov x b]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  exact ricciTensor_eq_sum_inner cov x b (b j) (b j)

/-- Vanishing Ricci curvature implies vanishing scalar curvature. -/
theorem scalarCurvature_eq_zero_of_ricciTensor_eq_zero (x : M)
    (h : cov.ricciTensor x = 0) : cov.scalarCurvature x = 0 := by
  rw [scalarCurvature_apply, h, map_zero]

/-- A point with zero curvature tensor has zero scalar curvature. -/
theorem scalarCurvature_eq_zero_of_curvatureTensor_eq_zero (x : M)
    (h : curvature x = 0) : cov.scalarCurvature x = 0 :=
  scalarCurvature_eq_zero_of_ricciTensor_eq_zero cov x
    (ricciTensor_eq_zero_of_curvatureTensor_eq_zero cov x h)

/-- If Ricci curvature is a scalar multiple of the metric, scalar curvature is that scalar times
the real dimension. -/
theorem scalarCurvature_eq_of_ricciTensor_eq_smul_inner (x : M) (c : ℝ)
    (h : cov.ricciTensor x = c • innerₗ (TangentSpace I x)) :
    cov.scalarCurvature x = (Module.finrank ℝ (TangentSpace I x) : ℝ) * c := by
  rw [scalarCurvature_apply, h, map_smul, TauCeti.bilinFormTrace_inner]
  simp only [smul_eq_mul]
  ring

/-- Contracting curvature of the form `R(w,u)v = B(u,v)w - B(w,v)u` gives scalar curvature
`(dim - 1) trace(B)`. -/
theorem scalarCurvature_eq_of_curvatureTensor_eq_smul_sub (x : M)
    (B : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (h : ∀ w u v, curvature x w u v = B u v • w - B w v • u) :
    cov.scalarCurvature x =
      (Module.finrank ℝ (TangentSpace I x) - 1 : ℝ) * TauCeti.bilinFormTrace B := by
  rw [scalarCurvature_apply, ricciTensor_eq_of_curvatureTensor_eq_smul_sub cov x B h,
    map_smul]
  simp only [smul_eq_mul]

/-- The scalar curvature of the constant-curvature model
`R(w,u)v = κ (⟨u,v⟩ w - ⟨w,v⟩ u)` is `n (n - 1) κ`. -/
theorem scalarCurvature_eq_of_curvatureTensor_eq_smul_inner_sub (x : M) (k : ℝ)
    (h : ∀ w u v, curvature x w u v =
      k • (inner ℝ u v • w - inner ℝ w v • u)) :
    cov.scalarCurvature x = (Module.finrank ℝ (TangentSpace I x) : ℝ) *
      (Module.finrank ℝ (TangentSpace I x) - 1) * k := by
  rw [scalarCurvature_apply, cov.ricciTensor_eq_of_curvatureTensor_eq_smul_inner_sub x k h,
    map_smul, TauCeti.bilinFormTrace_inner]
  simp only [smul_eq_mul]
  ring

end CovariantDerivative

namespace Bundle.ContMDiffRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
  (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))

/-- The scalar curvature of a smooth Riemannian metric `g`: the scalar curvature of the
Levi-Civita connection of `g`, with `g` as the fibre inner product. -/
def scalarCurvature (x : M) : ℝ :=
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  (CovariantDerivative.leviCivitaConnection I M).scalarCurvature x

/-- The scalar curvature of `g` is that of its Levi-Civita connection, with `g` installed as the
fibre inner product. -/
theorem scalarCurvature_def (x : M) :
    g.scalarCurvature x =
      letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
      (CovariantDerivative.leviCivitaConnection I M).scalarCurvature x :=
  (rfl)

/-- If the installed fibre metric is `g`, the scalar curvature of `g` is that of the Levi-Civita
connection. This transports scalar curvature along an equality of fibre metrics, such as
`toRiemannianMetric_ofLE`, which cannot be rewritten inside the instance-dependent arguments. -/
theorem scalarCurvature_eq_scalarCurvature_leviCivitaConnection
    [inst : RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    (hg : RiemannianBundle.g = g.toRiemannianMetric) (x : M) :
    g.scalarCurvature x = (CovariantDerivative.leviCivitaConnection I M).scalarCurvature x := by
  obtain ⟨_⟩ := inst
  subst hg
  rfl

/-- The scalar curvature of a rescaled metric `f g` at `x`, computed in an orthonormal basis `b` of
`T_x M` for `g`: it is `(f x)⁻¹ ∑ⱼ Ric^(f g)_x (b j) (b j)`, since dividing `b` by `√(f x)` gives a
basis orthonormal for `f g`. -/
theorem scalarCurvature_rescale_eq_sum {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (hf_pos : ∀ x, 0 < f x) {x : M} {ι : Type*} [Fintype ι]
    (b : letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      OrthonormalBasis ι ℝ (TangentSpace I x)) :
    (g.rescale f hf hf_pos).scalarCurvature x =
      (f x)⁻¹ * ∑ j, (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨(g.rescale f hf hf_pos).toRiemannianMetric⟩;
        (CovariantDerivative.leviCivitaConnection I M).ricciTensor x) (b j) (b j) := by
  classical
  -- `b` as a basis, with its orthonormality recorded through the inner products of `g` itself.
  obtain ⟨b₀, hb₀, hb⟩ : ∃ b₀ : Module.Basis ι ℝ (TangentSpace I x), ⇑b₀ = ⇑b ∧
      ∀ i j, g.inner x (b₀ i) (b₀ j) = if i = j then 1 else 0 := by
    let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    refine ⟨b.toBasis, b.coe_toBasis, fun i j ↦ ?_⟩
    rw [b.coe_toBasis, ← inner_riemannianBundle]
    exact orthonormal_iff_ite.1 b.orthonormal i j
  rw [← hb₀]
  set s := Real.sqrt (f x)
  have hs0 : 0 < s := Real.sqrt_pos.2 (hf_pos x)
  have hss : s⁻¹ * s⁻¹ = (f x)⁻¹ := by rw [← mul_inv, Real.mul_self_sqrt (hf_pos x).le]
  rw [scalarCurvature_def]
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
    ⟨(g.rescale f hf hf_pos).toRiemannianMetric⟩
  -- Dividing `b` by `√(f x)` gives a basis orthonormal for the rescaled metric at `x`.
  have hon : Orthonormal ℝ (b₀.unitsSMul fun _ ↦ Units.mk0 s⁻¹ (inv_ne_zero hs0.ne')) := by
    rw [orthonormal_iff_ite]
    intro i j
    simp only [Module.Basis.unitsSMul_apply, Units.smul_def, Units.val_mk0,
      inner_riemannianBundle, rescale_inner, map_smul, smul_apply, smul_eq_mul, hb]
    split_ifs
    · field_simp
      exact (Real.sq_sqrt (hf_pos x).le).symm
    · simp
  rw [CovariantDerivative.scalarCurvature_eq_sum _ x ((b₀.unitsSMul _).toOrthonormalBasis hon),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [Module.Basis.coe_toOrthonormalBasis, Module.Basis.unitsSMul_apply, Units.smul_def,
    Units.val_mk0, map_smul, LinearMap.smul_apply, smul_eq_mul, ← mul_assoc, hss]

/-- The scalar curvature of a smooth Riemannian metric is a smooth function. -/
theorem contMDiff_scalarCurvature : ContMDiff I 𝓘(ℝ) ∞ g.scalarCurvature := by
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  exact (CovariantDerivative.leviCivitaConnection I M).contMDiff_scalarCurvature

/-- The scalar curvature of a smooth Riemannian metric is continuous. -/
theorem continuous_scalarCurvature : Continuous g.scalarCurvature :=
  g.contMDiff_scalarCurvature.continuous

end Bundle.ContMDiffRiemannianMetric

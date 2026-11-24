/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Hessian
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric.Pairing
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.RoughLaplacian.Commutator
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.SecondCovariantDerivative.Hom
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric.Hom
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Regularity
import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.HilbertSchmidt

/-!
# The Bochner formula for the covariant derivative of a section

Let `∇` be a metric connection on a Riemannian vector bundle `V` over a Riemannian manifold `M`.
The covariant derivative `∇σ` of a smooth section `σ` is a section of `Hom(TM, V)`, the bundle of
`V`-valued one-forms, which carries the connection induced by the Levi-Civita connection and `∇`,
and the pointwise Hilbert–Schmidt inner product `⟪A, B⟫ = ∑ᵢ ⟪A eᵢ, B eᵢ⟫`
(`ContinuousLinearMap.hilbertSchmidtInner`). This file computes the Laplacian of
`|∇σ|² = ⟪∇σ, ∇σ⟫` (`CovariantDerivative.innerCovariantDerivative`): for every orthonormal basis
`eᵢ` of the tangent space at `x`,

`Δ |∇σ|² = 2 |∇²σ|² - 2 ⟪∇(∇*∇σ), ∇σ⟫ - 2 ∑ⱼ ⟪Kⱼ, ∇_{eⱼ} σ⟫`,

`Kⱼ = ∑ᵢ (2 R(eⱼ, eᵢ) ∇_{eᵢ}σ + (∇_{eᵢ}R)(eⱼ, eᵢ) σ - ∇_{Rᵀ(eⱼ, eᵢ) eᵢ} σ)`

(`CovariantDerivative.IsMetricCompatible.laplaceBeltrami_innerCovariantDerivative_self`), where
`Δ = div ∘ grad` is `TauCeti.Manifold.laplaceBeltrami`, `|∇²σ|² = ∑ᵢⱼ |∇²σ(eᵢ, eⱼ)|²`, `R` is the
curvature of `∇`, `∇R` its covariant derivative and `Rᵀ` the Riemann curvature. This is the
Bochner formula for the gradient of a section. If `σ` solves an equation of Laplace type
`∇*∇σ = Φ`, it expresses `-Δ |∇σ|² / 2 + |∇²σ|²` through `∇Φ` and terms of order zero in `σ` and
`∇σ`, which is the differential inequality behind maximum-principle bounds on the gradient, such as
Taubes's gradient bound for the large-parameter Seiberg–Witten equations
(`TauCeti.SeibergWitten.norm_sq_add_mul_norm_sq_le`). For `σ = f` a function, a section of the
trivial line bundle, it is the classical Bochner formula
`Δ |df|² / 2 = |∇²f|² + ⟪d Δf, df⟫ + Ric(df, df)`
(`TauCeti.Manifold.laplaceBeltrami_norm_sq_mgradient`).

The formula is assembled from three facts.

* **The Hilbert–Schmidt metric is parallel.** For differentiable sections `A`, `B` of
  `Hom(TM, V)`, `d⟪A, B⟫(v) = ⟪∇_v A, B⟫ + ⟪A, ∇_v B⟫`
  (`CovariantDerivative.IsMetricCompatible.mvfderiv_hilbertSchmidtInner`).
* **The Hessian and Laplacian of `|A|²`.** Differentiating once more, as for the squared norm of a
  section of a Riemannian bundle (`CovariantDerivative.IsMetricCompatible.hessian_norm_sq`),
  `Hess |A|²(u, w) = 2 ⟪∇²A(u, w), A⟫ + 2 ⟪∇_u A, ∇_w A⟫`
  (`CovariantDerivative.IsMetricCompatible.hessian_hilbertSchmidtInner_self`), and tracing,
  `Δ |A|² = 2 ∑ᵢ |∇_{eᵢ} A|² - 2 ⟪∇*∇A, A⟫`
  (`CovariantDerivative.IsMetricCompatible.laplaceBeltrami_hilbertSchmidtInner_self`). The bundle
  `Hom(TM, V)` is not given a Riemannian bundle structure, since its fibres already carry the
  operator norm, so these are proved for the Hilbert–Schmidt pairing directly.
* **The commutator of `∇*∇` with `∇`.** For `A = ∇σ`, the rough Laplacian `∇*∇(∇σ)` differs from
  `∇(∇*∇σ)` by the curvature terms `Kⱼ`, by
  `roughLaplacian_covariantDerivative_apply_sub_covariantDerivative_roughLaplacian`.

## Main results

* `CovariantDerivative.IsMetricCompatible.hessian_hilbertSchmidtInner_self`: the Hessian of `|A|²`.
* `CovariantDerivative.IsMetricCompatible.laplaceBeltrami_hilbertSchmidtInner_self`: the Laplacian
  of `|A|²`.
* `CovariantDerivative.IsMetricCompatible.laplaceBeltrami_innerCovariantDerivative_self`: the
  Bochner formula for `|∇σ|²`.
* `IsMetricCompatible.neg_laplaceBeltrami_innerCovariantDerivative_self_div_two_add_le` (in the
  namespace `CovariantDerivative`): the resulting inequality under bounds on `R`, on the Riemann
  curvature and on the divergence `∑ᵢ (∇_{eᵢ}R)(·, eᵢ) σ`.

## References

* P. Petersen, *Riemannian Geometry*, 3rd ed., Springer GTM 171 (2016), Chapter 9 (the Bochner
  technique).
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapters 4
  and 7 (induced connections on tensor bundles and the Ricci identities).
-/

public section

open Bundle FiberBundle Riemannian.Tensor
open scoped ContDiff Manifold RealInnerProductSpace Topology

noncomputable section

namespace CovariantDerivative.IsMetricCompatible

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  {cov : _root_.CovariantDerivative I F V}

/-! ### The Hessian and the Laplacian of `|A|²` -/

section Hessian

variable [T2Space M] [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [ContMDiffVectorBundle ∞ F V I] [IsContMDiffRiemannianBundle I ∞ F V]
  [ContMDiffCovariantDerivative cov ∞]

local notation "∇ᵀ" => CovariantDerivative.leviCivitaConnection I M

/-- **The Hessian of the squared Hilbert–Schmidt norm.** For a metric connection `∇` on `V` and a
smooth section `A` of `Hom(TM, V)`, with the connection on `Hom(TM, V)` induced by the
Levi-Civita connection and `∇`,
`Hess |A|²(u, w) = 2 ⟪∇²A(u, w), A⟫ + 2 ⟪∇_u A, ∇_w A⟫` for the Hilbert–Schmidt pairing. -/
theorem hessian_hilbertSchmidtInner_self (hcov : cov.IsMetricCompatible)
    {A : Π y : M, TangentSpace I y →L[ℝ] V y}
    (hA : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] F)) ∞
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] F) (E := fun z ↦ TangentSpace I z →L[ℝ] V z) y (A y)))
    (x : M) (u w : TangentSpace I x) :
    TauCeti.Manifold.hessian I (fun y ↦ (A y).hilbertSchmidtInner (A y)) x u w =
      2 * (((∇ᵀ).hom cov).secondCovariantDerivative (∇ᵀ) A x u w).hilbertSchmidtInner (A x) +
        2 * (((∇ᵀ).hom cov) A x u).hilbertSchmidtInner (((∇ᵀ).hom cov) A x w) := by
  let _ : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  have hcovT := CovariantDerivative.isMetricCompatible_leviCivitaConnection I (M := M)
  have hA' (y : M) := hA.mdifferentiableAt (n := ∞) (by simp) (x := y)
  -- The covariant derivative `∇A` is a smooth section of `Hom(TM, Hom(TM, V))`.
  have hDA := contMDiff_hom (∇ᵀ) cov hA
  -- The directional derivative of `|A|²` along a vector field `W` is `2 ⟪∇_W A, A⟫`.
  have hd (y : M) (w' : TangentSpace I y) :
      mvfderiv I (fun z ↦ (A z).hilbertSchmidtInner (A z)) y w' =
        2 * (((∇ᵀ).hom cov) A y w').hilbertSchmidtInner (A y) := by
    rw [mvfderiv_hilbertSchmidtInner hcovT hcov (hA' y) (hA' y),
      ContinuousLinearMap.hilbertSchmidtInner_comm (A y)]
    ring
  obtain ⟨U, _, rfl⟩ := FiberBundle.exists_contMDiff_section_eq I E ∞ u
  obtain ⟨W, hW, rfl⟩ := FiberBundle.exists_contMDiff_section_eq I E ∞ w
  have hW' : MDiffAt (T% W) x := hW.mdifferentiableAt (by simp)
  have hsq : ContMDiffAt I 𝓘(ℝ) 2 (fun y ↦ (A y).hilbertSchmidtInner (A y)) x :=
    ((hA.hilbertSchmidtInner_bundle hA).of_le (by simp)).contMDiffAt
  -- The section `∇_W A` of `Hom(TM, V)` is smooth.
  have hAWs : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] F)) ∞ (fun y ↦ TotalSpace.mk' (E →L[ℝ] F)
      (E := fun z ↦ TangentSpace I z →L[ℝ] V z) y (((∇ᵀ).hom cov) A y (W y))) :=
    hDA.clm_bundle_apply hW
  have hAW := hAWs.mdifferentiableAt (n := ∞) (by simp) (x := x)
  have h2 : mvfderiv I (fun y ↦ 2 *
      (((∇ᵀ).hom cov) A y (W y)).hilbertSchmidtInner (A y)) x =
      (2 : ℝ) • mvfderiv I (fun y ↦ (((∇ᵀ).hom cov) A y (W y)).hilbertSchmidtInner (A y)) x := by
    simpa only [smul_eq_mul] using TauCeti.mvfderiv_const_smul
      ((hAWs.hilbertSchmidtInner_bundle hA).mdifferentiableAt (by simp)) (2 : ℝ)
  rw [TauCeti.Manifold.hessian_apply_eq_mvfderiv_sub x hsq U W hW', funext fun y ↦ hd y (W y), hd,
    h2, smul_apply, smul_eq_mul,
    mvfderiv_hilbertSchmidtInner hcovT hcov hAW (hA' x),
    covariantDerivative_clm_apply (∇ᵀ) ((∇ᵀ).hom cov) (hDA.mdifferentiableAt (by simp)) hW',
    secondCovariantDerivative_eq_hom_apply ((∇ᵀ).hom cov) (∇ᵀ) hA,
    ContinuousLinearMap.hilbertSchmidtInner_add_left,
    ContinuousLinearMap.hilbertSchmidtInner_comm (((∇ᵀ).hom cov) A x (W x))]
  ring

/-- **The Laplacian of the squared Hilbert–Schmidt norm.** For a metric connection `∇` on `V`, a
smooth section `A` of `Hom(TM, V)` and an orthonormal basis `eᵢ` of the tangent space at `x`,
`Δ |A|² = 2 ∑ᵢ |∇_{eᵢ} A|² - 2 ⟪∇*∇A, A⟫` for the Hilbert–Schmidt pairing, where `Δ = div ∘ grad`
is the Laplace–Beltrami operator and `∇*∇` is the rough Laplacian of the connection on `Hom(TM, V)`
induced by the Levi-Civita connection and `∇`. -/
theorem laplaceBeltrami_hilbertSchmidtInner_self (hcov : cov.IsMetricCompatible)
    {A : Π y : M, TangentSpace I y →L[ℝ] V y}
    (hA : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] F)) ∞
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] F) (E := fun z ↦ TangentSpace I z →L[ℝ] V z) y (A y)))
    (x : M) {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ (TangentSpace I x)) :
    TauCeti.Manifold.laplaceBeltrami I (fun y ↦ (A y).hilbertSchmidtInner (A y)) x =
      2 * ∑ i, (((∇ᵀ).hom cov) A x (b i)).hilbertSchmidtInner (((∇ᵀ).hom cov) A x (b i)) -
        2 * (((∇ᵀ).hom cov).roughLaplacian (∇ᵀ) A x).hilbertSchmidtInner (A x) := by
  rw [TauCeti.Manifold.laplaceBeltrami_eq_sum_hessian I _ x b,
    ((∇ᵀ).hom cov).roughLaplacian_eq_sum (∇ᵀ) A x b]
  simp only [hcov.hessian_hilbertSchmidtInner_self hA,
    ContinuousLinearMap.hilbertSchmidtInner_eq_sum _ _ b, neg_apply,
    sum_apply, inner_neg_left, sum_inner, Finset.sum_neg_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum]
  rw [Finset.sum_comm]
  ring

/-! ### The Bochner formula for `|∇σ|²` -/

/-- **The Bochner formula for the covariant derivative of a section.** For a metric connection `∇`
on `V`, a smooth section `σ` and an orthonormal basis `eᵢ` of the tangent space at `x`, the
Laplacian of `|∇σ|² = ∑ᵢ |∇_{eᵢ} σ|²` is

`Δ |∇σ|² = 2 ∑ᵢⱼ |∇²σ(eᵢ, eⱼ)|² - 2 ∑ⱼ ⟪∇_{eⱼ}(∇*∇σ), ∇_{eⱼ}σ⟫ - 2 ∑ⱼ ⟪Kⱼ, ∇_{eⱼ}σ⟫`,

`Kⱼ = ∑ᵢ (2 R(eⱼ, eᵢ) ∇_{eᵢ}σ + (∇_{eᵢ}R)(eⱼ, eᵢ) σ - ∇_{Rᵀ(eⱼ, eᵢ) eᵢ} σ)`,

where `Δ = div ∘ grad`, `∇*∇` is the rough Laplacian, `R` the curvature of `∇`, `∇R` its covariant
derivative and `Rᵀ` the Riemann curvature. -/
theorem laplaceBeltrami_innerCovariantDerivative_self (hcov : cov.IsMetricCompatible)
    {σ : Π y : M, V y} (hσ : CMDiff ∞ (T% σ)) (x : M) {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (TangentSpace I x)) :
    TauCeti.Manifold.laplaceBeltrami I (cov.innerCovariantDerivative σ σ) x =
      2 * ∑ i, ∑ j, ‖cov.secondCovariantDerivative (∇ᵀ) σ x (b i) (b j)‖ ^ 2 -
        2 * ∑ j, ⟪cov (cov.roughLaplacian (∇ᵀ) σ) x (b j), cov σ x (b j)⟫ -
        2 * ∑ j, ⟪∑ i, ((2 : ℝ) • cov.curvatureTensor x (b j) (b i) (cov σ x (b i)) +
          cov.derivCurvatureTensor (∇ᵀ) x (b i) (b j) (b i) (σ x) -
          cov σ x ((∇ᵀ).curvatureTensor x (b j) (b i) (b i))), cov σ x (b j)⟫ := by
  have hLC := CovariantDerivative.isLeviCivitaConnection_leviCivitaConnection I (M := M)
  have ht : (∇ᵀ).IsTorsionFree :=
    (CovariantDerivative.isTorsionFree_iff_torsion_eq_zero (∇ᵀ)).2 hLC.torsion
  have hDσ := cov.contMDiff_covariantDerivative (n := ∞) (by simpa using hσ)
  have hfun : cov.innerCovariantDerivative σ σ =
      fun y ↦ (cov σ y).hilbertSchmidtInner (cov σ y) :=
    funext fun y ↦ cov.innerCovariantDerivative_def σ σ y
  -- Apply the Laplacian of `|A|²` to `A = ∇σ`, then commute `∇*∇` past `∇`.
  have hcomm (j : ι) :=
    roughLaplacian_covariantDerivative_apply_sub_covariantDerivative_roughLaplacian
      cov (∇ᵀ) ht hLC.isMetricCompatible hσ x b (b j)
  rw [hfun, hcov.laplaceBeltrami_hilbertSchmidtInner_self hDσ x b]
  simp only [ContinuousLinearMap.hilbertSchmidtInner_eq_sum _ _ b,
    ← secondCovariantDerivative_eq_hom_apply cov (∇ᵀ) hσ, real_inner_self_eq_norm_sq,
    sub_eq_iff_eq_add.1 (hcomm _), inner_add_left, Finset.sum_add_distrib]
  ring

omit [IsContMDiffRiemannianBundle I ∞ F V] in
/-- The curvature term `Kⱼ` of the Bochner formula has norm at most `n (2 c_R + c_T) |∇σ| + D`. -/
private theorem norm_sum_curvature_le {σ : Π y : M, V y} (x : M) {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (TangentSpace I x)) {cR cT D : ℝ}
    (hR : ∀ u v s, ‖cov.curvatureTensor x u v s‖ ≤ cR * ‖u‖ * ‖v‖ * ‖s‖)
    (hRT : ∀ u v w, ‖(∇ᵀ).curvatureTensor x u v w‖ ≤ cT * ‖u‖ * ‖v‖ * ‖w‖)
    (hD : ∀ j, ‖∑ i, cov.derivCurvatureTensor (∇ᵀ) x (b i) (b j) (b i) (σ x)‖ ≤ D) (j : ι) :
    ‖∑ i, ((2 : ℝ) • cov.curvatureTensor x (b j) (b i) (cov σ x (b i)) +
      cov.derivCurvatureTensor (∇ᵀ) x (b i) (b j) (b i) (σ x) -
      cov σ x ((∇ᵀ).curvatureTensor x (b j) (b i) (b i)))‖ ≤
        Fintype.card ι * (2 * cR + cT) * √(cov.innerCovariantDerivative σ σ x) + D := by
  set A := √(cov.innerCovariantDerivative σ σ x) with hAdef
  have hA0 : 0 ≤ A := Real.sqrt_nonneg _
  have hsum : ∑ i, ‖cov σ x (b i)‖ ^ 2 = A ^ 2 := by
    rw [hAdef, Real.sq_sqrt (cov.innerCovariantDerivative_self_nonneg σ x),
      cov.innerCovariantDerivative_eq_sum σ σ x b]
    simp only [real_inner_self_eq_norm_sq]
  -- `∇σ` has operator norm at most `A = |∇σ|`, so each `‖∇_{eᵢ} σ‖ ≤ A`.
  have hop := (cov σ x).le_of_opNorm_le (cov.norm_le_sqrt_innerCovariantDerivative σ x)
  have ha (i : ι) : ‖cov σ x (b i)‖ ≤ A := by simpa [b.orthonormal.1 i] using hop (b i)
  -- The curvature of `∇` acting on `∇_{eᵢ} σ`.
  have hRa (i j : ι) : ‖cov.curvatureTensor x (b j) (b i) (cov σ x (b i))‖ ≤ cR * A := by
    rcases le_or_gt 0 cR with hcR | hcR
    · refine (hR _ _ _).trans ?_
      rw [b.orthonormal.1 j, b.orthonormal.1 i, mul_one, mul_one]
      exact mul_le_mul_of_nonneg_left (ha i) hcR
    · -- A negative bound forces `V x = 0`, so both sides vanish.
      have h0 (s : V x) : s = 0 := by
        have h := (norm_nonneg _).trans (hR (b j) (b j) s)
        rw [b.orthonormal.1 j, mul_one, mul_one] at h
        exact norm_le_zero_iff.1 (nonpos_of_mul_nonneg_right h hcR)
      have hA : A = 0 := by
        rw [← sq_eq_zero_iff, ← hsum]
        simp [h0 (cov σ x _)]
      simp [h0 (cov σ x (b i)), hA]
  have hRT' (i j : ι) : ‖cov σ x ((∇ᵀ).curvatureTensor x (b j) (b i) (b i))‖ ≤ A * cT := by
    refine (hop _).trans (mul_le_mul_of_nonneg_left ?_ hA0)
    refine (hRT _ _ _).trans_eq ?_
    rw [b.orthonormal.1 j, b.orthonormal.1 i, mul_one, mul_one, mul_one]
  -- The bound on the curvature term `Kⱼ` of the Bochner formula.
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have h1 : ‖∑ i, (2 : ℝ) • cov.curvatureTensor x (b j) (b i) (cov σ x (b i))‖ ≤
      Fintype.card ι * (2 * (cR * A)) := by
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_card_nsmul _ _ (2 * (cR * A)) fun i _ ↦ ?_).trans_eq (by simp)
    rw [norm_smul, Real.norm_two]
    exact mul_le_mul_of_nonneg_left (hRa i j) zero_le_two
  have h2 : ‖∑ i, cov σ x ((∇ᵀ).curvatureTensor x (b j) (b i) (b i))‖ ≤
      Fintype.card ι * (A * cT) := by
    refine (norm_sum_le _ _).trans ?_
    exact (Finset.sum_le_card_nsmul _ _ (A * cT) fun i _ ↦ hRT' i j).trans_eq (by simp)
  linarith [norm_sub_le (∑ i, (2 : ℝ) • cov.curvatureTensor x (b j) (b i) (cov σ x (b i)) +
    ∑ i, cov.derivCurvatureTensor (∇ᵀ) x (b i) (b j) (b i) (σ x))
      (∑ i, cov σ x ((∇ᵀ).curvatureTensor x (b j) (b i) (b i))),
    norm_add_le (∑ i, (2 : ℝ) • cov.curvatureTensor x (b j) (b i) (cov σ x (b i)))
      (∑ i, cov.derivCurvatureTensor (∇ᵀ) x (b i) (b j) (b i) (σ x)), hD j]

/-- **The Bochner inequality for an equation of Laplace type.** Under curvature bounds at `x`,
the Bochner formula bounds `-Δ |∇σ|² / 2 + |∇²σ|²` by the pairing of `∇(∇*∇σ)` with `∇σ` plus
terms of order at most two in `|∇σ|`. Suppose that, for an orthonormal basis `eᵢ` of the tangent
space at `x` with `n` elements, `|R(u, v) s| ≤ c_R |u| |v| |s|` for the curvature `R` of `∇`,
`|Rᵀ(u, v) w| ≤ c_T |u| |v| |w|` for the Riemann curvature `Rᵀ`, and the divergence of `R`
applied to `σ` satisfies `|∑ᵢ (∇_{eᵢ}R)(eⱼ, eᵢ) σ| ≤ D` for every `j`. Then, with
`|∇σ| = √⟪∇σ, ∇σ⟫` the Hilbert–Schmidt norm,

`-Δ |∇σ|² / 2 + ∑ᵢⱼ |∇²σ(eᵢ, eⱼ)|² ≤`
`  ∑ⱼ ⟪∇_{eⱼ}(∇*∇σ), ∇_{eⱼ}σ⟫ + n (n (2 c_R + c_T) |∇σ| + D) |∇σ|`.

Only the divergence of `R`, not all of `∇R`, enters. -/
theorem neg_laplaceBeltrami_innerCovariantDerivative_self_div_two_add_le
    (hcov : cov.IsMetricCompatible) {σ : Π y : M, V y} (hσ : CMDiff ∞ (T% σ)) (x : M)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ (TangentSpace I x)) {cR cT D : ℝ}
    (hR : ∀ u v s, ‖cov.curvatureTensor x u v s‖ ≤ cR * ‖u‖ * ‖v‖ * ‖s‖)
    (hRT : ∀ u v w, ‖(∇ᵀ).curvatureTensor x u v w‖ ≤ cT * ‖u‖ * ‖v‖ * ‖w‖)
    (hD : ∀ j, ‖∑ i, cov.derivCurvatureTensor (∇ᵀ) x (b i) (b j) (b i) (σ x)‖ ≤ D) :
    -(TauCeti.Manifold.laplaceBeltrami I (cov.innerCovariantDerivative σ σ) x / 2) +
        ∑ i, ∑ j, ‖cov.secondCovariantDerivative (∇ᵀ) σ x (b i) (b j)‖ ^ 2 ≤
      ∑ j, ⟪cov (cov.roughLaplacian (∇ᵀ) σ) x (b j), cov σ x (b j)⟫ +
        Fintype.card ι * (Fintype.card ι * (2 * cR + cT) *
          √(cov.innerCovariantDerivative σ σ x) + D) * √(cov.innerCovariantDerivative σ σ x) := by
  rw [hcov.laplaceBeltrami_innerCovariantDerivative_self hσ x b]
  set A := √(cov.innerCovariantDerivative σ σ x)
  have ha (i : ι) : ‖cov σ x (b i)‖ ≤ A := by
    simpa [b.orthonormal.1 i] using
      (cov σ x).le_of_opNorm_le (cov.norm_le_sqrt_innerCovariantDerivative σ x) (b i)
  have hK := norm_sum_curvature_le x b hR hRT hD
  have hKa : ∑ j, ⟪∑ i, ((2 : ℝ) • cov.curvatureTensor x (b j) (b i) (cov σ x (b i)) +
      cov.derivCurvatureTensor (∇ᵀ) x (b i) (b j) (b i) (σ x) -
      cov σ x ((∇ᵀ).curvatureTensor x (b j) (b i) (b i))), cov σ x (b j)⟫ ≤
        Fintype.card ι * ((Fintype.card ι * (2 * cR + cT) * A + D) * A) := by
    refine (Finset.sum_le_card_nsmul _ _ ((Fintype.card ι * (2 * cR + cT) * A + D) * A)
      fun j _ ↦ ?_).trans_eq (by simp)
    refine (real_inner_le_norm _ _).trans ?_
    exact mul_le_mul (hK j) (ha j) (norm_nonneg _) ((norm_nonneg _).trans (hK j))
  linarith

end Hessian

end CovariantDerivative.IsMetricCompatible

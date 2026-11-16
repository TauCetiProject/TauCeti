/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.HilbertSchmidt.Inner
public import TauCeti.Geometry.Manifold.Riemannian.DivergenceTheorem
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.RoughLaplacian.Codifferential
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Riesz
import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Support
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric.Basic

/-!
# Formal adjunction, Green's identities, and harmonic sections for the rough Laplacian

Let `∇` be a metric-compatible connection on a Riemannian vector bundle `V` over a Riemannian
manifold `M`, and let `∇*` (`CovariantDerivative.codifferential`) and `∇*∇`
(`CovariantDerivative.roughLaplacian`) be its codifferential and rough (connection) Laplacian built
with the Levi–Civita connection on `TM`.

For any `V`-valued one-form `η` and section `τ` of `V` that are differentiable at `x`, let `X` be
the tangent vector field fibrewise dual to the covector `v ↦ ⟪τ, η v⟫`. Metric compatibility of
both `∇` and the Levi–Civita connection yields the pointwise divergence identity

`div X = ⟨η, ∇τ⟩_{HS} - ⟪∇* η, τ⟫`

(`CovariantDerivative.IsMetricCompatible.divergence_rieszDual_innerSL_comp`), where `⟨·, ·⟩_{HS}`
is the fibrewise Hilbert–Schmidt inner product (`ContinuousLinearMap.hilbertSchmidtInner`). No
orientation, boundarylessness, Hausdorffness, or compactness is needed for the pointwise identity.

On a smooth `σ`-compact Hausdorff Riemannian manifold without boundary, integrating against the
orientation-free Riemannian volume (`TauCeti.riemannianVolume`) via the divergence theorem
(`TauCeti.Manifold.integral_divergence_eq_zero`) yields:

* **Formal adjunction of `∇*` and `∇`**
  (`CovariantDerivative.IsMetricCompatible.integral_codifferential_inner`,
  `CovariantDerivative.IsMetricCompatible.integral_smoothCodifferential_inner`):
  `∫ ⟪∇* η, τ⟫ dV = ∫ ⟨η, ∇τ⟩_{HS} dV` whenever `η` or `τ` has compact support.
* **Green's first identity / Dirichlet energy**
  (`CovariantDerivative.IsMetricCompatible.integral_roughLaplacian_inner`,
  `CovariantDerivative.IsMetricCompatible.integral_roughLaplacian_inner_self`,
  `CovariantDerivative.IsMetricCompatible.integral_roughLaplacian_inner_self_eq_sum`):
  `∫ ⟪∇*∇σ, τ⟫ dV = ∫ ⟨∇σ, ∇τ⟩_{HS} dV`, and for `τ = σ` with compact support,
  `∫ ⟪∇*∇σ, σ⟫ dV = ∫ (∇σ).hilbertSchmidtNorm ^ 2 dV = ∫ (∑ᵢ ‖∇_{bᵢ} σ‖ ^ 2) dV` in arbitrary
  (not necessarily continuous) pointwise orthonormal bases `b`.
* **Green's second identity / formal self-adjointness of `∇*∇`**
  (`CovariantDerivative.IsMetricCompatible.integral_roughLaplacian_inner_eq_inner_roughLaplacian`,
  bundled in `integral_smoothRoughLaplacian_inner_eq_inner_smoothRoughLaplacian`):
  `∫ ⟪∇*∇σ, τ⟫ dV = ∫ ⟪σ, ∇*∇τ⟫ dV` whenever `σ` or `τ` has compact support.
* **Characterization of rough-harmonic sections**
  (`CovariantDerivative.IsMetricCompatible.roughLaplacian_eq_zero_iff`,
  `CovariantDerivative.IsMetricCompatible.roughLaplacian_eq_zero_iff_of_compactSpace`):
  for a compactly supported smooth section `σ` (in particular for every smooth section when `M` is
  compact), `∇*∇σ = 0` everywhere if and only if `∇σ = 0` everywhere. On a preconnected manifold,
  any rough-harmonic compactly supported smooth section that vanishes at one point—and on a
  noncompact preconnected manifold, every rough-harmonic compactly supported smooth section—vanishes
  identically
  (`CovariantDerivative.IsMetricCompatible.eq_zero_of_roughLaplacian_eq_zero_of_apply_eq_zero`,
  `CovariantDerivative.IsMetricCompatible.eq_zero_of_roughLaplacian_eq_zero_of_noncompactSpace`).

## References

* N. Berline, E. Getzler, and M. Vergne, *Heat Kernels and Dirac Operators*, Grundlehren der
  mathematischen Wissenschaften 298, Springer (1992), Section 2.1, Proposition 2.4.
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapters 2 and 4.
* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry*, Princeton Mathematical Series 38 (1989),
  Chapter II, Proposition 8.1.
-/

public section

open Bundle FiberBundle MeasureTheory Riemannian.Tensor Set
open scoped ContDiff Manifold RealInnerProductSpace Topology

noncomputable section

/-! ### Smoothness of the fibrewise Hilbert–Schmidt inner product and Riesz pairing field -/

section Smoothness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {n : ℕ∞ω}
  [IsManifold I 1 M] [IsManifold I (n + 1) M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I n E (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  [IsContMDiffRiemannianBundle I n F V]

/-- The fibrewise Hilbert–Schmidt inner product of two `C^n` sections of `Hom(TM, V)` is `C^n`. -/
theorem ContMDiff.hilbertSchmidtInner {η₁ η₂ : Π y : M, TangentSpace I y →L[ℝ] V y}
    (hη₁ : CMDiff n
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] F) (E := fun z ↦ TangentSpace I z →L[ℝ] V z) y (η₁ y)))
    (hη₂ : CMDiff n
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] F) (E := fun z ↦ TangentSpace I z →L[ℝ] V z) y (η₂ y))) :
    ContMDiff I 𝓘(ℝ) n
      (fun y ↦ ContinuousLinearMap.hilbertSchmidtInner (η₁ y) (η₂ y)) := by
  intro x
  have hGinv (i j : Fin (Module.finrank ℝ E)) :
      ContMDiffOn I 𝓘(ℝ) n (fun y ↦ chartInvGramMatrix (I := I) x y i j)
        (chartAt H x).source := by
    simpa only [TangentBundle.trivializationAt_baseSet] using
      contMDiffOn_chartInvGramMatrix_entry (I := I) (n := n) x i j
  have hframe (i : Fin (Module.finrank ℝ E)) :
      CMDiff[(chartAt H x).source] n (T% (chartLocalFrame (I := I) x i)) := by
    simpa only [TangentBundle.trivializationAt_baseSet] using
      contMDiffOn_chartLocalFrame (I := I) (n := n) x i
  have hsum : ContMDiffOn I 𝓘(ℝ) n (fun y ↦
      ∑ i, ∑ j, chartInvGramMatrix (I := I) x y i j *
        ⟪η₁ y (chartLocalFrame (I := I) x i y), η₂ y (chartLocalFrame (I := I) x j y)⟫)
      (chartAt H x).source :=
    contMDiffOn_finsetSum fun i _ ↦ contMDiffOn_finsetSum fun j _ ↦
      (hGinv i j).mul ((hη₁.contMDiffOn.clm_bundle_apply (hframe i)).inner_bundle
        (hη₂.contMDiffOn.clm_bundle_apply (hframe j)))
  refine (hsum.congr fun y hy ↦ ?_).contMDiffAt
    ((chartAt H x).open_source.mem_nhds (mem_chart_source H x))
  let b := (trivializationAt E (TangentSpace I) x).basisAt (Module.finBasis ℝ E)
    (by simpa only [TangentBundle.trivializationAt_baseSet] using hy)
  have hb (k : Fin (Module.finrank ℝ E)) : b k = chartLocalFrame (I := I) x k y := by
    simpa only [b] using (chartLocalFrame_apply_of_mem_chart_source (I := I) x hy k).symm
  have hgram : Matrix.gram ℝ b = chartGramMatrix (I := I) x y := by
    ext i j; rw [Matrix.gram_apply, hb i, hb j, chartGramMatrix_apply]
  rw [ContinuousLinearMap.hilbertSchmidtInner_eq_sum_inv_gram (η₁ y) (η₂ y) b, hgram,
    ← chartInvGramMatrix_def]
  simp only [hb]

/-- For a `C^n` section `η` of `Hom(TM, V)` and a `C^n` section `τ` of `V`, the tangent vector
field fibrewise Riesz-dual to `v ↦ ⟪τ, η v⟫` is `C^n`. -/
theorem ContMDiff.rieszDual_innerSL_comp {η : Π y : M, TangentSpace I y →L[ℝ] V y}
    {τ : Π y : M, V y}
    (hη : CMDiff n
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] F) (E := fun z ↦ TangentSpace I z →L[ℝ] V z) y (η y)))
    (hτ : CMDiff n (T% τ)) :
    ContMDiff I I.tangent n
      (T% fun y ↦ rieszDual (I := I) y ((innerSL ℝ (τ y)).comp (η y))) := by
  intro x
  refine contMDiffAt_rieszDual x (mem_chart_source H x) fun j ↦ ?_
  have hframe : CMDiffAt n (T% (chartLocalFrame (I := I) x j)) x := by
    have hOn : CMDiff[(chartAt H x).source] n (T% (chartLocalFrame (I := I) x j)) := by
      simpa only [TangentBundle.trivializationAt_baseSet] using
        contMDiffOn_chartLocalFrame (I := I) (n := n) x j
    exact hOn.contMDiffAt ((chartAt H x).open_source.mem_nhds (mem_chart_source H x))
  exact (hτ x).inner_bundle ((hη x).clm_bundle_apply hframe)

end Smoothness

namespace CovariantDerivative

/-! ### Pointwise divergence identity for a metric connection -/

section PointwiseDivergence

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle 1 F V I]
  [IsContMDiffRiemannianBundle I 1 F V]
  {cov : CovariantDerivative I F V}

omit [FiniteDimensional ℝ F] [ContMDiffVectorBundle 1 F V I] in
/-- Differentiability at `x` of the tangent vector field fibrewise Riesz-dual to `v ↦ ⟪τ, η v⟫`. -/
private theorem mdifferentiableAt_rieszDual_innerSL_comp
    {η : Π y : M, TangentSpace I y →L[ℝ] V y} {τ : Π y : M, V y} {x : M}
    (hη : MDiffAt
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] F) (E := fun z ↦ TangentSpace I z →L[ℝ] V z) y (η y)) x)
    (hτ : MDiffAt (T% τ) x) :
    MDiffAt (T% fun y ↦ rieszDual (I := I) y ((innerSL ℝ (τ y)).comp (η y))) x := by
  have : IsManifold I (1 + 1) M := by rw [one_add_one_eq_two]; infer_instance
  have hmem : (chartAt H x).source ∈ 𝓝 x :=
    (chartAt H x).open_source.mem_nhds (mem_chart_source H x)
  have hGinv (i j : Fin (Module.finrank ℝ E)) :
      MDiffAt (fun y ↦ chartInvGramMatrix (I := I) x y i j) x := by
    have hOn : ContMDiffOn I 𝓘(ℝ) 1
        (fun y ↦ chartInvGramMatrix (I := I) x y i j) (chartAt H x).source := by
      simpa only [TangentBundle.trivializationAt_baseSet] using
        contMDiffOn_chartInvGramMatrix_entry (I := I) (n := 1) x i j
    exact (hOn.contMDiffAt hmem).mdifferentiableAt one_ne_zero
  have hframe (i : Fin (Module.finrank ℝ E)) :
      MDiffAt (T% (chartLocalFrame (I := I) x i)) x := by
    have hOn : CMDiff[(chartAt H x).source] 1 (T% (chartLocalFrame (I := I) x i)) := by
      simpa only [TangentBundle.trivializationAt_baseSet] using
        contMDiffOn_chartLocalFrame (I := I) (n := 1) x i
    exact (hOn.contMDiffAt hmem).mdifferentiableAt one_ne_zero
  have hc (i : Fin (Module.finrank ℝ E)) : MDiffAt (fun y ↦
      ∑ j, chartInvGramMatrix (I := I) x y i j *
        ⟪τ y, η y (chartLocalFrame (I := I) x j y)⟫) x := by
    simpa only [Finset.sum_fn, Pi.mul_apply] using MDifferentiableAt.sum (t := Finset.univ)
      fun j _ ↦ (hGinv i j).mul (hτ.inner_bundle (hη.clm_bundle_apply (hframe j)))
  have hsum : MDiffAt (T% fun y ↦
      ∑ i, (∑ j, chartInvGramMatrix (I := I) x y i j *
        ⟪τ y, η y (chartLocalFrame (I := I) x j y)⟫) • chartLocalFrame (I := I) x i y) x :=
    MDifferentiableAt.sum_section fun i _ ↦ (hc i).smul_section (hframe i)
  refine hsum.congr_of_eventuallyEq (Filter.eventually_of_mem hmem fun y hy ↦ ?_)
  simpa only [Matrix.mulVec, dotProduct, ContinuousLinearMap.comp_apply, innerSL_apply_apply] using
    congrArg (TotalSpace.mk' E y)
      (rieszDual_eq_sum_chartLocalFrame (I := I) x hy ((innerSL ℝ (τ y)).comp (η y)))

/-- **Pointwise divergence identity for the covariant codifferential.** For a metric-compatible
connection `∇` on `V`, a section `η` of `Hom(TM, V)` and a section `τ` of `V` differentiable at `x`,
the divergence of the vector field dual to `v ↦ ⟪τ, η v⟫` equals `⟨η, ∇τ⟩_{HS} - ⟪∇* η, τ⟫`. -/
theorem IsMetricCompatible.divergence_rieszDual_innerSL_comp (hcov : cov.IsMetricCompatible)
    {η : Π y : M, TangentSpace I y →L[ℝ] V y} {τ : Π y : M, V y} {x : M}
    (hη : MDiffAt
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] F) (E := fun z ↦ TangentSpace I z →L[ℝ] V z) y (η y)) x)
    (hτ : MDiffAt (T% τ) x) :
    TauCeti.Manifold.divergence I
        (fun y ↦ rieszDual (I := I) y ((innerSL ℝ (τ y)).comp (η y))) x =
      ContinuousLinearMap.hilbertSchmidtInner (η x) (cov τ x) -
        ⟪cov.codifferential (leviCivitaConnection I M) η x, τ x⟫ := by
  let b := stdOrthonormalBasis ℝ (TangentSpace I x)
  let X : Π y : M, TangentSpace I y :=
    fun y ↦ rieszDual (I := I) y ((innerSL ℝ (τ y)).comp (η y))
  have hX : MDiffAt (T% X) x := mdifferentiableAt_rieszDual_innerSL_comp hη hτ
  have hLC := (isLeviCivitaConnection_leviCivitaConnection (I := I) (M := M)).isMetricCompatible
  have hterm (i : Fin (Module.finrank ℝ (TangentSpace I x))) :
      ⟪leviCivitaConnection I M X x (b i), b i⟫ =
        ⟪η x (b i), cov τ x (b i)⟫ +
          ⟪(leviCivitaConnection I M).hom cov η x (b i) (b i), τ x⟫ := by
    let Y : Π y : M, TangentSpace I y := extend E (b i)
    have hY : MDiffAt (T% Y) x := mdifferentiableAt_extend I E (b i)
    have hLCi := hLC.mvfderiv_inner_eq Y hX hY
    have hVi := hcov.mvfderiv_inner_eq Y hτ (hη.clm_bundle_apply hY)
    have hfun : (fun y ↦ ⟪X y, Y y⟫) = fun y ↦ ⟪τ y, η y (Y y)⟫ :=
      funext fun y ↦ inner_rieszDual ((innerSL ℝ (τ y)).comp (η y)) (Y y)
    have hYX : ⟪X x, leviCivitaConnection I M Y x (b i)⟫ =
        ⟪τ x, η x (leviCivitaConnection I M Y x (b i))⟫ :=
      inner_rieszDual ((innerSL ℝ (τ x)).comp (η x)) _
    have hhom := hom_apply (leviCivitaConnection I M) cov hη hY (b i)
    dsimp only at hLCi hVi
    simp only [Y, extend_apply_self] at hLCi hVi hhom
    rw [hfun] at hLCi
    rw [hVi, hYX] at hLCi
    simp only [Y] at hLCi
    rw [real_inner_comm _ (η x (b i)), real_inner_comm (τ x), hhom, inner_sub_right]
    linarith
  rw [TauCeti.Manifold.divergence_eq_sum_inner I X x b]
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, ← ContinuousLinearMap.hilbertSchmidtInner_eq_sum (η x) (cov τ x) b,
    codifferential_eq_sum cov (leviCivitaConnection I M) η x b, inner_neg_left, sum_inner,
    sub_neg_eq_add]

end PointwiseDivergence

/-- **Pointwise divergence identity for the rough Laplacian.** Applying
`IsMetricCompatible.divergence_rieszDual_innerSL_comp` to `η = ∇σ` expresses `div X` as
`⟨∇σ, ∇τ⟩_{HS} - ⟪∇*∇σ, τ⟫`. -/
theorem IsMetricCompatible.divergence_rieszDual_innerSL_comp_cov
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
    [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
    [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
    [IsContMDiffRiemannianBundle I ∞ F V]
    {cov : CovariantDerivative I F V} [ContMDiffCovariantDerivative cov ∞]
    (hcov : cov.IsMetricCompatible) {σ τ : Π y : M, V y} {x : M}
    (hσ : CMDiff ∞ (T% σ)) (hτ : MDiffAt (T% τ) x) :
    TauCeti.Manifold.divergence I
        (fun y ↦ rieszDual (I := I) y ((innerSL ℝ (τ y)).comp (cov σ y))) x =
      ContinuousLinearMap.hilbertSchmidtInner (cov σ x) (cov τ x) -
        ⟪cov.roughLaplacian (leviCivitaConnection I M) σ x, τ x⟫ := by
  have hcovσ : CMDiff ∞
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] F) (E := fun z ↦ TangentSpace I z →L[ℝ] V z) y (cov σ y)) :=
    contMDiffOn_univ.mp
      (ContMDiffCovariantDerivative.contMDiff.contMDiff (by simpa using hσ.contMDiffOn))
  rw [hcov.divergence_rieszDual_innerSL_comp (hcovσ.mdifferentiableAt (by simp)) hτ,
    codifferential_covariantDerivative cov (leviCivitaConnection I M) hσ x]

/-! ### Formal adjunction, Green's identities, and rough-harmonic sections -/

section Integral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [MeasurableSpace M] [BorelSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  [IsContMDiffRiemannianBundle I ∞ F V]
  {cov : CovariantDerivative I F V} [ContMDiffCovariantDerivative cov ∞]

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] [MeasurableSpace M] [BorelSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
  [FiniteDimensional ℝ F] [ContMDiffVectorBundle ∞ F V I]
  [IsContMDiffRiemannianBundle I ∞ F V] in
private theorem contMDiff_cov {σ : Π y : M, V y} (hσ : CMDiff ∞ (T% σ)) :
    CMDiff ∞ (fun y ↦ TotalSpace.mk' (E →L[ℝ] F)
      (E := fun z ↦ TangentSpace I z →L[ℝ] V z) y (cov σ y)) :=
  contMDiffOn_univ.mp
    (ContMDiffCovariantDerivative.contMDiff.contMDiff (by simpa using hσ.contMDiffOn))

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] [IsManifold I ∞ M]
  [MeasurableSpace M] [BorelSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
  [FiniteDimensional ℝ F] [ContMDiffVectorBundle ∞ F V I]
  [IsContMDiffRiemannianBundle I ∞ F V] [ContMDiffCovariantDerivative cov ∞] in
/-- A covariant derivative vanishes off the closure of a section's nonzero locus. -/
private theorem covariantDerivative_eq_zero_of_notMem_closure {σ : Π y : M, V y} {x : M}
    (hx : x ∉ closure {y | σ y ≠ 0}) : cov σ x = 0 := by
  have hzero : ∀ᶠ y in 𝓝 x, σ y = (0 : Π z, V z) y :=
    Filter.eventually_of_mem (isClosed_closure.isOpen_compl.mem_nhds hx) fun y hy ↦
      by_contra fun h ↦ hy (subset_closure h)
  have h0 : MDiffAt (T% (0 : Π z, V z)) x := mdifferentiableAt_zeroSection ..
  have hT : (T% σ) =ᶠ[𝓝 x] (T% (0 : Π z, V z)) :=
    hzero.mono fun y hy ↦ congrArg (TotalSpace.mk' F y) hy
  rw [cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
    (h0.congr_of_eventuallyEq hT) h0 Filter.univ_mem hzero,
    cov.isCovariantDerivativeOnUniv.zero]

omit [I.Boundaryless] [MeasurableSpace M] [BorelSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
  [FiniteDimensional ℝ F] [ContMDiffVectorBundle ∞ F V I]
  [IsContMDiffRiemannianBundle I ∞ F V] [ContMDiffCovariantDerivative cov ∞] in
/-- Compact support of `η` or `τ` gives compact support of the Riesz-dual pairing field and of the
two scalar pairings in the divergence identity. -/
private theorem hasCompactSupport_divergence_terms
    {η : Π y : M, TangentSpace I y →L[ℝ] V y} {τ : Π y : M, V y}
    (hsupp : IsCompact (closure {y | η y ≠ 0}) ∨ IsCompact (closure {y | τ y ≠ 0})) :
    HasCompactSupport (β := E)
        (fun y ↦ rieszDual (I := I) y ((innerSL ℝ (τ y)).comp (η y))) ∧
      HasCompactSupport (fun y ↦ ContinuousLinearMap.hilbertSchmidtInner (η y) (cov τ y)) ∧
      HasCompactSupport (fun y ↦ ⟪cov.codifferential (leviCivitaConnection I M) η y, τ y⟫) := by
  rcases hsupp with hηc | hτc
  · refine ⟨HasCompactSupport.intro hηc fun x hx ↦ ?_,
      HasCompactSupport.intro hηc fun x hx ↦ ?_,
      HasCompactSupport.intro hηc fun x hx ↦ ?_⟩
    · have h0 : η x = 0 := by_contra fun h ↦ hx (subset_closure h)
      exact (rieszDual (I := I) x).map_eq_zero_iff.mpr (by simp [h0])
    · have h0 : η x = 0 := by_contra fun h ↦ hx (subset_closure h)
      simp [h0]
    · rw [codifferential_eq_zero_of_notMem_closure cov (leviCivitaConnection I M) hx,
        inner_zero_left]
  · refine ⟨HasCompactSupport.intro hτc fun x hx ↦ ?_,
      HasCompactSupport.intro hτc fun x hx ↦ ?_,
      HasCompactSupport.intro hτc fun x hx ↦ ?_⟩
    · have h0 : τ x = 0 := by_contra fun h ↦ hx (subset_closure h)
      exact (rieszDual (I := I) x).map_eq_zero_iff.mpr (by simp [h0])
    · rw [covariantDerivative_eq_zero_of_notMem_closure (cov := cov) hx, map_zero]
    · have h0 : τ x = 0 := by_contra fun h ↦ hx (subset_closure h)
      simp [h0]

/-- **Formal adjunction of `∇*` and `∇`.** On a `σ`-compact boundaryless Riemannian manifold, if
`∇` is metric-compatible and either `η` or `τ` has compact support, then
`∫ ⟪∇* η, τ⟫ dV = ∫ ⟨η, ∇τ⟩_{HS} dV`. -/
theorem IsMetricCompatible.integral_codifferential_inner [SigmaCompactSpace M]
    (hcov : cov.IsMetricCompatible)
    {η : Π y : M, TangentSpace I y →L[ℝ] V y} {τ : Π y : M, V y}
    (hη : CMDiff ∞
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] F) (E := fun z ↦ TangentSpace I z →L[ℝ] V z) y (η y)))
    (hτ : CMDiff ∞ (T% τ))
    (hsupp : IsCompact (closure {y | η y ≠ 0}) ∨ IsCompact (closure {y | τ y ≠ 0})) :
    ∫ x, ⟪cov.codifferential (leviCivitaConnection I M) η x, τ x⟫
        ∂TauCeti.riemannianVolume I M =
      ∫ x, ContinuousLinearMap.hilbertSchmidtInner (η x) (cov τ x)
        ∂TauCeti.riemannianVolume I M := by
  let _ : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  obtain ⟨hXc, hf₁c, hf₂c⟩ := hasCompactSupport_divergence_terms (cov := cov) hsupp
  have hX : ContMDiff I I.tangent 1
      (T% fun y ↦ rieszDual (I := I) y ((innerSL ℝ (τ y)).comp (η y))) :=
    (ContMDiff.rieszDual_innerSL_comp (n := ∞) hη hτ).of_le (by simp)
  have hf₁ : Integrable (fun x ↦ ContinuousLinearMap.hilbertSchmidtInner (η x) (cov τ x))
      (TauCeti.riemannianVolume I M) :=
    (ContMDiff.hilbertSchmidtInner (n := ∞) hη
      (contMDiff_cov hτ)).continuous.integrable_of_hasCompactSupport hf₁c
  have hf₂ : Integrable (fun x ↦ ⟪cov.codifferential (leviCivitaConnection I M) η x, τ x⟫)
      (TauCeti.riemannianVolume I M) :=
    ((cov.contMDiff_codifferential (leviCivitaConnection I M) hη).inner_bundle
      hτ).continuous.integrable_of_hasCompactSupport hf₂c
  have hzero := TauCeti.Manifold.integral_divergence_eq_zero hX hXc
  have hpt : ∀ x, TauCeti.Manifold.divergence I
      (fun y ↦ rieszDual (I := I) y ((innerSL ℝ (τ y)).comp (η y))) x =
        ContinuousLinearMap.hilbertSchmidtInner (η x) (cov τ x) -
          ⟪cov.codifferential (leviCivitaConnection I M) η x, τ x⟫ := fun x ↦
    hcov.divergence_rieszDual_innerSL_comp (hη.mdifferentiableAt (by simp))
      (hτ.mdifferentiableAt (by simp))
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_sub hf₁ hf₂] at hzero
  exact (sub_eq_zero.mp hzero).symm

/-- **Formal adjunction of `smoothCodifferential` and `smoothCovariantDerivative`** on bundled
smooth sections when at least one section is compactly supported. -/
theorem IsMetricCompatible.integral_smoothCodifferential_inner [SigmaCompactSpace M]
    (hcov : cov.IsMetricCompatible)
    (η : Cₛ^∞⟮I; E →L[ℝ] F, fun x ↦ TangentSpace I x →L[ℝ] V x⟯)
    (τ : Cₛ^∞⟮I; F, V⟯)
    (hsupp : η ∈ ContMDiffSection.compactlySupported I (E →L[ℝ] F) ∞
        (fun x ↦ TangentSpace I x →L[ℝ] V x) ∨
      τ ∈ ContMDiffSection.compactlySupported I F ∞ V) :
    ∫ x, ⟪cov.smoothCodifferential (leviCivitaConnection I M) η x, τ x⟫
        ∂TauCeti.riemannianVolume I M =
      ∫ x, ContinuousLinearMap.hilbertSchmidtInner (η x) (cov.smoothCovariantDerivative τ x)
        ∂TauCeti.riemannianVolume I M := by
  simp only [smoothCodifferential_apply, smoothCovariantDerivative_apply]
  exact hcov.integral_codifferential_inner η.contMDiff τ.contMDiff <|
    hsupp.imp (fun h ↦ by rwa [ContMDiffSection.mem_compactlySupported,
        ContMDiffSection.tsupport_def] at h)
      (fun h ↦ by rwa [ContMDiffSection.mem_compactlySupported,
        ContMDiffSection.tsupport_def] at h)

/-- **Green's first identity for the rough Laplacian.** On a `σ`-compact boundaryless Riemannian
manifold, if `∇` is metric-compatible and either `σ` or `τ` has compact support, then
`∫ ⟪∇*∇σ, τ⟫ dV = ∫ ⟨∇σ, ∇τ⟩_{HS} dV`. -/
theorem IsMetricCompatible.integral_roughLaplacian_inner [SigmaCompactSpace M]
    (hcov : cov.IsMetricCompatible) {σ τ : Π y : M, V y}
    (hσ : CMDiff ∞ (T% σ)) (hτ : CMDiff ∞ (T% τ))
    (hsupp : IsCompact (closure {y | σ y ≠ 0}) ∨ IsCompact (closure {y | τ y ≠ 0})) :
    ∫ x, ⟪cov.roughLaplacian (leviCivitaConnection I M) σ x, τ x⟫
        ∂TauCeti.riemannianVolume I M =
      ∫ x, ContinuousLinearMap.hilbertSchmidtInner (cov σ x) (cov τ x)
        ∂TauCeti.riemannianVolume I M := by
  have hsupp' : IsCompact (closure {y | cov σ y ≠ 0}) ∨ IsCompact (closure {y | τ y ≠ 0}) := by
    refine hsupp.imp (fun hσc ↦ hσc.of_isClosed_subset isClosed_closure ?_) id
    exact closure_minimal
      (fun x hx ↦ by_contra fun h ↦ hx (covariantDerivative_eq_zero_of_notMem_closure h))
      isClosed_closure
  have hadj := hcov.integral_codifferential_inner (contMDiff_cov hσ) hτ hsupp'
  refine (integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)).trans hadj
  rw [codifferential_covariantDerivative cov (leviCivitaConnection I M) hσ x]

/-- **Bundled Green's first identity** for `smoothRoughLaplacian`. -/
theorem IsMetricCompatible.integral_smoothRoughLaplacian_inner [SigmaCompactSpace M]
    (hcov : cov.IsMetricCompatible) (σ τ : Cₛ^∞⟮I; F, V⟯)
    (hsupp : σ ∈ ContMDiffSection.compactlySupported I F ∞ V ∨
      τ ∈ ContMDiffSection.compactlySupported I F ∞ V) :
    ∫ x, ⟪cov.smoothRoughLaplacian (leviCivitaConnection I M) σ x, τ x⟫
        ∂TauCeti.riemannianVolume I M =
      ∫ x, ContinuousLinearMap.hilbertSchmidtInner
        (cov.smoothCovariantDerivative σ x) (cov.smoothCovariantDerivative τ x)
        ∂TauCeti.riemannianVolume I M := by
  simp only [smoothRoughLaplacian_apply, smoothCovariantDerivative_apply]
  exact hcov.integral_roughLaplacian_inner σ.contMDiff τ.contMDiff <|
    hsupp.imp (fun h ↦ by rwa [ContMDiffSection.mem_compactlySupported,
        ContMDiffSection.tsupport_def] at h)
      (fun h ↦ by rwa [ContMDiffSection.mem_compactlySupported,
        ContMDiffSection.tsupport_def] at h)

/-- **Dirichlet energy identity for the rough Laplacian.** For a compactly supported smooth section
`σ` and a metric-compatible connection `∇`,
`∫ ⟪∇*∇σ, σ⟫ dV = ∫ (cov σ x).hilbertSchmidtNorm ^ 2 dV`. -/
theorem IsMetricCompatible.integral_roughLaplacian_inner_self [SigmaCompactSpace M]
    (hcov : cov.IsMetricCompatible) {σ : Π y : M, V y}
    (hσ : CMDiff ∞ (T% σ)) (hσc : IsCompact (closure {y | σ y ≠ 0})) :
    ∫ x, ⟪cov.roughLaplacian (leviCivitaConnection I M) σ x, σ x⟫
        ∂TauCeti.riemannianVolume I M =
      ∫ x, (cov σ x).hilbertSchmidtNorm ^ 2 ∂TauCeti.riemannianVolume I M := by
  rw [hcov.integral_roughLaplacian_inner hσ hσ (Or.inl hσc)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
  have : CompleteSpace (TangentSpace I x) :=
    FiniteDimensional.completeSpace ℝ (TangentSpace I x)
  exact ContinuousLinearMap.real_hilbertSchmidtInner_self_eq_hilbertSchmidtNorm_sq (cov σ x)

/-- **Dirichlet energy identity in arbitrary pointwise orthonormal bases.** The bases `b x` need
not vary continuously with `x`. -/
theorem IsMetricCompatible.integral_roughLaplacian_inner_self_eq_sum [SigmaCompactSpace M]
    (hcov : cov.IsMetricCompatible) {σ : Π y : M, V y}
    (hσ : CMDiff ∞ (T% σ)) (hσc : IsCompact (closure {y | σ y ≠ 0}))
    {ι : Type*} [Fintype ι] (b : ∀ x : M, OrthonormalBasis ι ℝ (TangentSpace I x)) :
    ∫ x, ⟪cov.roughLaplacian (leviCivitaConnection I M) σ x, σ x⟫
        ∂TauCeti.riemannianVolume I M =
      ∫ x, (∑ i, ‖cov σ x (b x i)‖ ^ 2) ∂TauCeti.riemannianVolume I M := by
  rw [hcov.integral_roughLaplacian_inner hσ hσ (Or.inl hσc)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
  simp [ContinuousLinearMap.hilbertSchmidtInner_eq_sum (cov σ x) (cov σ x) (b x)]

/-- **Green's second identity / formal self-adjointness of `∇*∇`.** On a `σ`-compact boundaryless
Riemannian manifold, if `∇` is metric-compatible and either `σ` or `τ` has compact support, then
`∫ ⟪∇*∇σ, τ⟫ dV = ∫ ⟪σ, ∇*∇τ⟫ dV`. -/
theorem IsMetricCompatible.integral_roughLaplacian_inner_eq_inner_roughLaplacian
    [SigmaCompactSpace M] (hcov : cov.IsMetricCompatible) {σ τ : Π y : M, V y}
    (hσ : CMDiff ∞ (T% σ)) (hτ : CMDiff ∞ (T% τ))
    (hsupp : IsCompact (closure {y | σ y ≠ 0}) ∨ IsCompact (closure {y | τ y ≠ 0})) :
    ∫ x, ⟪cov.roughLaplacian (leviCivitaConnection I M) σ x, τ x⟫
        ∂TauCeti.riemannianVolume I M =
      ∫ x, ⟪σ x, cov.roughLaplacian (leviCivitaConnection I M) τ x⟫
        ∂TauCeti.riemannianVolume I M := by
  have h₁ := hcov.integral_roughLaplacian_inner hσ hτ hsupp
  have h₂ := hcov.integral_roughLaplacian_inner hτ hσ hsupp.symm
  have hsymm : (∫ x, ⟪σ x, cov.roughLaplacian (leviCivitaConnection I M) τ x⟫
      ∂TauCeti.riemannianVolume I M) =
        ∫ x, ⟪cov.roughLaplacian (leviCivitaConnection I M) τ x, σ x⟫
          ∂TauCeti.riemannianVolume I M :=
    integral_congr_ae (Filter.Eventually.of_forall fun x ↦ real_inner_comm _ _)
  rw [h₁, hsymm, h₂]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x ↦
    ContinuousLinearMap.hilbertSchmidtInner_comm (cov σ x) (cov τ x))

/-- **Bundled Green's second identity** for `smoothRoughLaplacian`. -/
theorem IsMetricCompatible.integral_smoothRoughLaplacian_inner_eq_inner_smoothRoughLaplacian
    [SigmaCompactSpace M] (hcov : cov.IsMetricCompatible) (σ τ : Cₛ^∞⟮I; F, V⟯)
    (hsupp : σ ∈ ContMDiffSection.compactlySupported I F ∞ V ∨
      τ ∈ ContMDiffSection.compactlySupported I F ∞ V) :
    ∫ x, ⟪cov.smoothRoughLaplacian (leviCivitaConnection I M) σ x, τ x⟫
        ∂TauCeti.riemannianVolume I M =
      ∫ x, ⟪σ x, cov.smoothRoughLaplacian (leviCivitaConnection I M) τ x⟫
        ∂TauCeti.riemannianVolume I M := by
  simp only [smoothRoughLaplacian_apply]
  exact hcov.integral_roughLaplacian_inner_eq_inner_roughLaplacian σ.contMDiff τ.contMDiff <|
    hsupp.imp (fun h ↦ by rwa [ContMDiffSection.mem_compactlySupported,
        ContMDiffSection.tsupport_def] at h)
      (fun h ↦ by rwa [ContMDiffSection.mem_compactlySupported,
        ContMDiffSection.tsupport_def] at h)

/-- **Nonnegativity of the rough Laplacian.** For a compactly supported smooth section `σ` and a
metric-compatible connection `∇`, `0 ≤ ∫ ⟪∇*∇σ, σ⟫ dV`. -/
theorem IsMetricCompatible.integral_roughLaplacian_inner_self_nonneg [SigmaCompactSpace M]
    (hcov : cov.IsMetricCompatible) {σ : Π y : M, V y}
    (hσ : CMDiff ∞ (T% σ)) (hσc : IsCompact (closure {y | σ y ≠ 0})) :
    0 ≤ ∫ x, ⟪cov.roughLaplacian (leviCivitaConnection I M) σ x, σ x⟫
      ∂TauCeti.riemannianVolume I M := by
  rw [hcov.integral_roughLaplacian_inner hσ hσ (Or.inl hσc)]
  exact integral_nonneg fun x ↦ ContinuousLinearMap.hilbertSchmidtInner_self_nonneg (cov σ x)

/-- **Characterization of rough-harmonic compactly supported sections.** On a `σ`-compact
boundaryless Riemannian manifold, a compactly supported smooth section `σ` satisfies `∇*∇σ = 0`
everywhere if and only if `σ` is parallel (`∇σ = 0` everywhere). -/
theorem IsMetricCompatible.roughLaplacian_eq_zero_iff [SigmaCompactSpace M]
    (hcov : cov.IsMetricCompatible) {σ : Π y : M, V y}
    (hσ : CMDiff ∞ (T% σ)) (hσc : IsCompact (closure {y | σ y ≠ 0})) :
    (∀ x, cov.roughLaplacian (leviCivitaConnection I M) σ x = 0) ↔ ∀ x, cov σ x = 0 := by
  refine ⟨fun hΔ x ↦ ?_, fun hpar x ↦ ?_⟩
  · let _ : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
    let g : M → ℝ := fun y ↦ ContinuousLinearMap.hilbertSchmidtInner (cov σ y) (cov σ y)
    have hg_cont : Continuous g :=
      (ContMDiff.hilbertSchmidtInner (n := ∞) (contMDiff_cov hσ) (contMDiff_cov hσ)).continuous
    have hg_supp : HasCompactSupport g :=
      HasCompactSupport.intro hσc fun y hy ↦ by
        simp [g, covariantDerivative_eq_zero_of_notMem_closure (cov := cov) hy]
    have hzero : ∫ y, g y ∂TauCeti.riemannianVolume I M = 0 := by
      have h := (hcov.integral_roughLaplacian_inner hσ hσ (Or.inl hσc)).symm
      simpa only [g, hΔ, inner_zero_left, integral_zero] using h
    have hae := (integral_eq_zero_iff_of_nonneg
      (fun y ↦ ContinuousLinearMap.hilbertSchmidtInner_self_nonneg (cov σ y))
      (hg_cont.integrable_of_hasCompactSupport hg_supp)).mp hzero
    exact ContinuousLinearMap.hilbertSchmidtInner_self_eq_zero.mp
      (congrFun ((hg_cont.ae_eq_iff_eq _ continuous_zero).mp hae) x)
  · rw [← codifferential_covariantDerivative cov (leviCivitaConnection I M) hσ x,
      show cov σ = 0 from funext hpar, codifferential_zero]

/-- **Characterization of rough-harmonic sections on a closed manifold.** On a compact boundaryless
Riemannian manifold, a smooth section satisfies `∇*∇σ = 0` everywhere if and only if it is
parallel (`∇σ = 0` everywhere). -/
theorem IsMetricCompatible.roughLaplacian_eq_zero_iff_of_compactSpace [CompactSpace M]
    (hcov : cov.IsMetricCompatible) {σ : Π y : M, V y} (hσ : CMDiff ∞ (T% σ)) :
    (∀ x, cov.roughLaplacian (leviCivitaConnection I M) σ x = 0) ↔ ∀ x, cov σ x = 0 :=
  hcov.roughLaplacian_eq_zero_iff hσ isClosed_closure.isCompact

/-- **Bundled characterization of compactly supported rough-harmonic smooth sections.** -/
theorem IsMetricCompatible.smoothRoughLaplacian_eq_zero_iff [SigmaCompactSpace M]
    (hcov : cov.IsMetricCompatible) (σ : Cₛ^∞⟮I; F, V⟯)
    (hσc : σ ∈ ContMDiffSection.compactlySupported I F ∞ V) :
    cov.smoothRoughLaplacian (leviCivitaConnection I M) σ = 0 ↔
      cov.smoothCovariantDerivative σ = 0 := by
  have hσc' : IsCompact (closure {y | σ y ≠ 0}) := by
    rwa [ContMDiffSection.mem_compactlySupported, ContMDiffSection.tsupport_def] at hσc
  simpa only [ContMDiffSection.ext_iff, smoothRoughLaplacian_apply,
    smoothCovariantDerivative_apply, ContMDiffSection.coe_zero, Pi.zero_apply] using
    hcov.roughLaplacian_eq_zero_iff σ.contMDiff hσc'

/-- **Bundled characterization of rough-harmonic smooth sections on a closed manifold.** -/
theorem IsMetricCompatible.smoothRoughLaplacian_eq_zero_iff_of_compactSpace [CompactSpace M]
    (hcov : cov.IsMetricCompatible) (σ : Cₛ^∞⟮I; F, V⟯) :
    cov.smoothRoughLaplacian (leviCivitaConnection I M) σ = 0 ↔
      cov.smoothCovariantDerivative σ = 0 :=
  hcov.smoothRoughLaplacian_eq_zero_iff σ (by simp)

/-- On a preconnected `σ`-compact boundaryless Riemannian manifold, a compactly supported
rough-harmonic smooth section that vanishes at one point vanishes everywhere. -/
theorem IsMetricCompatible.eq_zero_of_roughLaplacian_eq_zero_of_apply_eq_zero
    [SigmaCompactSpace M] [PreconnectedSpace M] (hcov : cov.IsMetricCompatible)
    {σ : Π y : M, V y} (hσ : CMDiff ∞ (T% σ)) (hσc : IsCompact (closure {y | σ y ≠ 0}))
    (hΔ : ∀ x, cov.roughLaplacian (leviCivitaConnection I M) σ x = 0)
    {x₀ : M} (hx₀ : σ x₀ = 0) (x : M) : σ x = 0 := by
  have hpar := (hcov.roughLaplacian_eq_zero_iff hσ hσc).mp hΔ
  have hdiff : MDiff[univ] (T% σ) := (hσ.mdifferentiable (by simp)).mdifferentiableOn
  have hconst := hcov.inner_eq_of_isPreconnected_of_cov_eq_zero isOpen_univ isPreconnected_univ
    hdiff hdiff (fun y _ ↦ hpar y) (fun y _ ↦ hpar y) (mem_univ x) (mem_univ x₀)
  rw [hx₀, inner_zero_left, inner_self_eq_zero] at hconst
  exact hconst

/-- On a noncompact preconnected `σ`-compact boundaryless Riemannian manifold, every compactly
supported rough-harmonic smooth section vanishes identically. -/
theorem IsMetricCompatible.eq_zero_of_roughLaplacian_eq_zero_of_noncompactSpace
    [SigmaCompactSpace M] [PreconnectedSpace M] [NoncompactSpace M]
    (hcov : cov.IsMetricCompatible) {σ : Π y : M, V y}
    (hσ : CMDiff ∞ (T% σ)) (hσc : IsCompact (closure {y | σ y ≠ 0}))
    (hΔ : ∀ x, cov.roughLaplacian (leviCivitaConnection I M) σ x = 0) (x : M) : σ x = 0 := by
  obtain ⟨x₀, hx₀⟩ := nonempty_compl.mpr hσc.ne_univ
  exact hcov.eq_zero_of_roughLaplacian_eq_zero_of_apply_eq_zero hσ hσc hΔ
    (by_contra fun h ↦ hx₀ (subset_closure h)) x

end Integral

end CovariantDerivative

end

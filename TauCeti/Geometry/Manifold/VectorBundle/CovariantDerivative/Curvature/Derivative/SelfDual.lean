/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.HodgeStar.Bianchi
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Derivative.Form
public import Mathlib.Topology.VectorBundle.Riemannian
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Derivative.Connection
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric.HodgeStar

/-!
# The divergence of the curvature of a connection over a four-manifold

Let `∇` be a smooth connection on a vector bundle `V` over a Riemannian manifold `M`, with
curvature `R`, and let `∇ᵀ` be a smooth torsion-free connection on the tangent bundle, such as the
Levi-Civita connection. At a point `x`, the covariant derivative `∇_v R` of the curvature
(`CovariantDerivative.derivCurvatureTensor`) is antisymmetric in its two curvature arguments, so it
is a two-form on `T_x M` with values in the endomorphisms of `V x`,
`CovariantDerivative.derivCurvatureForm`, with `u ∧ w ↦ (∇_v R)(u, w)`
(`TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Derivative.Form`). The
second Bianchi identity for these forms
(`CovariantDerivative.derivCurvatureForm_cyclic_eq_zero`) says that this linear family of
two-forms is a Bianchi family in the sense of
`TauCeti.Analysis.InnerProductSpace.HodgeStar.Bianchi`.

The **divergence of the curvature** at `x`, along an orthonormal basis `(eᵢ)` of `T_x M`, is
`a ↦ ∑ᵢ (∇_{eᵢ} R)(a, eᵢ)`, the endomorphism-valued one-form `d_∇^* R`. When `M` has dimension four
and `T_x M` is oriented, the Hodge star acts on the form side of `∇_v R`, and the pointwise results
of that file give:

* the divergence of the Hodge dual of `∇R` vanishes,
  `∑ᵢ (⋆∇_{eᵢ} R)(a ∧ eᵢ) = 0`
  (`CovariantDerivative.sum_vectorFormHodgeStar_derivCurvatureForm_apply_ιMulti_eq_zero`);
* the divergence of the curvature is twice the divergence of the self-dual part of `∇R`, and twice
  that of its anti-self-dual part:
  `∑ᵢ (∇_{eᵢ} R)(a, eᵢ) = 2 ∑ᵢ (∇_{eᵢ} R)⁺(a ∧ eᵢ) = 2 ∑ᵢ (∇_{eᵢ} R)⁻(a ∧ eᵢ)`
  (`CovariantDerivative.sum_derivCurvatureTensor_eq_two_smul_sum_vectorFormSelfDualPart`,
  `CovariantDerivative.sum_derivCurvatureTensor_eq_two_smul_sum_vectorFormAntiSelfDualPart`).

Here `(∇_v R)⁺` is the self-dual part of the two-form `∇_v R`, not the covariant derivative of the
self-dual part `R⁺` of the curvature. The two agree when `∇ᵀ` is metric-compatible, such as the
Levi-Civita connection, since `∇_v` then commutes with `⋆`
(`CovariantDerivative.IsMetricCompatible.hom_hom_apply_eq_smul_add_smul_sum_sum_volumeForm_smul`).
For a field `P` which near `x` is the self-dual part of the curvature in a local frame with constant
inner products, the covariant derivative of `P`, taken with the connection induced on
`Hom(TM, Hom(TM, End V))`, is the self-dual part of `∇_v R`
(`CovariantDerivative.IsMetricCompatible.hom_hom_apply_eq_vectorFormSelfDualPart`), and the
identity above becomes `d_∇^* F = 2 d_∇^* F⁺` of four-dimensional gauge theory
(`CovariantDerivative.IsMetricCompatible.sum_derivCurvatureTensor_eq_two_smul_sum_hom_hom`). For the
large-parameter Seiberg–Witten equations, whose curvature equation prescribes the self-dual part of
the curvature but not its anti-self-dual part, this is the route by which the curvature equation
is expected to control the divergence `∑ᵢ (∇_{eᵢ} R)(·, eᵢ)` that enters the differentiated
Weitzenböck inequalities behind Taubes's gradient bound
(`TauCeti.SeibergWitten.innerCovariantDerivative_self_add_mul_innerCovariantDerivative_self_le`),
although `∇R` itself is not bounded.

## Main results

* `CovariantDerivative.sum_vectorFormHodgeStar_derivCurvatureForm_apply_ιMulti_eq_zero`: the
  divergence of the Hodge dual of `∇R` vanishes in dimension four.
* `CovariantDerivative.sum_derivCurvatureTensor_eq_two_smul_sum_vectorFormSelfDualPart`,
  `CovariantDerivative.sum_derivCurvatureTensor_eq_two_smul_sum_vectorFormAntiSelfDualPart`: the
  divergence of the curvature is twice that of the self-dual part of `∇R`, and twice that of its
  anti-self-dual part.
* `CovariantDerivative.IsMetricCompatible.hom_hom_apply_eq_vectorFormSelfDualPart`: for a
  metric-compatible `∇ᵀ`, the covariant derivative of the self-dual part of the curvature is the
  self-dual part of `∇R`.
* `CovariantDerivative.IsMetricCompatible.sum_derivCurvatureTensor_eq_two_smul_sum_hom_hom`:
  `d_∇^* F = 2 d_∇^* F⁺` for a metric-compatible torsion-free `∇ᵀ`.

## References

* S. K. Donaldson and P. B. Kronheimer, *The Geometry of Four-Manifolds*, Oxford University Press,
  1990, Section 2.1.
* C. H. Taubes, *SW ⇒ Gr: From the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918, Section 2.
-/

public section

open Bundle Module exteriorPower
open scoped ContDiff Manifold

noncomputable section

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  (cov : CovariantDerivative I F V) [ContMDiffCovariantDerivative cov ∞]
  (covT : CovariantDerivative I E (TangentSpace I : M → Type _))

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [ContMDiffCovariantDerivative covT ∞]
  (ht : covT.torsion = 0) (x : M) [Fact (finrank ℝ (TangentSpace I x) = 4)]
  (o : Orientation ℝ (TangentSpace I x) (Fin 4)) (hkl : 2 + 2 = finrank ℝ (TangentSpace I x))
  {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ (TangentSpace I x)) (a : TangentSpace I x)
include ht

/-- **The divergence of the Hodge dual of `∇R` vanishes** in dimension four: for a smooth
torsion-free `∇ᵀ`, an orientation of `T_x M` and an orthonormal basis `(eᵢ)`,
`∑ᵢ (⋆∇_{eᵢ} R)(a ∧ eᵢ) = 0`. -/
theorem sum_vectorFormHodgeStar_derivCurvatureForm_apply_ιMulti_eq_zero :
    ∑ i, o.vectorFormHodgeStar hkl (cov.derivCurvatureForm covT x (b i)) (ιMulti ℝ 2 ![a, b i]) =
      0 :=
  o.sum_vectorFormHodgeStar_apply_ιMulti_eq_zero hkl b _
    (cov.derivCurvatureForm_cyclic_eq_zero covT ht x) a

/-- **The divergence of the curvature is twice that of the self-dual part of `∇R`** in dimension
four: for a smooth torsion-free `∇ᵀ`, an orientation of `T_x M` and an orthonormal basis `(eᵢ)`,
`∑ᵢ (∇_{eᵢ} R)(a, eᵢ) = 2 ∑ᵢ (∇_{eᵢ} R)⁺(a ∧ eᵢ)`. This is `d_∇^* F = 2 d_∇^* F⁺` once `∇_v`
commutes with `⋆`, as it does for a metric-compatible `∇ᵀ`. -/
theorem sum_derivCurvatureTensor_eq_two_smul_sum_vectorFormSelfDualPart :
    ∑ i, cov.derivCurvatureTensor covT x (b i) a (b i) =
      (2 : ℝ) • ∑ i, o.vectorFormSelfDualPart hkl (cov.derivCurvatureForm covT x (b i))
        (ιMulti ℝ 2 ![a, b i]) := by
  simpa using o.sum_apply_ιMulti_eq_two_smul_sum_vectorFormSelfDualPart hkl b _
    (cov.derivCurvatureForm_cyclic_eq_zero covT ht x) a

/-- **The divergence of the curvature is twice that of the anti-self-dual part of `∇R`** in
dimension four: `∑ᵢ (∇_{eᵢ} R)(a, eᵢ) = 2 ∑ᵢ (∇_{eᵢ} R)⁻(a ∧ eᵢ)`. This is
`d_∇^* F = 2 d_∇^* F⁻` once `∇_v` commutes with `⋆`, as it does for a metric-compatible `∇ᵀ`. -/
theorem sum_derivCurvatureTensor_eq_two_smul_sum_vectorFormAntiSelfDualPart :
    ∑ i, cov.derivCurvatureTensor covT x (b i) a (b i) =
      (2 : ℝ) • ∑ i, o.vectorFormAntiSelfDualPart hkl (cov.derivCurvatureForm covT x (b i))
        (ιMulti ℝ 2 ![a, b i]) := by
  simpa using o.sum_apply_ιMulti_eq_two_smul_sum_vectorFormAntiSelfDualPart hkl b _
    (cov.derivCurvatureForm_cyclic_eq_zero covT ht x) a

end CovariantDerivative

open Filter
open scoped Topology

namespace CovariantDerivative

section MetricCompatible

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, NormedSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  (cov : CovariantDerivative I F V) [ContMDiffCovariantDerivative cov ∞]
  {covT : CovariantDerivative I E (TangentSpace I : M → Type _)}
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  (hT : IsMetricCompatible (V := fun y : M ↦ TangentSpace I y) covT) {x : M}
  [Fact (finrank ℝ (TangentSpace I x) = 4)] (o : Orientation ℝ (TangentSpace I x) (Fin 4))
  (hkl : 2 + 2 = finrank ℝ (TangentSpace I x)) {ι : Type*} [Fintype ι]
  (b : OrthonormalBasis ι ℝ (TangentSpace I x)) {e : ι → Π y : M, TangentSpace I y}
  (he : ∀ i, MDiffAt (T% (e i)) x) (hb : ∀ i, e i x = b i)
  (hon : ∀ i j, (fun y ↦ inner ℝ (e i y) (e j y)) =ᶠ[𝓝 x] fun _ ↦ inner ℝ (b i) (b j))
  {P : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] V y →L[ℝ] V y}
  (hP :
    -- Cache the standard model instances while elaborating the nested operator spaces.
    let _ : NormedAddCommGroup (F →L[ℝ] F) := inferInstance
    let _ : NormedSpace ℝ (F →L[ℝ] F) := inferInstance
    MDifferentiableAt I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] F →L[ℝ] F))
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] F →L[ℝ] F)
        (E := fun z ↦ TangentSpace I z →L[ℝ] TangentSpace I z →L[ℝ] V z →L[ℝ] V z) y (P y)) x)
  (hPR : ∀ᶠ y in 𝓝 x, ∀ i j, P y (e i y) (e j y) = (2⁻¹ : ℝ) •
    (cov.curvatureTensorCLM y (e i y) (e j y) + (2⁻¹ : ℝ) •
      ∑ k, ∑ l, o.volumeForm ![b i, b j, b k, b l] • cov.curvatureTensorCLM y (e k y) (e l y)))
include hT hkl he hb hon hP hPR

/-- **The covariant derivative of the self-dual part of the curvature is the self-dual part of
`∇R`.** Let `∇ᵀ` be a metric-compatible connection on the tangent bundle, `(eₖ)` a local frame
near `x` with constant inner products and value an orthonormal basis `(bₖ)` at `x`, and `o` an
orientation of the four-dimensional `T_x M`. If, near `x`, the field `P` of endomorphism-valued
two-forms is the self-dual part `R⁺ = (R + ⋆R) / 2` of the curvature in the frame `(eₖ)`, then at
`x` its covariant derivative is the self-dual part of the covariant derivative of the curvature:
`(∇_v P)(u, w) = (∇_v R)⁺(u ∧ w)`. -/
theorem IsMetricCompatible.hom_hom_apply_eq_vectorFormSelfDualPart (v u w : TangentSpace I x)
    (s : V x) :
    covT.hom (covT.hom (cov.hom cov)) P x v u w s =
      o.vectorFormSelfDualPart hkl (cov.derivCurvatureForm covT x v) (ιMulti ℝ 2 ![u, w]) s := by
  -- Cache the nested operator norms to bound instance search for the Hom-bundle evaluations.
  let _ : NormedAddCommGroup (F →L[ℝ] F) := inferInstance
  let _ : NormedSpace ℝ (F →L[ℝ] F) := inferInstance
  let _ : NormedAddCommGroup (E →L[ℝ] F →L[ℝ] F) := inferInstance
  let _ : NormedSpace ℝ (E →L[ℝ] F →L[ℝ] F) := inferInstance
  let _ : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] F →L[ℝ] F) := inferInstance
  let _ : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] F →L[ℝ] F) := inferInstance
  have hR : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] F →L[ℝ] F)) ∞
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] F →L[ℝ] F) y
        (cov.curvatureTensorCLM y)) := cov.contMDiff_curvatureTensorCLM
  have h := hT.hom_hom_apply_eq_smul_add_smul_sum_sum_volumeForm_smul (cov.hom cov) o b he hb hon
    (hR.mdifferentiableAt (by simp)) hP (2⁻¹) (2⁻¹)
    (hPR.mono fun y hy i j ↦ by rw [hy i j, smul_add]) v u w
  rw [← derivCurvatureTensorCLM_eq_hom] at h
  rw [h, o.vectorFormSelfDualPart_apply, LinearMap.smul_apply, LinearMap.add_apply,
    o.vectorFormHodgeStar_apply_ιMulti_two hkl b]
  simp [smul_add]

/-- **The divergence of the curvature is twice that of its self-dual part**,
`d_∇^* F = 2 d_∇^* F⁺`, for a smooth metric-compatible torsion-free `∇ᵀ`, such as the Levi-Civita
connection. If, near `x`, the field `P` is the self-dual part of the curvature in a local frame
`(eₖ)` with constant inner products and value the orthonormal basis `(bₖ)` at `x`, then for every
vector `a` and every `s ∈ V x`, `∑ᵢ (∇_{bᵢ} R)(a, bᵢ) s = 2 ∑ᵢ (∇_{bᵢ} P)(a, bᵢ) s`. So an
equation prescribing the self-dual part of the curvature controls the divergence of the whole
curvature through the derivative of the prescribed field. -/
theorem IsMetricCompatible.sum_derivCurvatureTensor_eq_two_smul_sum_hom_hom
    [ContMDiffCovariantDerivative covT ∞] (ht : covT.torsion = 0) (a : TangentSpace I x)
    (s : V x) :
    ∑ i, cov.derivCurvatureTensor covT x (b i) a (b i) s =
      (2 : ℝ) • ∑ i, covT.hom (covT.hom (cov.hom cov)) P x (b i) a (b i) s := by
  have h := LinearMap.congr_fun
    (cov.sum_derivCurvatureTensor_eq_two_smul_sum_vectorFormSelfDualPart covT ht x o hkl b a) s
  simp only [LinearMap.sum_apply, LinearMap.smul_apply] at h
  rw [h]
  congr 1
  exact Finset.sum_congr rfl fun i _ ↦
    (hT.hom_hom_apply_eq_vectorFormSelfDualPart cov o hkl b he hb hon hP hPR (b i) a (b i) s).symm

end MetricCompatible

end CovariantDerivative

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Volume
public import TauCeti.Geometry.Manifold.Riemannian.Basic
public import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic
public import Mathlib.Analysis.InnerProductSpace.NormDet
public import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Change of variables for the Riemannian volume

Let `f : F → M` be a map from a finite-dimensional real vector space to a Riemannian manifold and
let `b` be a basis of `F`. The Riemannian Jacobian `TauCeti.riemannianJacobian b f x` is the square
root of the Gram determinant `det ⟪df_x (b i), df_x (b j)⟫` in the metric at `f x`. It is the
density of the pulled back Riemannian volume with respect to `b.addHaar`, the Haar measure giving
the parallelepiped spanned by `b` measure one. A change of basis multiplies the Jacobian and the
Haar measure by inverse factors, so the weighted coordinate measure does not depend on `b`. For an
orthonormal basis of an inner product space the Jacobian is Mathlib's `LinearMap.normDet` of the
differential.

If `f` is injective and differentiable on a measurable set `s` whose image is measurable and lies
in a preferred chart, then `∫⁻ y in f '' s, φ y ∂vol = ∫⁻ x in s, J_b f x * φ (f x) ∂b.addHaar`.
A countable chart cover gives the global statement: a `C¹` partial diffeomorphism `Φ` from `F` to
`M` carries `b.addHaar` on its source, weighted by its Jacobian, to the Riemannian volume on its
target.

The space `F` and the model space of `M` may differ, provided they have the same dimension. No
orientation is used, and `M` may have boundary or corners.

## Main definitions

* `TauCeti.riemannianJacobian`: the Riemannian Jacobian of a map from a vector space with a basis.

## Main results

* `TauCeti.riemannianJacobian_changeBasis`: a change of basis multiplies the Jacobian by the
  absolute value of its determinant.
* `TauCeti.riemannianJacobian_eq_normDet`: for an orthonormal basis, the Jacobian is the norm
  determinant of the differential.
* `TauCeti.setLIntegral_riemannianJacobian_changeBasis`: the Jacobian-weighted coordinate integral
  does not depend on the basis.
* `TauCeti.setLIntegral_riemannianVolume_image_of_subset_chart`: change of variables for an
  injective differentiable map whose image lies in a preferred chart.
* `PartialDiffeomorph.map_withDensity_riemannianJacobian`: a partial diffeomorphism carries the
  Jacobian-weighted coordinate measure on its source to the Riemannian volume on its target.
* `PartialDiffeomorph.setLIntegral_riemannianVolume_eq`: the corresponding change of variables
  formula for integrals over the target.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 2.
-/

open Bundle FiberBundle MeasureTheory Set Riemannian.Tensor
open scoped ENNReal InnerProductSpace Manifold

public noncomputable section

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {ι ι' : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']

section Jacobian

/-- The **Riemannian Jacobian** of `f : F → M` at `x` with respect to a basis `b` of `F`: the
square root of the Gram determinant of the vectors `mfderiv f x (b i)` in the Riemannian metric
at `f x`. It is the density of the pulled back Riemannian volume with respect to `b.addHaar`. -/
def riemannianJacobian (b : Module.Basis ι ℝ F) (f : F → M) (x : F) : ℝ :=
  Real.sqrt (Matrix.gram ℝ (fun i ↦ mfderiv 𝓘(ℝ, F) I f x (b i))).det

/-- The coordinate formula for the Riemannian Jacobian. -/
theorem riemannianJacobian_eq_sqrt_det_gram (b : Module.Basis ι ℝ F) (f : F → M) (x : F) :
    riemannianJacobian (I := I) b f x =
      Real.sqrt (Matrix.gram ℝ (fun i ↦ mfderiv 𝓘(ℝ, F) I f x (b i))).det :=
  (rfl)

/-- The Riemannian Jacobian is nonnegative. -/
theorem riemannianJacobian_nonneg (b : Module.Basis ι ℝ F) (f : F → M) (x : F) :
    0 ≤ riemannianJacobian (I := I) b f x :=
  Real.sqrt_nonneg _

/-- Relabeling the basis leaves the Riemannian Jacobian unchanged. -/
@[simp]
theorem riemannianJacobian_reindex (b : Module.Basis ι ℝ F) (e : ι ≃ ι') (f : F → M) (x : F) :
    riemannianJacobian (I := I) (b.reindex e) f x = riemannianJacobian (I := I) b f x := by
  rw [riemannianJacobian_eq_sqrt_det_gram, riemannianJacobian_eq_sqrt_det_gram]
  congr 1
  have hm : Matrix.gram ℝ (fun i ↦ mfderiv 𝓘(ℝ, F) I f x ((b.reindex e) i)) =
      (Matrix.gram ℝ (fun i ↦ mfderiv 𝓘(ℝ, F) I f x (b i))).submatrix e.symm e.symm := by
    ext i j
    simp only [Matrix.gram_apply, Matrix.submatrix_apply, Module.Basis.reindex_apply]
  rw [hm, Matrix.det_submatrix_equiv_self]

/-- A change of basis multiplies the Riemannian Jacobian by the absolute value of the
determinant of the change of basis. -/
theorem riemannianJacobian_changeBasis (b c : Module.Basis ι ℝ F) (f : F → M) (x : F) :
    riemannianJacobian (I := I) c f x = |b.det c| * riemannianJacobian (I := I) b f x := by
  let D : F →L[ℝ] TangentSpace I (f x) := mfderiv 𝓘(ℝ, F) I f x
  let B := LinearMap.BilinForm.comp (innerₗ (TangentSpace I (f x))) D.toLinearMap D.toLinearMap
  have hgram (a : Module.Basis ι ℝ F) :
      Matrix.gram ℝ (fun i ↦ D (a i)) = LinearMap.BilinForm.toMatrix a B := by
    ext i j
    simp [B, Matrix.gram_apply, LinearMap.BilinForm.toMatrix_apply]
  have hdet : (LinearMap.BilinForm.toMatrix c B).det =
      (b.det c) ^ 2 * (LinearMap.BilinForm.toMatrix b B).det := by
    rw [← LinearMap.BilinForm.toMatrix_mul_basis_toMatrix b c B,
      Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Module.Basis.det_apply]
    ring
  rw [riemannianJacobian_eq_sqrt_det_gram, riemannianJacobian_eq_sqrt_det_gram]
  -- `D` is `mfderiv 𝓘(ℝ, F) I f x` with its domain `TangentSpace 𝓘(ℝ, F) x` read as `F`. Mathlib
  -- implements this identification definitionally, so no rewrite lemma restates the Gram matrices
  -- in terms of `D`, and `rw [hgram]` cannot see through the two domain types.
  change Real.sqrt (Matrix.gram ℝ (fun i ↦ D (c i))).det =
    |b.det c| * Real.sqrt (Matrix.gram ℝ (fun i ↦ D (b i))).det
  rw [hgram, hgram, hdet, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]

/-- Precomposing with a continuous linear equivalence `A` transports the Riemannian Jacobian to
the image of the basis under `A`. -/
theorem riemannianJacobian_comp_continuousLinearEquiv {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] (A : G ≃L[ℝ] F) (b : Module.Basis ι ℝ G) {f : F → M} {x : G}
    (hf : MDifferentiableAt 𝓘(ℝ, F) I f (A x)) :
    riemannianJacobian (I := I) b (f ∘ A) x =
      riemannianJacobian (I := I) (b.map A.toLinearEquiv) f (A x) := by
  rw [riemannianJacobian_eq_sqrt_det_gram, riemannianJacobian_eq_sqrt_det_gram]
  congr 2
  ext i j
  rw [Matrix.gram_apply, Matrix.gram_apply,
    (hf.hasMFDerivAt.comp x A.hasFDerivAt.hasMFDerivAt).mfderiv]
  -- The composite acts on `TangentSpace 𝓘(ℝ, G) x`, which Mathlib identifies with `G` only
  -- definitionally, so `ContinuousLinearMap.comp_apply` does not match; evaluate it by `change`.
  change ⟪mfderiv 𝓘(ℝ, F) I f (A x) (A (b i)),
    mfderiv 𝓘(ℝ, F) I f (A x) (A (b j))⟫_ℝ = _
  simp only [Module.Basis.map_apply, ContinuousLinearEquiv.coe_toLinearEquiv]

/-- For an orthonormal basis of an inner product space, the Riemannian Jacobian is the norm
determinant of the differential. -/
theorem riemannianJacobian_eq_normDet {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (b : OrthonormalBasis ι ℝ V) (f : V → M) (x : V) :
    riemannianJacobian (I := I) b.toBasis f x =
      LinearMap.normDet (U := V) (mfderiv 𝓘(ℝ, V) I f x).toLinearMap := by
  have h := LinearMap.normDet_sq_eq_det_gram (U := V) (mfderiv 𝓘(ℝ, V) I f x).toLinearMap b
  simp only [RCLike.ofReal_real_eq_id, id_eq] at h
  refine Eq.trans ?_ (Real.sqrt_sq (LinearMap.normDet_nonneg (U := V) _))
  rw [h, riemannianJacobian_eq_sqrt_det_gram, OrthonormalBasis.coe_toBasis]
  rfl

end Jacobian

section Integral

variable [MeasurableSpace F] [BorelSpace F]

/-- The Jacobian-weighted coordinate integral does not depend on the basis, when it is taken
against the Haar measure of the same basis. The weight need not be measurable. -/
theorem setLIntegral_riemannianJacobian_changeBasis (b c : Module.Basis ι ℝ F) (f : F → M)
    (s : Set F) (φ : F → ℝ≥0∞) :
    ∫⁻ x in s, ENNReal.ofReal (riemannianJacobian (I := I) b f x) * φ x ∂b.addHaar =
      ∫⁻ x in s, ENNReal.ofReal (riemannianJacobian (I := I) c f x) * φ x ∂c.addHaar := by
  have : FiniteDimensional ℝ F := b.finiteDimensional_of_finite
  have hd : b.det c ≠ 0 := (b.isUnit_det c).ne_zero
  have hμ : c.addHaar = (|b.det c|⁻¹).toNNReal • b.addHaar := by
    rw [Module.Basis.addHaar_eq_iff, smul_apply, Module.Basis.coe_parallelepiped,
      Measure.addHaar_parallelepiped, ENNReal.smul_def, smul_eq_mul, ← ENNReal.ofReal.eq_1,
      ← ENNReal.ofReal_mul (by positivity)]
    simp [hd]
  rw [hμ, Measure.restrict_smul, lintegral_smul_measure]
  simp only [riemannianJacobian_changeBasis b c, ENNReal.ofReal_mul (abs_nonneg _), mul_assoc]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ENNReal.smul_def, smul_eq_mul,
    ← ENNReal.ofReal.eq_1, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  simp [hd]

end Integral

section Chart

variable [IsManifold I 1 M]

section Continuity

variable [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

/-- The Riemannian Jacobian of a `C¹` map is continuous on an open set. -/
theorem continuousOn_riemannianJacobian (b : Module.Basis ι ℝ F)
    {f : F → M} {U : Set F} (hf : ContMDiffOn 𝓘(ℝ, F) I 1 f U) (hU : IsOpen U) :
    ContinuousOn (riemannianJacobian (I := I) b f) U := by
  have : IsContMDiffRiemannianBundle I 0 E (fun x : M ↦ TangentSpace I x) :=
    IsContinuousRiemannianBundle.toIsContMDiffZero
  have hgram : ContinuousOn (fun x ↦ Matrix.gram ℝ
      (fun i ↦ mfderiv 𝓘(ℝ, F) I f x (b i))) U :=
    continuousOn_pi.mpr fun i ↦ continuousOn_pi.mpr fun j ↦ by
      simpa only [Matrix.gram_apply] using
        (hf.contDiffOn_inner_mfderiv (m := 0) (by simp) hU (b i) (b j)).continuousOn
  exact Real.continuous_sqrt.comp_continuousOn (continuous_id.matrix_det.comp_continuousOn hgram)

end Continuity

variable [FiniteDimensional ℝ E]

/-- In the preferred chart at `α`, the Riemannian Jacobian of `f : E → M` in the basis
`Module.finBasis ℝ E` is the absolute determinant of the coordinate derivative of `f` times the
chart volume density at `f x`. -/
theorem riemannianJacobian_finBasis_eq_abs_det_mul_chartVolumeDensity
    {f : E → M} {x : E} {α : M} (hx : f x ∈ (chartAt H α).source) :
    riemannianJacobian (I := I) (Module.finBasis ℝ E) f x =
      |(mfderiv I 𝓘(ℝ, E) (extChartAt I α) (f x) ∘L
        mfderiv 𝓘(ℝ, E) I f x : E →L[ℝ] E).det| *
      chartVolumeDensity (I := I) α (f x) := by
  have hα : f x ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    simpa only [TangentBundle.trivializationAt_baseSet] using hx
  let b := Module.finBasis ℝ E
  let bα := (trivializationAt E (TangentSpace I) α).basisAt b hα
  let D : E →L[ℝ] TangentSpace I (f x) := mfderiv 𝓘(ℝ, E) I f x
  let L : E →L[ℝ] E := mfderiv I 𝓘(ℝ, E) (extChartAt I α) (f x) ∘L D
  have hmat : LinearMap.toMatrix b bα D.toLinearMap =
      LinearMap.toMatrix b b L.toLinearMap := by
    ext k i
    simp only [LinearMap.toMatrix_apply, bα, Trivialization.basisAt,
      Module.Basis.map_repr, LinearEquiv.trans_apply, LinearEquiv.symm_symm,
      Trivialization.linearEquivAt_apply]
    rw [← Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) _ hα,
      TangentBundle.continuousLinearMapAt_trivializationAt hx]
    rfl
  have hgram : Matrix.gram ℝ (fun i ↦ D (b i)) =
      LinearMap.BilinForm.toMatrix b
        (LinearMap.BilinForm.comp (innerₗ (TangentSpace I (f x))) D.toLinearMap D.toLinearMap) := by
    ext i j
    simp [Matrix.gram_apply, LinearMap.BilinForm.toMatrix_apply]
  have hdet : (Matrix.gram ℝ (fun i ↦ D (b i))).det =
      L.det ^ 2 * (chartGramMatrix (I := I) α (f x)).det := by
    rw [hgram, chartGramMatrix_eq_toMatrix α hα,
      LinearMap.BilinForm.toMatrix_comp bα b, hmat, Matrix.det_mul, Matrix.det_mul,
      Matrix.det_transpose, LinearMap.det_toMatrix, ContinuousLinearMap.det]
    ring
  rw [riemannianJacobian_eq_sqrt_det_gram]
  -- As in `riemannianJacobian_changeBasis`: `D` is the differential with its domain
  -- `TangentSpace 𝓘(ℝ, E) x` read as `E`, an identification Mathlib makes definitionally.
  change Real.sqrt (Matrix.gram ℝ (fun i ↦ D (b i))).det = _
  rw [hdet, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs, chartVolumeDensity_def]

variable [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
  [MeasurableSpace M] [BorelSpace M] [LindelofSpace M]

attribute [local instance] extChartAtMeasurableSpaceE extChartAtBorelSpaceE

private theorem setLIntegral_riemannianVolume_image_finBasis_of_subset_chart
    {f : E → M} {s : Set E} {α : M} (hs : MeasurableSet s)
    (himage : MeasurableSet (f '' s)) (hinj : InjOn f s)
    (hmap : MapsTo f s (chartAt H α).source)
    (hf : ∀ x ∈ s, MDifferentiableAt 𝓘(ℝ, E) I f x) (φ : M → ℝ≥0∞) :
    ∫⁻ y in f '' s, φ y ∂riemannianVolume I M =
      ∫⁻ x in s, ENNReal.ofReal
        (riemannianJacobian (I := I) (Module.finBasis ℝ E) f x) * φ (f x)
        ∂(Module.finBasis ℝ E).addHaar := by
  let g := extChartAt I α ∘ f
  let D := fun x ↦ (mfderiv I 𝓘(ℝ, E) (extChartAt I α) (f x) ∘L
    mfderiv 𝓘(ℝ, E) I f x : E →L[ℝ] E)
  have hg (x : E) (hx : x ∈ s) : HasFDerivAt g (D x) x := by
    have h := (hf x hx).hasMFDerivAt.hasFDerivAt_extChartAt_comp (hmap hx)
    rw [TangentBundle.continuousLinearMapAt_trivializationAt (hmap hx)] at h
    exact h
  have hinjg : InjOn g s := by
    intro x hx y hy hxy
    apply hinj hx hy
    apply (extChartAt I α).injOn
    · simpa only [extChartAt_source] using hmap hx
    · simpa only [extChartAt_source] using hmap hy
    · exact hxy
  have him : g '' s = extChartAt I α '' (f '' s) := by
    simp only [g, image_image, Function.comp_def]
  rw [setLIntegral_riemannianVolume_of_subset hmap.image_subset himage φ,
    ← him, lintegral_image_eq_lintegral_abs_det_fderiv_mul
      (Module.finBasis ℝ E).addHaar hs (fun x hx ↦ (hg x hx).hasFDerivWithinAt) hinjg]
  apply setLIntegral_congr_fun hs
  intro x hx
  have hx' : f x ∈ (extChartAt I α).source := by
    simpa only [extChartAt_source] using hmap hx
  simp only [g, Function.comp_apply, (extChartAt I α).left_inv hx']
  rw [riemannianJacobian_finBasis_eq_abs_det_mul_chartVolumeDensity (hmap hx),
    ENNReal.ofReal_mul (abs_nonneg _), mul_assoc]

private theorem setLIntegral_riemannianVolume_image_of_subset_chart_of_model
    (b : Module.Basis ι ℝ E)
    {f : E → M} {s : Set E} {α : M} (hs : MeasurableSet s)
    (himage : MeasurableSet (f '' s)) (hinj : InjOn f s)
    (hmap : MapsTo f s (chartAt H α).source)
    (hf : ∀ x ∈ s, MDifferentiableAt 𝓘(ℝ, E) I f x) (φ : M → ℝ≥0∞) :
    ∫⁻ y in f '' s, φ y ∂riemannianVolume I M =
      ∫⁻ x in s, ENNReal.ofReal (riemannianJacobian (I := I) b f x) * φ (f x) ∂b.addHaar := by
  rw [setLIntegral_riemannianVolume_image_finBasis_of_subset_chart hs himage hinj hmap hf φ]
  let e : ι ≃ Fin (Module.finrank ℝ E) :=
    Fintype.equivFinOfCardEq (Module.finrank_eq_card_basis b).symm
  simpa only [Module.Basis.addHaar_reindex, riemannianJacobian_reindex, Function.comp_apply] using
    setLIntegral_riemannianJacobian_changeBasis (Module.finBasis ℝ E) (b.reindex e) f s (φ ∘ f)

variable [MeasurableSpace F] [BorelSpace F]

/-- **Change of variables** for the Riemannian volume, for an injective differentiable map `f`
whose image lies in a preferred chart: the integral of `φ` over `f '' s` is the integral over `s`
of `φ ∘ f` weighted by the Riemannian Jacobian, against the Haar measure of the same basis. The
weight `φ` need not be measurable. -/
theorem setLIntegral_riemannianVolume_image_of_subset_chart
    (b : Module.Basis ι ℝ F) (hdim : Module.finrank ℝ F = Module.finrank ℝ E)
    {f : F → M} {s : Set F} {α : M} (hs : MeasurableSet s)
    (himage : MeasurableSet (f '' s)) (hinj : InjOn f s)
    (hmap : MapsTo f s (chartAt H α).source)
    (hf : ∀ x ∈ s, MDifferentiableAt 𝓘(ℝ, F) I f x) (φ : M → ℝ≥0∞) :
    ∫⁻ y in f '' s, φ y ∂riemannianVolume I M =
      ∫⁻ x in s, ENNReal.ofReal (riemannianJacobian (I := I) b f x) * φ (f x) ∂b.addHaar := by
  have : FiniteDimensional ℝ F := b.finiteDimensional_of_finite
  let A : E ≃L[ℝ] F := ContinuousLinearEquiv.ofFinrankEq hdim.symm
  let c := b.map A.symm.toLinearEquiv
  have hcb : c.map A.toLinearEquiv = b := by
    ext i
    simp [c, Module.Basis.map_apply]
  have hμ : Measure.map A c.addHaar = b.addHaar := by
    rw [Module.Basis.map_addHaar, hcb]
  have him : (f ∘ A) '' (A ⁻¹' s) = f '' s := by
    rw [image_comp, image_preimage_eq _ A.surjective]
  have hcov := setLIntegral_riemannianVolume_image_of_subset_chart_of_model c
    (hs.preimage A.continuous.measurable) (him ▸ himage)
    (hinj.comp A.injective.injOn (fun _ hx ↦ hx))
    (fun x hx ↦ hmap hx) (fun x hx ↦ (hf (A x) hx).comp x A.differentiableAt.mdifferentiableAt) φ
  rw [him] at hcov
  have hA : MeasurableEmbedding A := A.toHomeomorph.measurableEmbedding
  rw [hcov, ← hμ, hA.restrict_map, hA.lintegral_map]
  apply setLIntegral_congr_fun (hs.preimage A.continuous.measurable)
  intro x hx
  simp only [Function.comp_apply]
  rw [riemannianJacobian_comp_continuousLinearEquiv A c (hf _ hx), hcb]

/-- A `C¹` partial diffeomorphism `Φ` from `F` to `M` carries the Haar measure of `b` on its
source, weighted by the Riemannian Jacobian, to the Riemannian volume on its target. Neither a
single chart containing the target nor an orientation is needed. -/
theorem _root_.PartialDiffeomorph.map_withDensity_riemannianJacobian
    (Φ : PartialDiffeomorph 𝓘(ℝ, F) I F M 1) (b : Module.Basis ι ℝ F)
    (hdim : Module.finrank ℝ F = Module.finrank ℝ E) :
    Measure.map Φ ((b.addHaar.restrict Φ.source).withDensity
      (fun x ↦ ENNReal.ofReal (riemannianJacobian (I := I) b Φ x))) =
      (riemannianVolume I M).restrict Φ.target := by
  have : FiniteDimensional ℝ F := b.finiteDimensional_of_finite
  have hΦ : AEMeasurable Φ ((b.addHaar.restrict Φ.source).withDensity
      (fun x ↦ ENNReal.ofReal (riemannianJacobian (I := I) b Φ x))) :=
    (Φ.contMDiffOn_toFun.continuousOn.aemeasurable Φ.open_source.measurableSet).mono_ac
      (withDensity_absolutelyContinuous _ _)
  obtain ⟨t, ht, hcover⟩ := LindelofSpace.elim_nhds_subcover
    (fun x : M ↦ (chartAt H x).source) fun x ↦ chart_source_mem_nhds H x
  refine Measure.ext_of_biUnion_eq_univ ht hcover fun α _ ↦ Measure.ext fun s hs ↦ ?_
  have hT : MeasurableSet (s ∩ (chartAt H α).source) :=
    hs.inter (chartAt H α).open_source.measurableSet
  have hS : MeasurableSet (Φ ⁻¹' (s ∩ (chartAt H α).source) ∩ Φ.source) := by
    rw [inter_comm, ← Subtype.image_preimage_coe]
    exact (MeasurableEmbedding.subtype_coe Φ.open_source.measurableSet).measurableSet_image.mpr
      (Φ.contMDiffOn_toFun.continuousOn.domRestrict.measurable hT)
  have himage : Φ '' (Φ ⁻¹' (s ∩ (chartAt H α).source) ∩ Φ.source) =
      (s ∩ (chartAt H α).source) ∩ Φ.target := by
    rw [inter_comm, image_inter_preimage, Φ.toPartialEquiv.image_source_eq_target, inter_comm]
  have hcov := setLIntegral_riemannianVolume_image_of_subset_chart b hdim hS
    (himage ▸ hT.inter Φ.open_target.measurableSet)
    (Φ.toPartialEquiv.injOn.mono inter_subset_right) (fun x hx ↦ hx.1.2)
    (fun x hx ↦ (Φ.contMDiffOn_toFun.contMDiffAt (Φ.open_source.mem_nhds hx.2)).mdifferentiableAt
      one_ne_zero) (fun _ ↦ 1)
  simp only [lintegral_one, Measure.restrict_apply_univ, mul_one, himage] at hcov
  rw [Measure.restrict_apply hs, Measure.restrict_apply hs,
    Measure.restrict_apply hT, Measure.map_apply_of_aemeasurable hΦ hT,
    withDensity_apply', Measure.restrict_restrict' Φ.open_source.measurableSet]
  exact hcov.symm

/-- **Change of variables** over the target of a `C¹` partial diffeomorphism `Φ` from `F` to `M`:
the integral of a measurable `φ` over the target against the Riemannian volume is the integral of
`φ ∘ Φ` over the source, weighted by the Riemannian Jacobian, against the Haar measure of `b`. -/
theorem _root_.PartialDiffeomorph.setLIntegral_riemannianVolume_eq
    (Φ : PartialDiffeomorph 𝓘(ℝ, F) I F M 1) (b : Module.Basis ι ℝ F)
    (hdim : Module.finrank ℝ F = Module.finrank ℝ E) {φ : M → ℝ≥0∞} (hφ : Measurable φ) :
    ∫⁻ y in Φ.target, φ y ∂riemannianVolume I M =
      ∫⁻ x in Φ.source, ENNReal.ofReal (riemannianJacobian (I := I) b Φ x) * φ (Φ x)
        ∂b.addHaar := by
  have : FiniteDimensional ℝ F := b.finiteDimensional_of_finite
  have hρ : AEMeasurable (fun x ↦ ENNReal.ofReal (riemannianJacobian (I := I) b Φ x))
      (b.addHaar.restrict Φ.source) :=
    (ENNReal.continuous_ofReal.comp_continuousOn
      (continuousOn_riemannianJacobian b Φ.contMDiffOn_toFun Φ.open_source)).aemeasurable
      Φ.open_source.measurableSet
  have hΦ : AEMeasurable Φ ((b.addHaar.restrict Φ.source).withDensity
      (fun x ↦ ENNReal.ofReal (riemannianJacobian (I := I) b Φ x))) :=
    (Φ.contMDiffOn_toFun.continuousOn.aemeasurable Φ.open_source.measurableSet).mono_ac
      (withDensity_absolutelyContinuous _ _)
  rw [← Φ.map_withDensity_riemannianJacobian b hdim, lintegral_map' hφ.aemeasurable hΦ]
  simpa only [Function.comp_apply, Pi.mul_apply] using
    lintegral_withDensity_eq_lintegral_mul₀' hρ (hφ.comp_aemeasurable hΦ)

end Chart

end TauCeti

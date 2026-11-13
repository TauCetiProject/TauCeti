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
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Injective

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
The global formula holds for any measurable injective carrier, assuming differentiability at
every point of the carrier, and for arbitrary nonnegative weights. It applies to measurable
subdomains such as truncated strips even when the map is not injective on an open neighborhood.
It also identifies the pushforward of the Jacobian-weighted coordinate measure.

For maps that are `C¹` on an open neighborhood of the carrier, the Bochner formula and its
integrability equivalence allow weights in any real normed space. The integrand need not be
measurable or integrable for the integral equality. Specializations cover partial diffeomorphisms
and local diffeomorphisms injective on open domains, at any regularity `n ≥ 1`.

The space `F` and the model space of `M` may differ, provided they have the same dimension. No
orientation is used, and `M` may have boundary or corners.

## Main definitions

* `TauCeti.riemannianJacobian`: the Riemannian Jacobian of a map from a vector space with a basis.

## Main results

* `TauCeti.riemannianJacobian_unique`: for a basis consisting of a single vector, the Jacobian is
  the norm of the image of that vector under the differential.
* `TauCeti.riemannianJacobian_changeBasis`: a change of basis multiplies the Jacobian by the
  absolute value of its determinant.
* `TauCeti.riemannianJacobian_eq_normDet`: for an orthonormal basis, the Jacobian is the norm
  determinant of the differential.
* `TauCeti.setLIntegral_riemannianJacobian_changeBasis`: the Jacobian-weighted coordinate integral
  does not depend on the basis.
* `TauCeti.setLIntegral_riemannianVolume_image_of_subset_chart`: change of variables for an
  injective differentiable map whose image lies in a preferred chart.
* `Module.Basis.setLIntegral_riemannianVolume_image_of_injOn`: nonnegative change of variables
  on a measurable injective carrier, without measurability assumptions on the weight.
* `Module.Basis.map_withDensity_riemannianJacobian_of_injOn`: the corresponding pushforward
  measure identity.
* `Module.Basis.setIntegral_riemannianVolume_image_of_injOn` and
  `Module.Basis.integrableOn_riemannianVolume_image_iff_of_injOn`: Bochner change of variables
  and integrability on measurable injective carriers of maps that are `C¹` nearby.
* `PartialDiffeomorph.map_withDensity_riemannianJacobian` and
  `PartialDiffeomorph.setLIntegral_riemannianVolume_eq`: the measure and nonnegative integral
  specializations to partial diffeomorphisms.
* `PartialDiffeomorph.setIntegral_riemannianVolume_eq` and
  `PartialDiffeomorph.integrableOn_riemannianVolume_iff`: Bochner integral and integrability
  formulas for partial diffeomorphisms.
* `IsLocalDiffeomorphOn.setIntegral_riemannianVolume_image` and
  `IsLocalDiffeomorphOn.integrableOn_riemannianVolume_image_iff`: the corresponding formulas
  for local diffeomorphisms injective on open sets.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 2.
-/

open Bundle FiberBundle MeasureTheory Set Riemannian.Tensor
open scoped ENNReal InnerProductSpace Manifold ContDiff

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

/-- With respect to a basis consisting of a single vector, the Riemannian Jacobian is the norm of
the image of that vector under the differential. -/
theorem riemannianJacobian_unique [Unique ι] (b : Module.Basis ι ℝ F) (f : F → M) (x : F) :
    riemannianJacobian (I := I) b f x = ‖mfderiv 𝓘(ℝ, F) I f x (b default)‖ := by
  rw [riemannianJacobian_eq_sqrt_det_gram, Matrix.det_unique, Matrix.gram_apply]
  exact (norm_eq_sqrt_real_inner _).symm

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

/-- Change of variables for an injective map differentiable at every point of a measurable
carrier. The nonnegative weight need not be measurable, and the manifold need not be Hausdorff. -/
theorem _root_.Module.Basis.setLIntegral_riemannianVolume_image_of_injOn
    (b : Module.Basis ι ℝ F) (hdim : Module.finrank ℝ F = Module.finrank ℝ E)
    {f : F → M} {s : Set F} (hs : MeasurableSet s) (hinj : InjOn f s)
    (hf : ∀ x ∈ s, MDifferentiableAt 𝓘(ℝ, F) I f x) (φ : M → ℝ≥0∞) :
    ∫⁻ y in f '' s, φ y ∂riemannianVolume I M =
      ∫⁻ x in s, ENNReal.ofReal (riemannianJacobian (I := I) b f x) * φ (f x) ∂b.addHaar := by
  have : FiniteDimensional ℝ F := b.finiteDimensional_of_finite
  have hc : ContinuousOn f s := fun x hx ↦ (hf x hx).continuousAt.continuousWithinAt
  have he := I.measurableEmbedding_domRestrict_of_continuousOn_injOn hc hs hinj
  have himage {a : Set F} (ha : MeasurableSet a) (has : a ⊆ s) :
      MeasurableSet (f '' a) := by
    rw [← inter_eq_right.mpr has, ← Subtype.image_preimage_coe, ← image_comp]
    exact he.measurableSet_image.mpr (ha.preimage measurable_subtype_coe)
  -- Partition the target into disjoint measurable chart pieces and pull them back to the carrier.
  obtain ⟨t, ht, hcover⟩ := LindelofSpace.elim_nhds_subcover
    (fun x : M ↦ (chartAt H x).source) fun x ↦ chart_source_mem_nhds H x
  have htne : t.Nonempty := by
    obtain ⟨α, hα, _⟩ := mem_iUnion₂.mp (hcover.symm ▸ mem_univ (f 0))
    exact ⟨α, hα⟩
  obtain ⟨c, rfl⟩ := ht.exists_eq_range htne
  simp only [Set.biUnion_range] at hcover
  let d := disjointed (fun n ↦ (chartAt H (c n)).source)
  let a := fun n ↦ f ⁻¹' d n ∩ s
  have hd (n : ℕ) : MeasurableSet (d n) :=
    MeasurableSet.disjointed (fun n ↦ (chartAt H (c n)).open_source.measurableSet) n
  have ha (n : ℕ) : MeasurableSet (a n) := by
    dsimp only [a]
    rw [inter_comm, ← Subtype.image_preimage_coe]
    exact (MeasurableEmbedding.subtype_coe hs).measurableSet_image.mpr
      (hc.domRestrict.measurable (hd n))
  have has (n : ℕ) : a n ⊆ s := inter_subset_right
  have hmap (n : ℕ) : MapsTo f (a n) (chartAt H (c n)).source :=
    fun _ hx ↦ disjointed_subset (fun n ↦ (chartAt H (c n)).source) n hx.1
  have hdisj : Pairwise (fun i j ↦ Disjoint (a i) (a j)) := fun i j hij ↦
    ((disjoint_disjointed (fun n ↦ (chartAt H (c n)).source) hij).preimage f).mono
      inter_subset_left inter_subset_left
  have himdisj : Pairwise (fun i j ↦ Disjoint (f '' a i) (f '' a j)) := fun i j hij ↦
    (disjoint_disjointed (fun n ↦ (chartAt H (c n)).source) hij).mono
      (image_subset_iff.mpr fun _ hx ↦ hx.1) (image_subset_iff.mpr fun _ hx ↦ hx.1)
  have hUnion : ⋃ n, a n = s := by
    simp only [a, ← iUnion_inter, ← preimage_iUnion, d, iUnion_disjointed, hcover,
      preimage_univ, univ_inter]
  -- Sum the single-chart formula over the partition, allowing arbitrary nonnegative weights.
  calc
    _ = ∫⁻ y in ⋃ n, f '' a n, φ y ∂riemannianVolume I M := by
      rw [← image_iUnion, hUnion]
    _ = ∑' n, ∫⁻ y in f '' a n, φ y ∂riemannianVolume I M :=
      lintegral_iUnion (fun n ↦ himage (ha n) (has n)) himdisj φ
    _ = ∑' n, ∫⁻ x in a n,
        ENNReal.ofReal (riemannianJacobian (I := I) b f x) * φ (f x) ∂b.addHaar :=
      tsum_congr fun n ↦ setLIntegral_riemannianVolume_image_of_subset_chart b hdim (ha n)
        (himage (ha n) (has n)) (hinj.mono (has n)) (hmap n)
        (fun x hx ↦ hf x (has n hx)) φ
    _ = _ := by rw [← lintegral_iUnion ha hdisj, hUnion]

/-- An injective map differentiable at every point of a measurable carrier pushes its
Jacobian-weighted coordinate measure to Riemannian volume restricted to its image. -/
theorem _root_.Module.Basis.map_withDensity_riemannianJacobian_of_injOn
    (b : Module.Basis ι ℝ F) (hdim : Module.finrank ℝ F = Module.finrank ℝ E)
    {f : F → M} {s : Set F} (hs : MeasurableSet s) (hinj : InjOn f s)
    (hf : ∀ x ∈ s, MDifferentiableAt 𝓘(ℝ, F) I f x) :
    Measure.map f ((b.addHaar.restrict s).withDensity
      (fun x ↦ ENNReal.ofReal (riemannianJacobian (I := I) b f x))) =
      (riemannianVolume I M).restrict (f '' s) := by
  have hc : ContinuousOn f s := fun x hx ↦ (hf x hx).continuousAt.continuousWithinAt
  have hF := (hc.aemeasurable hs).mono_ac (withDensity_absolutelyContinuous
    (b.addHaar.restrict s) (fun x ↦ ENNReal.ofReal (riemannianJacobian (I := I) b f x)))
  ext A hA
  have hS : MeasurableSet (f ⁻¹' A ∩ s) := by
    rw [inter_comm, ← Subtype.image_preimage_coe]
    exact (MeasurableEmbedding.subtype_coe hs).measurableSet_image.mpr
      (hc.domRestrict.measurable hA)
  have hcov := b.setLIntegral_riemannianVolume_image_of_injOn hdim hS
    (hinj.mono inter_subset_right) (fun x hx ↦ hf x hx.2) (fun _ ↦ 1)
  simp only [image_preimage_inter, lintegral_one, Measure.restrict_apply_univ, mul_one] at hcov
  rw [Measure.restrict_apply hA, Measure.map_apply_of_aemeasurable hF hA,
    withDensity_apply', Measure.restrict_restrict' hs]
  exact hcov.symm

/-- A `C¹` partial diffeomorphism carries the Jacobian-weighted coordinate measure on its
source to Riemannian volume restricted to its target. -/
theorem _root_.PartialDiffeomorph.map_withDensity_riemannianJacobian
    (Φ : PartialDiffeomorph 𝓘(ℝ, F) I F M 1) (b : Module.Basis ι ℝ F)
    (hdim : Module.finrank ℝ F = Module.finrank ℝ E) :
    Measure.map Φ ((b.addHaar.restrict Φ.source).withDensity
      (fun x ↦ ENNReal.ofReal (riemannianJacobian (I := I) b Φ x))) =
      (riemannianVolume I M).restrict Φ.target := by
  simpa only [Φ.toPartialEquiv.image_source_eq_target] using
    b.map_withDensity_riemannianJacobian_of_injOn hdim Φ.open_source.measurableSet
      Φ.toPartialEquiv.injOn (fun x hx ↦
        (Φ.contMDiffOn_toFun.contMDiffAt (Φ.open_source.mem_nhds hx)).mdifferentiableAt one_ne_zero)

/-- Change of variables over the target of a `C¹` partial diffeomorphism, for arbitrary
nonnegative weights. -/
theorem _root_.PartialDiffeomorph.setLIntegral_riemannianVolume_eq
    (Φ : PartialDiffeomorph 𝓘(ℝ, F) I F M 1) (b : Module.Basis ι ℝ F)
    (hdim : Module.finrank ℝ F = Module.finrank ℝ E) (φ : M → ℝ≥0∞) :
    ∫⁻ y in Φ.target, φ y ∂riemannianVolume I M =
      ∫⁻ x in Φ.source, ENNReal.ofReal (riemannianJacobian (I := I) b Φ x) * φ (Φ x)
        ∂b.addHaar := by
  simpa only [Φ.toPartialEquiv.image_source_eq_target] using
    b.setLIntegral_riemannianVolume_image_of_injOn hdim Φ.open_source.measurableSet
      Φ.toPartialEquiv.injOn (fun x hx ↦
        (Φ.contMDiffOn_toFun.contMDiffAt (Φ.open_source.mem_nhds hx)).mdifferentiableAt one_ne_zero)
      φ

private theorem map_withDensity_riemannianJacobian_domRestrict
    (b : Module.Basis ι ℝ F) (hdim : Module.finrank ℝ F = Module.finrank ℝ E)
    {f : F → M} {s : Set F} (hs : MeasurableSet s) (hinj : InjOn f s)
    (hf : ∀ x ∈ s, MDifferentiableAt 𝓘(ℝ, F) I f x) :
    Measure.map (s.domRestrict f)
      ((b.addHaar.withDensity (fun x ↦ ENNReal.ofReal
        (riemannianJacobian (I := I) b f x))).comap (Subtype.val : s → F)) =
      (riemannianVolume I M).restrict (f '' s) := by
  have hc : ContinuousOn f s := fun x hx ↦ (hf x hx).continuousAt.continuousWithinAt
  rw [← b.map_withDensity_riemannianJacobian_of_injOn hdim hs hinj hf,
    ← restrict_withDensity hs, ← map_comap_subtype_coe hs,
    AEMeasurable.map_map_of_aemeasurable]
  · rw [Set.domRestrict_eq]
  · rw [map_comap_subtype_coe hs, restrict_withDensity hs]
    exact (hc.aemeasurable hs).mono_ac (withDensity_absolutelyContinuous _ _)
  · exact measurable_subtype_coe.aemeasurable

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Bochner change of variables on a measurable injective carrier for a map that is `C¹`
on an open neighborhood of the carrier. The integrand need not be measurable or integrable. -/
theorem _root_.Module.Basis.setIntegral_riemannianVolume_image_of_injOn
    (b : Module.Basis ι ℝ F) (hdim : Module.finrank ℝ F = Module.finrank ℝ E)
    {f : F → M} {s U : Set F} (hs : MeasurableSet s) (hU : IsOpen U) (hsub : s ⊆ U)
    (hf : ContMDiffOn 𝓘(ℝ, F) I 1 f U) (hinj : InjOn f s) (φ : M → G) :
    ∫ y in f '' s, φ y ∂riemannianVolume I M =
      ∫ x in s, riemannianJacobian (I := I) b f x • φ (f x) ∂b.addHaar := by
  have : FiniteDimensional ℝ F := b.finiteDimensional_of_finite
  have he := I.measurableEmbedding_domRestrict_of_continuousOn_injOn
    (hf.continuousOn.mono hsub) hs hinj
  have hdiff (x : F) (hx : x ∈ s) : MDifferentiableAt 𝓘(ℝ, F) I f x :=
    (hf.contMDiffAt (hU.mem_nhds (hsub hx))).mdifferentiableAt one_ne_zero
  have hρ : AEMeasurable (fun x ↦ ENNReal.ofReal (riemannianJacobian (I := I) b f x))
      (b.addHaar.restrict s) :=
    ((ENNReal.continuous_ofReal.comp_continuousOn
      (continuousOn_riemannianJacobian b hf hU)).mono hsub).aemeasurable hs
  rw [← map_withDensity_riemannianJacobian_domRestrict b hdim hs hinj hdiff,
    he.integral_map]
  simp only [Set.domRestrict_apply]
  rw [integral_subtype_comap hs (fun x ↦ φ (f x)),
    setIntegral_withDensity_eq_setIntegral_toReal_smul₀ hρ
      (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top) _ hs]
  simp only [ENNReal.toReal_ofReal (riemannianJacobian_nonneg b f _)]

/-- Integrability on an injective image of a measurable carrier is equivalent to integrability
of the Jacobian-weighted pullback, for a map that is `C¹` on an open neighborhood. -/
theorem _root_.Module.Basis.integrableOn_riemannianVolume_image_iff_of_injOn
    (b : Module.Basis ι ℝ F) (hdim : Module.finrank ℝ F = Module.finrank ℝ E)
    {f : F → M} {s U : Set F} (hs : MeasurableSet s) (hU : IsOpen U) (hsub : s ⊆ U)
    (hf : ContMDiffOn 𝓘(ℝ, F) I 1 f U) (hinj : InjOn f s) (φ : M → G) :
    IntegrableOn φ (f '' s) (riemannianVolume I M) ↔
      IntegrableOn (fun x ↦ riemannianJacobian (I := I) b f x • φ (f x)) s b.addHaar := by
  have : FiniteDimensional ℝ F := b.finiteDimensional_of_finite
  have he := I.measurableEmbedding_domRestrict_of_continuousOn_injOn
    (hf.continuousOn.mono hsub) hs hinj
  have hdiff (x : F) (hx : x ∈ s) : MDifferentiableAt 𝓘(ℝ, F) I f x :=
    (hf.contMDiffAt (hU.mem_nhds (hsub hx))).mdifferentiableAt one_ne_zero
  have hρ : AEMeasurable (fun x ↦ ENNReal.ofReal (riemannianJacobian (I := I) b f x))
      (b.addHaar.restrict s) :=
    ((ENNReal.continuous_ofReal.comp_continuousOn
      (continuousOn_riemannianJacobian b hf hU)).mono hsub).aemeasurable hs
  rw [IntegrableOn, ← map_withDensity_riemannianJacobian_domRestrict b hdim hs hinj hdiff,
    he.integrable_map_iff]
  rw [Set.domRestrict_eq, ← Function.comp_assoc,
    ← integrableOn_iff_comap_subtypeVal hs, IntegrableOn, restrict_withDensity hs,
    integrable_withDensity_iff_integrable_smul₀' hρ
      (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (riemannianJacobian_nonneg b f _), Function.comp_apply,
    IntegrableOn]

/-- Bochner change of variables over the target of a `C^n` partial diffeomorphism, for `n ≥ 1`.
No measurability or integrability assumption on the integrand is needed. -/
theorem _root_.PartialDiffeomorph.setIntegral_riemannianVolume_eq
    {n : ℕ∞ω} (Φ : PartialDiffeomorph 𝓘(ℝ, F) I F M n) (hn : 1 ≤ n)
    (b : Module.Basis ι ℝ F) (hdim : Module.finrank ℝ F = Module.finrank ℝ E) (φ : M → G) :
    ∫ y in Φ.target, φ y ∂riemannianVolume I M =
      ∫ x in Φ.source, riemannianJacobian (I := I) b Φ x • φ (Φ x) ∂b.addHaar := by
  simpa only [Φ.toPartialEquiv.image_source_eq_target] using
    b.setIntegral_riemannianVolume_image_of_injOn hdim Φ.open_source.measurableSet
      Φ.open_source Subset.rfl (Φ.contMDiffOn_toFun.of_le hn) Φ.toPartialEquiv.injOn φ

/-- Integrability on the target of a `C^n` partial diffeomorphism, for `n ≥ 1`, is equivalent
to integrability of the Jacobian-weighted pullback on its source. -/
theorem _root_.PartialDiffeomorph.integrableOn_riemannianVolume_iff
    {n : ℕ∞ω} (Φ : PartialDiffeomorph 𝓘(ℝ, F) I F M n) (hn : 1 ≤ n)
    (b : Module.Basis ι ℝ F) (hdim : Module.finrank ℝ F = Module.finrank ℝ E) (φ : M → G) :
    IntegrableOn φ Φ.target (riemannianVolume I M) ↔
      IntegrableOn (fun x ↦ riemannianJacobian (I := I) b Φ x • φ (Φ x)) Φ.source b.addHaar := by
  simpa only [Φ.toPartialEquiv.image_source_eq_target] using
    b.integrableOn_riemannianVolume_image_iff_of_injOn hdim Φ.open_source.measurableSet
      Φ.open_source Subset.rfl (Φ.contMDiffOn_toFun.of_le hn) Φ.toPartialEquiv.injOn φ

/-- Bochner change of variables for a `C^n` local diffeomorphism, `n ≥ 1`, injective on an
open set. The integrand need not be measurable or integrable. -/
theorem _root_.IsLocalDiffeomorphOn.setIntegral_riemannianVolume_image
    {n : ℕ∞ω} {g : F → M} {U : Set F} (hg : IsLocalDiffeomorphOn 𝓘(ℝ, F) I n g U)
    (hn : 1 ≤ n) (hU : IsOpen U) (hinj : InjOn g U) (b : Module.Basis ι ℝ F)
    (hdim : Module.finrank ℝ F = Module.finrank ℝ E) (φ : M → G) :
    ∫ y in g '' U, φ y ∂riemannianVolume I M =
      ∫ x in U, riemannianJacobian (I := I) b g x • φ (g x) ∂b.addHaar := by
  simpa only [IsLocalDiffeomorphOn.partialDiffeomorphOfInjOn_source,
    IsLocalDiffeomorphOn.partialDiffeomorphOfInjOn_target,
    IsLocalDiffeomorphOn.coe_partialDiffeomorphOfInjOn] using
    (hg.partialDiffeomorphOfInjOn hU hinj).setIntegral_riemannianVolume_eq hn b hdim φ

/-- Integrability over the image of an injective `C^n` local diffeomorphism, `n ≥ 1`, on an
open set is equivalent to integrability of its Jacobian-weighted pullback. -/
theorem _root_.IsLocalDiffeomorphOn.integrableOn_riemannianVolume_image_iff
    {n : ℕ∞ω} {g : F → M} {U : Set F} (hg : IsLocalDiffeomorphOn 𝓘(ℝ, F) I n g U)
    (hn : 1 ≤ n) (hU : IsOpen U) (hinj : InjOn g U) (b : Module.Basis ι ℝ F)
    (hdim : Module.finrank ℝ F = Module.finrank ℝ E) (φ : M → G) :
    IntegrableOn φ (g '' U) (riemannianVolume I M) ↔
      IntegrableOn (fun x ↦ riemannianJacobian (I := I) b g x • φ (g x)) U b.addHaar := by
  simpa only [IsLocalDiffeomorphOn.partialDiffeomorphOfInjOn_source,
    IsLocalDiffeomorphOn.partialDiffeomorphOfInjOn_target,
    IsLocalDiffeomorphOn.coe_partialDiffeomorphOfInjOn] using
    (hg.partialDiffeomorphOfInjOn hU hinj).integrableOn_riemannianVolume_iff hn b hdim φ

end Chart

end TauCeti

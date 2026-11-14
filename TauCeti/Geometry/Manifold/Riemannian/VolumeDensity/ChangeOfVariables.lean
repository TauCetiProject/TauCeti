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
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv
import TauCeti.Geometry.Manifold.ChartedSpace
import TauCeti.Geometry.Manifold.Polish
import TauCeti.MeasureTheory.Covering.DisjointCover

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

For maps differentiable at every point of the carrier, the Bochner formula and its
integrability equivalence allow weights in any real normed space. The integrand need not be
measurable or integrable for the integral equality. Specializations cover partial diffeomorphisms
and local diffeomorphisms injective on measurable carriers, at any regularity `n ≠ 0`.

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
* `Module.Basis.map_withDensity_riemannianJacobian_of_injOn` and
  `Module.Basis.restrict_map_withDensity_riemannianJacobian_of_injOn`: the corresponding
  pushforward identities for the map and its subtype restriction.
* `Module.Basis.aemeasurable_ofReal_riemannianJacobian`: almost everywhere measurability of the
  Jacobian weight on a carrier of pointwise differentiability.
* `Module.Basis.setIntegral_riemannianVolume_image_of_injOn` and
  `Module.Basis.integrableOn_riemannianVolume_image_iff_of_injOn`: Bochner change of variables
  and integrability on measurable injective carriers of pointwise differentiable maps.
* `PartialDiffeomorph.map_withDensity_riemannianJacobian` and
  `PartialDiffeomorph.setLIntegral_riemannianVolume_eq`: the measure and nonnegative integral
  specializations to partial diffeomorphisms.
* `PartialDiffeomorph.setIntegral_riemannianVolume_eq` and
  `PartialDiffeomorph.integrableOn_riemannianVolume_iff`: Bochner integral and integrability
  formulas for partial diffeomorphisms.
* `IsLocalDiffeomorphOn.map_withDensity_riemannianJacobian`,
  `IsLocalDiffeomorphOn.setLIntegral_riemannianVolume_image`,
  `IsLocalDiffeomorphOn.setIntegral_riemannianVolume_image` and
  `IsLocalDiffeomorphOn.integrableOn_riemannianVolume_image_iff`: the corresponding formulas
  for local diffeomorphisms injective on measurable sets.

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

omit [MeasurableSpace M] [BorelSpace M] [LindelofSpace M] in
private theorem aemeasurable_ofReal_riemannianJacobian_of_model
    (b : Module.Basis ι ℝ E) {f : E → M} {s : Set E} (hs : MeasurableSet s)
    (hf : ∀ x ∈ s, MDifferentiableAt 𝓘(ℝ, E) I f x) :
    AEMeasurable (fun x ↦ ENNReal.ofReal (riemannianJacobian (I := I) b f x))
      (b.addHaar.restrict s) := by
  have hc : ContinuousOn f s := fun x hx ↦ (hf x hx).continuousAt.continuousWithinAt
  have : IsManifold I (0 + 1) M := by
    simpa using (inferInstance : IsManifold I 1 M)
  have : IsContMDiffRiemannianBundle I 0 E (fun x : M ↦ TangentSpace I x) :=
    IsContinuousRiemannianBundle.toIsContMDiffZero
  obtain ⟨t, ht, -, hcover⟩ :=
    ((HereditarilyLindelofSpace.isLindelof s).image_of_continuousOn hc).elim_nhds_subcover
      (fun x : M ↦ (chartAt H x).source) fun x _ ↦ chart_source_mem_nhds H x
  have : Countable t := ht.to_subtype
  let a := fun α : t ↦ f ⁻¹' (chartAt H α.val).source ∩ s
  have ha (α : t) : MeasurableSet (a α) := by
    dsimp only [a]
    rw [inter_comm, ← Subtype.image_preimage_coe]
    exact (MeasurableEmbedding.subtype_coe hs).measurableSet_image.mpr
      ((chartAt H α.val).open_source.preimage hc.domRestrict).measurableSet
  have hUnion : ⋃ α, a α = s := by
    apply Subset.antisymm (iUnion_subset fun _ ↦ inter_subset_right)
    intro x hx
    obtain ⟨α, hα, hxα⟩ := mem_iUnion₂.mp (hcover (mem_image_of_mem f hx))
    exact mem_iUnion.mpr ⟨⟨α, hα⟩, hxα, hx⟩
  -- On each chart piece, the coordinate derivative is a.e. measurable and the metric is continuous.
  have hfin : AEMeasurable (fun x ↦ ENNReal.ofReal
      (riemannianJacobian (I := I) (Module.finBasis ℝ E) f x)) (b.addHaar.restrict s) := by
    rw [← hUnion]
    apply AEMeasurable.iUnion
    intro α
    let D := fun x ↦ (mfderiv I 𝓘(ℝ, E) (extChartAt I α.val) (f x) ∘L
      mfderiv 𝓘(ℝ, E) I f x : E →L[ℝ] E)
    have hD : ∀ x ∈ a α, HasFDerivWithinAt (extChartAt I α.val ∘ f) (D x) (a α) x := by
      intro x hx
      have h := (hf x hx.2).hasMFDerivAt.hasFDerivAt_extChartAt_comp hx.1
      rw [TangentBundle.continuousLinearMapAt_trivializationAt hx.1] at h
      exact h.hasFDerivWithinAt
    have hdensity : ContinuousOn
        (fun x ↦ ENNReal.ofReal (chartVolumeDensity (I := I) α.val (f x))) (a α) := by
      apply ENNReal.continuous_ofReal.comp_continuousOn
      apply (contMDiffOn_chartVolumeDensity (I := I) (n := 0) α.val).continuousOn.comp
        (hc.mono inter_subset_right)
      intro x hx
      rw [TangentBundle.trivializationAt_baseSet]
      exact hx.1
    apply ((aemeasurable_ofReal_abs_det_fderivWithin b.addHaar (ha α) hD).mul
      (hdensity.aemeasurable (ha α))).congr
    filter_upwards [ae_restrict_mem (ha α)] with x hx
    rw [riemannianJacobian_finBasis_eq_abs_det_mul_chartVolumeDensity hx.1,
      ENNReal.ofReal_mul (abs_nonneg _)]
    rfl
  -- Transfer the weight from the coordinate basis to the chosen basis.
  let e : ι ≃ Fin (Module.finrank ℝ E) :=
    Fintype.equivFinOfCardEq (Module.finrank_eq_card_basis b).symm
  apply (aemeasurable_const.mul hfin : AEMeasurable
      (fun x ↦ ENNReal.ofReal |(Module.finBasis ℝ E).det (b.reindex e)| *
        ENNReal.ofReal (riemannianJacobian (I := I) (Module.finBasis ℝ E) f x))
      (b.addHaar.restrict s)).congr
  exact Filter.Eventually.of_forall fun x ↦ by
    simp only [Pi.mul_apply]
    rw [← ENNReal.ofReal_mul (abs_nonneg _),
      ← riemannianJacobian_changeBasis, riemannianJacobian_reindex]

omit [MeasurableSpace M] [BorelSpace M] [LindelofSpace M] in
/-- The Jacobian weight is almost everywhere measurable on a measurable carrier on which the
map is differentiable at every point, when the source and target model have equal dimension. -/
theorem _root_.Module.Basis.aemeasurable_ofReal_riemannianJacobian
    (b : Module.Basis ι ℝ F) (hdim : Module.finrank ℝ F = Module.finrank ℝ E)
    {f : F → M} {s : Set F} (hs : MeasurableSet s)
    (hf : ∀ x ∈ s, MDifferentiableAt 𝓘(ℝ, F) I f x) :
    AEMeasurable (fun x ↦ ENNReal.ofReal (riemannianJacobian (I := I) b f x))
      (b.addHaar.restrict s) := by
  have : FiniteDimensional ℝ F := b.finiteDimensional_of_finite
  let A : E ≃L[ℝ] F := ContinuousLinearEquiv.ofFinrankEq hdim.symm
  let c := b.map A.symm.toLinearEquiv
  have hcb : c.map A.toLinearEquiv = b := by
    ext i
    simp [c, Module.Basis.map_apply]
  have hμ : Measure.map A c.addHaar = b.addHaar := by
    rw [Module.Basis.map_addHaar, hcb]
  have hA : MeasurableEmbedding A := A.toHomeomorph.measurableEmbedding
  rw [← hμ, hA.restrict_map, hA.aemeasurable_map_iff]
  apply (aemeasurable_ofReal_riemannianJacobian_of_model c
    (hs.preimage A.continuous.measurable)
    (fun x hx ↦ (hf (A x) hx).comp x A.differentiableAt.mdifferentiableAt)).congr
  filter_upwards [ae_restrict_mem (hs.preimage A.continuous.measurable)] with x hx
  simp only [Function.comp_apply,
    riemannianJacobian_comp_continuousLinearEquiv A c (hf _ hx), hcb]

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
  have : T2Space H := I.isClosedEmbedding.isEmbedding.t2Space
  have he := hc.measurableEmbedding_chartedSpace F H hs hinj
  have himage {a : Set F} (ha : MeasurableSet a) (has : a ⊆ s) :
      MeasurableSet (f '' a) := by
    rw [← inter_eq_right.mpr has, ← Subtype.image_preimage_coe, ← image_comp]
    exact he.measurableSet_image.mpr (ha.preimage measurable_subtype_coe)
  -- Partition the target into disjoint measurable chart pieces and pull them back to the carrier.
  have := I.secondCountableTopology
  have := ChartedSpace.secondCountable_of_lindelof H M
  obtain ⟨d, hd, hddisj, hcover, hsub⟩ :=
    exists_disjoint_measurableSet_cover_of_mem_nhds (S := univ) ⟨f 0, mem_univ _⟩
      (fun x : M ↦ (chartAt H x).source) (fun x _ ↦ chart_source_mem_nhds H x)
      (fun x _ ↦ (chartAt H x).open_source.measurableSet)
  choose c _ hcsub using hsub
  let a := fun n ↦ f ⁻¹' d n ∩ s
  have ha (n : ℕ) : MeasurableSet (a n) := by
    dsimp only [a]
    rw [inter_comm, ← Subtype.image_preimage_coe]
    exact (MeasurableEmbedding.subtype_coe hs).measurableSet_image.mpr
      (hc.domRestrict.measurable (hd n))
  have has (n : ℕ) : a n ⊆ s := inter_subset_right
  have hmap (n : ℕ) : MapsTo f (a n) (chartAt H (c n)).source :=
    fun _ hx ↦ hcsub n hx.1
  have hdisj : Pairwise (fun i j ↦ Disjoint (a i) (a j)) := fun i j hij ↦
    ((hddisj hij).preimage f).mono
      inter_subset_left inter_subset_left
  have himdisj : Pairwise (fun i j ↦ Disjoint (f '' a i) (f '' a j)) := fun i j hij ↦
    (hddisj hij).mono
      (image_subset_iff.mpr fun _ hx ↦ hx.1) (image_subset_iff.mpr fun _ hx ↦ hx.1)
  have hUnion : ⋃ n, a n = s := by
    have hcover' : ⋃ n, d n = univ := eq_univ_of_univ_subset hcover
    simp only [a, ← iUnion_inter, ← preimage_iUnion, hcover', preimage_univ, univ_inter]
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

/-- The subtype restriction of an injective differentiable map pushes the Jacobian-weighted
coordinate measure to Riemannian volume on its image. -/
theorem _root_.Module.Basis.restrict_map_withDensity_riemannianJacobian_of_injOn
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

/-- Bochner change of variables on a measurable injective carrier for a map differentiable
at every point of the carrier. The integrand need not be measurable or integrable. -/
theorem _root_.Module.Basis.setIntegral_riemannianVolume_image_of_injOn
    (b : Module.Basis ι ℝ F) (hdim : Module.finrank ℝ F = Module.finrank ℝ E)
    {f : F → M} {s : Set F} (hs : MeasurableSet s) (hinj : InjOn f s)
    (hf : ∀ x ∈ s, MDifferentiableAt 𝓘(ℝ, F) I f x) (φ : M → G) :
    ∫ y in f '' s, φ y ∂riemannianVolume I M =
      ∫ x in s, riemannianJacobian (I := I) b f x • φ (f x) ∂b.addHaar := by
  have : FiniteDimensional ℝ F := b.finiteDimensional_of_finite
  have : T2Space H := I.isClosedEmbedding.isEmbedding.t2Space
  have hc : ContinuousOn f s := fun x hx ↦ (hf x hx).continuousAt.continuousWithinAt
  have he := hc.measurableEmbedding_chartedSpace F H hs hinj
  have hρ := b.aemeasurable_ofReal_riemannianJacobian hdim hs hf
  rw [← b.restrict_map_withDensity_riemannianJacobian_of_injOn hdim hs hinj hf,
    he.integral_map]
  simp only [Set.domRestrict_apply]
  rw [integral_subtype_comap hs (fun x ↦ φ (f x)),
    setIntegral_withDensity_eq_setIntegral_toReal_smul₀ hρ
      (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top) _ hs]
  simp only [ENNReal.toReal_ofReal (riemannianJacobian_nonneg b f _)]

/-- Integrability on an injective image of a measurable carrier is equivalent to integrability
of the Jacobian-weighted pullback, for a map differentiable at every point of the carrier. -/
theorem _root_.Module.Basis.integrableOn_riemannianVolume_image_iff_of_injOn
    (b : Module.Basis ι ℝ F) (hdim : Module.finrank ℝ F = Module.finrank ℝ E)
    {f : F → M} {s : Set F} (hs : MeasurableSet s) (hinj : InjOn f s)
    (hf : ∀ x ∈ s, MDifferentiableAt 𝓘(ℝ, F) I f x) (φ : M → G) :
    IntegrableOn φ (f '' s) (riemannianVolume I M) ↔
      IntegrableOn (fun x ↦ riemannianJacobian (I := I) b f x • φ (f x)) s b.addHaar := by
  have : FiniteDimensional ℝ F := b.finiteDimensional_of_finite
  have : T2Space H := I.isClosedEmbedding.isEmbedding.t2Space
  have hc : ContinuousOn f s := fun x hx ↦ (hf x hx).continuousAt.continuousWithinAt
  have he := hc.measurableEmbedding_chartedSpace F H hs hinj
  have hρ := b.aemeasurable_ofReal_riemannianJacobian hdim hs hf
  rw [IntegrableOn, ← b.restrict_map_withDensity_riemannianJacobian_of_injOn hdim hs hinj hf,
    he.integrable_map_iff]
  rw [Set.domRestrict_eq, ← Function.comp_assoc,
    ← integrableOn_iff_comap_subtypeVal hs, IntegrableOn, restrict_withDensity hs,
    integrable_withDensity_iff_integrable_smul₀' hρ
      (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (riemannianJacobian_nonneg b f _), Function.comp_apply,
    IntegrableOn]

/-- An injective local diffeomorphism on a measurable carrier pushes its Jacobian-weighted
coordinate measure to Riemannian volume on its image. -/
theorem _root_.IsLocalDiffeomorphOn.map_withDensity_riemannianJacobian
    {n : ℕ∞ω} {g : F → M} {s : Set F} (hg : IsLocalDiffeomorphOn 𝓘(ℝ, F) I n g s)
    (hn : n ≠ 0) (hs : MeasurableSet s) (hinj : InjOn g s) (b : Module.Basis ι ℝ F) :
    Measure.map g ((b.addHaar.restrict s).withDensity
      (fun x ↦ ENNReal.ofReal (riemannianJacobian (I := I) b g x))) =
      (riemannianVolume I M).restrict (g '' s) := by
  obtain rfl | ⟨x, hx⟩ := s.eq_empty_or_nonempty
  · simp
  have hdim := (hg ⟨x, hx⟩).finrank_eq hn
  exact b.map_withDensity_riemannianJacobian_of_injOn hdim hs hinj
    (fun x hx ↦ (hg ⟨x, hx⟩).mdifferentiableAt hn)

/-- Nonnegative change of variables for an injective local diffeomorphism on a measurable
carrier. The weight need not be measurable. -/
theorem _root_.IsLocalDiffeomorphOn.setLIntegral_riemannianVolume_image
    {n : ℕ∞ω} {g : F → M} {s : Set F} (hg : IsLocalDiffeomorphOn 𝓘(ℝ, F) I n g s)
    (hn : n ≠ 0) (hs : MeasurableSet s) (hinj : InjOn g s) (b : Module.Basis ι ℝ F)
    (φ : M → ℝ≥0∞) :
    ∫⁻ y in g '' s, φ y ∂riemannianVolume I M =
      ∫⁻ x in s, ENNReal.ofReal (riemannianJacobian (I := I) b g x) * φ (g x) ∂b.addHaar := by
  obtain rfl | ⟨x, hx⟩ := s.eq_empty_or_nonempty
  · simp
  have hdim := (hg ⟨x, hx⟩).finrank_eq hn
  exact b.setLIntegral_riemannianVolume_image_of_injOn hdim hs hinj
    (fun x hx ↦ (hg ⟨x, hx⟩).mdifferentiableAt hn) φ

/-- Bochner change of variables for an injective local diffeomorphism on a measurable carrier.
The integrand need not be measurable or integrable. -/
theorem _root_.IsLocalDiffeomorphOn.setIntegral_riemannianVolume_image
    {n : ℕ∞ω} {g : F → M} {s : Set F} (hg : IsLocalDiffeomorphOn 𝓘(ℝ, F) I n g s)
    (hn : n ≠ 0) (hs : MeasurableSet s) (hinj : InjOn g s) (b : Module.Basis ι ℝ F)
    (φ : M → G) :
    ∫ y in g '' s, φ y ∂riemannianVolume I M =
      ∫ x in s, riemannianJacobian (I := I) b g x • φ (g x) ∂b.addHaar := by
  obtain rfl | ⟨x, hx⟩ := s.eq_empty_or_nonempty
  · simp
  have hdim := (hg ⟨x, hx⟩).finrank_eq hn
  exact b.setIntegral_riemannianVolume_image_of_injOn hdim hs hinj
    (fun x hx ↦ (hg ⟨x, hx⟩).mdifferentiableAt hn) φ

/-- Integrability over the image of an injective local diffeomorphism on a measurable carrier
is equivalent to integrability of its Jacobian-weighted pullback. -/
theorem _root_.IsLocalDiffeomorphOn.integrableOn_riemannianVolume_image_iff
    {n : ℕ∞ω} {g : F → M} {s : Set F} (hg : IsLocalDiffeomorphOn 𝓘(ℝ, F) I n g s)
    (hn : n ≠ 0) (hs : MeasurableSet s) (hinj : InjOn g s) (b : Module.Basis ι ℝ F)
    (φ : M → G) :
    IntegrableOn φ (g '' s) (riemannianVolume I M) ↔
      IntegrableOn (fun x ↦ riemannianJacobian (I := I) b g x • φ (g x)) s b.addHaar := by
  obtain rfl | ⟨x, hx⟩ := s.eq_empty_or_nonempty
  · simp
  have hdim := (hg ⟨x, hx⟩).finrank_eq hn
  exact b.integrableOn_riemannianVolume_image_iff_of_injOn hdim hs hinj
    (fun x hx ↦ (hg ⟨x, hx⟩).mdifferentiableAt hn) φ

/-- A `C^n` partial diffeomorphism, with `n ≠ 0`, carries the Jacobian-weighted coordinate measure
on its source to Riemannian volume restricted to its target. -/
theorem _root_.PartialDiffeomorph.map_withDensity_riemannianJacobian
    {n : ℕ∞ω} (Φ : PartialDiffeomorph 𝓘(ℝ, F) I F M n) (hn : n ≠ 0)
    (b : Module.Basis ι ℝ F) :
    Measure.map Φ ((b.addHaar.restrict Φ.source).withDensity
      (fun x ↦ ENNReal.ofReal (riemannianJacobian (I := I) b Φ x))) =
      (riemannianVolume I M).restrict Φ.target := by
  simpa only [Φ.toPartialEquiv.image_source_eq_target] using
    IsLocalDiffeomorphOn.map_withDensity_riemannianJacobian
      (fun x ↦ Φ.isLocalDiffeomorphAt 𝓘(ℝ, F) I n x.2) hn Φ.open_source.measurableSet
      Φ.toPartialEquiv.injOn b

/-- Change of variables over the target of a `C^n` partial diffeomorphism, with `n ≠ 0`, for
arbitrary nonnegative weights. -/
theorem _root_.PartialDiffeomorph.setLIntegral_riemannianVolume_eq
    {n : ℕ∞ω} (Φ : PartialDiffeomorph 𝓘(ℝ, F) I F M n) (hn : n ≠ 0)
    (b : Module.Basis ι ℝ F) (φ : M → ℝ≥0∞) :
    ∫⁻ y in Φ.target, φ y ∂riemannianVolume I M =
      ∫⁻ x in Φ.source, ENNReal.ofReal (riemannianJacobian (I := I) b Φ x) * φ (Φ x)
        ∂b.addHaar := by
  simpa only [Φ.toPartialEquiv.image_source_eq_target] using
    IsLocalDiffeomorphOn.setLIntegral_riemannianVolume_image
      (fun x ↦ Φ.isLocalDiffeomorphAt 𝓘(ℝ, F) I n x.2) hn Φ.open_source.measurableSet
      Φ.toPartialEquiv.injOn b φ

/-- Bochner change of variables over the target of a `C^n` partial diffeomorphism, for `n ≠ 0`.
No measurability or integrability assumption on the integrand is needed. -/
theorem _root_.PartialDiffeomorph.setIntegral_riemannianVolume_eq
    {n : ℕ∞ω} (Φ : PartialDiffeomorph 𝓘(ℝ, F) I F M n) (hn : n ≠ 0)
    (b : Module.Basis ι ℝ F) (φ : M → G) :
    ∫ y in Φ.target, φ y ∂riemannianVolume I M =
      ∫ x in Φ.source, riemannianJacobian (I := I) b Φ x • φ (Φ x) ∂b.addHaar := by
  simpa only [Φ.toPartialEquiv.image_source_eq_target] using
    IsLocalDiffeomorphOn.setIntegral_riemannianVolume_image
      (fun x ↦ Φ.isLocalDiffeomorphAt 𝓘(ℝ, F) I n x.2) hn Φ.open_source.measurableSet
      Φ.toPartialEquiv.injOn b φ

/-- Integrability on the target of a `C^n` partial diffeomorphism, for `n ≠ 0`, is equivalent
to integrability of the Jacobian-weighted pullback on its source. -/
theorem _root_.PartialDiffeomorph.integrableOn_riemannianVolume_iff
    {n : ℕ∞ω} (Φ : PartialDiffeomorph 𝓘(ℝ, F) I F M n) (hn : n ≠ 0)
    (b : Module.Basis ι ℝ F) (φ : M → G) :
    IntegrableOn φ Φ.target (riemannianVolume I M) ↔
      IntegrableOn (fun x ↦ riemannianJacobian (I := I) b Φ x • φ (Φ x)) Φ.source b.addHaar := by
  simpa only [Φ.toPartialEquiv.image_source_eq_target] using
    IsLocalDiffeomorphOn.integrableOn_riemannianVolume_image_iff
      (fun x ↦ Φ.isLocalDiffeomorphAt 𝓘(ℝ, F) I n x.2) hn Φ.open_source.measurableSet
      Φ.toPartialEquiv.injOn b φ

end Chart

end TauCeti

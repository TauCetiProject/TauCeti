/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
public import TauCeti.Analysis.Complex.UpperHalfPlane.Geodesic
public import TauCeti.Analysis.Complex.UpperHalfPlane.SmulDeriv
public import TauCeti.Geometry.Manifold.Riemannian.Distance
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Action
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Distance
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Volume
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Conformal
import Mathlib.Analysis.Complex.UpperHalfPlane.FixedPoints
import TauCeti.Analysis.Complex.UpperHalfPlane.Manifold
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic
import TauCeti.Geometry.Manifold.Riemannian.PathELength
import TauCeti.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# The Poincaré Riemannian metric, its isometries, and its distance

The canonical tensor on the upper half-plane is the Euclidean inner product divided by the
square of the imaginary coordinate. We construct it as a smooth real Riemannian metric, the
Euclidean metric rescaled by `im⁻²` through `Bundle.ContMDiffRiemannianMetric.rescale`, and
install it as the Riemannian structure of the tangent bundle of `ℍ`.

Its Riemannian volume is Mathlib's invariant measure `volume : Measure ℍ`, whose density is
`y⁻² dx dy`. In the inclusion chart the Gram matrix of the Poincaré tensor is `y⁻²` times the
Euclidean Gram matrix, so the Riemannian volume density is `y⁻²` against Lebesgue measure on `ℂ`.
Thus the hyperbolic areas computed with `volume`, such as covolumes of Fuchsian groups and the
Gauss–Bonnet formula, are areas for the Poincaré metric.

Every element of `GL(2, ℝ)` acts smoothly on `ℍ` as a real manifold — orientation-preserving
elements holomorphically and negative-determinant elements through the reflection
`UpperHalfPlane.J : z ↦ -conj z` — and preserves the Poincaré inner product on tangent spaces.
This yields group homomorphisms from `GL(2, ℝ)`, `PGL(2, ℝ)`, `SL(2, R)`, and `PSL(2, R)` to the
Riemannian isometry group `TauCeti.Isom 𝓘(ℝ, ℂ) ℍ`.

Finally, the Riemannian extended distance of the Poincaré metric coincides with Mathlib's
hyperbolic distance on `ℍ` (`instIsRiemannianManifold`): each geodesic line `geodesicLine g` has
unit Poincaré speed and hence arc length `b - a` on `[a, b]`, the horocycle height projection
`z ↦ log (Im z)` is distance-nonincreasing, and `PSL(2, ℝ)` carries every pair of points to the
upward imaginary axis. Since `ℍ` is proper in Mathlib's metric, its Poincaré Riemannian metric is
complete (`completeSpace_of_riemannianMetric`).

## Main definitions

* `TauCeti.UpperHalfPlane.poincareRiemannianMetric`: the Poincaré metric, with tangent-coordinate
  formulas `UpperHalfPlane.poincareRiemannianMetric_inner`, `inner_def`, `norm_def`, and
  `eNorm_def`.
* `TauCeti.UpperHalfPlane.glToIsom`, `TauCeti.UpperHalfPlane.pglToIsom`,
  `TauCeti.UpperHalfPlane.slToIsom`, `TauCeti.UpperHalfPlane.pslToIsom`: the group homomorphisms
  into `TauCeti.Isom 𝓘(ℝ, ℂ) ℍ`.

## Main results

* `UpperHalfPlane.riemannianVolume_eq_volume`: the Riemannian volume of the Poincaré metric is
  Mathlib's invariant measure `volume`.
* `TauCeti.UpperHalfPlane.tangentSpaceCastModel_mfderiv_smul` and
  `TauCeti.UpperHalfPlane.inner_mfderiv_gl_smul`: the differential of `g • ·` in model
  coordinates is `UpperHalfPlane.smulFDeriv g z` and preserves the Poincaré inner product.
* `TauCeti.UpperHalfPlane.pathELength_geodesicLine`: every geodesic line has Poincaré path length
  `ENNReal.ofReal (b - a)` on `[a, b]`.
* `TauCeti.UpperHalfPlane.riemannianEDist_eq_edist` and
  `TauCeti.UpperHalfPlane.instIsRiemannianManifold`: Mathlib's hyperbolic distance on `ℍ` is the
  Riemannian distance of `poincareRiemannianMetric`.
* `TauCeti.UpperHalfPlane.completeSpace_of_riemannianMetric`: the Poincaré Riemannian metric is
  complete.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 3.
* S. Katok, *Fuchsian Groups*, University of Chicago Press (1992), §§1.1–1.2.
* A. F. Beardon, *The Geometry of Discrete Groups*, Springer GTM 91 (1983), §7.2.
-/

public section

open Bundle FiberBundle Manifold MeasureTheory Riemannian.Tensor Set Topology
open scoped ComplexConjugate ContDiff ENNReal Manifold MatrixGroups NNReal UpperHalfPlane

noncomputable section

namespace TauCeti.UpperHalfPlane

/-- The singleton complex chart also gives the upper half-plane its smooth real manifold
structure. -/
instance instIsManifoldReal : IsManifold 𝓘(ℝ, ℂ) ω ℍ :=
  _root_.UpperHalfPlane.isOpenEmbedding_coe.isManifold_singleton

private theorem poincare_symmL (α z : ℍ) (v : ℂ) :
    (trivializationAt ℂ (TangentSpace 𝓘(ℝ, ℂ) : ℍ → Type) α).symmL ℝ z v =
      (tangentSpaceCastModel 𝓘(ℝ, ℂ) z).symm v := by
  rw [TangentBundle.symmL_trivializationAt_eq_core (by simp)]
  -- The singleton atlas makes this change of coordinates a self transition.
  exact tangentCoordChange_self (x := z) (I := 𝓘(ℝ, ℂ)) (by simp)

private theorem poincare_symm (α z : ℍ) (v : ℂ) :
    (trivializationAt ℂ (TangentSpace 𝓘(ℝ, ℂ) : ℍ → Type) α).symm z v =
      (tangentSpaceCastModel 𝓘(ℝ, ℂ) z).symm v := by
  simpa only [Trivialization.symmL_apply (R := ℝ)
    (trivializationAt ℂ (TangentSpace 𝓘(ℝ, ℂ) : ℍ → Type) α) (by simp)] using
    poincare_symmL α z v

/-- The flat metric on the upper half-plane: the Euclidean tensor of `ℂ`, read through the
inclusion chart. -/
private def euclideanMetric :
    ContMDiffRiemannianMetric 𝓘(ℝ, ℂ) ∞ ℂ
      (fun z : ℍ ↦ TangentSpace 𝓘(ℝ, ℂ) z) where
  inner z := by
    -- Defining a foundational tangent metric uses the explicit identification with its model.
    let e := tangentSpaceCastModel 𝓘(ℝ, ℂ) z
    exact (e.symm.arrowCongr (e.symm.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ)))
      (innerSL ℝ (E := ℂ))
  symm z v w := by
    simp only [ContinuousLinearEquiv.arrowCongr_apply, ContinuousLinearEquiv.symm_symm,
      ContinuousLinearEquiv.refl_apply]
    exact real_inner_comm (tangentSpaceCastModel 𝓘(ℝ, ℂ) z v)
      (tangentSpaceCastModel 𝓘(ℝ, ℂ) z w) |>.symm
  pos z v hv := by
    simp only [ContinuousLinearEquiv.arrowCongr_apply, ContinuousLinearEquiv.symm_symm,
      ContinuousLinearEquiv.refl_apply]
    exact real_inner_self_pos.mpr ((tangentSpaceCastModel 𝓘(ℝ, ℂ) z).map_ne_zero_iff.mpr hv)
  isVonNBounded z := by
    let e := tangentSpaceCastModel 𝓘(ℝ, ℂ) z
    have hb := (NormedSpace.isVonNBounded_ball ℝ ℂ 1).image e.symm.toContinuousLinearMap
    apply Bornology.IsVonNBounded.subset (s₂ := e.symm '' Metric.ball (0 : ℂ) 1) ?_ hb
    intro v hv
    refine ⟨e v, ?_, e.symm_apply_apply v⟩
    rw [Metric.mem_ball, dist_zero_right]
    dsimp at hv
    erw [innerSL_apply_apply, real_inner_self_eq_norm_sq] at hv
    nlinarith [norm_nonneg (e v)]
  contMDiff := by
    intro α
    rw [contMDiffAt_section_iff]
    let euclidean : ℂ →L[ℝ] ℂ →L[ℝ] ℝ := innerSL ℝ
    have hconst : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ →L[ℝ] ℂ →L[ℝ] ℝ) ∞
        (fun _ : ℍ ↦ euclidean) α :=
      contMDiffAt_const
    convert hconst using 1
    ext z v w
    simp only [hom_trivializationAt_apply]
    rw [inCoordinates_apply_eq₂ (by simp) (by simp) (by simp)]
    simp [Trivial.fiberBundle_trivializationAt', Trivial.linearMapAt_trivialization,
      poincare_symm, euclidean, ContinuousLinearEquiv.arrowCongr_apply]

private theorem euclideanMetric_inner (z : ℍ) (v w : TangentSpace 𝓘(ℝ, ℂ) z) :
    euclideanMetric.inner z v w =
      inner ℝ (tangentSpaceCastModel 𝓘(ℝ, ℂ) z v) (tangentSpaceCastModel 𝓘(ℝ, ℂ) z w) := by
  simp only [euclideanMetric, ContinuousLinearEquiv.arrowCongr_apply,
    ContinuousLinearEquiv.symm_symm, ContinuousLinearEquiv.refl_apply]
  erw [innerSL_apply_apply]

/-- The factor `im⁻²` of the Poincaré metric is smooth on the upper half-plane. -/
private theorem contMDiff_inv_im_sq :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞ fun z : ℍ ↦ (z.im ^ 2)⁻¹ := by
  intro α
  have hcoe : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ _root_.UpperHalfPlane.coe α :=
    contMDiffAt_extChartAt
  have him : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞ _root_.UpperHalfPlane.im α :=
    Complex.imCLM.contMDiff.contMDiffAt.comp α hcoe
  exact (him.pow 2).inv₀ (by positivity)

/-- The smooth Poincaré metric: the Euclidean tensor rescaled by `im⁻²`. -/
def poincareRiemannianMetric :
    ContMDiffRiemannianMetric 𝓘(ℝ, ℂ) ∞ ℂ
      (fun z : ℍ ↦ TangentSpace 𝓘(ℝ, ℂ) z) :=
  euclideanMetric.rescale (fun z : ℍ ↦ (z.im ^ 2)⁻¹) contMDiff_inv_im_sq
    fun z ↦ inv_pos.mpr (sq_pos_of_pos z.im_pos)

/-- The Poincaré tensor in the tangent coordinates of the inclusion chart. -/
@[simp]
theorem _root_.UpperHalfPlane.poincareRiemannianMetric_inner (z : ℍ)
    (v w : TangentSpace 𝓘(ℝ, ℂ) z) :
    poincareRiemannianMetric.inner z v w =
      inner ℝ (tangentSpaceCastModel 𝓘(ℝ, ℂ) z v)
        (tangentSpaceCastModel 𝓘(ℝ, ℂ) z w) / z.im ^ 2 := by
  rw [poincareRiemannianMetric, Bundle.ContMDiffRiemannianMetric.rescale_inner,
    euclideanMetric_inner, div_eq_inv_mul]

/-- The tangent bundle of the upper half-plane carries the Poincaré tensor. -/
instance instRiemannianBundle : RiemannianBundle (fun z : ℍ ↦ TangentSpace 𝓘(ℝ, ℂ) z) :=
  ⟨poincareRiemannianMetric.toRiemannianMetric⟩

/-- The Poincaré tensor is smooth as a real Riemannian bundle. -/
instance instIsContMDiffRiemannianBundle : IsContMDiffRiemannianBundle 𝓘(ℝ, ℂ) ∞ ℂ
    (fun z : ℍ ↦ TangentSpace 𝓘(ℝ, ℂ) z) :=
  Bundle.instIsContMDiffRiemannianBundle poincareRiemannianMetric

/-- Continuity of the Poincaré tensor makes the Riemannian volume construction applicable. -/
instance instIsContinuousRiemannianBundle :
    IsContinuousRiemannianBundle ℂ (fun z : ℍ ↦ TangentSpace 𝓘(ℝ, ℂ) z) :=
  Bundle.instIsContinuousRiemannianBundle poincareRiemannianMetric.toContinuousRiemannianMetric

/-- In the inclusion chart, the Gram matrix of the Poincaré tensor is `im⁻²` times the Euclidean
Gram matrix of the model basis. -/
private theorem chartGramMatrix_eq (α z : ℍ) :
    chartGramMatrix (I := 𝓘(ℝ, ℂ)) α z =
      (z.im ^ 2)⁻¹ • Matrix.gram ℝ (Module.finBasis ℝ ℂ) := by
  ext i j
  have hz : z ∈ (chartAt ℂ α).source := by simp
  rw [chartGramMatrix_apply, chartLocalFrame_apply_of_mem_chart_source α hz,
    chartLocalFrame_apply_of_mem_chart_source α hz]
  refine (_root_.UpperHalfPlane.poincareRiemannianMetric_inner z _ _).trans ?_
  simp [Trivialization.basisAt, poincare_symm, Matrix.gram_apply, div_eq_inv_mul]

/-- In the inclusion chart, the Riemannian volume density of the Poincaré metric is `im⁻²` times
the Euclidean volume density of the model basis. -/
private theorem chartVolumeDensity_eq (α z : ℍ) :
    chartVolumeDensity (I := 𝓘(ℝ, ℂ)) α z =
      (z.im ^ 2)⁻¹ * √(Matrix.gram ℝ (Module.finBasis ℝ ℂ)).det := by
  have h : (z.im ^ 2)⁻¹ ^ Module.finrank ℝ ℂ = ((z.im ^ 2)⁻¹) ^ 2 := by
    rw [Complex.finrank_real_complex]
  rw [chartVolumeDensity_def, chartGramMatrix_eq, Matrix.det_smul, Fintype.card_fin, h,
    Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]

/-- The Riemannian volume of the Poincaré metric is Mathlib's invariant measure on the upper
half-plane, with density `y⁻² dx dy` against Lebesgue measure. -/
theorem _root_.UpperHalfPlane.riemannianVolume_eq_volume :
    riemannianVolume 𝓘(ℝ, ℂ) ℍ = volume := by
  symm
  rw [eq_riemannianVolume_iff]
  intro α
  ext s hs
  -- Both sides are integrals over the image of `s` in `ℂ`; compare the integrands there.
  have hsrc : (extChartAt 𝓘(ℝ, ℂ) α).source = univ := by simp
  have hcoe : ⇑(extChartAt 𝓘(ℝ, ℂ) α) = _root_.UpperHalfPlane.coe := by simp
  rw [chartRiemannianVolume_apply α hs, Measure.restrict_apply hs,
    _root_.UpperHalfPlane.volume_eq_lintegral, (Module.finBasis ℝ ℂ).volume_eq_smul_addHaar,
    setLIntegral_smul_measure, smul_eq_mul, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← extChartAt_source 𝓘(ℝ, ℂ), hsrc, inter_univ, hcoe]
  refine setLIntegral_congr_fun
    (_root_.UpperHalfPlane.measurableEmbedding_coe.measurableSet_image.mpr hs) ?_
  rintro _ ⟨z, -, rfl⟩
  have hz : (extChartAt 𝓘(ℝ, ℂ) α).symm z = z := by
    simpa [hcoe] using (extChartAt 𝓘(ℝ, ℂ) α).left_inv (x := z) (by simp)
  dsimp only
  rw [hz, chartVolumeDensity_eq, mul_comm, ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [← ENNReal.ofReal_coe_nnreal]
  congr 1
  simp [Real.nnNorm_of_nonneg z.im_pos.le]

/-! ### Installed bundle inner product and norms -/

/-- The inner product of two tangent vectors at a point of the upper half-plane is their
Euclidean inner product divided by the square of the imaginary coordinate. -/
@[simp]
theorem inner_def (z : ℍ) (v w : TangentSpace 𝓘(ℝ, ℂ) z) :
    inner ℝ v w =
      inner ℝ (tangentSpaceCastModel 𝓘(ℝ, ℂ) z v)
        (tangentSpaceCastModel 𝓘(ℝ, ℂ) z w) / z.im ^ 2 :=
  _root_.UpperHalfPlane.poincareRiemannianMetric_inner z v w

/-- The Poincaré norm of a tangent vector at `z` is its Euclidean norm divided by `Im z`. -/
@[simp]
theorem norm_def (z : ℍ) (v : TangentSpace 𝓘(ℝ, ℂ) z) :
    ‖v‖ = ‖tangentSpaceCastModel 𝓘(ℝ, ℂ) z v‖ / z.im := by
  rw [norm_eq_sqrt_real_inner, inner_def, real_inner_self_eq_norm_sq, ← div_pow,
    Real.sqrt_sq (div_nonneg (norm_nonneg _) z.im_pos.le)]

/-- The Poincaré extended norm of a tangent vector at `z` is its Euclidean extended norm divided
by `ENNReal.ofReal z.im`. -/
@[simp]
theorem eNorm_def (z : ℍ) (v : TangentSpace 𝓘(ℝ, ℂ) z) :
    ‖v‖ₑ = ‖tangentSpaceCastModel 𝓘(ℝ, ℂ) z v‖ₑ / ENNReal.ofReal z.im := by
  rw [← ofReal_norm, ← ofReal_norm, norm_def, ENNReal.ofReal_div_of_pos z.im_pos]

/-! ### Smoothness and differentials of the `GL(2, ℝ)` action -/

/-- The inclusion `ℍ → ℂ` is `C^n` over `ℝ` for every smoothness exponent `n`. -/
theorem contMDiff_coe_real {n : ℕ∞ω} :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) n (_root_.UpperHalfPlane.coe : ℍ → ℂ) :=
  fun _ ↦ contMDiffAt_extChartAt

/-- The orientation-reversing reflection `UpperHalfPlane.J : z ↦ -conj z` is `C^n` on `ℍ` as a
real manifold, for every smoothness exponent `n`. -/
theorem contMDiff_J_smul {n : ℕ∞ω} :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) n (_root_.UpperHalfPlane.J • · : ℍ → ℍ) := by
  apply ContMDiff.of_comp_isOpenEmbedding _root_.UpperHalfPlane.isOpenEmbedding_coe
  have hL : ContDiff ℝ n (-Complex.conjCLE : ℂ →L[ℝ] ℂ) := ContinuousLinearMap.contDiff _
  refine (hL.contMDiff.comp contMDiff_coe_real).congr fun z ↦ ?_
  simp [_root_.UpperHalfPlane.coe_J_smul]

private theorem contMDiff_gl_smul {n : ℕ∞ω} (g : GL (Fin 2) ℝ) :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) n (g • · : ℍ → ℍ) := by
  have hpos {h : GL (Fin 2) ℝ} (hh : 0 < h.det.val) :
      ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) n (h • · : ℍ → ℍ) := by
    apply ContMDiff.of_comp_isOpenEmbedding _root_.UpperHalfPlane.isOpenEmbedding_coe
    intro τ
    have hc : ContDiffAt ℂ n
        ((fun z : ℍ ↦ ((h • z : ℍ) : ℂ)) ∘ _root_.UpperHalfPlane.ofComplex) (τ : ℂ) :=
      _root_.UpperHalfPlane.contMDiffAt_iff.mp
        ((_root_.UpperHalfPlane.contMDiff_coe.comp (_root_.UpperHalfPlane.contMDiff_smul hh)) τ)
    refine ((hc.restrict_scalars ℝ).contMDiffAt.comp τ
      (contMDiff_coe_real τ)).congr_of_eventuallyEq (Filter.Eventually.of_forall fun z ↦ ?_)
    simp [_root_.UpperHalfPlane.ofComplex_apply]
  rcases g.det.ne_zero.lt_or_gt with hg | hg
  · have hJg : 0 < (_root_.UpperHalfPlane.J * g).det.val := by simpa using hg
    refine (contMDiff_J_smul.comp (hpos hJg)).congr fun z ↦ ?_
    simp [Function.comp_apply, smul_smul, ← mul_assoc, ← sq]
  · exact hpos hg

/-- Every element of `GL(2, ℝ)` acts on `ℍ` by a `C^n` map of real manifolds: matrices of positive
determinant act holomorphically, and matrices of negative determinant factor through the
reflection `UpperHalfPlane.J`. -/
instance instContMDiffConstSMulGL {n : ℕ∞ω} :
    ContMDiffConstSMul 𝓘(ℝ, ℂ) n (GL (Fin 2) ℝ) ℍ :=
  ⟨contMDiff_gl_smul⟩

/-- Every element of `PGL(2, ℝ)` acts on `ℍ` by a `C^n` map of real manifolds. -/
instance instContMDiffConstSMulPGL {n : ℕ∞ω} :
    ContMDiffConstSMul 𝓘(ℝ, ℂ) n PGL(2, ℝ) ℍ where
  contMDiff_const_smul q := by
    induction q using Matrix.ProjGenLinGroup.induction_on with | mk g =>
    simpa only [_root_.UpperHalfPlane.pglMk_smul] using contMDiff_const_smul g

/-- Every element of `SL(2, R)` (for coefficients mapping to `ℝ`) acts on `ℍ` by a `C^n` map of
real manifolds. -/
instance instContMDiffConstSMulSL {R : Type*} [CommRing R] [Algebra R ℝ] {n : ℕ∞ω} :
    ContMDiffConstSMul 𝓘(ℝ, ℂ) n SL(2, R) ℍ where
  contMDiff_const_smul g := by
    simpa only [MulAction.compHom_smul_def] using
      contMDiff_const_smul (Matrix.SpecialLinearGroup.mapGL ℝ g)

/-- Every element of `PSL(2, R)` (for coefficients mapping to `ℝ`) acts on `ℍ` by a `C^n` map of
real manifolds. -/
instance instContMDiffConstSMulPSL {R : Type*} [CommRing R] [Algebra R ℝ] {n : ℕ∞ω} :
    ContMDiffConstSMul 𝓘(ℝ, ℂ) n PSL(2, R) ℍ where
  contMDiff_const_smul q := by
    refine QuotientGroup.induction_on q fun g ↦ ?_
    simpa only [_root_.UpperHalfPlane.pslMk_smul] using contMDiff_const_smul g

private theorem tangentSpaceCastModel_mfderiv_congr {f₁ f₂ : ℍ → ℍ} (h : f₁ = f₂) (z : ℍ)
    (v : TangentSpace 𝓘(ℝ, ℂ) z) :
    tangentSpaceCastModel 𝓘(ℝ, ℂ) (f₁ z) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) f₁ z v) =
      tangentSpaceCastModel 𝓘(ℝ, ℂ) (f₂ z) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) f₂ z v) := by
  subst h
  rfl

/-- In model coordinates, the differential of `(g • · : ℍ → ℍ)` at `z` is Mathlib's real-linear
derivative `UpperHalfPlane.smulFDeriv g z`. -/
theorem tangentSpaceCastModel_mfderiv_smul (g : GL (Fin 2) ℝ) (z : ℍ)
    (v : TangentSpace 𝓘(ℝ, ℂ) z) :
    tangentSpaceCastModel 𝓘(ℝ, ℂ) (g • z)
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (g • ·) z v) =
      _root_.UpperHalfPlane.smulFDeriv g z (tangentSpaceCastModel 𝓘(ℝ, ℂ) z v) := by
  have hd : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (g • · : ℍ → ℍ) z :=
    ((contMDiff_const_smul (I := 𝓘(ℝ, ℂ)) (n := ∞) g) z).mdifferentiableAt (by simp)
  rw [hd.tangentSpaceCastModel_mfderiv_apply]
  have hloc : writtenInExtChartAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) z (g • · : ℍ → ℍ) =ᶠ[𝓝 (z : ℂ)]
      fun w : ℂ ↦ ((g • _root_.UpperHalfPlane.ofComplex w : ℍ) : ℂ) := by
    have hwritten : writtenInExtChartAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) z (g • · : ℍ → ℍ) =
        (fun x : ℍ ↦ ((g • x : ℍ) : ℂ)) ∘ (chartAt ℂ z).symm := by
      funext w
      simp [writtenInExtChartAt]
    rw [hwritten]
    exact comp_chartAt_symm_eventuallyEq (fun x : ℍ ↦ ((g • x : ℍ) : ℂ)) z
  have hchart : extChartAt 𝓘(ℝ, ℂ) z z = (z : ℂ) := by simp
  rw [hchart, hloc.fderiv_eq, (_root_.UpperHalfPlane.hasStrictFDerivAt_smul g z).hasFDerivAt.fderiv]

/-- In model coordinates, the differential of the reflection `UpperHalfPlane.J : z ↦ -conj z` is
`u ↦ -conj u`. -/
@[simp]
theorem tangentSpaceCastModel_mfderiv_J_smul (z : ℍ) (v : TangentSpace 𝓘(ℝ, ℂ) z) :
    tangentSpaceCastModel 𝓘(ℝ, ℂ) (_root_.UpperHalfPlane.J • z)
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (_root_.UpperHalfPlane.J • ·) z v) =
      -conj (tangentSpaceCastModel 𝓘(ℝ, ℂ) z v) := by
  rw [tangentSpaceCastModel_mfderiv_smul]
  have hJ : _root_.UpperHalfPlane.J * (1 : GL (Fin 2) ℝ) = _root_.UpperHalfPlane.J := mul_one _
  rw [← hJ, _root_.UpperHalfPlane.smulFDeriv_J_mul]
  simp [_root_.UpperHalfPlane.smulFDeriv, _root_.UpperHalfPlane.σ]

/-- In model coordinates, the differential of the Möbius action of `q : PSL(2, ℝ)` at `z`
multiplies tangent vectors by `Matrix.ProjectiveSpecialLinearGroup.smulDeriv q z`. -/
theorem tangentSpaceCastModel_mfderiv_psl_smul (q : PSL(2, ℝ)) (z : ℍ)
    (v : TangentSpace 𝓘(ℝ, ℂ) z) :
    tangentSpaceCastModel 𝓘(ℝ, ℂ) (q • z)
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (q • ·) z v) =
      Matrix.ProjectiveSpecialLinearGroup.smulDeriv q z *
        tangentSpaceCastModel 𝓘(ℝ, ℂ) z v := by
  induction q using QuotientGroup.induction_on with | _ g =>
  have hfun : ((g : PSL(2, ℝ)) • · : ℍ → ℍ) = (Matrix.SpecialLinearGroup.mapGL ℝ g • ·) := by
    funext w
    rw [_root_.UpperHalfPlane.pslMk_smul, _root_.Matrix.SpecialLinearGroup.mapGL_smul]
  rw [tangentSpaceCastModel_mfderiv_congr hfun z v, tangentSpaceCastModel_mfderiv_smul,
    Matrix.SpecialLinearGroup.smulDeriv_coe]
  simp [_root_.UpperHalfPlane.smulFDeriv, _root_.UpperHalfPlane.σ_eq_refl_of_det_pos, one_div,
    mul_comm]

/-! ### Riemannian isometry actions on `ℍ` -/

private theorem inner_σ (g : GL (Fin 2) ℝ) (u w : ℂ) :
    inner ℝ (_root_.UpperHalfPlane.σ g u) (_root_.UpperHalfPlane.σ g w) = inner ℝ u w := by
  simp only [_root_.UpperHalfPlane.σ]
  split_ifs <;> simp [Complex.inner]

private theorem inner_mul_right_complex (c u w : ℂ) :
    inner ℝ (u * c) (w * c) = Complex.normSq c * inner ℝ u w := by
  simp only [Complex.inner, Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
    Complex.conj_re, Complex.conj_im]
  ring

private theorem inner_mfderiv_congr {f₁ f₂ : ℍ → ℍ} (h : f₁ = f₂) (z : ℍ)
    (v w : TangentSpace 𝓘(ℝ, ℂ) z) :
    inner ℝ (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) f₁ z v) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) f₁ z w) =
      inner ℝ (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) f₂ z v) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) f₂ z w) := by
  subst h
  rfl

/-- The differential of `g • ·` preserves the Poincaré inner product for every `g : GL(2, ℝ)`,
both orientation-preserving (`det g > 0`) and orientation-reversing (`det g < 0`). -/
theorem inner_mfderiv_gl_smul (g : GL (Fin 2) ℝ) (z : ℍ) (v w : TangentSpace 𝓘(ℝ, ℂ) z) :
    inner ℝ (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (g • ·) z v) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (g • ·) z w) =
      inner ℝ v w := by
  rw [inner_def, inner_def, tangentSpaceCastModel_mfderiv_smul, tangentSpaceCastModel_mfderiv_smul]
  simp only [_root_.UpperHalfPlane.smulFDeriv, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, ContinuousAlgEquiv.coeCLE_apply,
    ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.toSpanSingleton_apply,
    smul_eq_mul, inner_σ, inner_mul_right_complex]
  rw [_root_.UpperHalfPlane.im_smul_eq_div_normSq, map_div₀, map_pow, Complex.normSq_ofReal]
  have hd : (g.det.val : ℝ) ≠ 0 := g.det.ne_zero
  have hden : Complex.normSq (_root_.UpperHalfPlane.denom g z) ≠ 0 :=
    _root_.UpperHalfPlane.normSq_denom_ne_zero g z.im_ne_zero
  have hz : z.im ≠ 0 := z.im_ne_zero
  have habs : |g.det.val| ^ 2 = g.det.val ^ 2 := sq_abs _
  field_simp
  rw [habs]
  ring

/-- The differential of `q • ·` preserves the Poincaré inner product for every `q : PGL(2, ℝ)`. -/
theorem inner_mfderiv_pgl_smul (q : PGL(2, ℝ)) (z : ℍ) (v w : TangentSpace 𝓘(ℝ, ℂ) z) :
    inner ℝ (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (q • ·) z v) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (q • ·) z w) =
      inner ℝ v w := by
  induction q using Matrix.ProjGenLinGroup.induction_on with | mk g =>
  have hfun : (Matrix.ProjGenLinGroup.mk g • · : ℍ → ℍ) = (g • ·) :=
    funext (_root_.UpperHalfPlane.pglMk_smul g)
  exact (inner_mfderiv_congr hfun z v w).trans (inner_mfderiv_gl_smul g z v w)

/-- The differential of `g • ·` preserves the Poincaré inner product for every `g : SL(2, R)`. -/
theorem inner_mfderiv_sl_smul {R : Type*} [CommRing R] [Algebra R ℝ] (g : SL(2, R)) (z : ℍ)
    (v w : TangentSpace 𝓘(ℝ, ℂ) z) :
    inner ℝ (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (g • ·) z v) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (g • ·) z w) =
      inner ℝ v w := by
  have hfun : (g • · : ℍ → ℍ) = (Matrix.SpecialLinearGroup.mapGL ℝ g • ·) :=
    funext fun τ ↦ MulAction.compHom_smul_def _ _ τ
  exact (inner_mfderiv_congr hfun z v w).trans
    (inner_mfderiv_gl_smul (Matrix.SpecialLinearGroup.mapGL ℝ g) z v w)

/-- The differential of `q • ·` preserves the Poincaré inner product for every `q : PSL(2, R)`. -/
theorem inner_mfderiv_psl_smul {R : Type*} [CommRing R] [Algebra R ℝ] (q : PSL(2, R)) (z : ℍ)
    (v w : TangentSpace 𝓘(ℝ, ℂ) z) :
    inner ℝ (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (q • ·) z v) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (q • ·) z w) =
      inner ℝ v w := by
  refine QuotientGroup.induction_on q fun g ↦ ?_
  have hfun : ((g : PSL(2, R)) • · : ℍ → ℍ) = (g • ·) :=
    funext (_root_.UpperHalfPlane.pslMk_smul g)
  exact (inner_mfderiv_congr hfun z v w).trans (inner_mfderiv_sl_smul g z v w)

/-- The group homomorphism from `GL(2, ℝ)` to the Riemannian isometry group of the Poincaré
upper half-plane. -/
def glToIsom : GL (Fin 2) ℝ →* Isom 𝓘(ℝ, ℂ) ℍ :=
  RiemannianIsometry.constSMulHom inner_mfderiv_gl_smul

/-- `glToIsom g` acts on `ℍ` as `g • ·`. -/
@[simp]
theorem glToIsom_apply (g : GL (Fin 2) ℝ) (z : ℍ) : glToIsom g z = g • z := by
  simp [glToIsom]

/-- The group homomorphism from `PGL(2, ℝ)` to the Riemannian isometry group of the Poincaré
upper half-plane. -/
def pglToIsom : PGL(2, ℝ) →* Isom 𝓘(ℝ, ℂ) ℍ :=
  RiemannianIsometry.constSMulHom inner_mfderiv_pgl_smul

/-- `pglToIsom q` acts on `ℍ` as `q • ·`. -/
@[simp]
theorem pglToIsom_apply (q : PGL(2, ℝ)) (z : ℍ) : pglToIsom q z = q • z := by
  simp [pglToIsom]

/-- `PGL(2, ℝ)` embeds faithfully into the Riemannian isometry group of `ℍ`. -/
theorem pglToIsom_injective : Function.Injective pglToIsom :=
  RiemannianIsometry.constSMulHom_injective _

/-- On the class of `g : GL(2, ℝ)`, `pglToIsom` agrees with `glToIsom g`. -/
@[simp]
theorem pglToIsom_mk (g : GL (Fin 2) ℝ) :
    pglToIsom (Matrix.ProjGenLinGroup.mk g) = glToIsom g := by
  ext z
  simp

/-- The group homomorphism from `SL(2, R)` to the Riemannian isometry group of the Poincaré
upper half-plane. -/
def slToIsom {R : Type*} [CommRing R] [Algebra R ℝ] : SL(2, R) →* Isom 𝓘(ℝ, ℂ) ℍ :=
  RiemannianIsometry.constSMulHom inner_mfderiv_sl_smul

/-- `slToIsom g` acts on `ℍ` as `g • ·`. -/
@[simp]
theorem slToIsom_apply {R : Type*} [CommRing R] [Algebra R ℝ] (g : SL(2, R)) (z : ℍ) :
    slToIsom g z = g • z := by
  simp [slToIsom]

/-- The group homomorphism from `PSL(2, R)` to the Riemannian isometry group of the Poincaré
upper half-plane. -/
def pslToIsom {R : Type*} [CommRing R] [Algebra R ℝ] : PSL(2, R) →* Isom 𝓘(ℝ, ℂ) ℍ :=
  RiemannianIsometry.constSMulHom inner_mfderiv_psl_smul

/-- `pslToIsom q` acts on `ℍ` as `q • ·`. -/
@[simp]
theorem pslToIsom_apply {R : Type*} [CommRing R] [Algebra R ℝ] (q : PSL(2, R)) (z : ℍ) :
    pslToIsom q z = q • z := by
  simp [pslToIsom]

/-- Whenever `PSL(2, R)` acts faithfully on `ℍ` (for instance `R = ℝ` or `R = ℤ`), it embeds
faithfully into the Riemannian isometry group of `ℍ`. -/
theorem pslToIsom_injective {R : Type*} [CommRing R] [Algebra R ℝ] [FaithfulSMul PSL(2, R) ℍ] :
    Function.Injective (pslToIsom (R := R)) :=
  RiemannianIsometry.constSMulHom_injective _

/-- On the class of `g : SL(2, R)`, `pslToIsom` agrees with `slToIsom g`. -/
@[simp]
theorem pslToIsom_mk {R : Type*} [CommRing R] [Algebra R ℝ] (g : SL(2, R)) :
    pslToIsom (g : PSL(2, R)) = slToIsom g := by
  ext z
  simp

/-- Embedding `PSL(2, ℝ)` into `PGL(2, ℝ)` via `toPGL` intertwines `pslToIsom` and `pglToIsom`. -/
@[simp]
theorem pglToIsom_toPGL (q : PSL(2, ℝ)) :
    pglToIsom (Matrix.ProjectiveSpecialLinearGroup.toPGL q) = pslToIsom q := by
  ext z
  simp

/-- The reflection `glToIsom UpperHalfPlane.J` is an involution in `Isom 𝓘(ℝ, ℂ) ℍ`. -/
@[simp]
theorem glToIsom_J_mul_self :
    glToIsom _root_.UpperHalfPlane.J * glToIsom _root_.UpperHalfPlane.J = 1 := by
  rw [← map_mul, ← sq, _root_.UpperHalfPlane.J_sq, map_one]

/-- The reflection `glToIsom UpperHalfPlane.J` is its own inverse in `Isom 𝓘(ℝ, ℂ) ℍ`. -/
@[simp]
theorem glToIsom_J_inv :
    (glToIsom _root_.UpperHalfPlane.J)⁻¹ = glToIsom _root_.UpperHalfPlane.J :=
  inv_eq_of_mul_eq_one_left glToIsom_J_mul_self

/-- The orientation-reversing reflection `glToIsom UpperHalfPlane.J` is induced by no element of
`PSL(2, ℝ)`. -/
theorem glToIsom_J_notMem_range_pslToIsom :
    glToIsom _root_.UpperHalfPlane.J ∉ Set.range (pslToIsom (R := ℝ)) := by
  rintro ⟨q, hq⟩
  induction q using QuotientGroup.induction_on with | H g =>
  have hmk : Matrix.ProjectiveSpecialLinearGroup.toPGL (QuotientGroup.mk g) =
      Matrix.ProjGenLinGroup.mk _root_.UpperHalfPlane.J :=
    pglToIsom_injective (by rw [pglToIsom_toPGL, pglToIsom_mk, hq])
  obtain ⟨u, hu⟩ : ∃ u : ℝˣ,
      (g : GL (Fin 2) ℝ) * Matrix.GeneralLinearGroup.scalar (Fin 2) u =
        _root_.UpperHalfPlane.J := by
    simpa [Matrix.ProjGenLinGroup.mk_eq_mk_iff] using hmk
  have hdet : (u : ℝ) ^ 2 = -1 := by
    simpa [Matrix.det_fin_two] using congr(Units.val (Matrix.GeneralLinearGroup.det $hu))
  nlinarith [sq_nonneg (u : ℝ)]

/-! ### Geodesic path lengths and the distance comparison -/

private theorem coe_geodesicLine_one (t : ℝ) :
    (geodesicLine 1 t : ℂ) = (Real.exp t : ℂ) * Complex.I := by
  rw [geodesicLine_one_apply, _root_.UpperHalfPlane.coe_mk]
  apply Complex.ext <;>
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_self, add_zero]

/-- Every geodesic line `geodesicLine g` is `C^n` as a curve into `ℍ` for every smoothness
exponent `n`. -/
theorem contMDiff_geodesicLine {n : ℕ∞ω} (g : PSL(2, ℝ)) :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) n (geodesicLine g) := by
  have hone : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) n (geodesicLine 1) := by
    apply ContMDiff.of_comp_isOpenEmbedding _root_.UpperHalfPlane.isOpenEmbedding_coe
    rw [contMDiff_iff_contDiff]
    have hfun : _root_.UpperHalfPlane.coe ∘ geodesicLine 1 =
        fun t : ℝ ↦ (Real.exp t : ℂ) * Complex.I :=
      funext coe_geodesicLine_one
    rw [hfun]
    exact (Complex.ofRealCLM.contDiff.comp Real.contDiff_exp).mul contDiff_const
  refine ((contMDiff_const_smul (I := 𝓘(ℝ, ℂ)) (n := n) g).comp hone).congr fun t ↦ ?_
  simp [Function.comp_apply]

/-- In model coordinates, the upward unit-speed imaginary axis `geodesicLine 1` has velocity
`exp t · i` at parameter `t`. -/
theorem tangentSpaceCastModel_curveVelocity_geodesicLine_one (t : ℝ) :
    tangentSpaceCastModel 𝓘(ℝ, ℂ) (geodesicLine 1 t)
        (TauCeti.Manifold.curveVelocity 𝓘(ℝ, ℂ) (geodesicLine 1) t) =
      (Real.exp t : ℂ) * Complex.I := by
  rw [TauCeti.Manifold.curveVelocity_apply]
  have hd : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) (geodesicLine 1) t :=
    (contMDiff_geodesicLine (n := ∞) 1 t).mdifferentiableAt (by simp)
  -- Retype `(1 : ℝ)` as `1 : TangentSpace 𝓘(ℝ, ℝ) t` so `tangentSpaceCastModel_mfderiv_apply`
  -- matches under implicit transparency.
  change tangentSpaceCastModel 𝓘(ℝ, ℂ) (geodesicLine 1 t)
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) (geodesicLine 1) t (1 : TangentSpace 𝓘(ℝ, ℝ) t)) =
    (Real.exp t : ℂ) * Complex.I
  rw [hd.tangentSpaceCastModel_mfderiv_apply]
  have hloc : writtenInExtChartAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) t (geodesicLine 1) =
      fun s : ℝ ↦ (Real.exp s : ℂ) * Complex.I := by
    funext s
    simp only [writtenInExtChartAt, Function.comp_apply, extChartAt_model_space_eq_id,
      PartialEquiv.refl_symm, PartialEquiv.refl_coe, id_eq]
    have hchart (z : ℍ) : extChartAt 𝓘(ℝ, ℂ) (geodesicLine 1 t) z = (z : ℂ) := by simp
    rw [hchart, coe_geodesicLine_one]
  have ht : extChartAt 𝓘(ℝ, ℝ) t t = t := by simp
  have hderiv : HasDerivAt (fun s : ℝ ↦ (Real.exp s : ℂ) * Complex.I)
      ((Real.exp t : ℂ) * Complex.I) t := by
    simpa using ((Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t
      (Real.hasDerivAt_exp t)).mul_const Complex.I)
  have hcast : tangentSpaceCastModel 𝓘(ℝ, ℝ) t 1 = 1 := rfl
  rw [hloc, ht, hderiv.hasFDerivAt.fderiv, hcast]
  simp

/-- Every geodesic line `geodesicLine g` has unit Poincaré speed at every parameter `t`. -/
@[simp 1100]
theorem norm_curveVelocity_geodesicLine (g : PSL(2, ℝ)) (t : ℝ) :
    ‖TauCeti.Manifold.curveVelocity 𝓘(ℝ, ℂ) (geodesicLine g) t‖ = 1 := by
  have hcomp : geodesicLine g = pslToIsom g ∘ geodesicLine 1 := funext fun s ↦ by simp
  have hd1 : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) (geodesicLine 1) t :=
    (contMDiff_geodesicLine (n := ∞) 1 t).mdifferentiableAt (by simp)
  rw [hcomp, TauCeti.Manifold.curveVelocity_apply,
    mfderiv_comp_apply t ((pslToIsom g).mdifferentiableAt _) hd1 (1 : ℝ),
    (pslToIsom g).norm_mfderiv, ← TauCeti.Manifold.curveVelocity_apply, norm_def,
    tangentSpaceCastModel_curveVelocity_geodesicLine_one, geodesicLine_one_apply]
  simp [(Real.exp_pos t).ne']

/-- Every geodesic line `geodesicLine g` has Poincaré path length `ENNReal.ofReal (b - a)` on
`[a, b]`. -/
@[simp]
theorem pathELength_geodesicLine (g : PSL(2, ℝ)) (a b : ℝ) :
    Manifold.pathELength 𝓘(ℝ, ℂ) (geodesicLine g) a b = ENNReal.ofReal (b - a) := by
  have hcomp : geodesicLine g = pslToIsom g ∘ geodesicLine 1 := funext fun s ↦ by simp
  rw [hcomp, (pslToIsom g).pathELength_comp, Manifold.pathELength_eq_lintegral_mfderiv_Ioo]
  have h1 : ∀ t : ℝ, ‖mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) (geodesicLine 1) t 1‖ₑ = 1 := fun t ↦ by
    -- Retype `1 : TangentSpace 𝓘(ℝ, ℝ) t` as `(1 : ℝ)` to match `curveVelocity_apply`.
    change ‖mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) (geodesicLine 1) t (1 : ℝ)‖ₑ = 1
    rw [← ofReal_norm, ← TauCeti.Manifold.curveVelocity_apply, norm_curveVelocity_geodesicLine,
      ENNReal.ofReal_one]
  simp [h1]

/-- The horocycle height projection `z ↦ log (Im z)` is `1`-Lipschitz for the Poincaré
Riemannian extended distance: `|log (Im z) - log (Im w)| ≤ riemannianEDist 𝓘(ℝ, ℂ) z w`. -/
theorem edist_log_im_le_riemannianEDist (z w : ℍ) :
    edist (Real.log z.im) (Real.log w.im) ≤ Manifold.riemannianEDist 𝓘(ℝ, ℂ) z w := by
  let f : ℍ → ℝ := fun τ ↦ Real.log τ.im
  have hf : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) 1 f := fun τ ↦ by
    have him : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) 1 _root_.UpperHalfPlane.im τ :=
      Complex.imCLM.contMDiff.contMDiffAt.comp τ (contMDiff_coe_real τ)
    exact (Real.contDiffAt_log.mpr τ.im_pos.ne').contMDiffAt.comp τ him
  have hnorm : ∀ (τ : ℍ) (v : TangentSpace 𝓘(ℝ, ℂ) τ),
      ‖mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) f τ v‖ ≤ (1 : ℝ≥0) * ‖v‖ := fun τ v ↦ by
    have hchart : extChartAt 𝓘(ℝ, ℂ) τ τ = (τ : ℂ) := by simp
    have hloc : f ∘ (extChartAt 𝓘(ℝ, ℂ) τ).symm =ᶠ[𝓝 (extChartAt 𝓘(ℝ, ℂ) τ τ)]
        fun u : ℂ ↦ Real.log u.im := by
      have hsymm : ⇑(extChartAt 𝓘(ℝ, ℂ) τ).symm = ⇑(chartAt ℂ τ).symm := by
        funext u
        simp
      rw [hchart, hsymm]
      refine (comp_chartAt_symm_eventuallyEq f τ).trans ?_
      filter_upwards [_root_.UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos] with u hu
      simp [f, _root_.UpperHalfPlane.ofComplex_apply_of_im_pos hu]
    have hfderiv : HasFDerivAt (fun u : ℂ ↦ Real.log u.im)
        ((τ.im)⁻¹ • Complex.imCLM) (τ : ℂ) := by
      simpa [Function.comp_def] using
        (Real.hasDerivAt_log τ.im_pos.ne').comp_hasFDerivAt (τ : ℂ) Complex.imCLM.hasFDerivAt
    have hm : NormedSpace.fromTangentSpace (f τ) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) f τ v) =
        mvfderiv 𝓘(ℝ, ℂ) f τ v := rfl
    have heval : mvfderiv 𝓘(ℝ, ℂ) f τ v =
        (tangentSpaceCastModel 𝓘(ℝ, ℂ) τ v).im / τ.im := by
      rw [TauCeti.mvfderiv_apply_eq_fderiv_comp_extChartAt_symm, hloc.fderiv_eq, hchart,
        hfderiv.fderiv]
      simp [div_eq_inv_mul]
    rw [norm_tangentSpace_vectorSpace, hm, heval, NNReal.coe_one, one_mul, norm_def,
      Real.norm_eq_abs, abs_div, abs_of_pos τ.im_pos]
    exact div_le_div_of_nonneg_right (Complex.abs_im_le_norm _) τ.im_pos.le
  have hle := TauCeti.Manifold.riemannianEDist_le_mul hf one_ne_zero hnorm z w
  rwa [← IsRiemannianManifold.out (I := 𝓘(ℝ, ℝ)), ENNReal.coe_one, one_mul] at hle

/-- **The Poincaré distance comparison.** The Riemannian extended distance of
`poincareRiemannianMetric` on `ℍ` coincides with Mathlib's hyperbolic extended distance. -/
@[simp]
theorem riemannianEDist_eq_edist (z w : ℍ) :
    Manifold.riemannianEDist 𝓘(ℝ, ℂ) z w = edist z w := by
  obtain ⟨g, hz, hw⟩ := exists_geodesicLine_zero_eq_and_dist_eq z w
  set t := dist z w with ht_def
  have ht : 0 ≤ t := dist_nonneg
  have hz' : z = pslToIsom g (geodesicLine 1 0) := by
    rw [← hz, pslToIsom_apply, smul_geodesicLine, mul_one]
  have hw' : w = pslToIsom g (geodesicLine 1 t) := by
    rw [← hw, pslToIsom_apply, smul_geodesicLine, mul_one]
  rw [edist_dist, ← ht_def]
  conv_lhs => rw [hz', hw', (pslToIsom g).riemannianEDist_eq]
  apply le_antisymm
  · obtain ⟨η, hη, hη0, hη1, hlen, -, -, -⟩ :=
      TauCeti.Manifold.exists_contMDiff_pathELength_eq_of_le (n := 1) ht
        (contMDiff_geodesicLine 1).contMDiffOn one_ne_zero
    calc Manifold.riemannianEDist 𝓘(ℝ, ℂ) (geodesicLine 1 0) (geodesicLine 1 t)
        ≤ Manifold.pathELength 𝓘(ℝ, ℂ) η 0 1 :=
          Manifold.riemannianEDist_le_pathELength hη.contMDiffOn hη0 hη1 zero_le_one
      _ = ENNReal.ofReal t := by rw [hlen, pathELength_geodesicLine, sub_zero]
  · calc ENNReal.ofReal t
        = edist (Real.log (geodesicLine 1 0).im) (Real.log (geodesicLine 1 t).im) := by
          simp [geodesicLine_one_apply, edist_dist, Real.dist_eq, abs_of_nonneg ht]
      _ ≤ Manifold.riemannianEDist 𝓘(ℝ, ℂ) (geodesicLine 1 0) (geodesicLine 1 t) :=
          edist_log_im_le_riemannianEDist _ _

/-- **Mathlib's hyperbolic metric on `ℍ` is the Riemannian distance of the Poincaré metric.** -/
instance instIsRiemannianManifold : IsRiemannianManifold 𝓘(ℝ, ℂ) ℍ where
  out z w := (riemannianEDist_eq_edist z w).symm

/-- Every two points of `ℍ` are joined on `[0, 1]` by a smooth path whose Poincaré length realizes
`edist z w`. -/
theorem exists_contMDiff_pathELength_eq_edist (z w : ℍ) :
    ∃ γ : ℝ → ℍ, ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ γ ∧ γ 0 = z ∧ γ 1 = w ∧
      Manifold.pathELength 𝓘(ℝ, ℂ) γ 0 1 = edist z w := by
  obtain ⟨g, hz, hw⟩ := exists_geodesicLine_zero_eq_and_dist_eq z w
  obtain ⟨γ, hγ, hγ0, hγ1, hlen, -, -, -⟩ :=
    TauCeti.Manifold.exists_contMDiff_pathELength_eq_of_le (n := (⊤ : ℕ∞))
      (dist_nonneg : 0 ≤ dist z w) (contMDiff_geodesicLine (n := ∞) g).contMDiffOn (by simp)
  refine ⟨γ, hγ, hγ0.trans hz, hγ1.trans hw, ?_⟩
  rw [hlen, pathELength_geodesicLine, sub_zero, edist_dist]

/-- Scaling `I` vertically by `2` moves it by hyperbolic distance `log 2`. -/
theorem dist_I_two_smul_I :
    dist _root_.UpperHalfPlane.I
      ((⟨2, zero_lt_two⟩ : {x : ℝ // 0 < x}) • _root_.UpperHalfPlane.I) = Real.log 2 := by
  have h0 : geodesicLine 1 0 = _root_.UpperHalfPlane.I := by
    rw [geodesicLine_zero, one_smul]
  have h2 : geodesicLine 1 (Real.log 2) =
      (⟨2, zero_lt_two⟩ : {x : ℝ // 0 < x}) • _root_.UpperHalfPlane.I := by
    apply _root_.UpperHalfPlane.ext
    rw [coe_geodesicLine_one_log zero_lt_two, _root_.UpperHalfPlane.coe_pos_real_smul,
      _root_.UpperHalfPlane.coe_I]
    apply Complex.ext <;> simp
  rw [← h2, ← h0, dist_geodesicLine, zero_sub, abs_neg,
    abs_of_pos (Real.log_pos one_lt_two)]

/-! ### Completeness of the Poincaré Riemannian metric -/

/-- The metric space induced by `poincareRiemannianMetric` via `MetricSpace.ofRiemannianMetric`
is literally Mathlib's `MetricSpace ℍ`. -/
theorem ofRiemannianMetric_eq :
    MetricSpace.ofRiemannianMetric 𝓘(ℝ, ℂ) ℍ = (inferInstance : MetricSpace ℍ) := by
  ext z w
  -- `MetricSpace.ofRiemannianMetric` defines `dist z w` as `(riemannianEDist 𝓘(ℝ, ℂ) z w).toReal`.
  change (Manifold.riemannianEDist 𝓘(ℝ, ℂ) z w).toReal = dist z w
  rw [riemannianEDist_eq_edist, dist_edist]

/-- **Completeness of the Poincaré Riemannian metric**, deduced from `ofRiemannianMetric_eq` and
Mathlib's `ProperSpace ℍ` (`CompleteSpace ℍ`). -/
theorem completeSpace_of_riemannianMetric :
    @CompleteSpace ℍ
      (MetricSpace.ofRiemannianMetric 𝓘(ℝ, ℂ) ℍ).toPseudoMetricSpace.toUniformSpace := by
  rw [ofRiemannianMetric_eq]
  infer_instance

end TauCeti.UpperHalfPlane

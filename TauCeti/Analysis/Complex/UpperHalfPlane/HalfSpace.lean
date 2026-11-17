/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Euclidean.Prod
public import TauCeti.Analysis.Complex.UpperHalfPlane.PoincareMetric.Distance
public import TauCeti.Geometry.Manifold.Riemannian.Hyperbolic
public import TauCeti.Geometry.Manifold.Riemannian.Hyperbolic.UpperHalfSpace.Curvature
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Curvature
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Distance
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic

/-!
# The upper half-plane and half-space metrics

The coordinate map `x + iy ↦ (x, y)` identifies the Poincaré metric on the complex upper
half-plane with the two-dimensional upper half-space metric. The identification is a
Riemannian isometry: its differential preserves the Euclidean inner product and its base map
preserves height, so both tensors are the same Euclidean tensor divided by squared height.
Transporting the half-space curvature along this map proves that the Poincaré metric has
constant curvature tensor `-1` (`UpperHalfPlane.curvatureTensor_eq`) and constant sectional
curvature `-1` (`TauCeti.UpperHalfPlane.hasConstantSectionalCurvature`); combined with metric
completeness this packages the Poincaré metric as a `HyperbolicMetric`
(`TauCeti.UpperHalfPlane.poincareHyperbolicMetric`, `TauCeti.UpperHalfPlane.isHyperbolic`).

Conjugating along `upperHalfSpaceIsometry` transports the Möbius Riemannian isometries of
`GL(2, ℝ)`, `PGL(2, ℝ)`, and `PSL(2, ℝ)` into the Riemannian isometry group of
`UpperHalfSpace ℝ` (`glHalfSpaceIsomHom`, `pglHalfSpaceIsomHom`, `pslHalfSpaceIsomHom`).
Because Mathlib's hyperbolic distance on `ℍ` agrees with the Poincaré Riemannian distance
(`TauCeti.isRiemannianManifold_upperHalfPlane`), the same map induces a metric-space isometry
`upperHalfSpaceIsometryEquiv : ℍ ≃ᵢ UpperHalfSpace ℝ` when `UpperHalfSpace ℝ` carries its
intrinsic Riemannian metric `MetricSpace.ofRiemannianMetric`.

The metric convention follows J. M. Lee, *Introduction to Riemannian Manifolds*, second
edition, Chapter 3 (the upper half-space model).
-/

public section

open Bundle Manifold CovariantDerivative
open scoped ContDiff Manifold MatrixGroups UpperHalfPlane

noncomputable section

namespace TauCeti.UpperHalfPlane

open Complex (equivRealProdLp)

private def halfSpaceEquiv : ℍ ≃ UpperHalfSpace ℝ where
  toFun z := UpperHalfSpace.mk (equivRealProdLp z) (by simpa using z.im_pos)
  invFun p := ⟨equivRealProdLp.symm p, by simpa using UpperHalfSpace.height_pos p⟩
  left_inv z := by
    apply _root_.UpperHalfPlane.ext
    simpa only [UpperHalfSpace.coe_mk] using equivRealProdLp.symm_apply_apply (z : ℂ)
  right_inv p := by
    apply UpperHalfSpace.ext
    simpa only [UpperHalfSpace.coe_mk] using equivRealProdLp.apply_symm_apply
      (p : WithLp 2 (ℝ × ℝ))

private theorem coe_halfSpaceEquiv (z : ℍ) :
    (halfSpaceEquiv z : WithLp 2 (ℝ × ℝ)) = equivRealProdLp z :=
  UpperHalfSpace.coe_mk _ _

private theorem height_halfSpaceEquiv (z : ℍ) :
    UpperHalfSpace.height (halfSpaceEquiv z) = z.im := by
  simp [← UpperHalfSpace.snd_coe, coe_halfSpaceEquiv]

private theorem coe_halfSpaceEquiv_symm (p : UpperHalfSpace ℝ) :
    (halfSpaceEquiv.symm p : ℂ) = equivRealProdLp.symm p := rfl

private theorem contMDiff_halfSpaceEquiv :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, WithLp 2 (ℝ × ℝ)) ∞ halfSpaceEquiv := by
  apply UpperHalfSpace.contMDiff_coe_comp_iff.mp
  have hcoe : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ _root_.UpperHalfPlane.coe :=
    fun _ ↦ contMDiffAt_extChartAt
  simpa only [Function.comp_def, coe_halfSpaceEquiv] using
    equivRealProdLp.contDiff.contMDiff.comp hcoe

private theorem contMDiff_halfSpaceEquiv_symm :
    ContMDiff 𝓘(ℝ, WithLp 2 (ℝ × ℝ)) 𝓘(ℝ, ℂ) ∞ halfSpaceEquiv.symm := by
  apply ContMDiff.of_comp_isOpenEmbedding _root_.UpperHalfPlane.isOpenEmbedding_coe
  simpa only [Function.comp_def, coe_halfSpaceEquiv_symm] using
    equivRealProdLp.symm.contDiff.contMDiff.comp (UpperHalfSpace.contMDiff_coe.of_le le_top)

private theorem differential_halfSpaceEquiv (z : ℍ) (v : TangentSpace 𝓘(ℝ, ℂ) z) :
    tangentSpaceCastModel 𝓘(ℝ, WithLp 2 (ℝ × ℝ)) (halfSpaceEquiv z)
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, WithLp 2 (ℝ × ℝ)) halfSpaceEquiv z v) =
      equivRealProdLp (tangentSpaceCastModel 𝓘(ℝ, ℂ) z v) := by
  rw [(contMDiff_halfSpaceEquiv.mdifferentiableAt (by simp)).tangentSpaceCastModel_mfderiv_apply]
  have hlocal : writtenInExtChartAt 𝓘(ℝ, ℂ) 𝓘(ℝ, WithLp 2 (ℝ × ℝ)) z halfSpaceEquiv
      =ᶠ[nhds (z : ℂ)] equivRealProdLp := by
    filter_upwards [isOpen_lt continuous_const Complex.continuous_im |>.mem_nhds z.im_pos]
      with w hw
    have hchart (p : UpperHalfSpace ℝ) :
        extChartAt 𝓘(ℝ, WithLp 2 (ℝ × ℝ)) (halfSpaceEquiv z) p =
          (p : WithLp 2 (ℝ × ℝ)) := by simp [UpperHalfSpace.chartAt_apply]
    simp only [writtenInExtChartAt, Function.comp_apply, hchart, coe_halfSpaceEquiv]
    congr 1
    exact (extChartAt 𝓘(ℝ, ℂ) z).right_inv (by simpa using hw)
  have hchart : extChartAt 𝓘(ℝ, ℂ) z z = (z : ℂ) := by simp
  rw [hchart, hlocal.fderiv_eq, equivRealProdLp.hasFDerivAt.fderiv]
  -- The continuous linear map underlying the isometry has the same pointwise application.
  rfl

/-- The coordinate identification `x + iy ↦ (x, y)` is a Riemannian isometry from the
Poincaré upper half-plane to the two-dimensional hyperbolic upper half-space. -/
def upperHalfSpaceIsometry :
    RiemannianIsometry 𝓘(ℝ, ℂ) 𝓘(ℝ, WithLp 2 (ℝ × ℝ)) ℍ (UpperHalfSpace ℝ) where
  toEquiv := halfSpaceEquiv
  contMDiff_toFun := contMDiff_halfSpaceEquiv
  contMDiff_invFun := contMDiff_halfSpaceEquiv_symm
  inner_mfderiv' z v w := by
    -- The source inner product is the installed Poincaré tensor; the bundled map has
    -- underlying function `halfSpaceEquiv`, so its differential lemma applies here.
    change inner ℝ
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, WithLp 2 (ℝ × ℝ)) halfSpaceEquiv z v)
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, WithLp 2 (ℝ × ℝ)) halfSpaceEquiv z w) =
      poincareRiemannianMetric.inner z v w
    rw [UpperHalfSpace.inner_def, differential_halfSpaceEquiv, differential_halfSpaceEquiv,
      _root_.UpperHalfPlane.poincareRiemannianMetric_inner]
    simp [height_halfSpaceEquiv, WithLp.prod_inner_apply, Complex.inner]

/-- The identification with half-space sends a point to its real and imaginary coordinates. -/
@[simp]
theorem _root_.UpperHalfPlane.coe_upperHalfSpaceIsometry_apply (z : ℍ) :
    (upperHalfSpaceIsometry z : WithLp 2 (ℝ × ℝ)) = WithLp.toLp 2 (z.re, z.im) := by
  -- Reduce the bundled map's coercion to its defining equivalence before rewriting coordinates.
  change (halfSpaceEquiv z : WithLp 2 (ℝ × ℝ)) = _
  simpa only [Complex.equivRealProdLp_apply,
    _root_.UpperHalfPlane.coe_re, _root_.UpperHalfPlane.coe_im] using coe_halfSpaceEquiv z

/-- The identification with half-space preserves height. -/
@[simp]
theorem _root_.UpperHalfPlane.height_upperHalfSpaceIsometry_apply (z : ℍ) :
    UpperHalfSpace.height (upperHalfSpaceIsometry z) = z.im :=
  height_halfSpaceEquiv z

/-- The inverse identification sends `(x, y)` to `x + iy`. -/
@[simp]
theorem coe_upperHalfSpaceIsometry_symm_apply (p : UpperHalfSpace ℝ) :
    (upperHalfSpaceIsometry.symm p : ℂ) =
      ((p : WithLp 2 (ℝ × ℝ)).fst : ℂ) + UpperHalfSpace.height p * Complex.I := by
  have h := congrArg UpperHalfSpace.coe (upperHalfSpaceIsometry.apply_symm_apply p)
  rw [_root_.UpperHalfPlane.coe_upperHalfSpaceIsometry_apply] at h
  apply Complex.ext
  · simpa using congrArg WithLp.fst h
  · simpa using congrArg WithLp.snd h

/-- The inverse identification recovers the horizontal coordinate as the real part. -/
@[simp]
theorem re_upperHalfSpaceIsometry_symm_apply (p : UpperHalfSpace ℝ) :
    (upperHalfSpaceIsometry.symm p).re = (p : WithLp 2 (ℝ × ℝ)).fst := by
  have h := congrArg Complex.re (coe_upperHalfSpaceIsometry_symm_apply p)
  rw [_root_.UpperHalfPlane.coe_re] at h
  simpa using h

/-- The inverse identification recovers height as the imaginary part. -/
@[simp]
theorem im_upperHalfSpaceIsometry_symm_apply (p : UpperHalfSpace ℝ) :
    (upperHalfSpaceIsometry.symm p).im = UpperHalfSpace.height p := by
  have h := congrArg Complex.im (coe_upperHalfSpaceIsometry_symm_apply p)
  rw [_root_.UpperHalfPlane.coe_im] at h
  simpa using h

/-- In model coordinates, the differential sends a tangent vector to its real and imaginary
parts. -/
theorem _root_.UpperHalfPlane.tangentSpaceCastModel_mfderiv_upperHalfSpaceIsometry
    (z : ℍ) (v : TangentSpace 𝓘(ℝ, ℂ) z) :
    tangentSpaceCastModel 𝓘(ℝ, WithLp 2 (ℝ × ℝ)) (upperHalfSpaceIsometry z)
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, WithLp 2 (ℝ × ℝ)) upperHalfSpaceIsometry z v) =
      WithLp.toLp 2 ((tangentSpaceCastModel 𝓘(ℝ, ℂ) z v).re,
        (tangentSpaceCastModel 𝓘(ℝ, ℂ) z v).im) := by
  -- The defining equivalence and the bundled isometry are the same function, including in mfderiv.
  change tangentSpaceCastModel 𝓘(ℝ, WithLp 2 (ℝ × ℝ)) (halfSpaceEquiv z)
    (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, WithLp 2 (ℝ × ℝ)) halfSpaceEquiv z v) = _
  simpa only [Complex.equivRealProdLp_apply] using differential_halfSpaceEquiv z v

/-- The Poincaré metric on the upper half-plane has constant sectional curvature `−1`. -/
theorem hasConstantSectionalCurvature :
    (leviCivitaConnection 𝓘(ℝ, ℂ) ℍ).HasConstantSectionalCurvature
      (isMetricCompatible_leviCivitaConnection 𝓘(ℝ, ℂ)) (-1) :=
  (upperHalfSpaceIsometry.hasConstantSectionalCurvature_iff (-1)).mp
    UpperHalfSpace.hasConstantSectionalCurvature

/-! ### Conjugated Möbius isometries on upper half-space -/

/-- The `GL(2, ℝ)` action on `UpperHalfSpace ℝ` by Riemannian isometries, obtained by conjugating
the Möbius action on `ℍ` along `upperHalfSpaceIsometry`. -/
def glHalfSpaceIsomHom :
    GL (Fin 2) ℝ →* Isom 𝓘(ℝ, WithLp 2 (ℝ × ℝ)) (UpperHalfSpace ℝ) :=
  upperHalfSpaceIsometry.conjMulEquiv.toMonoidHom.comp glIsomHom

/-- Evaluation of the conjugated `GL(2, ℝ)` Riemannian isometry on `UpperHalfSpace ℝ`. -/
@[simp]
theorem glHalfSpaceIsomHom_apply (g : GL (Fin 2) ℝ) (p : UpperHalfSpace ℝ) :
    glHalfSpaceIsomHom g p = upperHalfSpaceIsometry (g • upperHalfSpaceIsometry.symm p) := by
  rw [glHalfSpaceIsomHom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    RiemannianIsometry.conjMulEquiv_apply, glIsomHom_apply]

/-- The faithful `PGL(2, ℝ)` action on `UpperHalfSpace ℝ` by Riemannian isometries, obtained by
conjugating the Möbius action on `ℍ` along `upperHalfSpaceIsometry`. -/
def pglHalfSpaceIsomHom :
    PGL(2, ℝ) →* Isom 𝓘(ℝ, WithLp 2 (ℝ × ℝ)) (UpperHalfSpace ℝ) :=
  upperHalfSpaceIsometry.conjMulEquiv.toMonoidHom.comp pglIsomHom

/-- Evaluation of the conjugated `PGL(2, ℝ)` Riemannian isometry on `UpperHalfSpace ℝ`. -/
@[simp]
theorem pglHalfSpaceIsomHom_apply (q : PGL(2, ℝ)) (p : UpperHalfSpace ℝ) :
    pglHalfSpaceIsomHom q p = upperHalfSpaceIsometry (q • upperHalfSpaceIsometry.symm p) := by
  rw [pglHalfSpaceIsomHom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    RiemannianIsometry.conjMulEquiv_apply, pglIsomHom_apply]

/-- The conjugated `PGL(2, ℝ)` homomorphism agrees with `glHalfSpaceIsomHom` on representatives. -/
@[simp]
theorem pglHalfSpaceIsomHom_mk (g : GL (Fin 2) ℝ) :
    pglHalfSpaceIsomHom (Matrix.ProjGenLinGroup.mk g) = glHalfSpaceIsomHom g := by
  rw [pglHalfSpaceIsomHom, glHalfSpaceIsomHom, MonoidHom.comp_apply, MonoidHom.comp_apply,
    pglIsomHom_mk]

/-- The conjugated `PGL(2, ℝ)` action on `UpperHalfSpace ℝ` by Riemannian isometries is
faithful. -/
theorem pglHalfSpaceIsomHom_injective : Function.Injective pglHalfSpaceIsomHom :=
  upperHalfSpaceIsometry.conjMulEquiv.injective.comp pglIsomHom_injective

/-- The faithful `PSL(2, ℝ)` action on `UpperHalfSpace ℝ` by Riemannian isometries, obtained by
conjugating the Möbius action on `ℍ` along `upperHalfSpaceIsometry`. -/
def pslHalfSpaceIsomHom :
    PSL(2, ℝ) →* Isom 𝓘(ℝ, WithLp 2 (ℝ × ℝ)) (UpperHalfSpace ℝ) :=
  upperHalfSpaceIsometry.conjMulEquiv.toMonoidHom.comp pslIsomHom

/-- Evaluation of the conjugated `PSL(2, ℝ)` Riemannian isometry on `UpperHalfSpace ℝ`. -/
@[simp]
theorem pslHalfSpaceIsomHom_apply (q : PSL(2, ℝ)) (p : UpperHalfSpace ℝ) :
    pslHalfSpaceIsomHom q p = upperHalfSpaceIsometry (q • upperHalfSpaceIsometry.symm p) := by
  rw [pslHalfSpaceIsomHom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    RiemannianIsometry.conjMulEquiv_apply, pslIsomHom_apply]

/-- Restricting `pglHalfSpaceIsomHom` along `toPGL` recovers `pslHalfSpaceIsomHom`. -/
@[simp]
theorem pglHalfSpaceIsomHom_toPGL (q : PSL(2, ℝ)) :
    pglHalfSpaceIsomHom (Matrix.ProjectiveSpecialLinearGroup.toPGL q) = pslHalfSpaceIsomHom q := by
  rw [pglHalfSpaceIsomHom, pslHalfSpaceIsomHom, MonoidHom.comp_apply, MonoidHom.comp_apply,
    pglIsomHom_toPGL]

/-- The conjugated `PSL(2, ℝ)` action on `UpperHalfSpace ℝ` by Riemannian isometries is
faithful. -/
theorem pslHalfSpaceIsomHom_injective : Function.Injective pslHalfSpaceIsomHom :=
  upperHalfSpaceIsometry.conjMulEquiv.injective.comp pslIsomHom_injective

/-! ### Metric-space comparison with upper half-space -/

/-- The coordinate identification `x + iy ↦ (x, y)` is a metric-space isometry from `ℍ`
(with Mathlib's hyperbolic distance) to `UpperHalfSpace ℝ` equipped with its intrinsic Riemannian
metric `MetricSpace.ofRiemannianMetric`. -/
def upperHalfSpaceIsometryEquiv :
    letI : MetricSpace (UpperHalfSpace ℝ) :=
      MetricSpace.ofRiemannianMetric 𝓘(ℝ, WithLp 2 (ℝ × ℝ)) (UpperHalfSpace ℝ)
    ℍ ≃ᵢ UpperHalfSpace ℝ :=
  letI : MetricSpace (UpperHalfSpace ℝ) :=
    MetricSpace.ofRiemannianMetric 𝓘(ℝ, WithLp 2 (ℝ × ℝ)) (UpperHalfSpace ℝ)
  (upperHalfSpaceIsometry : ℍ ≃ᵢ UpperHalfSpace ℝ)

/-- Evaluation of the metric-space comparison isometry agrees with `upperHalfSpaceIsometry`. -/
@[simp]
theorem _root_.UpperHalfPlane.upperHalfSpaceIsometryEquiv_apply (z : ℍ) :
    upperHalfSpaceIsometryEquiv z = upperHalfSpaceIsometry z := by
  rfl

/-- Evaluation of the inverse metric-space comparison isometry agrees with
`upperHalfSpaceIsometry.symm`. -/
@[simp]
theorem upperHalfSpaceIsometryEquiv_symm_apply (p : UpperHalfSpace ℝ) :
    letI : MetricSpace (UpperHalfSpace ℝ) :=
      MetricSpace.ofRiemannianMetric 𝓘(ℝ, WithLp 2 (ℝ × ℝ)) (UpperHalfSpace ℝ)
    upperHalfSpaceIsometryEquiv.symm p = upperHalfSpaceIsometry.symm p := by
  let _ : MetricSpace (UpperHalfSpace ℝ) :=
    MetricSpace.ofRiemannianMetric 𝓘(ℝ, WithLp 2 (ℝ × ℝ)) (UpperHalfSpace ℝ)
  exact upperHalfSpaceIsometryEquiv.injective (by simp)

/-- The intrinsic Riemannian extended distance on `UpperHalfSpace ℝ` matches Mathlib's hyperbolic
extended distance on `ℍ` under `upperHalfSpaceIsometry`. -/
theorem _root_.UpperHalfPlane.edist_upperHalfSpaceIsometry_eq (z w : ℍ) :
    letI : MetricSpace (UpperHalfSpace ℝ) :=
      MetricSpace.ofRiemannianMetric 𝓘(ℝ, WithLp 2 (ℝ × ℝ)) (UpperHalfSpace ℝ)
    edist (upperHalfSpaceIsometry z) (upperHalfSpaceIsometry w) = edist z w :=
  let _ : MetricSpace (UpperHalfSpace ℝ) :=
    MetricSpace.ofRiemannianMetric 𝓘(ℝ, WithLp 2 (ℝ × ℝ)) (UpperHalfSpace ℝ)
  upperHalfSpaceIsometryEquiv.edist_eq z w

/-- The intrinsic Riemannian distance on `UpperHalfSpace ℝ` matches Mathlib's hyperbolic distance
on `ℍ` under `upperHalfSpaceIsometry`. -/
theorem _root_.UpperHalfPlane.dist_upperHalfSpaceIsometry_eq (z w : ℍ) :
    letI : MetricSpace (UpperHalfSpace ℝ) :=
      MetricSpace.ofRiemannianMetric 𝓘(ℝ, WithLp 2 (ℝ × ℝ)) (UpperHalfSpace ℝ)
    dist (upperHalfSpaceIsometry z) (upperHalfSpaceIsometry w) = dist z w :=
  let _ : MetricSpace (UpperHalfSpace ℝ) :=
    MetricSpace.ofRiemannianMetric 𝓘(ℝ, WithLp 2 (ℝ × ℝ)) (UpperHalfSpace ℝ)
  upperHalfSpaceIsometryEquiv.dist_eq z w

/-! ### Constant curvature tensor and hyperbolic metric -/

/-- The curvature tensor of the Poincaré metric on `ℍ` is the constant-curvature tensor with
parameter `-1`. -/
@[simp]
theorem _root_.UpperHalfPlane.curvatureTensor_eq (z : ℍ) (u v w : TangentSpace 𝓘(ℝ, ℂ) z) :
    (leviCivitaConnection 𝓘(ℝ, ℂ) ℍ).curvatureTensor z u v w =
      (-1 : ℝ) • (inner ℝ v w • u - inner ℝ u w • v) := by
  let e := upperHalfSpaceIsometry.mfderivToLinearIsometryEquiv z
  apply e.injective
  have he (x : TangentSpace 𝓘(ℝ, ℂ) z) :
      e x = mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, WithLp 2 (ℝ × ℝ)) upperHalfSpaceIsometry z x :=
    upperHalfSpaceIsometry.mfderivToLinearIsometryEquiv_apply z x
  rw [he, upperHalfSpaceIsometry.isLocalRiemannianIsometry.mfderiv_curvatureTensor,
    UpperHalfSpace.curvatureTensor_eq]
  simp only [map_smul, map_sub, he, upperHalfSpaceIsometry.inner_mfderiv]

/-- The Poincaré metric on `ℍ`, packaged with its metric completeness and constant curvature
`-1` as a `TauCeti.HyperbolicMetric`. -/
def poincareHyperbolicMetric : HyperbolicMetric (I := 𝓘(ℝ, ℂ)) (M := ℍ) where
  metric := poincareRiemannianMetric
  complete := completeSpace_of_riemannianMetric
  curvature := by
    rw [ContMDiffRiemannianMetric.isConstantCurvatureTensor_iff]
    exact _root_.UpperHalfPlane.curvatureTensor_eq

/-- The underlying Riemannian metric of `poincareHyperbolicMetric` is `poincareRiemannianMetric`. -/
@[simp]
theorem poincareHyperbolicMetric_metric :
    poincareHyperbolicMetric.metric = poincareRiemannianMetric := by
  rfl

/-- The complex upper half-plane `ℍ` is a hyperbolic manifold. -/
theorem isHyperbolic : IsHyperbolic (I := 𝓘(ℝ, ℂ)) (M := ℍ) :=
  TauCeti.isHyperbolic_iff.mpr ⟨poincareHyperbolicMetric⟩

end TauCeti.UpperHalfPlane

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Euclidean.Prod
public import TauCeti.Analysis.Complex.UpperHalfPlane.Riemannian.Distance
public import TauCeti.Geometry.Manifold.Riemannian.Hyperbolic
public import TauCeti.Geometry.Manifold.Riemannian.Hyperbolic.UpperHalfSpace.Curvature
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Congr
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Curvature
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Distance
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic

/-!
# The upper half-plane and half-space metrics

The coordinate map `x + iy ↦ (x, y)` identifies the Poincaré metric on the complex upper
half-plane with the two-dimensional upper half-space metric. The identification is a
Riemannian isometry (`TauCeti.UpperHalfPlane.upperHalfSpaceIsometry`): its differential preserves
the Euclidean inner product and its base map preserves height, so both tensors are the same
Euclidean tensor divided by squared height.

Once `TauCeti.isRiemannianManifold_upperHalfPlane` identifies Mathlib's hyperbolic distance on `ℍ`
with the Riemannian distance of the Poincaré metric, `upperHalfSpaceIsometry` upgrades to:

* **Transported isometry-group actions (`glToUpperHalfSpaceIsom`, `pglToUpperHalfSpaceIsom`,
  `slToUpperHalfSpaceIsom`, `pslToUpperHalfSpaceIsom`):** conjugating `glToIsom` along
  `upperHalfSpaceIsometry.isomCongr` transports the `GL(2, ℝ)`, `PGL(2, ℝ)`, `SL(2, R)`, and
  `PSL(2, R)` actions to smooth Riemannian isometries of `UpperHalfSpace ℝ`.
* **Metric comparison (`upperHalfSpaceIsometryEquiv`):** equipping `UpperHalfSpace ℝ` with
  `TauCeti.MetricSpace.ofRiemannianMetric`, `upperHalfSpaceIsometry` induces an isometric
  equivalence `ℍ ≃ᵢ UpperHalfSpace ℝ` with Mathlib's hyperbolic metric on `ℍ`.
* **Curvature and `HyperbolicMetric` (`UpperHalfPlane.curvatureTensor_eq`,
  `TauCeti.UpperHalfPlane.hyperbolicMetric`, `TauCeti.UpperHalfPlane.isHyperbolic`):** transporting
  the half-space curvature tensor along `upperHalfSpaceIsometry` proves that the Poincaré metric has
  constant curvature `−1`, and combining this with completeness packages it as a
  `TauCeti.HyperbolicMetric`.

## Main definitions

* `TauCeti.UpperHalfPlane.upperHalfSpaceIsometry`: the smooth Riemannian isometry
  `ℍ → UpperHalfSpace ℝ` given by `x + iy ↦ (x, y)`.
* `TauCeti.UpperHalfPlane.hyperbolicMetric`: the Poincaré metric on `ℍ` packaged as a
  `TauCeti.HyperbolicMetric`.
* `TauCeti.UpperHalfPlane.glToUpperHalfSpaceIsom`, `pglToUpperHalfSpaceIsom`,
  `slToUpperHalfSpaceIsom`, `pslToUpperHalfSpaceIsom`: transported homomorphisms from `GL(2, ℝ)`,
  `PGL(2, ℝ)`, `SL(2, R)`, and `PSL(2, R)` into `Isom 𝓘(ℝ, WithLp 2 (ℝ × ℝ)) (UpperHalfSpace ℝ)`.
* `TauCeti.UpperHalfPlane.upperHalfSpaceIsometryEquiv`: the metric equivalence
  `ℍ ≃ᵢ UpperHalfSpace ℝ` when `UpperHalfSpace ℝ` carries `TauCeti.MetricSpace.ofRiemannianMetric`.

## Main results

* `TauCeti.UpperHalfPlane.hasConstantSectionalCurvature` and
  `UpperHalfPlane.curvatureTensor_eq`: constant curvature `−1` of the Poincaré metric.
* `TauCeti.UpperHalfPlane.isHyperbolic`: `IsHyperbolic (I := 𝓘(ℝ, ℂ)) (M := ℍ)`.
* `UpperHalfPlane.riemannianEDist_upperHalfSpaceIsometry` and
  `TauCeti.UpperHalfPlane.riemannianEDist_upperHalfSpace_eq_edist_symm`: comparison of Mathlib's
  hyperbolic distance on `ℍ` with `riemannianEDist` on `UpperHalfSpace ℝ`.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 3
  (the upper half-plane and upper half-space models).
* Svetlana Katok, *Fuchsian Groups*, University of Chicago Press (1992), §§1.1–1.2.
-/

public section

open Bundle Manifold CovariantDerivative
open scoped ContDiff Manifold UpperHalfPlane

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

open scoped MatrixGroups

/-- The Poincaré metric on the upper half-plane has constant sectional curvature `−1`. -/
theorem hasConstantSectionalCurvature :
    (leviCivitaConnection 𝓘(ℝ, ℂ) ℍ).HasConstantSectionalCurvature
      (isMetricCompatible_leviCivitaConnection 𝓘(ℝ, ℂ)) (-1) :=
  (upperHalfSpaceIsometry.hasConstantSectionalCurvature_iff (-1)).mp
    UpperHalfSpace.hasConstantSectionalCurvature

/-- The Riemann curvature tensor of the Poincaré metric on `ℍ` is the constant-curvature tensor
with parameter `−1`. -/
@[simp]
theorem _root_.UpperHalfPlane.curvatureTensor_eq (z : ℍ)
    (u v w : TangentSpace 𝓘(ℝ, ℂ) z) :
    (leviCivitaConnection 𝓘(ℝ, ℂ) ℍ).curvatureTensor z u v w =
      (-1 : ℝ) • (inner ℝ v w • u - inner ℝ u w • v) := by
  apply (upperHalfSpaceIsometry.mfderivToLinearIsometryEquiv z).injective
  rw [upperHalfSpaceIsometry.mfderivToLinearIsometryEquiv_apply,
    upperHalfSpaceIsometry.isLocalRiemannianIsometry.mfderiv_curvatureTensor,
    UpperHalfSpace.curvatureTensor_eq, upperHalfSpaceIsometry.inner_mfderiv,
    upperHalfSpaceIsometry.inner_mfderiv,
    upperHalfSpaceIsometry.mfderivToLinearIsometryEquiv_apply]
  simp [map_smul, map_sub]

/-- The Poincaré metric on `ℍ` packaged as a complete smooth metric of constant curvature `−1`. -/
def hyperbolicMetric : HyperbolicMetric (I := 𝓘(ℝ, ℂ)) (M := ℍ) where
  metric := poincareRiemannianMetric
  complete := completeSpace_of_riemannianMetric
  curvature :=
    (ContMDiffRiemannianMetric.isConstantCurvatureTensor_iff_of_riemannianBundle_eq rfl (-1)).2
      _root_.UpperHalfPlane.curvatureTensor_eq

/-- The underlying smooth metric of `TauCeti.UpperHalfPlane.hyperbolicMetric` is
`poincareRiemannianMetric`. -/
@[simp]
theorem hyperbolicMetric_metric : hyperbolicMetric.metric = poincareRiemannianMetric := (rfl)

/-- The complex upper half-plane with its real smooth manifold structure admits a complete
hyperbolic metric. -/
theorem isHyperbolic : IsHyperbolic (I := 𝓘(ℝ, ℂ)) (M := ℍ) :=
  TauCeti.isHyperbolic_iff.mpr ⟨hyperbolicMetric⟩

/-! ### Transported matrix-group actions on `UpperHalfSpace ℝ` -/

/-- The group homomorphism from `GL(2, ℝ)` into the Riemannian isometry group of
`UpperHalfSpace ℝ`, obtained by conjugating `glToIsom` along `upperHalfSpaceIsometry`. -/
def glToUpperHalfSpaceIsom :
    GL (Fin 2) ℝ →* Isom 𝓘(ℝ, WithLp 2 (ℝ × ℝ)) (UpperHalfSpace ℝ) :=
  upperHalfSpaceIsometry.isomCongr.toMonoidHom.comp glToIsom

/-- Pointwise formula for `glToUpperHalfSpaceIsom` on `UpperHalfSpace ℝ`. -/
@[simp]
theorem glToUpperHalfSpaceIsom_apply (g : GL (Fin 2) ℝ) (p : UpperHalfSpace ℝ) :
    glToUpperHalfSpaceIsom g p = upperHalfSpaceIsometry (g • upperHalfSpaceIsometry.symm p) := by
  simp [glToUpperHalfSpaceIsom]

/-- `upperHalfSpaceIsometry` intertwines the `GL(2, ℝ)` action on `ℍ` with
`glToUpperHalfSpaceIsom`. -/
theorem _root_.UpperHalfPlane.glToUpperHalfSpaceIsom_apply_upperHalfSpaceIsometry
    (z : ℍ) (g : GL (Fin 2) ℝ) :
    glToUpperHalfSpaceIsom g (upperHalfSpaceIsometry z) = upperHalfSpaceIsometry (g • z) := by
  simp

/-- The group homomorphism from `PGL(2, ℝ)` into the Riemannian isometry group of
`UpperHalfSpace ℝ`, obtained by conjugating `pglToIsom` along `upperHalfSpaceIsometry`. -/
def pglToUpperHalfSpaceIsom :
    PGL(2, ℝ) →* Isom 𝓘(ℝ, WithLp 2 (ℝ × ℝ)) (UpperHalfSpace ℝ) :=
  upperHalfSpaceIsometry.isomCongr.toMonoidHom.comp pglToIsom

/-- Pointwise formula for `pglToUpperHalfSpaceIsom` on `UpperHalfSpace ℝ`. -/
@[simp]
theorem pglToUpperHalfSpaceIsom_apply (q : PGL(2, ℝ)) (p : UpperHalfSpace ℝ) :
    pglToUpperHalfSpaceIsom q p = upperHalfSpaceIsometry (q • upperHalfSpaceIsometry.symm p) := by
  simp [pglToUpperHalfSpaceIsom]

/-- `upperHalfSpaceIsometry` intertwines the `PGL(2, ℝ)` action on `ℍ` with
`pglToUpperHalfSpaceIsom`. -/
theorem _root_.UpperHalfPlane.pglToUpperHalfSpaceIsom_apply_upperHalfSpaceIsometry
    (z : ℍ) (q : PGL(2, ℝ)) :
    pglToUpperHalfSpaceIsom q (upperHalfSpaceIsometry z) = upperHalfSpaceIsometry (q • z) := by
  simp

/-- `pglToUpperHalfSpaceIsom` extends `glToUpperHalfSpaceIsom` along `GL(2, ℝ) →* PGL(2, ℝ)`. -/
@[simp]
theorem pglToUpperHalfSpaceIsom_mk (g : GL (Fin 2) ℝ) :
    pglToUpperHalfSpaceIsom (Matrix.ProjGenLinGroup.mk g) = glToUpperHalfSpaceIsom g := by
  simp [pglToUpperHalfSpaceIsom, glToUpperHalfSpaceIsom]

/-- `PGL(2, ℝ)` embeds faithfully into the Riemannian isometry group of `UpperHalfSpace ℝ`. -/
theorem pglToUpperHalfSpaceIsom_injective : Function.Injective pglToUpperHalfSpaceIsom :=
  upperHalfSpaceIsometry.isomCongr.injective.comp pglToIsom_injective

/-- The group homomorphism from `SL(2, R)` into the Riemannian isometry group of
`UpperHalfSpace ℝ`, obtained by conjugating `slToIsom` along `upperHalfSpaceIsometry`. -/
def slToUpperHalfSpaceIsom {R : Type*} [CommRing R] [Algebra R ℝ] :
    SL(2, R) →* Isom 𝓘(ℝ, WithLp 2 (ℝ × ℝ)) (UpperHalfSpace ℝ) :=
  upperHalfSpaceIsometry.isomCongr.toMonoidHom.comp slToIsom

/-- Pointwise formula for `slToUpperHalfSpaceIsom` on `UpperHalfSpace ℝ`. -/
@[simp]
theorem slToUpperHalfSpaceIsom_apply {R : Type*} [CommRing R] [Algebra R ℝ]
    (g : SL(2, R)) (p : UpperHalfSpace ℝ) :
    slToUpperHalfSpaceIsom g p = upperHalfSpaceIsometry (g • upperHalfSpaceIsometry.symm p) := by
  simp [slToUpperHalfSpaceIsom]

/-- `upperHalfSpaceIsometry` intertwines the `SL(2, R)` action on `ℍ` with
`slToUpperHalfSpaceIsom`. -/
theorem _root_.UpperHalfPlane.slToUpperHalfSpaceIsom_apply_upperHalfSpaceIsometry
    {R : Type*} [CommRing R] [Algebra R ℝ] (z : ℍ) (g : SL(2, R)) :
    slToUpperHalfSpaceIsom g (upperHalfSpaceIsometry z) = upperHalfSpaceIsometry (g • z) := by
  simp

/-- The group homomorphism from `PSL(2, R)` into the Riemannian isometry group of
`UpperHalfSpace ℝ`, obtained by conjugating `pslToIsom` along `upperHalfSpaceIsometry`. -/
def pslToUpperHalfSpaceIsom {R : Type*} [CommRing R] [Algebra R ℝ] :
    PSL(2, R) →* Isom 𝓘(ℝ, WithLp 2 (ℝ × ℝ)) (UpperHalfSpace ℝ) :=
  upperHalfSpaceIsometry.isomCongr.toMonoidHom.comp pslToIsom

/-- Pointwise formula for `pslToUpperHalfSpaceIsom` on `UpperHalfSpace ℝ`. -/
@[simp]
theorem pslToUpperHalfSpaceIsom_apply {R : Type*} [CommRing R] [Algebra R ℝ]
    (q : PSL(2, R)) (p : UpperHalfSpace ℝ) :
    pslToUpperHalfSpaceIsom q p = upperHalfSpaceIsometry (q • upperHalfSpaceIsometry.symm p) := by
  simp [pslToUpperHalfSpaceIsom]

/-- `upperHalfSpaceIsometry` intertwines the `PSL(2, R)` action on `ℍ` with
`pslToUpperHalfSpaceIsom`. -/
theorem _root_.UpperHalfPlane.pslToUpperHalfSpaceIsom_apply_upperHalfSpaceIsometry
    {R : Type*} [CommRing R] [Algebra R ℝ] (z : ℍ) (q : PSL(2, R)) :
    pslToUpperHalfSpaceIsom q (upperHalfSpaceIsometry z) = upperHalfSpaceIsometry (q • z) := by
  simp

/-- `pslToUpperHalfSpaceIsom` sends the class of `g : SL(2, R)` to `slToUpperHalfSpaceIsom g`. -/
@[simp]
theorem pslToUpperHalfSpaceIsom_mk {R : Type*} [CommRing R] [Algebra R ℝ] (g : SL(2, R)) :
    pslToUpperHalfSpaceIsom (g : PSL(2, R)) = slToUpperHalfSpaceIsom g := by
  simp [pslToUpperHalfSpaceIsom, slToUpperHalfSpaceIsom]

/-- Whenever `PSL(2, R)` acts faithfully on `ℍ`, `pslToUpperHalfSpaceIsom` is injective. -/
theorem pslToUpperHalfSpaceIsom_injective {R : Type*} [CommRing R] [Algebra R ℝ]
    [FaithfulSMul PSL(2, R) ℍ] : Function.Injective (pslToUpperHalfSpaceIsom (R := R)) :=
  upperHalfSpaceIsometry.isomCongr.injective.comp pslToIsom_injective

/-! ### Metric comparison between `ℍ` and `UpperHalfSpace ℝ` -/

/-- `upperHalfSpaceIsometry` carries Mathlib's `edist` on `ℍ` to the Riemannian extended distance
on `UpperHalfSpace ℝ`. -/
theorem _root_.UpperHalfPlane.riemannianEDist_upperHalfSpaceIsometry (z w : ℍ) :
    Manifold.riemannianEDist 𝓘(ℝ, WithLp 2 (ℝ × ℝ))
        (upperHalfSpaceIsometry z) (upperHalfSpaceIsometry w) = edist z w := by
  rw [upperHalfSpaceIsometry.riemannianEDist_eq, z.riemannianEDist_eq_edist w]

/-- The real value of the Riemannian extended distance between `upperHalfSpaceIsometry z` and
`upperHalfSpaceIsometry w` is Mathlib's hyperbolic `dist z w`. -/
theorem _root_.UpperHalfPlane.toReal_riemannianEDist_upperHalfSpaceIsometry (z w : ℍ) :
    (Manifold.riemannianEDist 𝓘(ℝ, WithLp 2 (ℝ × ℝ))
        (upperHalfSpaceIsometry z) (upperHalfSpaceIsometry w)).toReal = dist z w := by
  rw [z.riemannianEDist_upperHalfSpaceIsometry w, dist_edist]

/-- The Riemannian extended distance on `UpperHalfSpace ℝ` equals Mathlib's `edist` pulled back
along `upperHalfSpaceIsometry.symm`. -/
theorem riemannianEDist_upperHalfSpace_eq_edist_symm (p q : UpperHalfSpace ℝ) :
    Manifold.riemannianEDist 𝓘(ℝ, WithLp 2 (ℝ × ℝ)) p q =
      edist (upperHalfSpaceIsometry.symm p) (upperHalfSpaceIsometry.symm q) := by
  rw [← (upperHalfSpaceIsometry.symm p).riemannianEDist_upperHalfSpaceIsometry
    (upperHalfSpaceIsometry.symm q), upperHalfSpaceIsometry.apply_symm_apply,
    upperHalfSpaceIsometry.apply_symm_apply]

/-- Equipping `UpperHalfSpace ℝ` with its Riemannian metric-space structure
`TauCeti.MetricSpace.ofRiemannianMetric`, the coordinate identification `upperHalfSpaceIsometry` is
an isometric equivalence `ℍ ≃ᵢ UpperHalfSpace ℝ` with Mathlib's hyperbolic metric on `ℍ`. -/
def upperHalfSpaceIsometryEquiv :
    letI : MetricSpace (UpperHalfSpace ℝ) :=
      MetricSpace.ofRiemannianMetric 𝓘(ℝ, WithLp 2 (ℝ × ℝ)) (UpperHalfSpace ℝ)
    ℍ ≃ᵢ UpperHalfSpace ℝ :=
  letI : MetricSpace (UpperHalfSpace ℝ) :=
    MetricSpace.ofRiemannianMetric 𝓘(ℝ, WithLp 2 (ℝ × ℝ)) (UpperHalfSpace ℝ)
  (upperHalfSpaceIsometry : ℍ ≃ᵢ UpperHalfSpace ℝ)

/-- `upperHalfSpaceIsometryEquiv` has the same forward map as `upperHalfSpaceIsometry`. -/
@[simp]
theorem _root_.UpperHalfPlane.upperHalfSpaceIsometryEquiv_apply (z : ℍ) :
    (letI : MetricSpace (UpperHalfSpace ℝ) :=
      MetricSpace.ofRiemannianMetric 𝓘(ℝ, WithLp 2 (ℝ × ℝ)) (UpperHalfSpace ℝ)
    upperHalfSpaceIsometryEquiv z) = upperHalfSpaceIsometry z := (rfl)

/-- `upperHalfSpaceIsometryEquiv.symm` has the same map as `upperHalfSpaceIsometry.symm`. -/
@[simp]
theorem upperHalfSpaceIsometryEquiv_symm_apply (p : UpperHalfSpace ℝ) :
    (letI : MetricSpace (UpperHalfSpace ℝ) :=
      MetricSpace.ofRiemannianMetric 𝓘(ℝ, WithLp 2 (ℝ × ℝ)) (UpperHalfSpace ℝ)
    upperHalfSpaceIsometryEquiv.symm p) = upperHalfSpaceIsometry.symm p := by
  let _ : MetricSpace (UpperHalfSpace ℝ) :=
    MetricSpace.ofRiemannianMetric 𝓘(ℝ, WithLp 2 (ℝ × ℝ)) (UpperHalfSpace ℝ)
  rw [upperHalfSpaceIsometryEquiv, ← RiemannianIsometry.toIsometryEquiv_symm]
  rfl

end TauCeti.UpperHalfPlane

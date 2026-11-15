/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Euclidean.Prod
public import TauCeti.Analysis.Complex.UpperHalfPlane.PoincareMetric
public import TauCeti.Geometry.Manifold.Riemannian.Hyperbolic.UpperHalfSpace.Metric
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Congr
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Curvature
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic

/-!
# The upper half-plane and half-space metrics

The coordinate map `x + iy ↦ (x, y)` identifies the Poincaré metric on the complex upper
half-plane with the two-dimensional upper half-space metric. The identification is a
Riemannian isometry: its differential preserves the Euclidean inner product and its base map
preserves height, so both tensors are the same Euclidean tensor divided by squared height.

`TauCeti.UpperHalfPlane.upperHalfSpaceIsometry` gives this identification without changing
Mathlib's distance on the upper half-plane or installing a distance on the half-space. From it we
derive:

* **Conjugated isometry actions** (`glToUpperHalfSpaceIsom`, `pglToUpperHalfSpaceIsom`,
  `pslToUpperHalfSpaceIsom`): conjugating `glToIsom`, `pglToIsom`, and `pslToIsom` through
  `RiemannianIsometry.isomCongr upperHalfSpaceIsometry` carries the Möbius and reflection actions
  on `ℍ` to Riemannian self-isometries of `UpperHalfSpace ℝ`.
* **Comparison metric isometry** (`upperHalfSpaceIsometryEquiv`): equipping `UpperHalfSpace ℝ`
  with `MetricSpace.ofRiemannianMetric 𝓘(ℝ, WithLp 2 (ℝ × ℝ)) (UpperHalfSpace ℝ)`, the coordinate
  map becomes a metric equivalence `ℍ ≃ᵢ UpperHalfSpace ℝ` from Mathlib's `dist` to the half-space
  Riemannian distance (`dist_upperHalfSpace_one_two` checks that `(0, 1)` and `(0, 2)` are at
  distance `Real.log 2`).
* **Curvature and `HyperbolicMetric` package** (`curvatureTensor_eq`, `ricciTensor_eq`,
  `scalarCurvature_eq`, `hasConstantSectionalCurvature`, `hyperbolicMetric`, `isHyperbolic`):
  transporting the half-space curvature tensor along `upperHalfSpaceIsometry` and combining with
  `completeSpace_of_riemannianMetric` packages `poincareRiemannianMetric` as a complete hyperbolic
  metric on `ℍ`.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 3
  and Theorem 8.34.
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

/-! ### Conjugated `GL(2, ℝ)`, `PGL(2, ℝ)`, and `PSL(2, R)` actions on half-space -/

/-- Conjugation by `upperHalfSpaceIsometry` carries the `GL(2, ℝ)` action on `ℍ` to Riemannian
isometries of `UpperHalfSpace ℝ`. -/
def glToUpperHalfSpaceIsom : GL (Fin 2) ℝ →* Isom 𝓘(ℝ, WithLp 2 (ℝ × ℝ)) (UpperHalfSpace ℝ) :=
  upperHalfSpaceIsometry.isomCongr.toMonoidHom.comp glToIsom

/-- `glToUpperHalfSpaceIsom g` acts on half-space by conjugating `g • ·` across
`upperHalfSpaceIsometry`. -/
@[simp]
theorem glToUpperHalfSpaceIsom_apply (g : GL (Fin 2) ℝ) (p : UpperHalfSpace ℝ) :
    glToUpperHalfSpaceIsom g p = upperHalfSpaceIsometry (g • upperHalfSpaceIsometry.symm p) := by
  simp [glToUpperHalfSpaceIsom]

/-- Conjugation by `upperHalfSpaceIsometry` carries the faithful `PGL(2, ℝ)` action on `ℍ` to
Riemannian isometries of `UpperHalfSpace ℝ`. -/
def pglToUpperHalfSpaceIsom : PGL(2, ℝ) →* Isom 𝓘(ℝ, WithLp 2 (ℝ × ℝ)) (UpperHalfSpace ℝ) :=
  upperHalfSpaceIsometry.isomCongr.toMonoidHom.comp pglToIsom

/-- `pglToUpperHalfSpaceIsom q` acts on half-space by conjugating `q • ·` across
`upperHalfSpaceIsometry`. -/
@[simp]
theorem pglToUpperHalfSpaceIsom_apply (q : PGL(2, ℝ)) (p : UpperHalfSpace ℝ) :
    pglToUpperHalfSpaceIsom q p = upperHalfSpaceIsometry (q • upperHalfSpaceIsometry.symm p) := by
  simp [pglToUpperHalfSpaceIsom]

/-- `PGL(2, ℝ)` embeds faithfully into the Riemannian isometry group of `UpperHalfSpace ℝ`. -/
theorem pglToUpperHalfSpaceIsom_injective : Function.Injective pglToUpperHalfSpaceIsom :=
  upperHalfSpaceIsometry.isomCongr.injective.comp pglToIsom_injective

/-- On the class of `g : GL(2, ℝ)`, `pglToUpperHalfSpaceIsom` agrees with
`glToUpperHalfSpaceIsom g`. -/
@[simp]
theorem pglToUpperHalfSpaceIsom_mk (g : GL (Fin 2) ℝ) :
    pglToUpperHalfSpaceIsom (Matrix.ProjGenLinGroup.mk g) = glToUpperHalfSpaceIsom g := by
  ext p
  simp

/-- Conjugation by `upperHalfSpaceIsometry` carries the `PSL(2, R)` action on `ℍ` to Riemannian
isometries of `UpperHalfSpace ℝ`. -/
def pslToUpperHalfSpaceIsom {R : Type*} [CommRing R] [Algebra R ℝ] :
    PSL(2, R) →* Isom 𝓘(ℝ, WithLp 2 (ℝ × ℝ)) (UpperHalfSpace ℝ) :=
  upperHalfSpaceIsometry.isomCongr.toMonoidHom.comp pslToIsom

/-- `pslToUpperHalfSpaceIsom q` acts on half-space by conjugating `q • ·` across
`upperHalfSpaceIsometry`. -/
@[simp]
theorem pslToUpperHalfSpaceIsom_apply {R : Type*} [CommRing R] [Algebra R ℝ]
    (q : PSL(2, R)) (p : UpperHalfSpace ℝ) :
    pslToUpperHalfSpaceIsom q p = upperHalfSpaceIsometry (q • upperHalfSpaceIsometry.symm p) := by
  simp [pslToUpperHalfSpaceIsom]

/-- Whenever `PSL(2, R)` acts faithfully on `ℍ` (for instance `R = ℝ` or `R = ℤ`), it embeds
faithfully into the Riemannian isometry group of `UpperHalfSpace ℝ`. -/
theorem pslToUpperHalfSpaceIsom_injective {R : Type*} [CommRing R] [Algebra R ℝ]
    [FaithfulSMul PSL(2, R) ℍ] :
    Function.Injective (pslToUpperHalfSpaceIsom (R := R)) :=
  upperHalfSpaceIsometry.isomCongr.injective.comp pslToIsom_injective

/-! ### The comparison metric isometry `ℍ ≃ᵢ UpperHalfSpace ℝ` -/

/-- Equipping `UpperHalfSpace ℝ` with its Riemannian metric-space structure
`MetricSpace.ofRiemannianMetric 𝓘(ℝ, WithLp 2 (ℝ × ℝ)) (UpperHalfSpace ℝ)`, the coordinate
identification `upperHalfSpaceIsometry` becomes a metric isometry equivalence from Mathlib's
hyperbolic metric on `ℍ` to the half-space Riemannian distance. -/
def upperHalfSpaceIsometryEquiv :
    letI : MetricSpace (UpperHalfSpace ℝ) :=
      MetricSpace.ofRiemannianMetric 𝓘(ℝ, WithLp 2 (ℝ × ℝ)) (UpperHalfSpace ℝ)
    ℍ ≃ᵢ UpperHalfSpace ℝ :=
  letI : MetricSpace (UpperHalfSpace ℝ) :=
    MetricSpace.ofRiemannianMetric 𝓘(ℝ, WithLp 2 (ℝ × ℝ)) (UpperHalfSpace ℝ)
  (upperHalfSpaceIsometry : ℍ ≃ᵢ UpperHalfSpace ℝ)

/-- `upperHalfSpaceIsometryEquiv` has the same forward map as `upperHalfSpaceIsometry`. -/
@[simp]
theorem upperHalfSpaceIsometryEquiv_apply (z : ℍ) :
    letI : MetricSpace (UpperHalfSpace ℝ) :=
      MetricSpace.ofRiemannianMetric 𝓘(ℝ, WithLp 2 (ℝ × ℝ)) (UpperHalfSpace ℝ)
    upperHalfSpaceIsometryEquiv z = upperHalfSpaceIsometry z :=
  (rfl)

/-- `upperHalfSpaceIsometryEquiv.symm` has the same inverse map as `upperHalfSpaceIsometry.symm`. -/
@[simp]
theorem upperHalfSpaceIsometryEquiv_symm_apply (p : UpperHalfSpace ℝ) :
    letI : MetricSpace (UpperHalfSpace ℝ) :=
      MetricSpace.ofRiemannianMetric 𝓘(ℝ, WithLp 2 (ℝ × ℝ)) (UpperHalfSpace ℝ)
    upperHalfSpaceIsometryEquiv.symm p = upperHalfSpaceIsometry.symm p := by
  let _ : MetricSpace (UpperHalfSpace ℝ) :=
    MetricSpace.ofRiemannianMetric 𝓘(ℝ, WithLp 2 (ℝ × ℝ)) (UpperHalfSpace ℝ)
  exact DFunLike.congr_fun upperHalfSpaceIsometry.toIsometryEquiv_symm.symm p

/-- In `MetricSpace.ofRiemannianMetric 𝓘(ℝ, WithLp 2 (ℝ × ℝ)) (UpperHalfSpace ℝ)`, the vertical
pair `(0, 1)` and `(0, 2)` is at Riemannian distance `Real.log 2`, matching `dist_I_two_smul_I`
across `upperHalfSpaceIsometryEquiv`. -/
theorem dist_upperHalfSpace_one_two :
    letI : MetricSpace (UpperHalfSpace ℝ) :=
      MetricSpace.ofRiemannianMetric 𝓘(ℝ, WithLp 2 (ℝ × ℝ)) (UpperHalfSpace ℝ)
    dist (UpperHalfSpace.mk (WithLp.toLp 2 ((0 : ℝ), (1 : ℝ))) zero_lt_one)
      (UpperHalfSpace.mk (WithLp.toLp 2 ((0 : ℝ), (2 : ℝ))) zero_lt_two) = Real.log 2 := by
  let _ : MetricSpace (UpperHalfSpace ℝ) :=
    MetricSpace.ofRiemannianMetric 𝓘(ℝ, WithLp 2 (ℝ × ℝ)) (UpperHalfSpace ℝ)
  have h1 : upperHalfSpaceIsometryEquiv _root_.UpperHalfPlane.I =
      UpperHalfSpace.mk (WithLp.toLp 2 ((0 : ℝ), (1 : ℝ))) zero_lt_one := by
    apply UpperHalfSpace.ext
    refine (?_ : _ = WithLp.toLp 2 ((0 : ℝ), (1 : ℝ))).trans (UpperHalfSpace.coe_mk _ _).symm
    simp [_root_.UpperHalfPlane.coe_upperHalfSpaceIsometry_apply]
  have h2 : upperHalfSpaceIsometryEquiv
        ((⟨2, zero_lt_two⟩ : {x : ℝ // 0 < x}) • _root_.UpperHalfPlane.I) =
      UpperHalfSpace.mk (WithLp.toLp 2 ((0 : ℝ), (2 : ℝ))) zero_lt_two := by
    apply UpperHalfSpace.ext
    refine (?_ : _ = WithLp.toLp 2 ((0 : ℝ), (2 : ℝ))).trans (UpperHalfSpace.coe_mk _ _).symm
    simp [_root_.UpperHalfPlane.coe_upperHalfSpaceIsometry_apply]
  have hd := upperHalfSpaceIsometryEquiv.dist_eq _root_.UpperHalfPlane.I
    ((⟨2, zero_lt_two⟩ : {x : ℝ // 0 < x}) • _root_.UpperHalfPlane.I)
  rwa [h1, h2, dist_I_two_smul_I] at hd

/-! ### Curvature tensor and complete `HyperbolicMetric` structure on `ℍ` -/

/-- The Riemann curvature tensor of the Poincaré metric on `ℍ` is the constant-curvature tensor
with parameter `-1`. -/
@[simp]
theorem curvatureTensor_eq (z : ℍ) (u v w : TangentSpace 𝓘(ℝ, ℂ) z) :
    (leviCivitaConnection 𝓘(ℝ, ℂ) ℍ).curvatureTensor z u v w =
      (-1 : ℝ) • (inner ℝ v w • u - inner ℝ u w • v) := by
  have hinj :
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, WithLp 2 (ℝ × ℝ)) upperHalfSpaceIsometry z) :=
    (injective_iff_map_eq_zero _).2 fun t ht ↦
      norm_eq_zero.1 (by rw [← upperHalfSpaceIsometry.norm_mfderiv z t, ht, norm_zero])
  apply hinj
  rw [upperHalfSpaceIsometry.isLocalRiemannianIsometry.mfderiv_curvatureTensor,
    UpperHalfSpace.curvatureTensor_eq, map_smul, map_sub, map_smul, map_smul,
    upperHalfSpaceIsometry.inner_mfderiv, upperHalfSpaceIsometry.inner_mfderiv]

/-- The Ricci tensor of the Poincaré metric on `ℍ` is `-g`. -/
@[simp 1100]
theorem ricciTensor_eq (z : ℍ) (u v : TangentSpace 𝓘(ℝ, ℂ) z) :
    (leviCivitaConnection 𝓘(ℝ, ℂ) ℍ).ricciTensor z u v = -inner ℝ u v := by
  rw [← upperHalfSpaceIsometry.isLocalRiemannianIsometry.ricciTensor_mfderiv,
    UpperHalfSpace.ricciTensor_eq, Module.finrank_self, Nat.cast_one, neg_one_mul,
    upperHalfSpaceIsometry.inner_mfderiv]

/-- The scalar curvature of the Poincaré metric on `ℍ` is `-2`. -/
@[simp]
theorem scalarCurvature_eq (z : ℍ) :
    (leviCivitaConnection 𝓘(ℝ, ℂ) ℍ).scalarCurvature z = -2 := by
  rw [CovariantDerivative.scalarCurvature_eq_of_curvatureTensor_eq_smul_inner_sub _ z (-1)
    (curvatureTensor_eq z), (tangentSpaceCastModel 𝓘(ℝ, ℂ) z).toLinearEquiv.finrank_eq,
    Complex.finrank_real_complex]
  norm_num

/-- The Poincaré metric on `ℍ` packaged as a complete `HyperbolicMetric`. -/
def hyperbolicMetric : HyperbolicMetric (I := 𝓘(ℝ, ℂ)) (M := ℍ) where
  metric := poincareRiemannianMetric
  complete := completeSpace_of_riemannianMetric
  curvature := by
    rw [ContMDiffRiemannianMetric.isConstantCurvatureTensor_iff]
    exact curvatureTensor_eq

/-- Forgetting completeness and curvature recovers `poincareRiemannianMetric`. -/
@[simp]
theorem hyperbolicMetric_metric : hyperbolicMetric.metric = poincareRiemannianMetric := (rfl)

/-- The upper half-plane `ℍ` with its real smooth manifold structure admits a complete hyperbolic
metric. -/
theorem isHyperbolic : IsHyperbolic (I := 𝓘(ℝ, ℂ)) (M := ℍ) :=
  TauCeti.isHyperbolic_iff.mpr ⟨hyperbolicMetric⟩

end TauCeti.UpperHalfPlane

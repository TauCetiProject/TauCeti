/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Euclidean.Prod
public import TauCeti.Analysis.Complex.UpperHalfPlane.Riemannian.Distance
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

Together with the distance comparison `IsRiemannianManifold 𝓘(ℝ, ℂ) ℍ` on the upper half-plane
and the Riemannian `MetricSpace` structure on `UpperHalfSpace ℝ`, this Riemannian isometry has
several consequences:

* **Comparison isometry (`upperHalfSpaceIsometryEquiv`).** `upperHalfSpaceIsometry` upgrades to a
  metric isometry equivalence `ℍ ≃ᵢ UpperHalfSpace ℝ` between Mathlib's hyperbolic distance on `ℍ`
  and the Riemannian distance of `UpperHalfSpace ℝ`, transporting the explicit `cosh` distance
  formula to the two-dimensional half-space.
* **Conjugated `GL(2, ℝ)` action (`glUpperHalfSpaceIsomHom`).** Conjugating by
  `upperHalfSpaceIsometry` carries the Riemannian-isometry actions of `GL(2, ℝ)`, `PGL(2, ℝ)`, and
  `PSL(2, ℝ)` on `ℍ` to Riemannian isometries of `UpperHalfSpace ℝ`.
* **Curvature and `HyperbolicMetric` (`poincareHyperbolicMetric`).** Transporting the curvature
  tensor of `UpperHalfSpace ℝ` proves that the Poincaré metric has constant curvature `-1` in both
  sectional and curvature-tensor form, packaging `poincareRiemannianMetric` with its completeness
  as a `TauCeti.HyperbolicMetric`.

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

/-- The Riemann curvature tensor of the Poincaré metric on `ℍ` satisfies the constant-curvature-`-1`
identity `R(w, u) v = -(⟪u, v⟫ w - ⟪w, v⟫ u)`. -/
theorem _root_.UpperHalfPlane.curvatureTensor_eq (z : ℍ)
    (w u v : TangentSpace 𝓘(ℝ, ℂ) z) :
    (leviCivitaConnection 𝓘(ℝ, ℂ) ℍ).curvatureTensor z w u v =
      (-1 : ℝ) • (inner ℝ u v • w - inner ℝ w v • u) := by
  apply upperHalfSpaceIsometry.isLocalRiemannianIsometry.mfderiv_injective z
  rw [upperHalfSpaceIsometry.isLocalRiemannianIsometry.mfderiv_curvatureTensor,
    UpperHalfSpace.curvatureTensor_eq, map_smul, map_sub, map_smul, map_smul,
    upperHalfSpaceIsometry.inner_mfderiv, upperHalfSpaceIsometry.inner_mfderiv]

/-- The Poincaré metric on the upper half-plane packaged with its completeness and constant
curvature `-1` as a `TauCeti.HyperbolicMetric`. -/
def poincareHyperbolicMetric : HyperbolicMetric (I := 𝓘(ℝ, ℂ)) (M := ℍ) where
  metric := poincareRiemannianMetric
  complete := completeSpace_of_riemannianMetric
  curvature := by
    rw [ContMDiffRiemannianMetric.isConstantCurvatureTensor_iff]
    exact _root_.UpperHalfPlane.curvatureTensor_eq

@[simp]
theorem poincareHyperbolicMetric_metric :
    poincareHyperbolicMetric.metric = poincareRiemannianMetric := (rfl)

/-- The upper half-plane admits a complete smooth metric of constant curvature `-1`. -/
theorem isHyperbolic : IsHyperbolic (I := 𝓘(ℝ, ℂ)) (M := ℍ) :=
  TauCeti.isHyperbolic_iff.mpr ⟨poincareHyperbolicMetric⟩

/-! ### Conjugated `GL(2, ℝ)` action on the two-dimensional upper half-space -/

/-- Conjugation by `upperHalfSpaceIsometry` carries the `GL(2, ℝ)` action on `ℍ` to Riemannian
isometries of `UpperHalfSpace ℝ`. -/
def glUpperHalfSpaceIsomHom :
    GL (Fin 2) ℝ →* Isom 𝓘(ℝ, WithLp 2 (ℝ × ℝ)) (UpperHalfSpace ℝ) :=
  upperHalfSpaceIsometry.isomCongr.toMonoidHom.comp glIsomHom

@[simp]
theorem glUpperHalfSpaceIsomHom_apply_apply (g : GL (Fin 2) ℝ) (p : UpperHalfSpace ℝ) :
    glUpperHalfSpaceIsomHom g p =
      upperHalfSpaceIsometry (g • upperHalfSpaceIsometry.symm p) := by
  simp [glUpperHalfSpaceIsomHom]

/-- `upperHalfSpaceIsometry` intertwines the `GL(2, ℝ)` action on `ℍ` with
`glUpperHalfSpaceIsomHom`. -/
theorem glUpperHalfSpaceIsomHom_apply_upperHalfSpaceIsometry (g : GL (Fin 2) ℝ) (z : ℍ) :
    glUpperHalfSpaceIsomHom g (upperHalfSpaceIsometry z) = upperHalfSpaceIsometry (g • z) := by
  simp

/-- Conjugation by `upperHalfSpaceIsometry` embeds `PGL(2, ℝ)` into the Riemannian isometry group
of `UpperHalfSpace ℝ`. -/
def pglUpperHalfSpaceIsomHom :
    PGL(2, ℝ) →* Isom 𝓘(ℝ, WithLp 2 (ℝ × ℝ)) (UpperHalfSpace ℝ) :=
  upperHalfSpaceIsometry.isomCongr.toMonoidHom.comp pglIsomHom

@[simp]
theorem pglUpperHalfSpaceIsomHom_apply_apply (q : PGL(2, ℝ)) (p : UpperHalfSpace ℝ) :
    pglUpperHalfSpaceIsomHom q p =
      upperHalfSpaceIsometry (q • upperHalfSpaceIsometry.symm p) := by
  simp [pglUpperHalfSpaceIsomHom]

/-- `upperHalfSpaceIsometry` intertwines the `PGL(2, ℝ)` action on `ℍ` with
`pglUpperHalfSpaceIsomHom`. -/
theorem pglUpperHalfSpaceIsomHom_apply_upperHalfSpaceIsometry (q : PGL(2, ℝ)) (z : ℍ) :
    pglUpperHalfSpaceIsomHom q (upperHalfSpaceIsometry z) = upperHalfSpaceIsometry (q • z) := by
  simp

/-- `PGL(2, ℝ)` embeds faithfully into the Riemannian isometry group of `UpperHalfSpace ℝ`. -/
theorem pglUpperHalfSpaceIsomHom_injective : Function.Injective pglUpperHalfSpaceIsomHom :=
  upperHalfSpaceIsometry.isomCongr.injective.comp pglIsomHom_injective

/-- Conjugation by `upperHalfSpaceIsometry` carries the `SL(2, ℝ)` action on `ℍ` to Riemannian
isometries of `UpperHalfSpace ℝ`. -/
def slUpperHalfSpaceIsomHom :
    SL(2, ℝ) →* Isom 𝓘(ℝ, WithLp 2 (ℝ × ℝ)) (UpperHalfSpace ℝ) :=
  upperHalfSpaceIsometry.isomCongr.toMonoidHom.comp slIsomHom

@[simp]
theorem slUpperHalfSpaceIsomHom_apply_apply (g : SL(2, ℝ)) (p : UpperHalfSpace ℝ) :
    slUpperHalfSpaceIsomHom g p =
      upperHalfSpaceIsometry (g • upperHalfSpaceIsometry.symm p) := by
  simp [slUpperHalfSpaceIsomHom]

/-- `upperHalfSpaceIsometry` intertwines the `SL(2, ℝ)` action on `ℍ` with
`slUpperHalfSpaceIsomHom`. -/
theorem slUpperHalfSpaceIsomHom_apply_upperHalfSpaceIsometry (g : SL(2, ℝ)) (z : ℍ) :
    slUpperHalfSpaceIsomHom g (upperHalfSpaceIsometry z) = upperHalfSpaceIsometry (g • z) := by
  simp

/-- Conjugation by `upperHalfSpaceIsometry` embeds `PSL(2, ℝ)` into the Riemannian isometry group
of `UpperHalfSpace ℝ`. -/
def pslUpperHalfSpaceIsomHom :
    PSL(2, ℝ) →* Isom 𝓘(ℝ, WithLp 2 (ℝ × ℝ)) (UpperHalfSpace ℝ) :=
  upperHalfSpaceIsometry.isomCongr.toMonoidHom.comp pslIsomHom

@[simp]
theorem pslUpperHalfSpaceIsomHom_apply_apply (q : PSL(2, ℝ)) (p : UpperHalfSpace ℝ) :
    pslUpperHalfSpaceIsomHom q p =
      upperHalfSpaceIsometry (q • upperHalfSpaceIsometry.symm p) := by
  simp [pslUpperHalfSpaceIsomHom]

/-- `upperHalfSpaceIsometry` intertwines the `PSL(2, ℝ)` action on `ℍ` with
`pslUpperHalfSpaceIsomHom`. -/
theorem pslUpperHalfSpaceIsomHom_apply_upperHalfSpaceIsometry (q : PSL(2, ℝ)) (z : ℍ) :
    pslUpperHalfSpaceIsomHom q (upperHalfSpaceIsometry z) = upperHalfSpaceIsometry (q • z) := by
  simp

/-- `PSL(2, ℝ)` embeds faithfully into the Riemannian isometry group of `UpperHalfSpace ℝ`. -/
theorem pslUpperHalfSpaceIsomHom_injective : Function.Injective pslUpperHalfSpaceIsomHom :=
  upperHalfSpaceIsometry.isomCongr.injective.comp pslIsomHom_injective

/-! ### The metric comparison isometry `ℍ ≃ᵢ UpperHalfSpace ℝ` -/

/-- **The comparison isometry.** Because both `ℍ` and `UpperHalfSpace ℝ` carry their Riemannian
distances (`isRiemannianManifold_upperHalfPlane` and `UpperHalfSpace.instIsRiemannianManifold`),
the Riemannian isometry `upperHalfSpaceIsometry` is a metric isometry equivalence
`ℍ ≃ᵢ UpperHalfSpace ℝ`. -/
def upperHalfSpaceIsometryEquiv : ℍ ≃ᵢ UpperHalfSpace ℝ :=
  upperHalfSpaceIsometry

@[simp]
theorem coe_upperHalfSpaceIsometryEquiv :
    ⇑upperHalfSpaceIsometryEquiv = ⇑upperHalfSpaceIsometry := by
  ext z
  simp [upperHalfSpaceIsometryEquiv]

@[simp]
theorem upperHalfSpaceIsometryEquiv_symm_apply (p : UpperHalfSpace ℝ) :
    upperHalfSpaceIsometryEquiv.symm p = upperHalfSpaceIsometry.symm p := by
  apply upperHalfSpaceIsometry.injective
  simp [← coe_upperHalfSpaceIsometryEquiv]

@[simp]
theorem _root_.UpperHalfPlane.edist_upperHalfSpaceIsometry (z w : ℍ) :
    edist (upperHalfSpaceIsometry z) (upperHalfSpaceIsometry w) = edist z w :=
  upperHalfSpaceIsometryEquiv.isometry z w

@[simp]
theorem _root_.UpperHalfPlane.dist_upperHalfSpaceIsometry (z w : ℍ) :
    dist (upperHalfSpaceIsometry z) (upperHalfSpaceIsometry w) = dist z w :=
  upperHalfSpaceIsometryEquiv.isometry.dist_eq z w

end TauCeti.UpperHalfPlane

namespace TauCeti.UpperHalfSpace

open TauCeti.UpperHalfPlane

@[simp]
theorem edist_upperHalfSpaceIsometry_symm (p q : UpperHalfSpace ℝ) :
    edist (upperHalfSpaceIsometry.symm p) (upperHalfSpaceIsometry.symm q) = edist p q := by
  simpa using upperHalfSpaceIsometryEquiv.symm.isometry p q

@[simp]
theorem dist_upperHalfSpaceIsometry_symm (p q : UpperHalfSpace ℝ) :
    dist (upperHalfSpaceIsometry.symm p) (upperHalfSpaceIsometry.symm q) = dist p q := by
  simpa using upperHalfSpaceIsometryEquiv.symm.isometry.dist_eq p q

/-- Explicit `cosh` formula for the Riemannian distance on the two-dimensional upper half-space,
transported from Mathlib's `UpperHalfPlane.cosh_dist` along `upperHalfSpaceIsometryEquiv`. -/
theorem cosh_dist_real (p q : UpperHalfSpace ℝ) :
    Real.cosh (dist p q) =
      1 + dist (p : WithLp 2 (ℝ × ℝ)) q ^ 2 / (2 * height p * height q) := by
  have heucl : dist ((upperHalfSpaceIsometry.symm p : ℍ) : ℂ) (upperHalfSpaceIsometry.symm q) =
      dist (p : WithLp 2 (ℝ × ℝ)) q := by
    have hcoe (r : UpperHalfSpace ℝ) :
        Complex.equivRealProdLp ((upperHalfSpaceIsometry.symm r : ℍ) : ℂ) = r := by
      have h := congrArg UpperHalfSpace.coe (upperHalfSpaceIsometry.apply_symm_apply r)
      rw [_root_.UpperHalfPlane.coe_upperHalfSpaceIsometry_apply] at h
      simpa [Complex.equivRealProdLp_apply] using h
    rw [← Complex.equivRealProdLp.isometry.dist_eq, hcoe p, hcoe q]
  rw [← dist_upperHalfSpaceIsometry_symm, _root_.UpperHalfPlane.cosh_dist, heucl,
    im_upperHalfSpaceIsometry_symm_apply, im_upperHalfSpaceIsometry_symm_apply]

/-- Two points of `UpperHalfSpace ℝ` with equal horizontal coordinate have Riemannian distance
`dist (Real.log (height p)) (Real.log (height q))`. -/
theorem dist_real_of_fst_eq {p q : UpperHalfSpace ℝ}
    (h : (p : WithLp 2 (ℝ × ℝ)).fst = (q : WithLp 2 (ℝ × ℝ)).fst) :
    dist p q = dist (Real.log (height p)) (Real.log (height q)) := by
  rw [← dist_upperHalfSpaceIsometry_symm, _root_.UpperHalfPlane.dist_of_re_eq,
    im_upperHalfSpaceIsometry_symm_apply, im_upperHalfSpaceIsometry_symm_apply]
  simpa [re_upperHalfSpaceIsometry_symm_apply] using h

end TauCeti.UpperHalfSpace

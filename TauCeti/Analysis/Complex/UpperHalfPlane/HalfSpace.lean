/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Euclidean.Prod
public import TauCeti.Analysis.Complex.UpperHalfPlane.PoincareMetric.Basic
public import TauCeti.Analysis.Complex.UpperHalfPlane.PoincareMetric.Distance
public import TauCeti.Geometry.Manifold.Riemannian.Hyperbolic
public import TauCeti.Geometry.Manifold.Riemannian.Hyperbolic.UpperHalfSpace.Curvature
public import TauCeti.Geometry.Manifold.Riemannian.Hyperbolic.UpperHalfSpace.Metric
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Congr
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Curvature
import TauCeti.Analysis.Complex.UpperHalfPlane.MoebiusAction
import TauCeti.Analysis.Normed.Operator.LinearIsometryEquiv.Determinant
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic
import TauCeti.Geometry.Manifold.Riemannian.Isometry.UpperHalfSpace

/-!
# The upper half-plane and half-space metrics, distance comparison, and full isometry group

The coordinate map `x + iy ↦ (x, y)` identifies the Poincaré metric on the complex upper
half-plane `ℍ` with the two-dimensional upper half-space metric on `UpperHalfSpace ℝ`. The
identification is a smooth Riemannian isometry (`TauCeti.UpperHalfPlane.upperHalfSpaceIsometry`):
its differential preserves the Euclidean inner product and its base map preserves height, so both
tensors are the same Euclidean tensor divided by squared height.

Because both ambient metric spaces carry their Riemannian distances
(`TauCeti.isRiemannianManifold_upperHalfPlane` and
`TauCeti.UpperHalfSpace.instIsRiemannianManifold`), `upperHalfSpaceIsometry` also induces a metric
isometry equivalence `ℍ ≃ᵢ UpperHalfSpace ℝ` (`TauCeti.UpperHalfPlane.upperHalfSpaceIsometryEquiv`).
Transporting curvature and completeness packages the Poincaré metric as a `TauCeti.HyperbolicMetric`
(`TauCeti.UpperHalfPlane.poincareHyperbolicMetric`).

Finally, conjugating the `GL(2, ℝ)` and `PGL(2, ℝ)` Riemannian isometry actions on `ℍ` by
`upperHalfSpaceIsometry.isomCongr` transfers them to `UpperHalfSpace ℝ` and matches them against the
similarity-and-inversion classification of
`TauCeti.UpperHalfSpace.exists_eq_similarity_or_exists_eq_inversion_mul_similarity`, yielding the
group isomorphisms `PGL(2, ℝ) ≃* Isom 𝓘(ℝ, ℂ) ℍ` (`TauCeti.UpperHalfPlane.pglIsomMulEquiv`) and
`PGL(2, ℝ) ≃* Isom 𝓘(ℝ, WithLp 2 (ℝ × ℝ)) (UpperHalfSpace ℝ)`
(`TauCeti.UpperHalfPlane.pglUpperHalfSpaceIsomMulEquiv`).

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer, 2018, Chapter 3 and
  Theorem 8.34.
* S. Katok, *Fuchsian Groups*, University of Chicago Press, 1992, §1.1–1.2.
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

/-! ### Metric-space isometry `ℍ ≃ᵢ UpperHalfSpace ℝ` -/

/-- The coordinate map `x + iy ↦ (x, y)` as an isometry equivalence of metric spaces between
Mathlib's hyperbolic distance on `ℍ` and the Riemannian distance on `UpperHalfSpace ℝ`. -/
def upperHalfSpaceIsometryEquiv : ℍ ≃ᵢ UpperHalfSpace ℝ :=
  upperHalfSpaceIsometry

/-- Coercing `upperHalfSpaceIsometryEquiv` to a function agrees with `upperHalfSpaceIsometry`. -/
@[simp]
theorem coe_upperHalfSpaceIsometryEquiv :
    ⇑upperHalfSpaceIsometryEquiv = ⇑upperHalfSpaceIsometry := by
  rfl

/-- `upperHalfSpaceIsometryEquiv` agrees pointwise with `upperHalfSpaceIsometry`. -/
theorem upperHalfSpaceIsometryEquiv_apply (z : ℍ) :
    upperHalfSpaceIsometryEquiv z = upperHalfSpaceIsometry z := by
  rfl

/-- The inverse metric isometry of `upperHalfSpaceIsometryEquiv` comes from
`upperHalfSpaceIsometry.symm`. -/
@[simp]
theorem upperHalfSpaceIsometryEquiv_symm :
    upperHalfSpaceIsometryEquiv.symm = (upperHalfSpaceIsometry.symm : UpperHalfSpace ℝ ≃ᵢ ℍ) :=
  (RiemannianIsometry.toIsometryEquiv_symm upperHalfSpaceIsometry).symm

/-- `upperHalfSpaceIsometryEquiv.symm` agrees pointwise with `upperHalfSpaceIsometry.symm`. -/
theorem upperHalfSpaceIsometryEquiv_symm_apply (p : UpperHalfSpace ℝ) :
    upperHalfSpaceIsometryEquiv.symm p = upperHalfSpaceIsometry.symm p := by
  rw [upperHalfSpaceIsometryEquiv_symm]
  rfl

/-- `upperHalfSpaceIsometry` preserves hyperbolic distance. -/
@[simp]
theorem dist_upperHalfSpaceIsometry (z w : ℍ) :
    dist (upperHalfSpaceIsometry z) (upperHalfSpaceIsometry w) = dist z w :=
  upperHalfSpaceIsometryEquiv.dist_eq z w

/-- `upperHalfSpaceIsometry` preserves extended hyperbolic distance. -/
@[simp]
theorem edist_upperHalfSpaceIsometry (z w : ℍ) :
    edist (upperHalfSpaceIsometry z) (upperHalfSpaceIsometry w) = edist z w :=
  upperHalfSpaceIsometryEquiv.edist_eq z w

/-- Along the vertical axis of `UpperHalfSpace ℝ`, the Riemannian distance between `(0, 1)` and
`(0, 2)` is `Real.log 2`. -/
theorem dist_upperHalfSpaceIsometry_I_two_mul_I :
    dist (upperHalfSpaceIsometry _root_.UpperHalfPlane.I)
      (upperHalfSpaceIsometry ⟨2 * Complex.I, by simp⟩) = Real.log 2 := by
  rw [dist_upperHalfSpaceIsometry, ← _root_.UpperHalfPlane.toReal_riemannianEDist_eq_dist,
    _root_.UpperHalfPlane.toReal_riemannianEDist_I_two_mul_I]

/-! ### Curvature tensor and bundled `HyperbolicMetric` on `ℍ` -/

/-- The Riemann curvature tensor of the Poincaré metric on `ℍ` is the constant-curvature tensor with
parameter `−1`. -/
@[simp]
theorem curvatureTensor_eq (z : ℍ) (u v w : TangentSpace 𝓘(ℝ, ℂ) z) :
    (leviCivitaConnection 𝓘(ℝ, ℂ) ℍ).curvatureTensor z u v w =
      (-1 : ℝ) • (inner ℝ v w • u - inner ℝ u w • v) := by
  let e := upperHalfSpaceIsometry.mfderivToLinearIsometryEquiv z
  have he : ∀ t, e t = mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, WithLp 2 (ℝ × ℝ)) upperHalfSpaceIsometry z t :=
    upperHalfSpaceIsometry.mfderivToLinearIsometryEquiv_apply z
  apply e.injective
  rw [he, upperHalfSpaceIsometry.isLocalRiemannianIsometry.mfderiv_curvatureTensor,
    UpperHalfSpace.curvatureTensor_eq, upperHalfSpaceIsometry.inner_mfderiv,
    upperHalfSpaceIsometry.inner_mfderiv, ← he, ← he, map_smul, map_sub, map_smul, map_smul]

/-- The Poincaré metric on `ℍ` packaged as a `TauCeti.HyperbolicMetric`: smooth, complete, and of
constant curvature tensor `−1`. -/
def poincareHyperbolicMetric : HyperbolicMetric (I := 𝓘(ℝ, ℂ)) (M := ℍ) where
  metric := poincareRiemannianMetric
  complete := completeSpace_ofRiemannianMetric
  curvature :=
    (Bundle.ContMDiffRiemannianMetric.isConstantCurvatureTensor_iff_of_riemannianBundle_eq
      rfl (-1)).2 curvatureTensor_eq

/-- Forgetting completeness and curvature of `poincareHyperbolicMetric` recovers
`poincareRiemannianMetric`. -/
@[simp]
theorem metric_poincareHyperbolicMetric :
    poincareHyperbolicMetric.metric = poincareRiemannianMetric := by
  rfl

/-- The complex upper half-plane `ℍ` admits a hyperbolic metric. -/
theorem isHyperbolic : IsHyperbolic (I := 𝓘(ℝ, ℂ)) (M := ℍ) :=
  isHyperbolic_iff.mpr ⟨poincareHyperbolicMetric⟩

/-! ### Conjugated `GL(2, ℝ)` and `PGL(2, ℝ)` actions and full isometry group classification -/

local notation "K" => 𝓘(ℝ, WithLp 2 (ℝ × ℝ))

/-- The `GL(2, ℝ)` action on `UpperHalfSpace ℝ` obtained by conjugating `glToIsom` through
`upperHalfSpaceIsometry`. -/
def glToUpperHalfSpaceIsom : GL (Fin 2) ℝ →* Isom K (UpperHalfSpace ℝ) :=
  upperHalfSpaceIsometry.isomCongr.toMonoidHom.comp glToIsom

/-- `glToUpperHalfSpaceIsom g` acts pointwise by conjugating `g • ·` with
`upperHalfSpaceIsometry`. -/
@[simp]
theorem glToUpperHalfSpaceIsom_apply (g : GL (Fin 2) ℝ) (p : UpperHalfSpace ℝ) :
    glToUpperHalfSpaceIsom g p = upperHalfSpaceIsometry (g • upperHalfSpaceIsometry.symm p) := by
  simp [glToUpperHalfSpaceIsom]

/-- `upperHalfSpaceIsometry` is equivariant with respect to `GL(2, ℝ)` and
`glToUpperHalfSpaceIsom`. -/
theorem glToUpperHalfSpaceIsom_apply_upperHalfSpaceIsometry (g : GL (Fin 2) ℝ) (z : ℍ) :
    glToUpperHalfSpaceIsom g (upperHalfSpaceIsometry z) = upperHalfSpaceIsometry (g • z) := by
  simp

/-- The `PGL(2, ℝ)` action on `UpperHalfSpace ℝ` obtained by conjugating `pglToIsom` through
`upperHalfSpaceIsometry`. -/
def pglToUpperHalfSpaceIsom : PGL(2, ℝ) →* Isom K (UpperHalfSpace ℝ) :=
  upperHalfSpaceIsometry.isomCongr.toMonoidHom.comp pglToIsom

/-- `pglToUpperHalfSpaceIsom q` acts pointwise by conjugating `q • ·` with
`upperHalfSpaceIsometry`. -/
@[simp]
theorem pglToUpperHalfSpaceIsom_apply (q : PGL(2, ℝ)) (p : UpperHalfSpace ℝ) :
    pglToUpperHalfSpaceIsom q p = upperHalfSpaceIsometry (q • upperHalfSpaceIsometry.symm p) := by
  simp [pglToUpperHalfSpaceIsom]

/-- `upperHalfSpaceIsometry` is equivariant with respect to `PGL(2, ℝ)` and
`pglToUpperHalfSpaceIsom`. -/
theorem pglToUpperHalfSpaceIsom_apply_upperHalfSpaceIsometry (q : PGL(2, ℝ)) (z : ℍ) :
    pglToUpperHalfSpaceIsom q (upperHalfSpaceIsometry z) = upperHalfSpaceIsometry (q • z) := by
  simp

/-- `glToUpperHalfSpaceIsom` factors through `pglToUpperHalfSpaceIsom`. -/
@[simp]
theorem pglToUpperHalfSpaceIsom_mk (g : GL (Fin 2) ℝ) :
    pglToUpperHalfSpaceIsom (Matrix.ProjGenLinGroup.mk g) = glToUpperHalfSpaceIsom g := by
  simp [pglToUpperHalfSpaceIsom, glToUpperHalfSpaceIsom]

/-- `pglToUpperHalfSpaceIsom` is injective. -/
theorem pglToUpperHalfSpaceIsom_injective : Function.Injective pglToUpperHalfSpaceIsom :=
  upperHalfSpaceIsometry.isomCongr.injective.comp pglToIsom_injective

private theorem isom_upperHalfSpace_ext_iff {Φ Ψ : Isom K (UpperHalfSpace ℝ)} :
    Φ = Ψ ↔ ∀ z : ℍ, Φ (upperHalfSpaceIsometry z) = Ψ (upperHalfSpaceIsometry z) := by
  refine ⟨fun h z ↦ by rw [h], fun h ↦ ?_⟩
  ext p
  simpa using congrArg UpperHalfSpace.coe (h (upperHalfSpaceIsometry.symm p))

private theorem pglToUpperHalfSpaceIsom_mk_J :
    pglToUpperHalfSpaceIsom (Matrix.ProjGenLinGroup.mk _root_.UpperHalfPlane.J) =
      UpperHalfSpace.similarity 1 one_pos (.neg ℝ) 0 := by
  rw [isom_upperHalfSpace_ext_iff]
  intro z
  apply UpperHalfSpace.ext
  rw [pglToUpperHalfSpaceIsom_apply_upperHalfSpaceIsometry, _root_.UpperHalfPlane.pglMk_smul,
    _root_.UpperHalfPlane.coe_upperHalfSpaceIsometry_apply, UpperHalfSpace.coe_similarity_apply,
    _root_.UpperHalfPlane.height_upperHalfSpaceIsometry_apply,
    _root_.UpperHalfPlane.coe_upperHalfSpaceIsometry_apply,
    _root_.UpperHalfPlane.J_smul_re, _root_.UpperHalfPlane.J_smul_im]
  simp

private theorem pglToUpperHalfSpaceIsom_toPoint (c : ℝ) (hc : 0 < c) (b : ℝ) :
    pglToUpperHalfSpaceIsom ((_root_.UpperHalfPlane.toPoint ⟨⟨b, c⟩, hc⟩).toPGL) =
      UpperHalfSpace.similarity c hc (.refl ℝ ℝ) b := by
  rw [isom_upperHalfSpace_ext_iff]
  intro z
  apply UpperHalfSpace.ext
  have hcoe := _root_.UpperHalfPlane.coe_toPoint_smul ⟨⟨b, c⟩, hc⟩ z
  have hre : (_root_.UpperHalfPlane.toPoint ⟨⟨b, c⟩, hc⟩ • z).re = c * z.re + b := by
    simpa [← _root_.UpperHalfPlane.coe_re] using congrArg Complex.re hcoe
  have him : (_root_.UpperHalfPlane.toPoint ⟨⟨b, c⟩, hc⟩ • z).im = c * z.im := by
    simpa [← _root_.UpperHalfPlane.coe_im] using congrArg Complex.im hcoe
  rw [pglToUpperHalfSpaceIsom_apply_upperHalfSpaceIsometry, _root_.UpperHalfPlane.toPGL_smul,
    _root_.UpperHalfPlane.coe_upperHalfSpaceIsometry_apply, UpperHalfSpace.coe_similarity_apply,
    _root_.UpperHalfPlane.height_upperHalfSpaceIsometry_apply,
    _root_.UpperHalfPlane.coe_upperHalfSpaceIsometry_apply, hre, him]
  simp

private theorem exists_pgl_similarity (c : ℝ) (hc : 0 < c) (A : ℝ ≃ₗᵢ[ℝ] ℝ) (b : ℝ) :
    ∃ q : PGL(2, ℝ), pglToUpperHalfSpaceIsom q = UpperHalfSpace.similarity c hc A b := by
  rcases A.eq_refl_or_eq_neg (Module.finrank_self ℝ) with rfl | rfl
  · exact ⟨(_root_.UpperHalfPlane.toPoint ⟨⟨b, c⟩, hc⟩).toPGL,
      pglToUpperHalfSpaceIsom_toPoint c hc b⟩
  · refine ⟨(_root_.UpperHalfPlane.toPoint ⟨⟨b, c⟩, hc⟩).toPGL *
        Matrix.ProjGenLinGroup.mk _root_.UpperHalfPlane.J, ?_⟩
    rw [map_mul, pglToUpperHalfSpaceIsom_toPoint, pglToUpperHalfSpaceIsom_mk_J,
      UpperHalfSpace.similarity_mul_similarity]
    congr <;> simp

private theorem pglToUpperHalfSpaceIsom_inversion_zero_one :
    pglToUpperHalfSpaceIsom
        (Matrix.ProjGenLinGroup.mk _root_.UpperHalfPlane.J * TauCeti.pslS.toPGL) =
      UpperHalfSpace.inversion 0 1 one_ne_zero := by
  rw [isom_upperHalfSpace_ext_iff]
  intro z
  apply UpperHalfSpace.ext
  have himS : (TauCeti.pslS • z : ℍ).im = z.im / Complex.normSq (z : ℂ) := by
    rw [pslS_smul, _root_.UpperHalfPlane.modular_S_smul]
    simp [Complex.inv_im, neg_div]
  have hd : dist (WithLp.toLp 2 (z.re, z.im)) (WithLp.toLp 2 ((0 : ℝ), (0 : ℝ))) ^ 2 =
      Complex.normSq (z : ℂ) := by
    rw [Prod.mk_zero_zero, WithLp.toLp_zero, dist_zero_right, WithLp.prod_norm_sq_eq_of_L2]
    simp [Complex.normSq_apply, Real.norm_eq_abs, pow_two]
  rw [pglToUpperHalfSpaceIsom_apply_upperHalfSpaceIsometry, mul_smul,
    _root_.UpperHalfPlane.pglMk_smul, _root_.UpperHalfPlane.toPGL_smul,
    _root_.UpperHalfPlane.coe_upperHalfSpaceIsometry_apply, UpperHalfSpace.coe_inversion_apply,
    _root_.UpperHalfPlane.coe_upperHalfSpaceIsometry_apply,
    _root_.UpperHalfPlane.J_smul_re, _root_.UpperHalfPlane.J_smul_im, re_pslS_smul, himS,
    neg_div, neg_neg]
  simp only [EuclideanGeometry.inversion, vsub_eq_sub, one_div, inv_pow, hd]
  apply (WithLp.ext_iff 2).2
  ext <;> simp [smul_eq_mul, div_eq_mul_inv, mul_comm]

/-- Every Riemannian isometry of `UpperHalfSpace ℝ` comes from an element of `PGL(2, ℝ)`. -/
theorem pglToUpperHalfSpaceIsom_surjective : Function.Surjective pglToUpperHalfSpaceIsom := by
  intro Ψ
  rcases UpperHalfSpace.exists_eq_similarity_or_exists_eq_inversion_mul_similarity Ψ with
    ⟨c, hc, A, b, rfl⟩ | ⟨a, R, hR, c, hc, A, b, rfl⟩
  · exact exists_pgl_similarity c hc A b
  · obtain ⟨q₁, hq₁⟩ := exists_pgl_similarity (R ^ 2) (sq_pos_of_ne_zero hR) (.refl ℝ ℝ) a
    obtain ⟨q₂, hq₂⟩ := exists_pgl_similarity 1 one_pos (.refl ℝ ℝ) (-a)
    obtain ⟨q₃, hq₃⟩ := exists_pgl_similarity c hc A b
    refine ⟨q₁ * (Matrix.ProjGenLinGroup.mk _root_.UpperHalfPlane.J * TauCeti.pslS.toPGL) *
        q₂ * q₃, ?_⟩
    rw [map_mul, map_mul, map_mul, hq₁, hq₂, hq₃, pglToUpperHalfSpaceIsom_inversion_zero_one,
      UpperHalfSpace.inversion_eq_similarity_mul_inversion_mul_similarity a R hR]

/-- Every Riemannian isometry of `UpperHalfSpace ℝ` comes from an element of `GL(2, ℝ)`. -/
theorem glToUpperHalfSpaceIsom_surjective : Function.Surjective glToUpperHalfSpaceIsom := by
  intro Ψ
  obtain ⟨q, rfl⟩ := pglToUpperHalfSpaceIsom_surjective Ψ
  induction q using Matrix.ProjGenLinGroup.induction_on with | mk g =>
  exact ⟨g, (pglToUpperHalfSpaceIsom_mk g).symm⟩

/-- Every Riemannian isometry of the Poincaré upper half-plane `ℍ` comes from an element of
`PGL(2, ℝ)`. -/
theorem pglToIsom_surjective : Function.Surjective pglToIsom := by
  intro Φ
  obtain ⟨q, hq⟩ := pglToUpperHalfSpaceIsom_surjective (upperHalfSpaceIsometry.isomCongr Φ)
  exact ⟨q, upperHalfSpaceIsometry.isomCongr.injective hq⟩

/-- Every Riemannian isometry of the Poincaré upper half-plane `ℍ` comes from an element of
`GL(2, ℝ)`. -/
theorem glToIsom_surjective : Function.Surjective glToIsom := by
  intro Φ
  obtain ⟨q, rfl⟩ := pglToIsom_surjective Φ
  induction q using Matrix.ProjGenLinGroup.induction_on with | mk g =>
  exact ⟨g, (pglToIsom_mk g).symm⟩

/-- **Classification of the full Riemannian isometry group of `ℍ`:** `PGL(2, ℝ)` is canonically
isomorphic to `Isom 𝓘(ℝ, ℂ) ℍ`. -/
def pglIsomMulEquiv : PGL(2, ℝ) ≃* Isom 𝓘(ℝ, ℂ) ℍ :=
  MulEquiv.ofBijective pglToIsom ⟨pglToIsom_injective, pglToIsom_surjective⟩

/-- `pglIsomMulEquiv` agrees on elements with `pglToIsom`. -/
@[simp]
theorem pglIsomMulEquiv_apply (q : PGL(2, ℝ)) : pglIsomMulEquiv q = pglToIsom q := by
  rfl

/-- `pglIsomMulEquiv q` acts pointwise on `ℍ` by `q • z`. -/
theorem pglIsomMulEquiv_apply_apply (q : PGL(2, ℝ)) (z : ℍ) : pglIsomMulEquiv q z = q • z :=
  pglToIsom_apply q z

/-- Coercing `pglIsomMulEquiv` to a `MonoidHom` recovers `pglToIsom`. -/
@[simp]
theorem coe_pglIsomMulEquiv_monoidHom :
    (pglIsomMulEquiv : PGL(2, ℝ) →* Isom 𝓘(ℝ, ℂ) ℍ) = pglToIsom := by
  rfl

/-- Forgetting the inverse of `pglIsomMulEquiv` recovers `pglToIsom`. -/
theorem toMonoidHom_pglIsomMulEquiv : pglIsomMulEquiv.toMonoidHom = pglToIsom := by
  rfl

/-- **Classification of the full Riemannian isometry group of `UpperHalfSpace ℝ`:** `PGL(2, ℝ)` is
canonically isomorphic to `Isom 𝓘(ℝ, WithLp 2 (ℝ × ℝ)) (UpperHalfSpace ℝ)`. -/
def pglUpperHalfSpaceIsomMulEquiv : PGL(2, ℝ) ≃* Isom K (UpperHalfSpace ℝ) :=
  pglIsomMulEquiv.trans upperHalfSpaceIsometry.isomCongr

/-- `pglUpperHalfSpaceIsomMulEquiv` agrees on elements with `pglToUpperHalfSpaceIsom`. -/
@[simp]
theorem pglUpperHalfSpaceIsomMulEquiv_apply (q : PGL(2, ℝ)) :
    pglUpperHalfSpaceIsomMulEquiv q = pglToUpperHalfSpaceIsom q := by
  rfl

/-- Coercing `pglUpperHalfSpaceIsomMulEquiv` to a `MonoidHom` recovers `pglToUpperHalfSpaceIsom`. -/
@[simp]
theorem coe_pglUpperHalfSpaceIsomMulEquiv_monoidHom :
    (pglUpperHalfSpaceIsomMulEquiv : PGL(2, ℝ) →* Isom K (UpperHalfSpace ℝ)) =
      pglToUpperHalfSpaceIsom := by
  ext q p
  simp [pglUpperHalfSpaceIsomMulEquiv]

/-- Forgetting the inverse of `pglUpperHalfSpaceIsomMulEquiv` recovers
`pglToUpperHalfSpaceIsom`. -/
theorem toMonoidHom_pglUpperHalfSpaceIsomMulEquiv :
    pglUpperHalfSpaceIsomMulEquiv.toMonoidHom = pglToUpperHalfSpaceIsom :=
  coe_pglUpperHalfSpaceIsomMulEquiv_monoidHom

end TauCeti.UpperHalfPlane

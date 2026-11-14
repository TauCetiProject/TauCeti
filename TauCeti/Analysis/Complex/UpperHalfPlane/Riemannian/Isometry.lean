/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.PoincareMetric
public import TauCeti.Analysis.Complex.UpperHalfPlane.PSL.Manifold
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Action
import Mathlib.Analysis.Complex.UpperHalfPlane.FixedPoints
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic

/-!
# Riemannian isometries of the Poincaré upper half-plane

Mathlib's action `UpperHalfPlane.glAction` of `GL(2, ℝ)` on the complex upper half-plane `ℍ` sends
`z` to `(a z + b) / (c z + d)` when `det g > 0` and to `(a conj z + b) / (c conj z + d)` when
`det g < 0`. Every element of `GL(2, ℝ)` acts on `ℍ` by a real-analytic diffeomorphism for the
real manifold structure `𝓘(ℝ, ℂ)`: positive-determinant matrices act holomorphically, the
reflection `UpperHalfPlane.J : z ↦ -conj z` is the restriction of a continuous real-linear
involution of `ℂ`, and negative-determinant matrices factor through `J`.

In the singleton inclusion chart, the real differential at `z` is Mathlib's
`UpperHalfPlane.smulFDeriv g z`, namely complex multiplication by `det g / (c z + d) ^ 2` followed
by `UpperHalfPlane.σ g` (the identity for `det g > 0` and complex conjugation for `det g < 0`).
Both `id` and `conj` preserve the Euclidean inner product on `ℂ`, while multiplication by
`det g / (c z + d) ^ 2` scales Euclidean lengths by `|det g| / |c z + d| ^ 2 = Im(g • z) / Im z`
(`UpperHalfPlane.im_smul_eq_div_normSq`). Consequently every element of `GL(2, ℝ)` preserves the
Poincaré metric `(Re v Re w + Im v Im w) / (Im z) ^ 2` and defines an element of the Riemannian
isometry group `TauCeti.Isom 𝓘(ℝ, ℂ) ℍ`.

The resulting group homomorphism `TauCeti.UpperHalfPlane.glToIsom` descends to `PGL(2, ℝ)`
(`pglToIsom`, injective by faithfulness of the projective action) and restricts to `SL(2, R)` and
`PSL(2, R)` (`slToIsom`, `pslToIsom`) for any coefficient ring `R` with an algebra map to `ℝ`.

## Main definitions

* `UpperHalfPlane.instContMDiffConstSMulGLReal`, `UpperHalfPlane.instContMDiffConstSMulPGLReal`,
  `UpperHalfPlane.instContMDiffConstSMulSL2Real`, `UpperHalfPlane.instContMDiffConstSMulPSL2Real`:
  `GL(2, ℝ)`, `PGL(2, ℝ)`, `SL(2, R)`, and `PSL(2, R)` act on `ℍ` by real-analytic maps.
* `TauCeti.UpperHalfPlane.glToIsom`, `TauCeti.UpperHalfPlane.pglToIsom`,
  `TauCeti.UpperHalfPlane.slToIsom`, `TauCeti.UpperHalfPlane.pslToIsom`: group homomorphisms from
  `GL(2, ℝ)`, `PGL(2, ℝ)`, `SL(2, R)`, and `PSL(2, R)` into `Isom 𝓘(ℝ, ℂ) ℍ`.

## Main results

* `UpperHalfPlane.tangentSpaceCastModel_mfderiv_smul` and `UpperHalfPlane.inner_smulFDeriv`: in the
  inclusion chart, the differential of `w ↦ g • w` at `z` is `UpperHalfPlane.smulFDeriv g z` and
  preserves the Euclidean inner product divided by squared imaginary part.
* `TauCeti.UpperHalfPlane.pglToIsom_injective` and `TauCeti.UpperHalfPlane.pslToIsom_injective`:
  the projective homomorphisms into `Isom 𝓘(ℝ, ℂ) ℍ` are injective.
* `TauCeti.UpperHalfPlane.isPretransitive_isom`: `Isom 𝓘(ℝ, ℂ) ℍ` acts transitively on `ℍ`.

## References

* Svetlana Katok, *Fuchsian Groups*, University of Chicago Press (1992), §§1.1–1.2.
* Alan Beardon, *The Geometry of Discrete Groups*, Springer GTM 91 (1983), §7.2.
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 3.
-/

public section

open Bundle Manifold
open scoped ComplexConjugate ContDiff Manifold MatrixGroups UpperHalfPlane

noncomputable section

namespace UpperHalfPlane

/-- The reflection `UpperHalfPlane.J : z ↦ -conj z` is real-analytic on `ℍ`. -/
private theorem contMDiff_J_smul {n : ℕ∞ω} : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) n (J • · : ℍ → ℍ) := by
  apply ContMDiff.of_comp_isOpenEmbedding isOpenEmbedding_coe
  have hcoe : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) n UpperHalfPlane.coe := fun _ ↦ contMDiffAt_extChartAt
  have hfun : UpperHalfPlane.coe ∘ (J • · : ℍ → ℍ) = (-Complex.conjCLE : ℂ →L[ℝ] ℂ) ∘
      UpperHalfPlane.coe := by
    funext z
    simp [coe_J_smul]
  rw [hfun]
  exact (-Complex.conjCLE : ℂ →L[ℝ] ℂ).contDiff.contMDiff.comp hcoe

/-- Every element of `GL(2, ℝ)` acts on `ℍ` by a real-analytic map (and hence smoothly of every
order `n : ℕ∞ω`). -/
instance instContMDiffConstSMulGLReal {n : ℕ∞ω} :
    ContMDiffConstSMul 𝓘(ℝ, ℂ) n (GL (Fin 2) ℝ) ℍ where
  contMDiff_const_smul g := by
    -- Positive-determinant matrices act holomorphically; negative-determinant ones factor via `J`.
    have hpos {h : GL (Fin 2) ℝ} (hh : 0 < h.det.val) :
        ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) n (h • · : ℍ → ℍ) := by
      simpa only [modelWithCornersSelf_restrictScalars] using
        ((UpperHalfPlane.contMDiff_smul (n := ω) hh).restrictScalars ℝ).of_le le_top
    rcases g.det.ne_zero.lt_or_gt with hg | hg
    · have hJg : 0 < (J * g).det.val := by simpa using hg
      have hcomp : (g • · : ℍ → ℍ) = (J • ·) ∘ ((J * g) • ·) := by
        funext z
        simp [smul_smul, ← mul_assoc, ← sq]
      rw [hcomp]
      exact contMDiff_J_smul.comp (hpos hJg)
    · exact hpos hg

/-- Every element of `PGL(2, ℝ)` acts on `ℍ` by a real-analytic map. -/
instance instContMDiffConstSMulPGLReal {n : ℕ∞ω} :
    ContMDiffConstSMul 𝓘(ℝ, ℂ) n PGL(2, ℝ) ℍ where
  contMDiff_const_smul q := by
    induction q using Matrix.ProjGenLinGroup.induction_on with | mk g =>
    simpa only [pglMk_smul] using contMDiff_const_smul (I := 𝓘(ℝ, ℂ)) (n := n) g

/-- Every element of `SL(2, R)` acts on `ℍ` by a real-analytic map. -/
instance instContMDiffConstSMulSL2Real {R : Type*} [CommRing R] [Algebra R ℝ] {n : ℕ∞ω} :
    ContMDiffConstSMul 𝓘(ℝ, ℂ) n SL(2, R) ℍ where
  contMDiff_const_smul g := by
    simpa only [MulAction.compHom_smul_def] using
      contMDiff_const_smul (I := 𝓘(ℝ, ℂ)) (n := n) (Matrix.SpecialLinearGroup.mapGL ℝ g)

/-- Every element of `PSL(2, R)` acts on `ℍ` by a real-analytic map. -/
instance instContMDiffConstSMulPSL2Real {R : Type*} [CommRing R] [Algebra R ℝ] {n : ℕ∞ω} :
    ContMDiffConstSMul 𝓘(ℝ, ℂ) n PSL(2, R) ℍ where
  contMDiff_const_smul q := by
    refine QuotientGroup.induction_on q fun g ↦ ?_
    simpa only [pslMk_smul] using contMDiff_const_smul (I := 𝓘(ℝ, ℂ)) (n := n) g

/-- The Poincaré norm of a tangent vector at `z` is its Euclidean norm in the inclusion chart
divided by `Im z`. -/
theorem poincareRiemannianMetric_norm (z : ℍ) (v : TangentSpace 𝓘(ℝ, ℂ) z) :
    ‖v‖ = ‖tangentSpaceCastModel 𝓘(ℝ, ℂ) z v‖ / z.im := by
  -- The ambient tangent-space inner product is the installed Poincaré metric.
  have hinner : inner ℝ v v = TauCeti.UpperHalfPlane.poincareRiemannianMetric.inner z v v := rfl
  rw [norm_eq_sqrt_real_inner, hinner, poincareRiemannianMetric_inner, real_inner_self_eq_norm_sq,
    Real.sqrt_div (sq_nonneg _), Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq z.im_pos.le]

/-- In the tangent coordinates of the inclusion chart, the real differential of `w ↦ g • w` at `z`
is `UpperHalfPlane.smulFDeriv g z`. -/
theorem tangentSpaceCastModel_mfderiv_smul (z : ℍ) (g : GL (Fin 2) ℝ)
    (v : TangentSpace 𝓘(ℝ, ℂ) z) :
    tangentSpaceCastModel 𝓘(ℝ, ℂ) (g • z)
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (g • · : ℍ → ℍ) z v) =
      smulFDeriv g z (tangentSpaceCastModel 𝓘(ℝ, ℂ) z v) := by
  have hmdiff : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (g • · : ℍ → ℍ) z :=
    (contMDiff_const_smul (I := 𝓘(ℝ, ℂ)) (n := ∞) g z).mdifferentiableAt (by simp)
  rw [hmdiff.tangentSpaceCastModel_mfderiv_apply]
  have hlocal : writtenInExtChartAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) z (g • · : ℍ → ℍ)
      =ᶠ[nhds (z : ℂ)] fun w : ℂ ↦ ((g • ofComplex w : ℍ) : ℂ) := by
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds z.im_pos] with w _
    have hchart (p : ℍ) : extChartAt 𝓘(ℝ, ℂ) (g • z) p = (p : ℂ) := by simp
    simp only [writtenInExtChartAt, Function.comp_apply, hchart]
    congr 2
  have hchart : extChartAt 𝓘(ℝ, ℂ) z z = (z : ℂ) := by simp
  rw [hchart, hlocal.fderiv_eq, (hasStrictFDerivAt_smul g z).hasFDerivAt.fderiv]

/-- `UpperHalfPlane.smulFDeriv g z` preserves the Euclidean inner product divided by squared
imaginary part. -/
theorem inner_smulFDeriv (z : ℍ) (g : GL (Fin 2) ℝ) (u w : ℂ) :
    inner ℝ (smulFDeriv g z u) (smulFDeriv g z w) / (g • z).im ^ 2 =
      inner ℝ u w / z.im ^ 2 := by
  have hσ (x y : ℂ) : inner ℝ ((σ g : ℂ ≃L[ℝ] ℂ) x) ((σ g : ℂ ≃L[ℝ] ℂ) y) = inner ℝ x y := by
    simp only [σ]
    split_ifs
    · rfl
    · exact Complex.conjLIE.inner_map_map x y
  set α : ℂ := (g.det.val : ℂ) / denom g z ^ 2
  have hmul (x y : ℂ) : inner ℝ (x * α) (y * α) = Complex.normSq α * inner ℝ x y := by
    simp only [Complex.inner, Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
      Complex.conj_re, Complex.conj_im]
    ring
  have hα : Complex.normSq α = g.det.val ^ 2 / Complex.normSq (denom g z) ^ 2 := by
    simp [α, sq]
  have him : (g • z).im ^ 2 = g.det.val ^ 2 * z.im ^ 2 / Complex.normSq (denom g z) ^ 2 := by
    rw [im_smul_eq_div_normSq, div_pow, mul_pow, sq_abs]
  have hdet : g.det.val ≠ 0 := g.det.ne_zero
  have hdenom : Complex.normSq (denom g z) ≠ 0 := normSq_denom_ne_zero g z.im_ne_zero
  have hzim : z.im ≠ 0 := z.im_ne_zero
  simp only [smulFDeriv, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.toSpanSingleton_apply,
    smul_eq_mul, hσ]
  rw [hmul, hα, him]
  field_simp

end UpperHalfPlane

namespace TauCeti.UpperHalfPlane

open _root_.UpperHalfPlane

/-- An element of `GL(2, ℝ)` acts on `ℍ` as a smooth Riemannian isometry of the Poincaré metric. -/
private def glIsom (g : GL (Fin 2) ℝ) : Isom 𝓘(ℝ, ℂ) ℍ where
  toDiffeomorph := Diffeomorph.constSmul 𝓘(ℝ, ℂ) ∞ g
  inner_mfderiv' z v w := by
    have hinner (x : ℍ) (u₁ u₂ : TangentSpace 𝓘(ℝ, ℂ) x) :
        inner ℝ u₁ u₂ = poincareRiemannianMetric.inner x u₁ u₂ := rfl
    rw [hinner, hinner, Diffeomorph.coe_constSmul,
      poincareRiemannianMetric_inner, poincareRiemannianMetric_inner,
      z.tangentSpaceCastModel_mfderiv_smul g v, z.tangentSpaceCastModel_mfderiv_smul g w]
    exact z.inner_smulFDeriv g _ _

@[simp]
private theorem glIsom_apply (g : GL (Fin 2) ℝ) (z : ℍ) : glIsom g z = g • z := by
  rw [← RiemannianIsometry.coe_toDiffeomorph]
  exact Diffeomorph.constSmul_apply (I := 𝓘(ℝ, ℂ)) (n := ∞) g z

/-- The group homomorphism sending each element of `GL(2, ℝ)` to the Riemannian isometry it induces
on the Poincaré upper half-plane `ℍ`. Positive-determinant matrices act holomorphically and
negative-determinant matrices act antiholomorphically. -/
def glToIsom : GL (Fin 2) ℝ →* Isom 𝓘(ℝ, ℂ) ℍ where
  toFun := glIsom
  map_one' := by
    ext z
    simp
  map_mul' g h := by
    ext z
    simp [mul_smul]

/-- `glToIsom g` acts on `ℍ` by `g • z`. -/
@[simp]
theorem glToIsom_apply (g : GL (Fin 2) ℝ) (z : ℍ) : glToIsom g z = g • z :=
  glIsom_apply g z

/-- The inverse of `glToIsom g` acts on `ℍ` by `g⁻¹ • z`. -/
@[simp]
theorem glToIsom_symm_apply (g : GL (Fin 2) ℝ) (z : ℍ) : (glToIsom g).symm z = g⁻¹ • z := by
  rw [← RiemannianIsometry.inv_apply, ← map_inv, glToIsom_apply]

/-- The underlying diffeomorphism of `glToIsom g` is `Diffeomorph.constSmul 𝓘(ℝ, ℂ) ∞ g`. -/
@[simp]
theorem toDiffeomorph_glToIsom (g : GL (Fin 2) ℝ) :
    (glToIsom g).toDiffeomorph = Diffeomorph.constSmul 𝓘(ℝ, ℂ) ∞ g := (rfl)

/-- The group homomorphism sending each element of `PGL(2, ℝ)` to the Riemannian isometry it
induces on the Poincaré upper half-plane `ℍ`. -/
def pglToIsom : PGL(2, ℝ) →* Isom 𝓘(ℝ, ℂ) ℍ :=
  Matrix.ProjGenLinGroup.lift glToIsom <| by
    ext u z
    simp

/-- `pglToIsom` extends `glToIsom` along the quotient projection `GL(2, ℝ) →* PGL(2, ℝ)`. -/
@[simp]
theorem pglToIsom_mk (g : GL (Fin 2) ℝ) :
    pglToIsom (Matrix.ProjGenLinGroup.mk g) = glToIsom g := (rfl)

/-- Composing `pglToIsom` with `Matrix.ProjGenLinGroup.mk` recovers `glToIsom`. -/
@[simp]
theorem pglToIsom_comp_mk : pglToIsom.comp Matrix.ProjGenLinGroup.mk = glToIsom := (rfl)

/-- `pglToIsom q` acts on `ℍ` by `q • z`. -/
@[simp]
theorem pglToIsom_apply (q : PGL(2, ℝ)) (z : ℍ) : pglToIsom q z = q • z := by
  induction q using Matrix.ProjGenLinGroup.induction_on with | mk g =>
  simp

/-- The inverse of `pglToIsom q` acts on `ℍ` by `q⁻¹ • z`. -/
@[simp]
theorem pglToIsom_symm_apply (q : PGL(2, ℝ)) (z : ℍ) : (pglToIsom q).symm z = q⁻¹ • z := by
  rw [← RiemannianIsometry.inv_apply, ← map_inv, pglToIsom_apply]

/-- `PGL(2, ℝ)` embeds faithfully into the Riemannian isometry group of `ℍ`. -/
theorem pglToIsom_injective : Function.Injective pglToIsom :=
  fun _ _ h ↦ eq_of_smul_eq_smul fun z : ℍ ↦ by
    simpa only [pglToIsom_apply] using DFunLike.congr_fun h z

/-- The group homomorphism sending each element of `SL(2, R)` to its Riemannian isometry of `ℍ`. -/
def slToIsom {R : Type*} [CommRing R] [Algebra R ℝ] : SL(2, R) →* Isom 𝓘(ℝ, ℂ) ℍ :=
  glToIsom.comp (Matrix.SpecialLinearGroup.mapGL ℝ)

/-- `slToIsom g` acts on `ℍ` by `g • z`. -/
@[simp]
theorem slToIsom_apply {R : Type*} [CommRing R] [Algebra R ℝ] (g : SL(2, R)) (z : ℍ) :
    slToIsom g z = g • z := by
  simp [slToIsom, MulAction.compHom_smul_def]

/-- The inverse of `slToIsom g` acts on `ℍ` by `g⁻¹ • z`. -/
@[simp]
theorem slToIsom_symm_apply {R : Type*} [CommRing R] [Algebra R ℝ] (g : SL(2, R)) (z : ℍ) :
    (slToIsom g).symm z = g⁻¹ • z := by
  rw [← RiemannianIsometry.inv_apply, ← map_inv, slToIsom_apply]

/-- Restricting `glToIsom` along `mapGL ℝ` gives `slToIsom`. -/
@[simp]
theorem glToIsom_mapGL {R : Type*} [CommRing R] [Algebra R ℝ] (g : SL(2, R)) :
    glToIsom (Matrix.SpecialLinearGroup.mapGL ℝ g) = slToIsom g := (rfl)

/-- The group homomorphism sending each element of `PSL(2, R)` to its holomorphic Riemannian
isometry of the Poincaré upper half-plane. -/
def pslToIsom {R : Type*} [CommRing R] [Algebra R ℝ] : PSL(2, R) →* Isom 𝓘(ℝ, ℂ) ℍ :=
  QuotientGroup.lift (Subgroup.center SL(2, R)) slToIsom fun c hc ↦ by
    ext z
    simpa [slToIsom_apply] using smul_eq_self_of_mem_center c hc z

/-- `pslToIsom` sends the class of `g : SL(2, R)` to `slToIsom g`. -/
@[simp]
theorem pslToIsom_mk {R : Type*} [CommRing R] [Algebra R ℝ] (g : SL(2, R)) :
    pslToIsom (g : PSL(2, R)) = slToIsom g := (rfl)

/-- `pslToIsom q` acts on `ℍ` by `q • z`. -/
@[simp]
theorem pslToIsom_apply {R : Type*} [CommRing R] [Algebra R ℝ] (q : PSL(2, R)) (z : ℍ) :
    pslToIsom q z = q • z := by
  refine QuotientGroup.induction_on q fun g ↦ ?_
  simp

/-- The inverse of `pslToIsom q` acts on `ℍ` by `q⁻¹ • z`. -/
@[simp]
theorem pslToIsom_symm_apply {R : Type*} [CommRing R] [Algebra R ℝ] (q : PSL(2, R)) (z : ℍ) :
    (pslToIsom q).symm z = q⁻¹ • z := by
  rw [← RiemannianIsometry.inv_apply, ← map_inv, pslToIsom_apply]

/-- Restricting `pglToIsom` along the canonical inclusion `toPGL : PSL(2, ℝ) →* PGL(2, ℝ)` gives
`pslToIsom`. -/
@[simp]
theorem pglToIsom_toPGL (q : PSL(2, ℝ)) :
    pglToIsom (Matrix.ProjectiveSpecialLinearGroup.toPGL q) = pslToIsom q := by
  ext z
  simp

/-- Whenever `PSL(2, R)` acts faithfully on `ℍ` (for instance `R = ℝ` or `R = ℤ`), `pslToIsom` is
injective. -/
theorem pslToIsom_injective {R : Type*} [CommRing R] [Algebra R ℝ] [FaithfulSMul PSL(2, R) ℍ] :
    Function.Injective (pslToIsom (R := R)) :=
  fun _ _ h ↦ eq_of_smul_eq_smul fun z : ℍ ↦ by
    simpa only [pslToIsom_apply] using DFunLike.congr_fun h z

/-- The Riemannian isometry group of the Poincaré upper half-plane acts transitively on `ℍ`, so `ℍ`
is a homogeneous Riemannian manifold. -/
instance isPretransitive_isom : MulAction.IsPretransitive (Isom 𝓘(ℝ, ℂ) ℍ) ℍ :=
  .of_smul_eq glToIsom fun {g z} ↦ glToIsom_apply g z

end TauCeti.UpperHalfPlane

end

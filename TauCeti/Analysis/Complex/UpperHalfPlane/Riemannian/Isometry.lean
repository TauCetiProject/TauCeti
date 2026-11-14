/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.FixedPoints
public import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
public import TauCeti.Analysis.Complex.UpperHalfPlane.PoincareMetric
public import TauCeti.Analysis.Complex.UpperHalfPlane.PSL.Action
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Action
import TauCeti.Geometry.Manifold.ContMDiff.RestrictScalars
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic

/-!
# `GL(2, ℝ)` acts on the upper half-plane by Riemannian isometries

Mathlib's action `UpperHalfPlane.glAction` of `GL(2, ℝ)` on `ℍ` sends `z` to `(az + b)/(cz + d)`
when `det g > 0` and to `(a conj z + b)/(c conj z + d)` when `det g < 0`. Each element acts
smoothly on `ℍ` as a real manifold modelled on `𝓘(ℝ, ℂ)` and preserves the Poincaré Riemannian
metric `(Re u Re w + Im u Im w) / y²`:

* In model coordinates, the real differential of `(g • ·)` at `z : ℍ` is Mathlib's
  `UpperHalfPlane.smulFDeriv g z`, which multiplies by `det g / (cz + d)²` and applies complex
  conjugation when `det g < 0`.
* Complex conjugation preserves the real Euclidean inner product on `ℂ`, while multiplication by
  `det g / (cz + d)²` scales it by `(|det g| / |cz + d|²)²`, which equals `((g • z).im / z.im)²`
  by `UpperHalfPlane.im_smul_eq_div_normSq`. Dividing by `(g • z).im²` leaves the Poincaré inner
  product unchanged.

Consequently `GL(2, ℝ)`, `PGL(2, ℝ)`, `SL(2, ℝ)`, and `PSL(2, ℝ)` map homomorphically to the
Riemannian isometry group `TauCeti.Isom 𝓘(ℝ, ℂ) ℍ`, with the projective homomorphisms from
`PGL(2, ℝ)` and `PSL(2, ℝ)` injective. Because `UpperHalfPlane.J : z ↦ -conj z` has negative
Jacobian determinant at every point whereas elements of `PSL(2, ℝ)` have positive Jacobian
determinant, `glIsomHom J` lies outside the image of `pslIsomHom`.

## Main definitions and results

* `UpperHalfPlane.inner_tangentSpace` and `UpperHalfPlane.norm_tangentSpace`: the Poincaré inner
  product and norm on `TangentSpace 𝓘(ℝ, ℂ) z` in model coordinates.
* `UpperHalfPlane.instContMDiffConstSMulRealGL`, `instContMDiffConstSMulRealPGL`,
  `instContMDiffConstSMulRealSL`, `instContMDiffConstSMulRealPSL`: smooth real actions on `ℍ`.
* `UpperHalfPlane.tangentSpaceCastModel_mfderiv_smul`: the manifold derivative of `(g • ·)` in
  model coordinates is `UpperHalfPlane.smulFDeriv g z`.
* `UpperHalfPlane.inner_mfderiv_smul`: every element of `GL(2, ℝ)` preserves the Poincaré inner
  product on tangent spaces.
* `TauCeti.UpperHalfPlane.glIsomHom`, `pglIsomHom`, `slIsomHom`, `pslIsomHom`: group homomorphisms
  into `TauCeti.Isom 𝓘(ℝ, ℂ) ℍ`, with injectivity for `PGL(2, ℝ)` and `PSL(2, ℝ)`.
* `TauCeti.UpperHalfPlane.pslIsomHom_ne_glIsomHom_J`: the reflection `J` is induced by no element
  of `PSL(2, ℝ)`.
* `TauCeti.UpperHalfPlane.isPretransitive_isom`: `Isom 𝓘(ℝ, ℂ) ℍ` acts transitively on `ℍ`.

## References

* Svetlana Katok, *Fuchsian Groups*, §§1.1–1.2.
* Alan Beardon, *The Geometry of Discrete Groups*, §7.2.
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Chapter 3.
-/

public section

open Bundle Manifold Topology
open scoped ComplexConjugate ContDiff Manifold MatrixGroups UpperHalfPlane

noncomputable section

namespace UpperHalfPlane

/-- The installed inner product on `TangentSpace 𝓘(ℝ, ℂ) z` is the Euclidean real inner product in
model coordinates divided by `z.im ^ 2`. -/
theorem inner_tangentSpace (z : ℍ) (v w : TangentSpace 𝓘(ℝ, ℂ) z) :
    inner ℝ v w =
      inner ℝ (tangentSpaceCastModel 𝓘(ℝ, ℂ) z v)
        (tangentSpaceCastModel 𝓘(ℝ, ℂ) z w) / z.im ^ 2 := by
  rw [Bundle.ContMDiffRiemannianMetric.inner_riemannianBundle
    TauCeti.UpperHalfPlane.poincareRiemannianMetric z v w, poincareRiemannianMetric_inner]

/-- The installed norm on `TangentSpace 𝓘(ℝ, ℂ) z` is the Euclidean norm in model coordinates
divided by `z.im`. -/
theorem norm_tangentSpace (z : ℍ) (v : TangentSpace 𝓘(ℝ, ℂ) z) :
    ‖v‖ = ‖tangentSpaceCastModel 𝓘(ℝ, ℂ) z v‖ / z.im := by
  rw [norm_eq_sqrt_real_inner, inner_tangentSpace, Real.sqrt_div (real_inner_self_nonneg),
    real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq z.im_pos.le]

/-- The real Fréchet derivative of the reflection `J : z ↦ -conj z` is `v ↦ -conj v`. -/
@[simp]
theorem smulFDeriv_J (z : ℂ) :
    smulFDeriv J z = -Complex.conjCLE.toContinuousLinearMap := by
  have h := smulFDeriv_J_mul 1 z
  rw [mul_one] at h
  ext v
  have h1 : smulFDeriv 1 z v = v := by
    simp [smulFDeriv, σ, denom]
  simp [h, h1]

/-- `UpperHalfPlane.σ g` preserves the real Euclidean inner product on `ℂ`. -/
theorem inner_σ (g : GL (Fin 2) ℝ) (u w : ℂ) :
    inner ℝ (σ g u) (σ g w) = inner ℝ u w := by
  unfold σ
  split_ifs
  · rfl
  · exact Complex.conjLIE.inner_map_map u w

/-- In model coordinates, `smulFDeriv g z` preserves the Euclidean inner product divided by the
square of the imaginary coordinate. -/
theorem inner_smulFDeriv (z : ℍ) (g : GL (Fin 2) ℝ) (u w : ℂ) :
    inner ℝ (smulFDeriv g z u) (smulFDeriv g z w) / (g • z).im ^ 2 =
      inner ℝ u w / z.im ^ 2 := by
  have hscale (α : ℂ) : inner ℝ (u * α) (w * α) = Complex.normSq α * inner ℝ u w := by
    simp [Complex.inner, Complex.normSq_apply]
    ring
  have hsq : Complex.normSq ((g.det.val : ℂ) / denom g z ^ 2) = ((g • z).im / z.im) ^ 2 := by
    have hz : z.im ≠ 0 := z.im_ne_zero
    rw [map_div₀, map_pow, Complex.normSq_ofReal, im_smul_eq_div_normSq, ← sq, ← sq_abs]
    field_simp
  have hz : z.im ≠ 0 := z.im_ne_zero
  have him : (g • z).im ≠ 0 := (g • z).im_ne_zero
  have happly (x : ℂ) :
      smulFDeriv g z x = σ g (x * ((g.det.val : ℂ) / denom g z ^ 2)) := rfl
  rw [happly u, happly w, inner_σ, hscale, hsq]
  field_simp

/-- The reflection `UpperHalfPlane.J : z ↦ -conj z` is `C^n` as a map of real manifolds on `ℍ`. -/
theorem contMDiff_real_J_smul {n : WithTop ℕ∞} :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) n (J • · : ℍ → ℍ) := by
  apply ContMDiff.of_comp_isOpenEmbedding isOpenEmbedding_coe
  have hcoe : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) n UpperHalfPlane.coe :=
    fun _ ↦ contMDiffAt_extChartAt
  have hneg : ContDiff ℝ n fun z : ℂ ↦ -conj z :=
    (-Complex.conjCLE.toContinuousLinearMap).contDiff
  have hcomp :
      UpperHalfPlane.coe ∘ (J • · : ℍ → ℍ) = (fun z : ℂ ↦ -conj z) ∘ UpperHalfPlane.coe := by
    funext z
    exact coe_J_smul z
  rw [hcomp]
  exact hneg.contMDiff.comp hcoe

/-- Every element of `GL(2, ℝ)` acts on `ℍ` by a `C^n` map of real manifolds, including elements of
negative determinant. -/
theorem contMDiff_real_smul {n : WithTop ℕ∞} (g : GL (Fin 2) ℝ) :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) n (g • · : ℍ → ℍ) := by
  have hpos {h : GL (Fin 2) ℝ} (hh : 0 < (h.det : ℝ)) :
      ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) n (h • · : ℍ → ℍ) := by
    have hh' : 0 < h.val.det := by simpa [Matrix.GeneralLinearGroup.val_det_apply] using hh
    simpa only [modelWithCornersSelf_restrictScalars] using
      (contMDiff_smul (n := n) hh').restrictScalars ℝ
  rcases g.det.ne_zero.lt_or_gt with hg | hg
  · have hJg : 0 < ((J * g).det : ℝ) := by simpa using hg
    have hcomp : (g • · : ℍ → ℍ) = (J • ·) ∘ ((J * g) • ·) := by
      funext z
      simp [smul_smul, ← mul_assoc, ← sq]
    rw [hcomp]
    exact contMDiff_real_J_smul.comp (hpos hJg)
  · exact hpos hg

/-- The action of `GL(2, ℝ)` on `ℍ` is `C^n` for the real manifold structure `𝓘(ℝ, ℂ)`. -/
instance instContMDiffConstSMulRealGL {n : WithTop ℕ∞} :
    ContMDiffConstSMul 𝓘(ℝ, ℂ) n (GL (Fin 2) ℝ) ℍ :=
  ⟨contMDiff_real_smul⟩

/-- The action of `PGL(2, ℝ)` on `ℍ` is `C^n` for the real manifold structure `𝓘(ℝ, ℂ)`. -/
instance instContMDiffConstSMulRealPGL {n : WithTop ℕ∞} :
    ContMDiffConstSMul 𝓘(ℝ, ℂ) n PGL(2, ℝ) ℍ where
  contMDiff_const_smul q := by
    induction q using Matrix.ProjGenLinGroup.induction_on with | mk g =>
    simpa only [pglMk_smul] using contMDiff_real_smul g

/-- The action of `SL(2, ℝ)` on `ℍ` is `C^n` for the real manifold structure `𝓘(ℝ, ℂ)`. -/
instance instContMDiffConstSMulRealSL {n : WithTop ℕ∞} :
    ContMDiffConstSMul 𝓘(ℝ, ℂ) n SL(2, ℝ) ℍ where
  contMDiff_const_smul g := by
    simpa only [Matrix.SpecialLinearGroup.toGL_smul] using
      contMDiff_real_smul (Matrix.SpecialLinearGroup.toGL g)

/-- The action of `PSL(2, ℝ)` on `ℍ` is `C^n` for the real manifold structure `𝓘(ℝ, ℂ)`. -/
instance instContMDiffConstSMulRealPSL {n : WithTop ℕ∞} :
    ContMDiffConstSMul 𝓘(ℝ, ℂ) n PSL(2, ℝ) ℍ where
  contMDiff_const_smul q :=
    QuotientGroup.induction_on q fun g ↦ by
      simpa only [pslMk_smul] using contMDiff_const_smul (I := 𝓘(ℝ, ℂ)) (n := n) g

/-- In model coordinates, the manifold derivative of `(g • · : ℍ → ℍ)` at `z` is
`UpperHalfPlane.smulFDeriv g z`. -/
theorem tangentSpaceCastModel_mfderiv_smul (z : ℍ) (g : GL (Fin 2) ℝ)
    (v : TangentSpace 𝓘(ℝ, ℂ) z) :
    tangentSpaceCastModel 𝓘(ℝ, ℂ) (g • z) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (g • ·) z v) =
      smulFDeriv g z (tangentSpaceCastModel 𝓘(ℝ, ℂ) z v) := by
  rw [((contMDiff_real_smul (n := ∞) g).mdifferentiableAt
    (by simp)).tangentSpaceCastModel_mfderiv_apply]
  have hlocal : writtenInExtChartAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) z (g • · : ℍ → ℍ)
      =ᶠ[𝓝 (z : ℂ)] fun w : ℂ ↦ ↑(g • ofComplex w) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds z.im_pos]
      with w hw
    have hsymm : (extChartAt 𝓘(ℝ, ℂ) z).symm w = ⟨w, hw⟩ := by
      apply coe_injective
      exact (extChartAt 𝓘(ℝ, ℂ) z).right_inv (by simpa using hw)
    have hchart_apply (x : ℍ) : extChartAt 𝓘(ℝ, ℂ) (g • z) x = (x : ℂ) := by simp
    rw [writtenInExtChartAt, Function.comp_apply, Function.comp_apply, hsymm, hchart_apply,
      ofComplex_apply_of_im_pos hw]
  have hchart : extChartAt 𝓘(ℝ, ℂ) z z = (z : ℂ) := by simp
  rw [hchart, hlocal.fderiv_eq, (hasStrictFDerivAt_smul g z).hasFDerivAt.fderiv]

/-- Every element of `GL(2, ℝ)` preserves the Poincaré inner product on tangent spaces of `ℍ`. -/
theorem inner_mfderiv_smul (z : ℍ) (g : GL (Fin 2) ℝ) (u w : TangentSpace 𝓘(ℝ, ℂ) z) :
    inner ℝ (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (g • ·) z u) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (g • ·) z w) =
      inner ℝ u w := by
  rw [inner_tangentSpace, inner_tangentSpace, tangentSpaceCastModel_mfderiv_smul,
    tangentSpaceCastModel_mfderiv_smul, inner_smulFDeriv]

/-- Every element of `PGL(2, ℝ)` preserves the Poincaré inner product on tangent spaces of `ℍ`. -/
theorem inner_mfderiv_pgl_smul (z : ℍ) (q : PGL(2, ℝ)) (u w : TangentSpace 𝓘(ℝ, ℂ) z) :
    inner ℝ (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (q • ·) z u) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (q • ·) z w) =
      inner ℝ u w := by
  induction q using Matrix.ProjGenLinGroup.induction_on with | mk g =>
  have heq : (fun x : ℍ ↦ Matrix.ProjGenLinGroup.mk g • x) = fun x ↦ g • x :=
    funext (pglMk_smul g)
  rw [heq]
  exact inner_mfderiv_smul z g u w

/-- Every element of `SL(2, ℝ)` preserves the Poincaré inner product on tangent spaces of `ℍ`. -/
theorem inner_mfderiv_sl_smul (z : ℍ) (g : SL(2, ℝ)) (u w : TangentSpace 𝓘(ℝ, ℂ) z) :
    inner ℝ (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (g • ·) z u) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (g • ·) z w) =
      inner ℝ u w := by
  have heq : (fun x : ℍ ↦ g • x) = fun x ↦ Matrix.SpecialLinearGroup.toGL g • x :=
    funext fun x ↦ (Matrix.SpecialLinearGroup.toGL_smul g x).symm
  rw [heq]
  exact inner_mfderiv_smul z (Matrix.SpecialLinearGroup.toGL g) u w

/-- Every element of `PSL(2, ℝ)` preserves the Poincaré inner product on tangent spaces of `ℍ`. -/
theorem inner_mfderiv_psl_smul (z : ℍ) (q : PSL(2, ℝ)) (u w : TangentSpace 𝓘(ℝ, ℂ) z) :
    inner ℝ (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (q • ·) z u) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (q • ·) z w) =
      inner ℝ u w :=
  QuotientGroup.induction_on q fun g ↦ by
    have heq : (fun x : ℍ ↦ (QuotientGroup.mk g : PSL(2, ℝ)) • x) = fun x ↦ g • x :=
      funext (pslMk_smul g)
    rw [heq]
    exact inner_mfderiv_sl_smul z g u w

end UpperHalfPlane

namespace TauCeti.UpperHalfPlane

open _root_.UpperHalfPlane

/-- The action of `GL(2, ℝ)` on `ℍ` as a homomorphism to the Riemannian isometry group of the
Poincaré metric. -/
def glIsomHom : GL (Fin 2) ℝ →* Isom 𝓘(ℝ, ℂ) ℍ :=
  RiemannianIsometry.constSMulHom fun g z u w ↦ inner_mfderiv_smul z g u w

@[simp]
theorem glIsomHom_apply_apply (g : GL (Fin 2) ℝ) (z : ℍ) : glIsomHom g z = g • z := by
  simp [glIsomHom]

/-- The action of `PGL(2, ℝ)` on `ℍ` as an injective homomorphism to `Isom 𝓘(ℝ, ℂ) ℍ`. -/
def pglIsomHom : PGL(2, ℝ) →* Isom 𝓘(ℝ, ℂ) ℍ :=
  RiemannianIsometry.constSMulHom fun q z u w ↦ inner_mfderiv_pgl_smul z q u w

@[simp]
theorem pglIsomHom_apply_apply (q : PGL(2, ℝ)) (z : ℍ) : pglIsomHom q z = q • z := by
  simp [pglIsomHom]

/-- `PGL(2, ℝ)` embeds faithfully into the Riemannian isometry group of `ℍ`. -/
theorem pglIsomHom_injective : Function.Injective pglIsomHom :=
  RiemannianIsometry.constSMulHom_injective _

@[simp]
theorem pglIsomHom_mk (g : GL (Fin 2) ℝ) :
    pglIsomHom (Matrix.ProjGenLinGroup.mk g) = glIsomHom g := by
  ext z
  simp [pglMk_smul]

/-- The action of `SL(2, ℝ)` on `ℍ` as a homomorphism to `Isom 𝓘(ℝ, ℂ) ℍ`. -/
def slIsomHom : SL(2, ℝ) →* Isom 𝓘(ℝ, ℂ) ℍ :=
  RiemannianIsometry.constSMulHom fun g z u w ↦ inner_mfderiv_sl_smul z g u w

@[simp]
theorem slIsomHom_apply_apply (g : SL(2, ℝ)) (z : ℍ) : slIsomHom g z = g • z := by
  simp [slIsomHom]

@[simp]
theorem glIsomHom_toGL (g : SL(2, ℝ)) :
    glIsomHom (Matrix.SpecialLinearGroup.toGL g) = slIsomHom g := by
  ext z
  simp [Matrix.SpecialLinearGroup.toGL_smul]

/-- The action of `PSL(2, ℝ)` on `ℍ` as an injective homomorphism to `Isom 𝓘(ℝ, ℂ) ℍ`. -/
def pslIsomHom : PSL(2, ℝ) →* Isom 𝓘(ℝ, ℂ) ℍ :=
  RiemannianIsometry.constSMulHom fun q z u w ↦ inner_mfderiv_psl_smul z q u w

@[simp]
theorem pslIsomHom_apply_apply (q : PSL(2, ℝ)) (z : ℍ) : pslIsomHom q z = q • z := by
  simp [pslIsomHom]

/-- `PSL(2, ℝ)` embeds faithfully into the Riemannian isometry group of `ℍ`. -/
theorem pslIsomHom_injective : Function.Injective pslIsomHom :=
  RiemannianIsometry.constSMulHom_injective _

@[simp]
theorem pslIsomHom_mk (g : SL(2, ℝ)) :
    pslIsomHom (QuotientGroup.mk g) = slIsomHom g := by
  ext z
  simp [pslMk_smul]

/-- The orientation-reversing reflection `UpperHalfPlane.J : z ↦ -conj z` does not lie in the image
of `pslIsomHom`. -/
theorem pslIsomHom_ne_glIsomHom_J (q : PSL(2, ℝ)) :
    pslIsomHom q ≠ glIsomHom J := by
  refine QuotientGroup.induction_on q fun g h ↦ ?_
  have hJ : HasFDerivAt (fun z : ℂ ↦ (↑(Matrix.SpecialLinearGroup.toGL g • ofComplex z) : ℂ))
      (smulFDeriv J I) I := by
    refine (hasStrictFDerivAt_smul J I).hasFDerivAt.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun z ↦ ?_)
    have hz := DFunLike.congr_fun h (ofComplex z)
    simpa [pslMk_smul, Matrix.SpecialLinearGroup.toGL_smul] using
      congrArg UpperHalfPlane.coe hz
  have hfderiv : smulFDeriv (Matrix.SpecialLinearGroup.toGL g) (I : ℂ) = smulFDeriv J (I : ℂ) :=
    (hasStrictFDerivAt_smul (Matrix.SpecialLinearGroup.toGL g) I).hasFDerivAt.unique hJ
  have hdet_pos : 0 < (smulFDeriv (Matrix.SpecialLinearGroup.toGL g) (I : ℂ)).det := by
    rw [det_smulFDeriv]
    have hd : (Matrix.SpecialLinearGroup.toGL g).det = 1 := by simp
    have hdenom : 0 < ‖denom (Matrix.SpecialLinearGroup.toGL g) (I : ℂ)‖ ^ 4 :=
      pow_pos (norm_pos_iff.mpr (denom_ne_zero _ I)) 4
    rw [hd]
    simpa using div_pos one_pos hdenom
  have hdet_J : (smulFDeriv J (I : ℂ)).det = -1 := by
    rw [det_smulFDeriv]
    simp [sign_neg (neg_one_lt_zero : (-1 : ℝ) < 0)]
  linarith [congrArg ContinuousLinearMap.det hfderiv]

/-- The Riemannian isometry group of the Poincaré metric acts transitively on `ℍ`. -/
instance isPretransitive_isom : MulAction.IsPretransitive (Isom 𝓘(ℝ, ℂ) ℍ) ℍ where
  exists_smul_eq z w := by
    obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq (GL (Fin 2) ℝ) z w
    exact ⟨glIsomHom g, by simp⟩

end TauCeti.UpperHalfPlane

end

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.PoincareMetric.Basic
public import TauCeti.Analysis.Complex.UpperHalfPlane.PSL.Manifold
public import TauCeti.Analysis.Complex.UpperHalfPlane.SmulDeriv
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Action
import Mathlib.Analysis.Complex.UpperHalfPlane.FixedPoints
import TauCeti.Analysis.Complex.UpperHalfPlane.ProperAction
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic

/-!
# Riemannian isometries of the Poincaré metric on the upper half-plane

Mathlib's action `UpperHalfPlane.glAction` of `GL(2, ℝ)` on the complex upper half-plane `ℍ` sends
`z` to `(a z + b) / (c z + d)` when `det g > 0` and to `(a conj z + b) / (c conj z + d)` when
`det g < 0`. Every element acts smoothly on `ℍ` as a real manifold and preserves the Poincaré
tensor `(Re v · Re w + Im v · Im w) / (Im z)²`:

* An element of positive determinant acts holomorphically with complex derivative
  `det g / (c z + d)²`, whose modulus `|det g| / |c z + d|²` equals `Im (g • z) / Im z` by
  `UpperHalfPlane.im_smul_eq_div_normSq`.
* The reflection `UpperHalfPlane.J = diag(-1, 1)` acts by `z ↦ -conj z`, whose real differential
  `v ↦ -conj v` preserves the Euclidean inner product on `ℂ` while keeping `Im z` unchanged; any
  matrix `g` of negative determinant factors as `J * (J * g)` with `det (J * g) > 0`.

Consequently, `GL(2, ℝ)`, `PGL(2, ℝ)`, `PSL(2, ℝ)`, and `SL(2, ℝ)` act on `ℍ` by smooth
Riemannian isometries, packaged via `TauCeti.RiemannianIsometry.constSMulHom` as group
homomorphisms into `TauCeti.Isom 𝓘(ℝ, ℂ) ℍ`. Because `PGL(2, ℝ)` and `PSL(2, ℝ)` act faithfully
on `ℍ`, their homomorphisms into `Isom 𝓘(ℝ, ℂ) ℍ` are injective, and transitivity of the
`PSL(2, ℝ)`-action makes `(ℍ, poincareRiemannianMetric)` a homogeneous Riemannian manifold.

## Main declarations

* `UpperHalfPlane.inner_tangentSpace`, `UpperHalfPlane.norm_tangentSpace`,
  `UpperHalfPlane.eNorm_tangentSpace`: the installed Poincaré inner product, norm, and extended
  norm on `TangentSpace 𝓘(ℝ, ℂ) z`.
* `Matrix.ProjectiveSpecialLinearGroup.norm_smulDeriv`: `‖q.smulDeriv z‖ = (q • z).im / z.im`.
* `TauCeti.UpperHalfPlane.instContMDiffConstSMulGLReal`,
  `TauCeti.UpperHalfPlane.instContMDiffConstSMulPGLReal`,
  `TauCeti.UpperHalfPlane.instContMDiffConstSMulPSL2Real`,
  `TauCeti.UpperHalfPlane.instContMDiffConstSMulSL2Complex`,
  `TauCeti.UpperHalfPlane.instContMDiffConstSMulSL2Real`: `C^n` smoothness of the matrix actions.
* `UpperHalfPlane.tangentSpaceCastModel_mfderiv_smul`: the real differential of `g • ·` in model
  coordinates is Mathlib's `UpperHalfPlane.smulFDeriv g z`.
* `TauCeti.UpperHalfPlane.glToIsom`, `pglToIsom`, `pslToIsom`, `slToIsom`: group homomorphisms from
  `GL(2, ℝ)`, `PGL(2, ℝ)`, `PSL(2, ℝ)`, and `SL(2, ℝ)` to `TauCeti.Isom 𝓘(ℝ, ℂ) ℍ`, with
  `pglToIsom_injective` and `pslToIsom_injective`.
* `TauCeti.UpperHalfPlane.isPretransitive_isom`: `Isom 𝓘(ℝ, ℂ) ℍ` acts transitively on `ℍ`.

## References

* Svetlana Katok, *Fuchsian Groups*, Chicago Lectures in Mathematics, 1992, §§1.1–1.2.
* Alan Beardon, *The Geometry of Discrete Groups*, Springer GTM 91, 1983, §7.2.
* John M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176, 2018, Chapter 3.
-/

public section

open Bundle Manifold Matrix Matrix.SpecialLinearGroup UpperHalfPlane
open scoped ComplexConjugate ContDiff ENNReal Manifold MatrixGroups Topology UpperHalfPlane

noncomputable section

/-! ### Installed Poincaré inner product and norm on `TangentSpace 𝓘(ℝ, ℂ)` -/

namespace UpperHalfPlane

/-- The installed Riemannian inner product on `TangentSpace 𝓘(ℝ, ℂ) z` is the Euclidean inner
product on `ℂ` divided by `(Im z)²`. -/
theorem inner_tangentSpace (z : ℍ) (v w : TangentSpace 𝓘(ℝ, ℂ) z) :
    inner ℝ v w =
      inner ℝ (tangentSpaceCastModel 𝓘(ℝ, ℂ) z v)
        (tangentSpaceCastModel 𝓘(ℝ, ℂ) z w) / z.im ^ 2 :=
  -- `instRiemannianBundle` installs `poincareRiemannianMetric.toRiemannianMetric` by definition.
  poincareRiemannianMetric_inner z v w

/-- The Poincaré norm of a tangent vector at `z : ℍ` is its Euclidean norm divided by `Im z`. -/
theorem norm_tangentSpace (z : ℍ) (v : TangentSpace 𝓘(ℝ, ℂ) z) :
    ‖v‖ = ‖tangentSpaceCastModel 𝓘(ℝ, ℂ) z v‖ / z.im := by
  rw [norm_eq_sqrt_real_inner, inner_tangentSpace, real_inner_self_eq_norm_sq, ← div_pow,
    Real.sqrt_sq (div_nonneg (norm_nonneg _) z.im_pos.le)]

/-- The Poincaré extended norm of a tangent vector at `z : ℍ` is its Euclidean extended norm
divided by `ENNReal.ofReal z.im`. -/
theorem eNorm_tangentSpace (z : ℍ) (v : TangentSpace 𝓘(ℝ, ℂ) z) :
    ‖v‖ₑ = ‖tangentSpaceCastModel 𝓘(ℝ, ℂ) z v‖ₑ / ENNReal.ofReal z.im := by
  rw [← ofReal_norm, ← ofReal_norm, norm_tangentSpace, ENNReal.ofReal_div_of_pos z.im_pos]

end UpperHalfPlane

/-! ### Modulus of `smulDeriv` and derivative of `pslS` -/

namespace Matrix.ProjectiveSpecialLinearGroup

/-- **Modulus of the Möbius derivative.** For `q : PSL(2, ℝ)` and `z : ℍ`, the modulus of
`q.smulDeriv z` equals the imaginary-part ratio `(q • z).im / z.im`. -/
theorem norm_smulDeriv (q : PSL(2, ℝ)) (z : ℍ) :
    ‖q.smulDeriv z‖ = (q • z).im / z.im := by
  induction q using QuotientGroup.induction_on with | _ g =>
  have him := _root_.UpperHalfPlane.im_smul_eq_div_normSq (mapGL ℝ g) z
  rw [det_mapGL, Units.val_one, abs_one, one_mul, mapGL_smul] at him
  rw [smulDeriv_coe, norm_inv, norm_pow, ← Complex.normSq_eq_norm_sq, pslMk_smul, him,
    div_right_comm, div_self z.im_ne_zero, one_div]

/-- The inversion `TauCeti.pslS` (`z ↦ -1 / z`) has complex derivative `(z ^ 2)⁻¹` at `z : ℍ`. -/
theorem smulDeriv_pslS (z : ℍ) :
    smulDeriv TauCeti.pslS z = ((z : ℂ) ^ 2)⁻¹ := by
  rw [TauCeti.pslS_def, psl2zToPSL2R_mk, sl2zToPSL2R_apply, smulDeriv_coe]
  congr 2
  simp [denom, ModularGroup.coe_S]

end Matrix.ProjectiveSpecialLinearGroup

/-! ### Smoothness of the `GL(2, ℝ)`, `PGL(2, ℝ)`, `PSL(2, ℝ)` and `SL(2, ℝ)` actions -/

namespace TauCeti.UpperHalfPlane

/-- The orientation-reversing reflection `UpperHalfPlane.J : z ↦ -conj z` is `C^n` on `ℍ` as a
real manifold for every smoothness exponent `n`. -/
theorem contMDiff_J_smul {n : ℕ∞ω} :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) n (J • · : ℍ → ℍ) := by
  apply ContMDiff.of_comp_isOpenEmbedding _root_.UpperHalfPlane.isOpenEmbedding_coe
  have hcoe : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) n _root_.UpperHalfPlane.coe :=
    fun _ ↦ contMDiffAt_extChartAt
  have hfun : _root_.UpperHalfPlane.coe ∘ (J • · : ℍ → ℍ) =
      (-Complex.conjCLE.toContinuousLinearMap : ℂ →L[ℝ] ℂ) ∘ _root_.UpperHalfPlane.coe := by
    funext z
    simp [coe_J_smul]
  rw [hfun]
  exact (-Complex.conjCLE.toContinuousLinearMap).contDiff.contMDiff.comp hcoe

/-- Every element of `GL(2, ℝ)` acts on `ℍ` by a `C^n` map of real manifolds, including
orientation-reversing elements of negative determinant. -/
instance instContMDiffConstSMulGLReal {n : ℕ∞ω} :
    ContMDiffConstSMul 𝓘(ℝ, ℂ) n (GL (Fin 2) ℝ) ℍ where
  contMDiff_const_smul g := by
    have hpos {h : GL (Fin 2) ℝ} (hh : 0 < h.det.val) :
        ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) n (h • · : ℍ → ℍ) := by
      simpa using (_root_.UpperHalfPlane.contMDiff_smul (n := n) hh).restrictScalars ℝ
    rcases g.det.ne_zero.lt_or_gt with hg | hg
    · have hJg : 0 < (J * g).det.val := by simpa using hg
      have hcomp : (g • · : ℍ → ℍ) = (J • ·) ∘ ((J * g) • ·) := by
        funext z
        simp [smul_smul, ← mul_assoc, ← sq]
      rw [hcomp]
      exact contMDiff_J_smul.comp (hpos hJg)
    · exact hpos hg

/-- Every element of `PGL(2, ℝ)` acts on `ℍ` by a `C^n` map of real manifolds. -/
instance instContMDiffConstSMulPGLReal {n : ℕ∞ω} :
    ContMDiffConstSMul 𝓘(ℝ, ℂ) n PGL(2, ℝ) ℍ where
  contMDiff_const_smul q := by
    induction q using Matrix.ProjGenLinGroup.induction_on with | mk g =>
    simpa only [pglMk_smul] using contMDiff_const_smul (I := 𝓘(ℝ, ℂ)) (n := n) g

/-- Every element of `SL(2, ℝ)` acts holomorphically (`C^n` over `ℂ`) on `ℍ`. -/
instance instContMDiffConstSMulSL2Complex {n : ℕ∞ω} :
    ContMDiffConstSMul 𝓘(ℂ, ℂ) n SL(2, ℝ) ℍ where
  contMDiff_const_smul g := by
    simpa only [toGL_smul] using
      _root_.UpperHalfPlane.contMDiff_smul (n := n) (g := g.toGL) (by simp)

/-- Every element of `SL(2, ℝ)` acts on `ℍ` by a `C^n` map of real manifolds. -/
instance instContMDiffConstSMulSL2Real {n : ℕ∞ω} :
    ContMDiffConstSMul 𝓘(ℝ, ℂ) n SL(2, ℝ) ℍ :=
  ContMDiffConstSMul.restrictScalars ℝ instContMDiffConstSMulSL2Complex

/-- Every element of `PSL(2, ℝ)` acts on `ℍ` by a `C^n` map of real manifolds. -/
instance instContMDiffConstSMulPSL2Real {n : ℕ∞ω} :
    ContMDiffConstSMul 𝓘(ℝ, ℂ) n PSL(2, ℝ) ℍ where
  contMDiff_const_smul q := by
    induction q using QuotientGroup.induction_on with | _ g =>
    simpa only [pslMk_smul] using contMDiff_const_smul (I := 𝓘(ℝ, ℂ)) (n := n) g

/-! ### Differentials in model coordinates and preservation of the Poincaré metric -/

/-- In the inclusion chart, the real manifold derivative of `g • · : ℍ → ℍ` at `z : ℍ` is
Mathlib's `UpperHalfPlane.smulFDeriv g z`. -/
theorem _root_.UpperHalfPlane.tangentSpaceCastModel_mfderiv_smul (g : GL (Fin 2) ℝ) (z : ℍ)
    (v : TangentSpace 𝓘(ℝ, ℂ) z) :
    tangentSpaceCastModel 𝓘(ℝ, ℂ) (g • z) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (g • ·) z v) =
      _root_.UpperHalfPlane.smulFDeriv g z (tangentSpaceCastModel 𝓘(ℝ, ℂ) z v) := by
  have hmd : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (g • · : ℍ → ℍ) z :=
    (contMDiff_const_smul (I := 𝓘(ℝ, ℂ)) (n := (1 : ℕ∞ω)) g z).mdifferentiableAt one_ne_zero
  rw [hmd.tangentSpaceCastModel_mfderiv_apply]
  have hlocal : writtenInExtChartAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) z (g • · : ℍ → ℍ) =ᶠ[𝓝 (z : ℂ)]
      fun w : ℂ ↦ ((g • ofComplex w : ℍ) : ℂ) := by
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds z.im_pos] with w hw
    have hsymm : (extChartAt 𝓘(ℝ, ℂ) z).symm w = ofComplex w := by
      apply _root_.UpperHalfPlane.ext
      rw [ofComplex_apply_of_im_pos hw]
      exact (extChartAt 𝓘(ℝ, ℂ) z).right_inv (by simpa using hw)
    dsimp only [writtenInExtChartAt, Function.comp_apply]
    rw [hsymm]
    simp
  have hchart : extChartAt 𝓘(ℝ, ℂ) z z = (z : ℂ) := by simp
  rw [hchart, hlocal.fderiv_eq,
    (_root_.UpperHalfPlane.hasStrictFDerivAt_smul g z).hasFDerivAt.fderiv]

private theorem tangentSpaceCastModel_mfderiv_congr {f₁ f₂ : ℍ → ℍ} (h : f₁ = f₂) (z : ℍ)
    (v : TangentSpace 𝓘(ℝ, ℂ) z) :
    tangentSpaceCastModel 𝓘(ℝ, ℂ) (f₁ z) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) f₁ z v) =
      tangentSpaceCastModel 𝓘(ℝ, ℂ) (f₂ z) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) f₂ z v) := by
  cases h
  rfl

/-- For `g : GL (Fin 2) ℝ` of positive determinant, the real differential of `g • ·` at `z`
multiplies model tangent vectors by `det g / denom g z ^ 2`. -/
theorem _root_.UpperHalfPlane.tangentSpaceCastModel_mfderiv_smul_of_det_pos
    {g : GL (Fin 2) ℝ} (hg : 0 < g.det.val) (z : ℍ) (v : TangentSpace 𝓘(ℝ, ℂ) z) :
    tangentSpaceCastModel 𝓘(ℝ, ℂ) (g • z) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (g • ·) z v) =
      (g.det.val / denom g z ^ 2) * tangentSpaceCastModel 𝓘(ℝ, ℂ) z v := by
  rw [_root_.UpperHalfPlane.tangentSpaceCastModel_mfderiv_smul]
  simp [_root_.UpperHalfPlane.smulFDeriv,
    σ_eq_refl_of_det_pos (by rwa [← Matrix.GeneralLinearGroup.val_det_apply]), mul_comm]

/-- For `q : PSL(2, ℝ)`, the real differential of `q • ·` at `z` multiplies model tangent vectors
by the complex derivative `q.smulDeriv z`. -/
theorem _root_.Matrix.ProjectiveSpecialLinearGroup.tangentSpaceCastModel_mfderiv_smul
    (q : PSL(2, ℝ)) (z : ℍ) (v : TangentSpace 𝓘(ℝ, ℂ) z) :
    tangentSpaceCastModel 𝓘(ℝ, ℂ) (q • z) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (q • ·) z v) =
      q.smulDeriv z * tangentSpaceCastModel 𝓘(ℝ, ℂ) z v := by
  induction q using QuotientGroup.induction_on with | _ g =>
  have hfun : ((g : PSL(2, ℝ)) • · : ℍ → ℍ) = (mapGL ℝ g • ·) := by
    funext w
    rw [pslMk_smul, mapGL_smul]
  have hg : 0 < (mapGL ℝ g).det.val := by simp
  rw [tangentSpaceCastModel_mfderiv_congr hfun,
    _root_.UpperHalfPlane.tangentSpaceCastModel_mfderiv_smul_of_det_pos hg, smulDeriv_coe,
    det_mapGL, Units.val_one, Complex.ofReal_one, one_div]

/-- The real differential of the reflection `UpperHalfPlane.J : z ↦ -conj z` acts in model
coordinates by `v ↦ -conj v`. -/
theorem _root_.UpperHalfPlane.tangentSpaceCastModel_mfderiv_J_smul (z : ℍ)
    (v : TangentSpace 𝓘(ℝ, ℂ) z) :
    tangentSpaceCastModel 𝓘(ℝ, ℂ) (J • z) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (J • ·) z v) =
      -conj (tangentSpaceCastModel 𝓘(ℝ, ℂ) z v) := by
  rw [_root_.UpperHalfPlane.tangentSpaceCastModel_mfderiv_smul]
  simp [_root_.UpperHalfPlane.smulFDeriv, _root_.UpperHalfPlane.σ, denom,
    show ¬ (1 : ℝ) < 0 by norm_num]

/-- `UpperHalfPlane.smulFDeriv g z` scales Euclidean inner products on `ℂ` by
`((g • z).im / z.im) ^ 2`. -/
private theorem inner_smulFDeriv (g : GL (Fin 2) ℝ) (z : ℍ) (u w : ℂ) :
    inner ℝ (_root_.UpperHalfPlane.smulFDeriv g z u) (_root_.UpperHalfPlane.smulFDeriv g z w) =
      ((g • z).im / z.im) ^ 2 * inner ℝ u w := by
  set c : ℂ := g.det.val / denom g z ^ 2
  have hσ (a b : ℂ) : inner ℝ (σ g a) (σ g b) = inner ℝ a b := by
    dsimp only [σ]
    split_ifs <;> simp [Complex.inner]
  have hmul (a b : ℂ) : inner ℝ (a • c) (b • c) = ‖c‖ ^ 2 * inner ℝ a b := by
    simp only [smul_eq_mul, Complex.inner, Complex.mul_re, Complex.mul_im, Complex.conj_re,
      Complex.conj_im, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  have hnorm : ‖c‖ = (g • z).im / z.im := by
    rw [_root_.UpperHalfPlane.im_smul_eq_div_normSq, div_right_comm,
      mul_div_cancel_right₀ _ z.im_ne_zero]
    simp [c, Complex.normSq_eq_norm_sq]
  change inner ℝ (σ g (u • c)) (σ g (w • c)) = ((g • z).im / z.im) ^ 2 * inner ℝ u w
  rw [hσ, hmul, hnorm]

private theorem inner_mfderiv_congr {f₁ f₂ : ℍ → ℍ} (h : f₁ = f₂) (z : ℍ)
    (v w : TangentSpace 𝓘(ℝ, ℂ) z) :
    inner ℝ (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) f₁ z v) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) f₁ z w) =
      inner ℝ (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) f₂ z v) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) f₂ z w) := by
  cases h
  rfl

/-- Every element of `GL(2, ℝ)` preserves the Poincaré Riemannian inner product on `ℍ`. -/
theorem inner_mfderiv_gl_smul (g : GL (Fin 2) ℝ) (z : ℍ) (v w : TangentSpace 𝓘(ℝ, ℂ) z) :
    inner ℝ (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (g • ·) z v) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (g • ·) z w) =
      inner ℝ v w := by
  rw [_root_.UpperHalfPlane.inner_tangentSpace, _root_.UpperHalfPlane.inner_tangentSpace,
    _root_.UpperHalfPlane.tangentSpaceCastModel_mfderiv_smul,
    _root_.UpperHalfPlane.tangentSpaceCastModel_mfderiv_smul, inner_smulFDeriv]
  have hz : z.im ≠ 0 := z.im_ne_zero
  have hgz : (g • z).im ≠ 0 := (g • z).im_ne_zero
  field_simp

/-- Every element of `PGL(2, ℝ)` preserves the Poincaré Riemannian inner product on `ℍ`. -/
theorem inner_mfderiv_pgl_smul (q : PGL(2, ℝ)) (z : ℍ) (v w : TangentSpace 𝓘(ℝ, ℂ) z) :
    inner ℝ (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (q • ·) z v) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (q • ·) z w) =
      inner ℝ v w := by
  induction q using Matrix.ProjGenLinGroup.induction_on with | mk g =>
  rw [inner_mfderiv_congr (funext (pglMk_smul g))]
  exact inner_mfderiv_gl_smul g z v w

/-- Every element of `PSL(2, ℝ)` preserves the Poincaré Riemannian inner product on `ℍ`. -/
theorem inner_mfderiv_psl_smul (q : PSL(2, ℝ)) (z : ℍ) (v w : TangentSpace 𝓘(ℝ, ℂ) z) :
    inner ℝ (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (q • ·) z v) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (q • ·) z w) =
      inner ℝ v w := by
  rw [inner_mfderiv_congr (funext fun x ↦ (toPGL_smul q x).symm)]
  exact inner_mfderiv_pgl_smul q.toPGL z v w

/-- Every element of `SL(2, ℝ)` preserves the Poincaré Riemannian inner product on `ℍ`. -/
theorem inner_mfderiv_sl_smul (g : SL(2, ℝ)) (z : ℍ) (v w : TangentSpace 𝓘(ℝ, ℂ) z) :
    inner ℝ (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (g • ·) z v) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (g • ·) z w) =
      inner ℝ v w := by
  rw [inner_mfderiv_congr (funext fun x ↦ (toGL_smul g x).symm)]
  exact inner_mfderiv_gl_smul g.toGL z v w

/-! ### Homomorphisms into the Riemannian isometry group `Isom 𝓘(ℝ, ℂ) ℍ` -/

/-- The action of `GL(2, ℝ)` on `ℍ` as a group homomorphism into the Riemannian isometry group of
the Poincaré metric. -/
def glToIsom : GL (Fin 2) ℝ →* Isom 𝓘(ℝ, ℂ) ℍ :=
  RiemannianIsometry.constSMulHom inner_mfderiv_gl_smul

/-- `glToIsom g` acts pointwise on `ℍ` by `g • z`. -/
@[simp]
theorem glToIsom_apply (g : GL (Fin 2) ℝ) (z : ℍ) : glToIsom g z = g • z := by
  simp [glToIsom]

/-- The function underlying `glToIsom g` is `(g • ·)`. -/
@[simp]
theorem coe_glToIsom (g : GL (Fin 2) ℝ) : ⇑(glToIsom g) = (g • ·) :=
  funext (glToIsom_apply g)

/-- The inverse Riemannian isometry of `glToIsom g` is `glToIsom g⁻¹`. -/
@[simp]
theorem glToIsom_symm (g : GL (Fin 2) ℝ) : (glToIsom g).symm = glToIsom g⁻¹ := by
  ext z
  simp [RiemannianIsometry.coe_symm]

/-- The action of `PGL(2, ℝ)` on `ℍ` as a group homomorphism into the Riemannian isometry group of
the Poincaré metric. -/
def pglToIsom : PGL(2, ℝ) →* Isom 𝓘(ℝ, ℂ) ℍ :=
  RiemannianIsometry.constSMulHom inner_mfderiv_pgl_smul

/-- `pglToIsom q` acts pointwise on `ℍ` by `q • z`. -/
@[simp]
theorem pglToIsom_apply (q : PGL(2, ℝ)) (z : ℍ) : pglToIsom q z = q • z := by
  simp [pglToIsom]

/-- The function underlying `pglToIsom q` is `(q • ·)`. -/
@[simp]
theorem coe_pglToIsom (q : PGL(2, ℝ)) : ⇑(pglToIsom q) = (q • ·) :=
  funext (pglToIsom_apply q)

/-- The inverse Riemannian isometry of `pglToIsom q` is `pglToIsom q⁻¹`. -/
@[simp]
theorem pglToIsom_symm (q : PGL(2, ℝ)) : (pglToIsom q).symm = pglToIsom q⁻¹ := by
  ext z
  simp [RiemannianIsometry.coe_symm]

/-- The projective homomorphism `pglToIsom` is injective. -/
theorem pglToIsom_injective : Function.Injective pglToIsom :=
  RiemannianIsometry.constSMulHom_injective inner_mfderiv_pgl_smul

/-- `glToIsom` factors through `pglToIsom` along the quotient projection `ProjGenLinGroup.mk`. -/
@[simp]
theorem pglToIsom_mk (g : GL (Fin 2) ℝ) :
    pglToIsom (Matrix.ProjGenLinGroup.mk g) = glToIsom g := by
  ext z
  simp

/-- The orientation-preserving action of `PSL(2, ℝ)` on `ℍ` as a group homomorphism into the
Riemannian isometry group of the Poincaré metric. -/
def pslToIsom : PSL(2, ℝ) →* Isom 𝓘(ℝ, ℂ) ℍ :=
  RiemannianIsometry.constSMulHom inner_mfderiv_psl_smul

/-- `pslToIsom q` acts pointwise on `ℍ` by `q • z`. -/
@[simp]
theorem pslToIsom_apply (q : PSL(2, ℝ)) (z : ℍ) : pslToIsom q z = q • z := by
  simp [pslToIsom]

/-- The function underlying `pslToIsom q` is `(q • ·)`. -/
@[simp]
theorem coe_pslToIsom (q : PSL(2, ℝ)) : ⇑(pslToIsom q) = (q • ·) :=
  funext (pslToIsom_apply q)

/-- The inverse Riemannian isometry of `pslToIsom q` is `pslToIsom q⁻¹`. -/
@[simp]
theorem pslToIsom_symm (q : PSL(2, ℝ)) : (pslToIsom q).symm = pslToIsom q⁻¹ := by
  ext z
  simp [RiemannianIsometry.coe_symm]

/-- The projective homomorphism `pslToIsom` is injective. -/
theorem pslToIsom_injective : Function.Injective pslToIsom :=
  RiemannianIsometry.constSMulHom_injective inner_mfderiv_psl_smul

/-- `pslToIsom` agrees with `pglToIsom` along the embedding `PSL(2, ℝ) →* PGL(2, ℝ)`. -/
@[simp]
theorem pglToIsom_toPGL (q : PSL(2, ℝ)) : pglToIsom q.toPGL = pslToIsom q := by
  ext z
  simp

/-- A positive-determinant matrix in `GL(2, ℝ)` induces the same Riemannian isometry as its
determinant-normalized class in `PSL(2, ℝ)`. -/
theorem pslToIsom_glPosToPSL2R (g : GL(2, ℝ)⁺) :
    pslToIsom (glPosToPSL2R g) = glToIsom g.1 := by
  apply RiemannianIsometry.ext
  intro z
  rw [pslToIsom_apply, glPosToPSL2R_smul, glToIsom_apply]
  rfl

/-- The action of `SL(2, ℝ)` on `ℍ` as a group homomorphism into `Isom 𝓘(ℝ, ℂ) ℍ`. -/
def slToIsom : SL(2, ℝ) →* Isom 𝓘(ℝ, ℂ) ℍ :=
  RiemannianIsometry.constSMulHom inner_mfderiv_sl_smul

/-- `slToIsom g` acts pointwise on `ℍ` by `g • z`. -/
@[simp]
theorem slToIsom_apply (g : SL(2, ℝ)) (z : ℍ) : slToIsom g z = g • z := by
  simp [slToIsom]

/-- The function underlying `slToIsom g` is `(g • ·)`. -/
@[simp]
theorem coe_slToIsom (g : SL(2, ℝ)) : ⇑(slToIsom g) = (g • ·) :=
  funext (slToIsom_apply g)

/-- The inverse Riemannian isometry of `slToIsom g` is `slToIsom g⁻¹`. -/
@[simp]
theorem slToIsom_symm (g : SL(2, ℝ)) : (slToIsom g).symm = slToIsom g⁻¹ := by
  ext z
  simp [RiemannianIsometry.coe_symm]

/-- `slToIsom` factors through `pslToIsom` along the central quotient `SL(2, ℝ) →* PSL(2, ℝ)`. -/
@[simp]
theorem pslToIsom_coe (g : SL(2, ℝ)) : pslToIsom (g : PSL(2, ℝ)) = slToIsom g := by
  ext z
  simp

/-- `slToIsom` agrees with `glToIsom` along the inclusion `SL(2, ℝ) →* GL(2, ℝ)`. -/
@[simp]
theorem glToIsom_toGL (g : SL(2, ℝ)) : glToIsom g.toGL = slToIsom g := by
  ext z
  simp

/-- The Riemannian isometry group of the Poincaré metric acts transitively on `ℍ`. -/
instance isPretransitive_isom : MulAction.IsPretransitive (Isom 𝓘(ℝ, ℂ) ℍ) ℍ where
  exists_smul_eq x y := by
    obtain ⟨q, rfl⟩ := MulAction.exists_smul_eq PSL(2, ℝ) x y
    exact ⟨pslToIsom q, by simp [RiemannianIsometry.smul_def]⟩

end TauCeti.UpperHalfPlane

end

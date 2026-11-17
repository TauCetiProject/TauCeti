/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
public import TauCeti.Analysis.Complex.UpperHalfPlane.HalfSpace
public import TauCeti.Analysis.Complex.UpperHalfPlane.PSL.Action
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Action
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Congr
-- supplies `FaithfulSMul PGL(2, ℝ) ℍ`
import Mathlib.Analysis.Complex.UpperHalfPlane.FixedPoints
-- supplies `MulAction.IsPretransitive PSL(2, ℝ) ℍ`
import TauCeti.Analysis.Complex.UpperHalfPlane.ProperAction
import TauCeti.Geometry.Manifold.ContMDiff.RestrictScalars
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic

/-!
# Riemannian isometries of the upper half-plane

Every element of `GL(2, ℝ)` acts on the upper half-plane `ℍ` by a smooth Riemannian isometry of the
Poincaré metric `TauCeti.UpperHalfPlane.poincareRiemannianMetric` (including orientation-reversing
elements of negative determinant, which act antiholomorphically through complex conjugation).

In coordinates, Mathlib's `UpperHalfPlane.hasStrictFDerivAt_smul` identifies the real Fréchet
derivative of `g • ·` at `z` with `UpperHalfPlane.smulFDeriv g z`, the map
`v ↦ σ g ((det g / denom g z ^ 2) * v)` where `σ g` is the identity if `det g > 0` and complex
conjugation if `det g < 0`. Both cases preserve the Euclidean real inner product on `ℂ` up to the
factor `‖det g / denom g z ^ 2‖ ^ 2 = (|det g| / normSq (denom g z)) ^ 2 = ((g • z).im / z.im) ^ 2`
(`UpperHalfPlane.im_smul_eq_div_normSq`), so dividing by `(g • z).im ^ 2` recovers the Poincaré
inner product at `z` in a single unified calculation for all `g : GL (Fin 2) ℝ`.

Using `TauCeti.RiemannianIsometry.constSMulHom`, these actions package into group homomorphisms into
`TauCeti.Isom 𝓘(ℝ, ℂ) ℍ` for `GL(2, ℝ)`, `PGL(2, ℝ)`, and for `SL(2, R)` and `PSL(2, R)` over any
commutative ring `R` with `Algebra R ℝ`. The homomorphisms for `PGL(2, ℝ)` and any faithful
`PSL(2, R)` (in particular `PSL(2, ℝ)` and `PSL(2, ℤ)`) are injective, and `Isom 𝓘(ℝ, ℂ) ℍ` acts
transitively on `ℍ`. Conjugation along `TauCeti.UpperHalfPlane.upperHalfSpaceIsometry` via
`TauCeti.RiemannianIsometry.isomCongr` carries these actions to Riemannian isometries of the
two-dimensional upper half-space model `TauCeti.UpperHalfSpace ℝ`.

## Main definitions

* `TauCeti.UpperHalfPlane.glToIsom`, `pglToIsom`, `slToIsom`, `pslToIsom`: group homomorphisms
  into `TauCeti.Isom 𝓘(ℝ, ℂ) ℍ` realising the Möbius actions as smooth Riemannian isometries.
* `TauCeti.UpperHalfPlane.glToUpperHalfSpaceIsom`, `pglToUpperHalfSpaceIsom`,
  `slToUpperHalfSpaceIsom`, `pslToUpperHalfSpaceIsom`: the same actions conjugated to
  `TauCeti.Isom 𝓘(ℝ, WithLp 2 (ℝ × ℝ)) (UpperHalfSpace ℝ)` along `upperHalfSpaceIsometry`.

## Main results

* `UpperHalfPlane.inner_tangentSpace_eq`, `norm_tangentSpace_eq`, `enorm_tangentSpace_eq`:
  coordinate formulas for the Poincaré inner product, norm, and extended norm on `TangentSpace`.
* `UpperHalfPlane.inner_smulFDeriv`: `smulFDeriv g z` scales the Euclidean real inner product on
  `ℂ` by `((g • z).im / z.im) ^ 2`.
* `UpperHalfPlane.tangentSpaceCastModel_mfderiv_smul`: the manifold differential of `g • ·` in
  model coordinates is `UpperHalfPlane.smulFDeriv g z`.
* `TauCeti.UpperHalfPlane.glToIsom_J_notMem_range_pslToIsom`: the orientation-reversing
  reflection `z ↦ -conj z` is not induced by any element of `PSL(2, ℝ)`.
* `TauCeti.UpperHalfPlane.instIsPretransitiveIsom`: `Isom 𝓘(ℝ, ℂ) ℍ` acts transitively on `ℍ`.

## References

* S. Katok, *Fuchsian Groups*, University of Chicago Press, 1992, §1.1–§1.2.
* A. F. Beardon, *The Geometry of Discrete Groups*, Springer GTM 91, 1983, §7.2.
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176, 2018, Chapter 3.
-/

public section

open Bundle Manifold Set Topology
open scoped ComplexConjugate ContDiff ENNReal Manifold MatrixGroups UpperHalfPlane

noncomputable section

/-! ### Poincaré tangent norms and `smulFDeriv` inner products -/

namespace UpperHalfPlane

/-- The Poincaré inner product on `TangentSpace 𝓘(ℝ, ℂ) z` is the Euclidean real inner product
divided by `z.im ^ 2`. -/
theorem inner_tangentSpace_eq (z : ℍ) (v w : TangentSpace 𝓘(ℝ, ℂ) z) :
    inner ℝ v w =
      inner ℝ (tangentSpaceCastModel 𝓘(ℝ, ℂ) z v)
        (tangentSpaceCastModel 𝓘(ℝ, ℂ) z w) / z.im ^ 2 :=
  -- `TauCeti.UpperHalfPlane.instRiemannianBundle` installs `poincareRiemannianMetric`, so
  -- `inner ℝ v w` is `poincareRiemannianMetric.inner z v w` definitionally.
  UpperHalfPlane.poincareRiemannianMetric_inner z v w

/-- The Poincaré norm of a tangent vector at `z` is its Euclidean norm divided by `z.im`. -/
theorem norm_tangentSpace_eq (z : ℍ) (v : TangentSpace 𝓘(ℝ, ℂ) z) :
    ‖v‖ = ‖tangentSpaceCastModel 𝓘(ℝ, ℂ) z v‖ / z.im := by
  rw [norm_eq_sqrt_real_inner, inner_tangentSpace_eq, real_inner_self_eq_norm_sq, ← div_pow,
    Real.sqrt_sq (div_nonneg (norm_nonneg _) z.im_pos.le)]

/-- The Poincaré extended norm of a tangent vector at `z` is its Euclidean extended norm divided by
`ENNReal.ofReal z.im`. -/
theorem enorm_tangentSpace_eq (z : ℍ) (v : TangentSpace 𝓘(ℝ, ℂ) z) :
    ‖v‖ₑ = ‖tangentSpaceCastModel 𝓘(ℝ, ℂ) z v‖ₑ / ENNReal.ofReal z.im := by
  rw [← ofReal_norm, ← ofReal_norm, norm_tangentSpace_eq, ENNReal.ofReal_div_of_pos z.im_pos]

/-- The real algebra automorphism `UpperHalfPlane.σ g` (identity or complex conjugation) preserves
the real inner product on `ℂ`. -/
theorem inner_σ (g : GL (Fin 2) ℝ) (u w : ℂ) :
    inner ℝ (σ g u) (σ g w) = inner ℝ u w := by
  simp only [σ]
  split_ifs
  · rfl
  · simp [Complex.inner]

/-- The real derivative `smulFDeriv g z` of `g • ·` scales the Euclidean real inner product on `ℂ`
by `((g • z).im / z.im) ^ 2`, uniformly for both positive and negative determinant. -/
theorem inner_smulFDeriv (g : GL (Fin 2) ℝ) (z : ℍ) (u w : ℂ) :
    inner ℝ (smulFDeriv g z u) (smulFDeriv g z w) =
      ((g • z).im / z.im) ^ 2 * inner ℝ u w := by
  set c : ℂ := (g.det.val : ℂ) / denom g z ^ 2
  have hsmul : ∀ x : ℂ, smulFDeriv g z x = σ g (c * x) := fun x ↦ by
    simp only [smulFDeriv, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.toSpanSingleton_apply,
      smul_eq_mul, c, mul_comm]
    rfl
  have hmul : inner ℝ (c * u) (c * w) = Complex.normSq c * inner ℝ u w := by
    rw [Complex.inner, Complex.inner, map_mul]
    have heq : (c * w) * (conj c * conj u) = (c * conj c) * (w * conj u) := by ring
    rw [heq, Complex.mul_conj, Complex.re_ofReal_mul]
  have hnormSq : Complex.normSq c = ((g • z).im / z.im) ^ 2 := by
    have hz : z.im ≠ 0 := z.im_pos.ne'
    have hd : Complex.normSq (denom g z) ≠ 0 := (Complex.normSq_pos.mpr (denom_ne_zero g z)).ne'
    rw [im_smul_eq_div_normSq]
    simp only [c, map_div₀, map_pow, Complex.normSq_ofReal]
    field_simp
    simp [sq_abs]
  rw [hsmul u, hsmul w, inner_σ, hmul, hnormSq]

/-- Every element of `GL(2, ℝ)` acts smoothly on `ℍ` as a real manifold, including elements of
negative determinant, which act antiholomorphically. -/
theorem contMDiff_smul_real (g : GL (Fin 2) ℝ) :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (g • · : ℍ → ℍ) := by
  have hpos : ∀ h : GL (Fin 2) ℝ, 0 < h.det.val →
      ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (h • · : ℍ → ℍ) := fun h hh ↦ by
    have hC : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ∞ (h • · : ℍ → ℍ) := UpperHalfPlane.contMDiff_smul hh
    simpa only [modelWithCornersSelf_restrictScalars] using hC.restrictScalars ℝ
  have hJ : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (J • · : ℍ → ℍ) := by
    apply ContMDiff.of_comp_isOpenEmbedding UpperHalfPlane.isOpenEmbedding_coe
    have hcoe : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (UpperHalfPlane.coe : ℍ → ℂ) :=
      fun _ ↦ contMDiffAt_extChartAt
    have heq : UpperHalfPlane.coe ∘ (J • · : ℍ → ℍ) =
        (fun w : ℂ ↦ -(Complex.conjCLE w)) ∘ UpperHalfPlane.coe := by
      funext z
      exact UpperHalfPlane.coe_J_smul z
    rw [heq]
    exact Complex.conjCLE.contDiff.neg.contMDiff.comp hcoe
  rcases g.det.ne_zero.lt_or_gt with hg | hg
  · have hJg : 0 < (J * g).det.val := by simpa using hg
    have hcomp : (g • · : ℍ → ℍ) = (J • ·) ∘ ((J * g) • ·) := by
      funext z
      rw [Function.comp_apply, smul_smul, ← mul_assoc, ← sq, J_sq, one_mul]
    rw [hcomp]
    exact hJ.comp (hpos (J * g) hJg)
  · exact hpos g hg

/-- The differential of `g • · : ℍ → ℍ` in model coordinates is Mathlib's `smulFDeriv g z`. -/
theorem tangentSpaceCastModel_mfderiv_smul (g : GL (Fin 2) ℝ) (z : ℍ)
    (v : TangentSpace 𝓘(ℝ, ℂ) z) :
    tangentSpaceCastModel 𝓘(ℝ, ℂ) (g • z) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (g • ·) z v) =
      smulFDeriv g z (tangentSpaceCastModel 𝓘(ℝ, ℂ) z v) := by
  rw [((contMDiff_smul_real g).mdifferentiableAt (by simp)).tangentSpaceCastModel_mfderiv_apply]
  have hlocal :
      writtenInExtChartAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) z (g • · : ℍ → ℍ) =ᶠ[𝓝 (z : ℂ)]
        fun w : ℂ ↦ (↑(g • ofComplex w) : ℂ) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds z.im_pos]
      with w hw
    have hchart : ∀ τ : ℍ, extChartAt 𝓘(ℝ, ℂ) (g • z) τ = (τ : ℂ) := fun _ ↦ by simp
    have hinv : (extChartAt 𝓘(ℝ, ℂ) z).symm w = ofComplex w := by
      rw [ofComplex_apply_of_im_pos hw]
      apply UpperHalfPlane.ext
      simpa using (extChartAt 𝓘(ℝ, ℂ) z).right_inv (by simpa using hw)
    simp only [writtenInExtChartAt, Function.comp_apply, hchart, hinv]
  have hz : extChartAt 𝓘(ℝ, ℂ) z z = (z : ℂ) := by simp
  rw [hz, hlocal.fderiv_eq, (hasStrictFDerivAt_smul g z).hasFDerivAt.fderiv]

end UpperHalfPlane

/-! ### Smooth real actions and isometry group homomorphisms -/

namespace TauCeti.UpperHalfPlane

/-- Every element of `GL(2, ℝ)` acts smoothly on `ℍ` as a real manifold. -/
instance instContMDiffConstSMulGLReal : ContMDiffConstSMul 𝓘(ℝ, ℂ) ∞ (GL (Fin 2) ℝ) ℍ where
  contMDiff_const_smul := _root_.UpperHalfPlane.contMDiff_smul_real

/-- Every element of `PGL(2, ℝ)` acts smoothly on `ℍ` as a real manifold. -/
instance instContMDiffConstSMulPGLReal : ContMDiffConstSMul 𝓘(ℝ, ℂ) ∞ PGL(2, ℝ) ℍ where
  contMDiff_const_smul q := by
    induction q using Matrix.ProjGenLinGroup.induction_on with | mk g =>
    simpa only [_root_.UpperHalfPlane.pglMk_smul] using
      _root_.UpperHalfPlane.contMDiff_smul_real g

section GeneralRing

variable {R : Type*} [CommRing R] [Algebra R ℝ]

/-- Every element of `SL(2, R)` acts smoothly on `ℍ` as a real manifold, for any commutative ring
`R` mapping to `ℝ`. -/
instance instContMDiffConstSMulSLReal : ContMDiffConstSMul 𝓘(ℝ, ℂ) ∞ SL(2, R) ℍ where
  contMDiff_const_smul g := by
    have hfun : (g • · : ℍ → ℍ) = (Matrix.SpecialLinearGroup.mapGL ℝ g • ·) := by
      funext z
      rfl
    rw [hfun]
    exact _root_.UpperHalfPlane.contMDiff_smul_real (Matrix.SpecialLinearGroup.mapGL ℝ g)

/-- Every element of `PSL(2, R)` acts smoothly on `ℍ` as a real manifold, for any commutative ring
`R` mapping to `ℝ`. -/
instance instContMDiffConstSMulPSLReal : ContMDiffConstSMul 𝓘(ℝ, ℂ) ∞ PSL(2, R) ℍ where
  contMDiff_const_smul q := by
    refine QuotientGroup.induction_on q fun g ↦ ?_
    simpa only [_root_.UpperHalfPlane.pslMk_smul] using contMDiff_const_smul (I := 𝓘(ℝ, ℂ)) g

end GeneralRing

/-- Every element of `GL(2, ℝ)` preserves the Poincaré inner product on tangent spaces of `ℍ`. -/
theorem inner_mfderiv_smul_gl (g : GL (Fin 2) ℝ) (z : ℍ) (v w : TangentSpace 𝓘(ℝ, ℂ) z) :
    inner ℝ (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (g • ·) z v) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (g • ·) z w) =
      inner ℝ v w := by
  rw [_root_.UpperHalfPlane.inner_tangentSpace_eq, _root_.UpperHalfPlane.inner_tangentSpace_eq,
    _root_.UpperHalfPlane.tangentSpaceCastModel_mfderiv_smul,
    _root_.UpperHalfPlane.tangentSpaceCastModel_mfderiv_smul,
    _root_.UpperHalfPlane.inner_smulFDeriv]
  have hz : z.im ≠ 0 := z.im_pos.ne'
  have hgz : (g • z).im ≠ 0 := (g • z).im_pos.ne'
  field_simp

/-- The Möbius action of `GL(2, ℝ)` on `ℍ` as a group homomorphism into the smooth Riemannian
isometry group `TauCeti.Isom 𝓘(ℝ, ℂ) ℍ`. -/
def glToIsom : GL (Fin 2) ℝ →* Isom 𝓘(ℝ, ℂ) ℍ :=
  RiemannianIsometry.constSMulHom inner_mfderiv_smul_gl

/-- `glToIsom g` acts on `ℍ` by the Möbius transformation `g • ·`. -/
@[simp]
theorem glToIsom_apply_apply (g : GL (Fin 2) ℝ) (z : ℍ) : glToIsom g z = g • z := by
  rw [glToIsom, RiemannianIsometry.constSMulHom_apply, RiemannianIsometry.constSMul_apply]

/-- The effective `PGL(2, ℝ)` action on `ℍ` preserves the Poincaré inner product. -/
theorem inner_mfderiv_smul_pgl (q : PGL(2, ℝ)) (z : ℍ) (v w : TangentSpace 𝓘(ℝ, ℂ) z) :
    inner ℝ (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (q • ·) z v) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (q • ·) z w) =
      inner ℝ v w := by
  induction q using Matrix.ProjGenLinGroup.induction_on with | mk g =>
  have hfun : (Matrix.ProjGenLinGroup.mk g • · : ℍ → ℍ) = (g • ·) :=
    funext (_root_.UpperHalfPlane.pglMk_smul g)
  rw [hfun]
  exact inner_mfderiv_smul_gl g z v w

/-- The Möbius action of `PGL(2, ℝ)` on `ℍ` as a group homomorphism into the smooth Riemannian
isometry group `TauCeti.Isom 𝓘(ℝ, ℂ) ℍ`. -/
def pglToIsom : PGL(2, ℝ) →* Isom 𝓘(ℝ, ℂ) ℍ :=
  RiemannianIsometry.constSMulHom inner_mfderiv_smul_pgl

/-- `pglToIsom q` acts on `ℍ` by `q • ·`. -/
@[simp]
theorem pglToIsom_apply_apply (q : PGL(2, ℝ)) (z : ℍ) : pglToIsom q z = q • z := by
  rw [pglToIsom, RiemannianIsometry.constSMulHom_apply, RiemannianIsometry.constSMul_apply]

/-- `pglToIsom` descends `glToIsom` along the projective quotient `GL(2, ℝ) → PGL(2, ℝ)`. -/
@[simp]
theorem pglToIsom_mk (g : GL (Fin 2) ℝ) :
    pglToIsom (Matrix.ProjGenLinGroup.mk g) = glToIsom g := by
  ext z
  simp [_root_.UpperHalfPlane.pglMk_smul]

/-- The homomorphism `PGL(2, ℝ) →* Isom 𝓘(ℝ, ℂ) ℍ` is injective because `PGL(2, ℝ)` acts faithfully
on `ℍ`. -/
theorem pglToIsom_injective : Function.Injective pglToIsom :=
  RiemannianIsometry.constSMulHom_injective inner_mfderiv_smul_pgl

section GeneralRing

variable {R : Type*} [CommRing R] [Algebra R ℝ]

/-- Every element of `SL(2, R)` preserves the Poincaré inner product on tangent spaces of `ℍ`. -/
theorem inner_mfderiv_smul_sl (g : SL(2, R)) (z : ℍ) (v w : TangentSpace 𝓘(ℝ, ℂ) z) :
    inner ℝ (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (g • ·) z v) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (g • ·) z w) =
      inner ℝ v w := by
  have hfun : (g • · : ℍ → ℍ) = (Matrix.SpecialLinearGroup.mapGL ℝ g • ·) := funext fun _ ↦ rfl
  rw [hfun]
  exact inner_mfderiv_smul_gl (Matrix.SpecialLinearGroup.mapGL ℝ g) z v w

/-- The Möbius action of `SL(2, R)` on `ℍ` as a group homomorphism into `Isom 𝓘(ℝ, ℂ) ℍ`. -/
def slToIsom : SL(2, R) →* Isom 𝓘(ℝ, ℂ) ℍ :=
  RiemannianIsometry.constSMulHom inner_mfderiv_smul_sl

/-- `slToIsom g` acts on `ℍ` by `g • ·`. -/
@[simp]
theorem slToIsom_apply_apply (g : SL(2, R)) (z : ℍ) : slToIsom g z = g • z := by
  rw [slToIsom, RiemannianIsometry.constSMulHom_apply, RiemannianIsometry.constSMul_apply]

/-- `slToIsom` factors through `glToIsom` along `Matrix.SpecialLinearGroup.mapGL ℝ`. -/
theorem slToIsom_eq_glToIsom (g : SL(2, R)) :
    slToIsom g = glToIsom (Matrix.SpecialLinearGroup.mapGL ℝ g) := by
  ext z
  simp [MulAction.compHom_smul_def]

/-- Every element of `PSL(2, R)` preserves the Poincaré inner product on tangent spaces of `ℍ`. -/
theorem inner_mfderiv_smul_psl (q : PSL(2, R)) (z : ℍ) (v w : TangentSpace 𝓘(ℝ, ℂ) z) :
    inner ℝ (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (q • ·) z v) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (q • ·) z w) =
      inner ℝ v w := by
  refine QuotientGroup.induction_on q fun g ↦ ?_
  have hfun : ((g : PSL(2, R)) • · : ℍ → ℍ) = (g • ·) :=
    funext (_root_.UpperHalfPlane.pslMk_smul g)
  rw [hfun]
  exact inner_mfderiv_smul_sl g z v w

/-- The Möbius action of `PSL(2, R)` on `ℍ` as a group homomorphism into `Isom 𝓘(ℝ, ℂ) ℍ`. -/
def pslToIsom : PSL(2, R) →* Isom 𝓘(ℝ, ℂ) ℍ :=
  RiemannianIsometry.constSMulHom inner_mfderiv_smul_psl

/-- `pslToIsom q` acts on `ℍ` by `q • ·`. -/
@[simp]
theorem pslToIsom_apply_apply (q : PSL(2, R)) (z : ℍ) : pslToIsom q z = q • z := by
  rw [pslToIsom, RiemannianIsometry.constSMulHom_apply, RiemannianIsometry.constSMul_apply]

/-- `pslToIsom` descends `slToIsom` along the central quotient `SL(2, R) → PSL(2, R)`. -/
@[simp]
theorem pslToIsom_mk (g : SL(2, R)) :
    pslToIsom (g : PSL(2, R)) = slToIsom g := by
  ext z
  simp [_root_.UpperHalfPlane.pslMk_smul]

/-- For any ring `R` whose `PSL(2, R)`-action on `ℍ` is faithful (such as `ℝ` or `ℤ`),
`pslToIsom` is injective. -/
theorem pslToIsom_injective [FaithfulSMul PSL(2, R) ℍ] :
    Function.Injective (pslToIsom (R := R)) :=
  RiemannianIsometry.constSMulHom_injective inner_mfderiv_smul_psl

end GeneralRing

/-- `pslToIsom` for `R = ℝ` factors through `pglToIsom` along `toPGL`. -/
@[simp]
theorem pglToIsom_toPGL (q : PSL(2, ℝ)) :
    pglToIsom (Matrix.ProjectiveSpecialLinearGroup.toPGL q) = pslToIsom q := by
  ext z
  simp [_root_.UpperHalfPlane.toPGL_smul]

/-- The smooth Riemannian isometry group of `ℍ` acts transitively on `ℍ`, so `ℍ` with the
Poincaré metric is a homogeneous Riemannian manifold. -/
instance instIsPretransitiveIsom : MulAction.IsPretransitive (Isom 𝓘(ℝ, ℂ) ℍ) ℍ where
  exists_smul_eq x y := by
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq PSL(2, ℝ) x y
    exact ⟨pslToIsom g, by simpa using hg⟩

/-- The reflection `z ↦ -conj z` (the action of `UpperHalfPlane.J`) is orientation-reversing and
therefore does not lie in the image of `PSL(2, ℝ)` in `Isom 𝓘(ℝ, ℂ) ℍ`. -/
theorem glToIsom_J_notMem_range_pslToIsom :
    glToIsom _root_.UpperHalfPlane.J ∉ Set.range (pslToIsom (R := ℝ)) := by
  rintro ⟨q, hq⟩
  refine QuotientGroup.induction_on q (fun g hg ↦ ?_) hq
  -- Equate the real maps induced via `ofComplex` and compare Jacobian determinants at `I`.
  have hfun : (fun w : ℂ ↦ (↑(Matrix.SpecialLinearGroup.mapGL ℝ g •
      _root_.UpperHalfPlane.ofComplex w) : ℂ)) =
      fun w : ℂ ↦ (↑(_root_.UpperHalfPlane.J • _root_.UpperHalfPlane.ofComplex w) : ℂ) := by
    funext w
    have hw := DFunLike.congr_fun hg (_root_.UpperHalfPlane.ofComplex w)
    exact congrArg _root_.UpperHalfPlane.coe (by
      simpa [_root_.UpperHalfPlane.pslMk_smul, MulAction.compHom_smul_def] using hw)
  have h1 := (_root_.UpperHalfPlane.hasStrictFDerivAt_smul
    (Matrix.SpecialLinearGroup.mapGL ℝ g) _root_.UpperHalfPlane.I).hasFDerivAt
  have h2 := (_root_.UpperHalfPlane.hasStrictFDerivAt_smul
    _root_.UpperHalfPlane.J _root_.UpperHalfPlane.I).hasFDerivAt
  rw [hfun] at h1
  have hdet := congrArg ContinuousLinearMap.det (h1.unique h2)
  rw [_root_.UpperHalfPlane.det_smulFDeriv, _root_.UpperHalfPlane.det_smulFDeriv] at hdet
  have hdenom_g : 0 < ‖_root_.UpperHalfPlane.denom (Matrix.SpecialLinearGroup.mapGL ℝ g)
      (_root_.UpperHalfPlane.I : ℂ)‖ ^ 4 :=
    pow_pos (norm_pos_iff.mpr (_root_.UpperHalfPlane.denom_ne_zero _ _)) 4
  have hdenom_J : 0 < ‖_root_.UpperHalfPlane.denom _root_.UpperHalfPlane.J
      (_root_.UpperHalfPlane.I : ℂ)‖ ^ 4 :=
    pow_pos (norm_pos_iff.mpr (_root_.UpperHalfPlane.denom_ne_zero _ _)) 4
  have hdet_g : (Matrix.SpecialLinearGroup.mapGL ℝ g).det.val = 1 := by simp
  have hdet_J : _root_.UpperHalfPlane.J.det.val = -1 := by simp
  rw [hdet_g, hdet_J, sign_one, sign_neg (by norm_num : (-1 : ℝ) < 0)] at hdet
  simp only [SignType.coe_one, SignType.coe_neg, one_mul, one_pow, neg_mul, neg_one_sq,
    one_div] at hdet
  have hpos : (0 : ℝ) < (‖_root_.UpperHalfPlane.denom (Matrix.SpecialLinearGroup.mapGL ℝ g)
      (_root_.UpperHalfPlane.I : ℂ)‖ ^ 4)⁻¹ := inv_pos.mpr hdenom_g
  have hneg : -1 / ‖_root_.UpperHalfPlane.denom _root_.UpperHalfPlane.J
      (_root_.UpperHalfPlane.I : ℂ)‖ ^ 4 < 0 := div_neg_of_neg_of_pos (by norm_num) hdenom_J
  linarith

/-! ### Conjugating the actions to the two-dimensional upper half-space model -/

/-- The `GL(2, ℝ)` action transported to the two-dimensional upper half-space model by conjugation
along `upperHalfSpaceIsometry`. -/
def glToUpperHalfSpaceIsom :
    GL (Fin 2) ℝ →* Isom 𝓘(ℝ, WithLp 2 (ℝ × ℝ)) (UpperHalfSpace ℝ) :=
  (RiemannianIsometry.isomCongr upperHalfSpaceIsometry).toMonoidHom.comp glToIsom

/-- Pointwise evaluation of the conjugated `GL(2, ℝ)` action on `UpperHalfSpace ℝ`. -/
@[simp]
theorem glToUpperHalfSpaceIsom_apply_apply (g : GL (Fin 2) ℝ) (p : UpperHalfSpace ℝ) :
    glToUpperHalfSpaceIsom g p = upperHalfSpaceIsometry (g • upperHalfSpaceIsometry.symm p) := by
  simp [glToUpperHalfSpaceIsom]

/-- `upperHalfSpaceIsometry` intertwines the `GL(2, ℝ)` action on `ℍ` with
`glToUpperHalfSpaceIsom` on `UpperHalfSpace ℝ`. -/
theorem upperHalfSpaceIsometry_smul_eq (g : GL (Fin 2) ℝ) (z : ℍ) :
    upperHalfSpaceIsometry (g • z) = glToUpperHalfSpaceIsom g (upperHalfSpaceIsometry z) := by
  simp

/-- The `PGL(2, ℝ)` action transported to `UpperHalfSpace ℝ` by conjugation along
`upperHalfSpaceIsometry`. -/
def pglToUpperHalfSpaceIsom :
    PGL(2, ℝ) →* Isom 𝓘(ℝ, WithLp 2 (ℝ × ℝ)) (UpperHalfSpace ℝ) :=
  (RiemannianIsometry.isomCongr upperHalfSpaceIsometry).toMonoidHom.comp pglToIsom

/-- Pointwise evaluation of the conjugated `PGL(2, ℝ)` action on `UpperHalfSpace ℝ`. -/
@[simp]
theorem pglToUpperHalfSpaceIsom_apply_apply (q : PGL(2, ℝ)) (p : UpperHalfSpace ℝ) :
    pglToUpperHalfSpaceIsom q p = upperHalfSpaceIsometry (q • upperHalfSpaceIsometry.symm p) := by
  simp [pglToUpperHalfSpaceIsom]

/-- `pglToUpperHalfSpaceIsom` descends `glToUpperHalfSpaceIsom` along the projective quotient. -/
@[simp]
theorem pglToUpperHalfSpaceIsom_mk (g : GL (Fin 2) ℝ) :
    pglToUpperHalfSpaceIsom (Matrix.ProjGenLinGroup.mk g) = glToUpperHalfSpaceIsom g := by
  ext p
  simp [_root_.UpperHalfPlane.pglMk_smul]

/-- The conjugated homomorphism `PGL(2, ℝ) →* Isom (UpperHalfSpace ℝ)` is injective. -/
theorem pglToUpperHalfSpaceIsom_injective : Function.Injective pglToUpperHalfSpaceIsom :=
  (RiemannianIsometry.isomCongr upperHalfSpaceIsometry).injective.comp pglToIsom_injective

section GeneralRingHalfSpace

variable {R : Type*} [CommRing R] [Algebra R ℝ]

/-- The `SL(2, R)` action transported to `UpperHalfSpace ℝ` by conjugation along
`upperHalfSpaceIsometry`. -/
def slToUpperHalfSpaceIsom :
    SL(2, R) →* Isom 𝓘(ℝ, WithLp 2 (ℝ × ℝ)) (UpperHalfSpace ℝ) :=
  (RiemannianIsometry.isomCongr upperHalfSpaceIsometry).toMonoidHom.comp slToIsom

/-- Pointwise evaluation of the conjugated `SL(2, R)` action on `UpperHalfSpace ℝ`. -/
@[simp]
theorem slToUpperHalfSpaceIsom_apply_apply (g : SL(2, R)) (p : UpperHalfSpace ℝ) :
    slToUpperHalfSpaceIsom g p = upperHalfSpaceIsometry (g • upperHalfSpaceIsometry.symm p) := by
  simp [slToUpperHalfSpaceIsom]

/-- `slToUpperHalfSpaceIsom` factors through `glToUpperHalfSpaceIsom` along
`Matrix.SpecialLinearGroup.mapGL ℝ`. -/
theorem slToUpperHalfSpaceIsom_eq_glToUpperHalfSpaceIsom (g : SL(2, R)) :
    slToUpperHalfSpaceIsom g = glToUpperHalfSpaceIsom (Matrix.SpecialLinearGroup.mapGL ℝ g) := by
  ext p
  simp [MulAction.compHom_smul_def]

/-- The `PSL(2, R)` action transported to `UpperHalfSpace ℝ` by conjugation along
`upperHalfSpaceIsometry`. -/
def pslToUpperHalfSpaceIsom :
    PSL(2, R) →* Isom 𝓘(ℝ, WithLp 2 (ℝ × ℝ)) (UpperHalfSpace ℝ) :=
  (RiemannianIsometry.isomCongr upperHalfSpaceIsometry).toMonoidHom.comp pslToIsom

/-- Pointwise evaluation of the conjugated `PSL(2, R)` action on `UpperHalfSpace ℝ`. -/
@[simp]
theorem pslToUpperHalfSpaceIsom_apply_apply (q : PSL(2, R)) (p : UpperHalfSpace ℝ) :
    pslToUpperHalfSpaceIsom q p = upperHalfSpaceIsometry (q • upperHalfSpaceIsometry.symm p) := by
  simp [pslToUpperHalfSpaceIsom]

/-- `pslToUpperHalfSpaceIsom` descends `slToUpperHalfSpaceIsom` along the central quotient
`SL(2, R) → PSL(2, R)`. -/
@[simp]
theorem pslToUpperHalfSpaceIsom_mk (g : SL(2, R)) :
    pslToUpperHalfSpaceIsom (g : PSL(2, R)) = slToUpperHalfSpaceIsom g := by
  ext p
  simp [_root_.UpperHalfPlane.pslMk_smul]

/-- The conjugated homomorphism `PSL(2, R) →* Isom (UpperHalfSpace ℝ)` is injective whenever
`PSL(2, R)` acts faithfully on `ℍ`. -/
theorem pslToUpperHalfSpaceIsom_injective [FaithfulSMul PSL(2, R) ℍ] :
    Function.Injective (pslToUpperHalfSpaceIsom (R := R)) :=
  (RiemannianIsometry.isomCongr upperHalfSpaceIsometry).injective.comp pslToIsom_injective

end GeneralRingHalfSpace

/-- `pslToUpperHalfSpaceIsom` for `R = ℝ` factors through `pglToUpperHalfSpaceIsom` along
`toPGL`. -/
@[simp]
theorem pglToUpperHalfSpaceIsom_toPGL (q : PSL(2, ℝ)) :
    pglToUpperHalfSpaceIsom (Matrix.ProjectiveSpecialLinearGroup.toPGL q) =
      pslToUpperHalfSpaceIsom q := by
  ext p
  simp [_root_.UpperHalfPlane.toPGL_smul]

end TauCeti.UpperHalfPlane

end

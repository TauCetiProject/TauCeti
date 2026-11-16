/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
public import TauCeti.Analysis.Complex.UpperHalfPlane.PoincareMetric
public import TauCeti.Analysis.Complex.UpperHalfPlane.PSL.Action
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Action
import Mathlib.Analysis.Complex.UpperHalfPlane.FixedPoints
import TauCeti.Analysis.Complex.UpperHalfPlane.Manifold
import TauCeti.Geometry.Manifold.ContMDiff.RestrictScalars
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic

/-!
# Möbius transformations as Riemannian isometries of the Poincaré metric

Every element of `GL(2, ℝ)` acts on the upper half-plane `ℍ` by a smooth real diffeomorphism:
elements of positive determinant act holomorphically by `z ↦ (az + b) / (cz + d)`, while elements
of negative determinant act antiholomorphically by `z ↦ (a conj z + b) / (c conj z + d)` (the
composition of the reflection `J : z ↦ -conj z` with a positive-determinant element).

In the inclusion chart `ℍ ↪ ℂ`, the real differential of `g • ·` at `z` is Mathlib's
`UpperHalfPlane.smulFDeriv g z`, which composes multiplication by `det g / (cz + d)²` with either
the identity (when `det g > 0`) or complex conjugation (when `det g < 0`). Both maps scale
Euclidean inner products by `(|det g| / |cz + d|²)²`, which matches the ratio `(Im (g • z) / Im z)²`
from `UpperHalfPlane.im_smul_eq_div_normSq`. Thus the Poincaré inner product
`⟪v, w⟫_ℝ / (Im z)²` is preserved, yielding group homomorphisms from `GL(2, ℝ)`, `PGL(2, ℝ)`,
`SL(2, R)`, and `PSL(2, R)` into the Riemannian isometry group `TauCeti.Isom 𝓘(ℝ, ℂ) ℍ`.

## Main definitions

* `TauCeti.UpperHalfPlane.instContMDiffConstSMulGL`, `instContMDiffConstSMulPGL`,
  `instContMDiffConstSMulSL`, `instContMDiffConstSMulPSL`: smooth real actions on `ℍ`.
* `TauCeti.UpperHalfPlane.glToIsom`: the group homomorphism `GL (Fin 2) ℝ →* Isom 𝓘(ℝ, ℂ) ℍ`.
* `TauCeti.UpperHalfPlane.pglToIsom`: the injective group homomorphism
  `PGL(2, ℝ) →* Isom 𝓘(ℝ, ℂ) ℍ`.
* `TauCeti.UpperHalfPlane.slToIsom` and `TauCeti.UpperHalfPlane.pslToIsom`: the induced
  homomorphisms from `SL(2, R)` and `PSL(2, R)` into `Isom 𝓘(ℝ, ℂ) ℍ`.

## Main results

* `UpperHalfPlane.tangentSpaceCastModel_mfderiv_smul`: the differential of `g • ·` in model
  coordinates is `UpperHalfPlane.smulFDeriv g z`.
* `UpperHalfPlane.inner_mfderiv_smul`: the differential of `g • ·` preserves the Poincaré metric.
* `TauCeti.UpperHalfPlane.pglToIsom_injective` and `TauCeti.UpperHalfPlane.pslToIsom_injective`:
  the projective homomorphisms into `Isom 𝓘(ℝ, ℂ) ℍ` are injective.
* `TauCeti.UpperHalfPlane.instIsPretransitiveIsom`: the Poincaré upper half-plane is homogeneous
  under its Riemannian isometry group.

## References

* Svetlana Katok, *Fuchsian Groups*, Chicago Lectures in Mathematics, 1992, §1.2.
* Alan Beardon, *The Geometry of Discrete Groups*, Springer GTM 91, 1983, §7.2.
-/

public section

open Bundle Manifold
open scoped ContDiff Manifold MatrixGroups UpperHalfPlane

noncomputable section

namespace TauCeti.UpperHalfPlane

/-! ### Smoothness of the real Möbius actions -/

private theorem contMDiff_smul_of_det_pos {g : GL (Fin 2) ℝ} (hg : 0 < g.det.val) :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (g • · : ℍ → ℍ) := by
  simpa only [modelWithCornersSelf_restrictScalars] using
    (_root_.UpperHalfPlane.contMDiff_smul (n := ∞) hg).restrictScalars ℝ

private theorem contMDiff_J_smul :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (_root_.UpperHalfPlane.J • · : ℍ → ℍ) := by
  refine ContMDiff.of_comp_isOpenEmbedding _root_.UpperHalfPlane.isOpenEmbedding_coe ?_
  have hcoe : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ _root_.UpperHalfPlane.coe :=
    fun _ ↦ contMDiffAt_extChartAt
  have heq : (_root_.UpperHalfPlane.coe ∘ (_root_.UpperHalfPlane.J • · : ℍ → ℍ)) =
      (fun w : ℂ ↦ -Complex.conjCLE w) ∘ _root_.UpperHalfPlane.coe :=
    funext fun z ↦ _root_.UpperHalfPlane.coe_J_smul z
  rw [heq]
  exact Complex.conjCLE.contDiff.neg.contMDiff.comp hcoe

/-- Every element of `GL(2, ℝ)` acts smoothly on `ℍ` as a real manifold, including the
orientation-reversing elements of negative determinant. -/
instance instContMDiffConstSMulGL : ContMDiffConstSMul 𝓘(ℝ, ℂ) ∞ (GL (Fin 2) ℝ) ℍ where
  contMDiff_const_smul g := by
    rcases g.det.ne_zero.lt_or_gt with hg | hg
    · have hJg : 0 < (_root_.UpperHalfPlane.J * g).det.val := by simpa using hg
      have hcomp : (g • · : ℍ → ℍ) =
          (_root_.UpperHalfPlane.J • ·) ∘ ((_root_.UpperHalfPlane.J * g) • ·) := by
        funext z
        rw [Function.comp_apply, smul_smul, ← mul_assoc, ← sq, _root_.UpperHalfPlane.J_sq, one_mul]
      rw [hcomp]
      exact contMDiff_J_smul.comp (contMDiff_smul_of_det_pos hJg)
    · exact contMDiff_smul_of_det_pos hg

/-- Every element of `PGL(2, ℝ)` acts smoothly on `ℍ` as a real manifold. -/
instance instContMDiffConstSMulPGL : ContMDiffConstSMul 𝓘(ℝ, ℂ) ∞ PGL(2, ℝ) ℍ where
  contMDiff_const_smul q := by
    induction q using Matrix.ProjGenLinGroup.induction_on with | mk g =>
    simpa only [_root_.UpperHalfPlane.pglMk_smul] using
      contMDiff_const_smul (I := 𝓘(ℝ, ℂ)) (n := ∞) g

/-- Every element of `SL(2, R)` (for any commutative ring `R` mapping to `ℝ`) acts smoothly on `ℍ`
as a real manifold. -/
instance instContMDiffConstSMulSL {R : Type*} [CommRing R] [Algebra R ℝ] :
    ContMDiffConstSMul 𝓘(ℝ, ℂ) ∞ SL(2, R) ℍ where
  contMDiff_const_smul g := by
    simpa only [MulAction.compHom_smul_def] using
      contMDiff_const_smul (I := 𝓘(ℝ, ℂ)) (n := ∞) (Matrix.SpecialLinearGroup.mapGL ℝ g)

/-- Every element of `PSL(2, R)` (for any commutative ring `R` mapping to `ℝ`) acts smoothly on `ℍ`
as a real manifold. -/
instance instContMDiffConstSMulPSL {R : Type*} [CommRing R] [Algebra R ℝ] :
    ContMDiffConstSMul 𝓘(ℝ, ℂ) ∞ PSL(2, R) ℍ where
  contMDiff_const_smul q := by
    refine QuotientGroup.induction_on q fun g ↦ ?_
    simpa only [_root_.UpperHalfPlane.pslMk_smul] using
      contMDiff_const_smul (I := 𝓘(ℝ, ℂ)) (n := ∞) g

/-! ### Differential and metric preservation -/

/-- In the model coordinates of the inclusion chart, the real manifold differential of `g • ·` at
`z` is Mathlib's `UpperHalfPlane.smulFDeriv g z`. -/
theorem _root_.UpperHalfPlane.tangentSpaceCastModel_mfderiv_smul (g : GL (Fin 2) ℝ) (z : ℍ)
    (v : TangentSpace 𝓘(ℝ, ℂ) z) :
    tangentSpaceCastModel 𝓘(ℝ, ℂ) (g • z)
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (g • · : ℍ → ℍ) z v) =
      _root_.UpperHalfPlane.smulFDeriv g z (tangentSpaceCastModel 𝓘(ℝ, ℂ) z v) := by
  have hd : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (g • · : ℍ → ℍ) z :=
    (contMDiff_const_smul (I := 𝓘(ℝ, ℂ)) (n := ∞) g).mdifferentiable (by simp) z
  rw [hd.tangentSpaceCastModel_mfderiv_apply]
  have hlocal : writtenInExtChartAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) z (g • · : ℍ → ℍ)
      =ᶠ[nhds (z : ℂ)] fun w : ℂ ↦ ((g • _root_.UpperHalfPlane.ofComplex w : ℍ) : ℂ) := by
    filter_upwards [comp_chartAt_symm_eventuallyEq (fun w : ℍ ↦ ((g • w : ℍ) : ℂ)) z] with w hw
    simpa only [writtenInExtChartAt, Function.comp_apply, extChartAt_coe,
      modelWithCornersSelf_coe, Function.id_comp, extChartAt_coe_symm,
      modelWithCornersSelf_coe_symm, Function.comp_id,
      _root_.UpperHalfPlane.isOpenEmbedding_coe.singletonChartedSpace_chartAt_eq] using hw
  have hchart : extChartAt 𝓘(ℝ, ℂ) z z = (z : ℂ) := by simp
  rw [hchart, hlocal.fderiv_eq,
    (_root_.UpperHalfPlane.hasStrictFDerivAt_smul g z).hasFDerivAt.fderiv]

private theorem inner_smulFDeriv (g : GL (Fin 2) ℝ) (z : ℍ) (u w : ℂ) :
    inner ℝ (_root_.UpperHalfPlane.smulFDeriv g z u) (_root_.UpperHalfPlane.smulFDeriv g z w) =
      (|g.det.val| / Complex.normSq (_root_.UpperHalfPlane.denom g z)) ^ 2 * inner ℝ u w := by
  have hσ (a b : ℂ) :
      inner ℝ ((_root_.UpperHalfPlane.σ g : ℂ →L[ℝ] ℂ) a)
          ((_root_.UpperHalfPlane.σ g : ℂ →L[ℝ] ℂ) b) =
        inner ℝ a b := by
    unfold _root_.UpperHalfPlane.σ
    split_ifs <;> simp [Complex.inner]
  have hmul (c a b : ℂ) : inner ℝ (a * c) (b * c) = Complex.normSq c * inner ℝ a b := by
    simp only [Complex.inner, map_mul, Complex.mul_re, Complex.mul_im, Complex.conj_re,
      Complex.conj_im, Complex.normSq_apply]
    ring
  rw [_root_.UpperHalfPlane.smulFDeriv, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, hσ]
  simp only [ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.toSpanSingleton_apply,
    smul_eq_mul]
  rw [hmul, map_div₀, map_pow, Complex.normSq_ofReal, ← sq, div_pow, sq_abs]

/-- Every element of `GL(2, ℝ)` preserves the Poincaré inner product on tangent spaces of `ℍ`. -/
theorem _root_.UpperHalfPlane.inner_mfderiv_smul (g : GL (Fin 2) ℝ) (z : ℍ)
    (v w : TangentSpace 𝓘(ℝ, ℂ) z) :
    inner ℝ (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (g • · : ℍ → ℍ) z v)
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (g • · : ℍ → ℍ) z w) =
      inner ℝ v w := by
  rw [_root_.UpperHalfPlane.inner_tangentSpace_eq, _root_.UpperHalfPlane.inner_tangentSpace_eq,
    _root_.UpperHalfPlane.tangentSpaceCastModel_mfderiv_smul,
    _root_.UpperHalfPlane.tangentSpaceCastModel_mfderiv_smul, inner_smulFDeriv,
    _root_.UpperHalfPlane.im_smul_eq_div_normSq]
  have hdet : |g.det.val| ≠ 0 := abs_ne_zero.mpr g.det.ne_zero
  have hden : Complex.normSq (_root_.UpperHalfPlane.denom g z) ≠ 0 :=
    _root_.UpperHalfPlane.normSq_denom_ne_zero g z.im_ne_zero
  have him : z.im ≠ 0 := z.im_ne_zero
  field_simp

private theorem inner_mfderiv_congr {f₁ f₂ : ℍ → ℍ} (h : f₁ = f₂) (z : ℍ)
    (v w : TangentSpace 𝓘(ℝ, ℂ) z)
    (hf : inner ℝ (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) f₁ z v) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) f₁ z w) =
      inner ℝ v w) :
    inner ℝ (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) f₂ z v) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) f₂ z w) =
      inner ℝ v w := by
  subst h
  exact hf

/-! ### Homomorphisms into the Riemannian isometry group -/

/-- The group homomorphism sending each element of `GL(2, ℝ)` to its Riemannian isometry of the
Poincaré upper half-plane. -/
def glToIsom : GL (Fin 2) ℝ →* Isom 𝓘(ℝ, ℂ) ℍ :=
  RiemannianIsometry.constSMulHom _root_.UpperHalfPlane.inner_mfderiv_smul

/-- `glToIsom g` acts on `ℍ` as `g • ·`. -/
@[simp]
theorem glToIsom_apply (g : GL (Fin 2) ℝ) (z : ℍ) : glToIsom g z = g • z := by
  rw [glToIsom, RiemannianIsometry.constSMulHom_apply, RiemannianIsometry.constSMul_apply]

/-- The group homomorphism sending each element of `PGL(2, ℝ)` to its Riemannian isometry of the
Poincaré upper half-plane. -/
def pglToIsom : PGL(2, ℝ) →* Isom 𝓘(ℝ, ℂ) ℍ :=
  RiemannianIsometry.constSMulHom fun q z v w ↦ by
    induction q using Matrix.ProjGenLinGroup.induction_on with | mk g =>
    exact inner_mfderiv_congr (funext fun x ↦ (_root_.UpperHalfPlane.pglMk_smul g x).symm) z v w
      (_root_.UpperHalfPlane.inner_mfderiv_smul g z v w)

/-- `pglToIsom q` acts on `ℍ` as `q • ·`. -/
@[simp]
theorem pglToIsom_apply (q : PGL(2, ℝ)) (z : ℍ) : pglToIsom q z = q • z := by
  rw [pglToIsom, RiemannianIsometry.constSMulHom_apply, RiemannianIsometry.constSMul_apply]

/-- `pglToIsom` descends `glToIsom` along the projective quotient map. -/
@[simp]
theorem pglToIsom_mk (g : GL (Fin 2) ℝ) :
    pglToIsom (Matrix.ProjGenLinGroup.mk g) = glToIsom g := by
  ext z
  simp [_root_.UpperHalfPlane.pglMk_smul]

/-- `PGL(2, ℝ)` embeds into the Riemannian isometry group of the Poincaré upper half-plane. -/
theorem pglToIsom_injective : Function.Injective pglToIsom :=
  RiemannianIsometry.constSMulHom_injective _

/-- The group homomorphism sending each element of `SL(2, R)` (for any commutative ring `R`
mapping to `ℝ`) to its Riemannian isometry of the Poincaré upper half-plane. -/
def slToIsom {R : Type*} [CommRing R] [Algebra R ℝ] : SL(2, R) →* Isom 𝓘(ℝ, ℂ) ℍ :=
  RiemannianIsometry.constSMulHom fun g z v w ↦
    inner_mfderiv_congr (funext fun x ↦ (MulAction.compHom_smul_def _ g x).symm) z v w
      (_root_.UpperHalfPlane.inner_mfderiv_smul (Matrix.SpecialLinearGroup.mapGL ℝ g) z v w)

/-- `slToIsom g` acts on `ℍ` as `g • ·`. -/
@[simp]
theorem slToIsom_apply {R : Type*} [CommRing R] [Algebra R ℝ] (g : SL(2, R)) (z : ℍ) :
    slToIsom g z = g • z := by
  rw [slToIsom, RiemannianIsometry.constSMulHom_apply, RiemannianIsometry.constSMul_apply]

/-- The group homomorphism sending each element of `PSL(2, R)` (for any commutative ring `R`
mapping to `ℝ`) to its Riemannian isometry of the Poincaré upper half-plane. -/
def pslToIsom {R : Type*} [CommRing R] [Algebra R ℝ] : PSL(2, R) →* Isom 𝓘(ℝ, ℂ) ℍ :=
  RiemannianIsometry.constSMulHom fun q z v w ↦ by
    refine QuotientGroup.induction_on q fun g ↦ ?_
    exact inner_mfderiv_congr
      (funext fun x ↦ by
        rw [_root_.UpperHalfPlane.pslMk_smul, MulAction.compHom_smul_def]).symm z v w
      (_root_.UpperHalfPlane.inner_mfderiv_smul (Matrix.SpecialLinearGroup.mapGL ℝ g) z v w)

/-- `pslToIsom q` acts on `ℍ` as `q • ·`. -/
@[simp]
theorem pslToIsom_apply {R : Type*} [CommRing R] [Algebra R ℝ] (q : PSL(2, R)) (z : ℍ) :
    pslToIsom q z = q • z := by
  rw [pslToIsom, RiemannianIsometry.constSMulHom_apply, RiemannianIsometry.constSMul_apply]

/-- `pslToIsom` descends `slToIsom` along the central quotient map. -/
@[simp]
theorem pslToIsom_coe {R : Type*} [CommRing R] [Algebra R ℝ] (g : SL(2, R)) :
    pslToIsom (g : PSL(2, R)) = slToIsom g := by
  ext z
  simp [_root_.UpperHalfPlane.pslMk_smul]

/-- `pslToIsom` factors through `pglToIsom` along `Matrix.ProjectiveSpecialLinearGroup.toPGL`. -/
@[simp]
theorem pglToIsom_toPGL (q : PSL(2, ℝ)) :
    pglToIsom (Matrix.ProjectiveSpecialLinearGroup.toPGL q) = pslToIsom q := by
  ext z
  simp [_root_.UpperHalfPlane.toPGL_smul]

/-- Whenever `PSL(2, R)` acts faithfully on `ℍ` (for example `R = ℝ` or `R = ℤ`), `pslToIsom` is
injective. -/
theorem pslToIsom_injective {R : Type*} [CommRing R] [Algebra R ℝ] [FaithfulSMul PSL(2, R) ℍ] :
    Function.Injective (pslToIsom (R := R)) :=
  RiemannianIsometry.constSMulHom_injective _

/-- The Poincaré upper half-plane is homogeneous: its Riemannian isometry group acts transitively
on `ℍ`. -/
instance instIsPretransitiveIsom : MulAction.IsPretransitive (Isom 𝓘(ℝ, ℂ) ℍ) ℍ where
  exists_smul_eq z w := by
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq SL(2, ℝ) z w
    exact ⟨slToIsom g, by simpa using hg⟩

end TauCeti.UpperHalfPlane

end

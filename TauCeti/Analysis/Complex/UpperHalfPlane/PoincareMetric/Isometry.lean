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
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic

/-!
# Möbius transformations as Riemannian isometries of the Poincaré metric

Every element of `GL(2, ℝ)` acts on the upper half-plane `ℍ` by a real-analytic diffeomorphism,
preserving orientation when `det g > 0` (acting by `z ↦ (az + b)/(cz + d)`) and reversing it
when `det g < 0` (acting through complex conjugation via `UpperHalfPlane.σ`). In the inclusion
chart its real Fréchet derivative is `UpperHalfPlane.smulFDeriv g z`, which scales the Euclidean
inner product by `(det g)² / |cz + d|⁴`. Since `(g • z).im = |det g| · z.im / |cz + d|²`, the
Poincaré inner product `⟪·, ·⟫ / im²` is preserved identically.

Descending along the projective quotients gives injective group homomorphisms from `PGL(2, ℝ)`
and `PSL(2, ℝ)` into the Riemannian isometry group `Isom 𝓘(ℝ, ℂ) ℍ`. Because `SL(2, ℝ)` already
acts transitively on `ℍ`, the upper half-plane is homogeneous as a Riemannian manifold.

## Main definitions

* `UpperHalfPlane.instContMDiffConstSMulGLReal`, `UpperHalfPlane.instContMDiffConstSMulSLReal`,
  `UpperHalfPlane.instContMDiffConstSMulPGLReal`, `UpperHalfPlane.instContMDiffConstSMulPSLReal`:
  `GL(2, ℝ)`, `SL(2, R)`, `PGL(2, ℝ)`, and `PSL(2, R)` act on `ℍ` by real-analytic maps.
* `TauCeti.UpperHalfPlane.glIsomHom`: the group homomorphism `GL (Fin 2) ℝ →* Isom 𝓘(ℝ, ℂ) ℍ`.
* `TauCeti.UpperHalfPlane.pglIsomHom`: the injective homomorphism `PGL(2, ℝ) →* Isom 𝓘(ℝ, ℂ) ℍ`.
* `TauCeti.UpperHalfPlane.pslIsomHom`: the injective homomorphism `PSL(2, ℝ) →* Isom 𝓘(ℝ, ℂ) ℍ`.
* `TauCeti.UpperHalfPlane.isPretransitive_isom`: `Isom 𝓘(ℝ, ℂ) ℍ` acts transitively on `ℍ`.

## Main results

* `UpperHalfPlane.tangentSpaceCastModel_mfderiv_smul`: in inclusion-chart coordinates, the
  differential of `g • ·` is `UpperHalfPlane.smulFDeriv g z`.
* `UpperHalfPlane.inner_mfderiv_smul`, `UpperHalfPlane.inner_mfderiv_pgl_smul`,
  `UpperHalfPlane.inner_mfderiv_psl_smul`: the Möbius actions preserve the Poincaré inner product.
* `TauCeti.UpperHalfPlane.pglIsomHom_injective` and `TauCeti.UpperHalfPlane.pslIsomHom_injective`:
  the projective homomorphisms into `Isom 𝓘(ℝ, ℂ) ℍ` are injective.

## References

* S. Katok, *Fuchsian Groups*, University of Chicago Press (1992), §1.1.
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 3.
-/

public section

open Bundle Manifold
open scoped ContDiff Manifold MatrixGroups UpperHalfPlane

noncomputable section

namespace UpperHalfPlane

/-! ### Real-analyticity of the Möbius actions -/

/-- Every element of `GL(2, ℝ)` acts on `ℍ` by a real-analytic map of the underlying real
manifold. -/
instance instContMDiffConstSMulGLReal : ContMDiffConstSMul 𝓘(ℝ, ℂ) ω (GL (Fin 2) ℝ) ℍ where
  contMDiff_const_smul g := by
    refine ContMDiff.of_comp_isOpenEmbedding isOpenEmbedding_coe ?_
    have hcomp : ((↑) : ℍ → ℂ) ∘ (g • · : ℍ → ℍ) =
        (fun w : ℂ ↦ σ g (num g w / denom g w)) ∘ ((↑) : ℍ → ℂ) :=
      funext fun z ↦ coe_smul g z
    rw [hcomp]
    have hnum : ContDiff ℂ ω (fun w : ℂ ↦ num g w) :=
      (contDiff_const.mul contDiff_id).add contDiff_const
    have hdenom : ContDiff ℂ ω (fun w : ℂ ↦ denom g w) :=
      (contDiff_const.mul contDiff_id).add contDiff_const
    intro z
    have hdiv : ContDiffAt ℝ ω (fun w : ℂ ↦ num g w / denom g w) (z : ℂ) :=
      (hnum.contDiffAt.div hdenom.contDiffAt (denom_ne_zero g z)).restrict_scalars ℝ
    have hmap : ContDiffAt ℝ ω (fun w : ℂ ↦ σ g (num g w / denom g w)) (z : ℂ) :=
      (σ g : ℂ →L[ℝ] ℂ).contDiff.contDiffAt.comp (z : ℂ) hdiv
    exact hmap.contMDiffAt.comp z (contMDiffAt_extChartAt (I := 𝓘(ℝ, ℂ)))

/-- Every element of `SL(2, R)` (for any commutative ring `R` mapping to `ℝ`) acts on `ℍ` by a
real-analytic map. -/
instance instContMDiffConstSMulSLReal {R : Type*} [CommRing R] [Algebra R ℝ] :
    ContMDiffConstSMul 𝓘(ℝ, ℂ) ω SL(2, R) ℍ where
  contMDiff_const_smul g := by
    simpa only [MulAction.compHom_smul_def] using
      contMDiff_const_smul (I := 𝓘(ℝ, ℂ)) (n := ω) (Matrix.SpecialLinearGroup.mapGL ℝ g)

/-- Every element of `PGL(2, ℝ)` acts on `ℍ` by a real-analytic map. -/
instance instContMDiffConstSMulPGLReal : ContMDiffConstSMul 𝓘(ℝ, ℂ) ω PGL(2, ℝ) ℍ where
  contMDiff_const_smul q := by
    induction q using Matrix.ProjGenLinGroup.induction_on with | mk g =>
    simpa only [pglMk_smul] using contMDiff_const_smul (I := 𝓘(ℝ, ℂ)) (n := ω) g

/-- Every element of `PSL(2, R)` (for any commutative ring `R` mapping to `ℝ`) acts on `ℍ` by a
real-analytic map. -/
instance instContMDiffConstSMulPSLReal {R : Type*} [CommRing R] [Algebra R ℝ] :
    ContMDiffConstSMul 𝓘(ℝ, ℂ) ω PSL(2, R) ℍ where
  contMDiff_const_smul q := by
    induction q using QuotientGroup.induction_on with | _ g =>
    simpa only [pslMk_smul] using contMDiff_const_smul (I := 𝓘(ℝ, ℂ)) (n := ω) g

/-! ### Differential and metric preservation -/

/-- In the coordinates of the inclusion chart, the real differential of the Möbius action of
`g : GL (Fin 2) ℝ` at `z : ℍ` is `UpperHalfPlane.smulFDeriv g z`. -/
theorem tangentSpaceCastModel_mfderiv_smul (g : GL (Fin 2) ℝ) (z : ℍ)
    (v : TangentSpace 𝓘(ℝ, ℂ) z) :
    tangentSpaceCastModel 𝓘(ℝ, ℂ) (g • z) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (g • ·) z v) =
      smulFDeriv g z (tangentSpaceCastModel 𝓘(ℝ, ℂ) z v) := by
  have hd : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (g • ·) z :=
    (contMDiff_const_smul (I := 𝓘(ℝ, ℂ)) (n := ω) g z).mdifferentiableAt (by simp)
  rw [hd.tangentSpaceCastModel_mfderiv_apply]
  have hlocal : writtenInExtChartAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) z (g • ·) =ᶠ[nhds (z : ℂ)]
      fun w : ℂ ↦ ((g • ofComplex w : ℍ) : ℂ) := by
    simpa [writtenInExtChartAt, extChartAt, Function.comp_def] using
      TauCeti.UpperHalfPlane.comp_chartAt_symm_eventuallyEq (fun w : ℍ ↦ ((g • w : ℍ) : ℂ)) z
  have hchart : extChartAt 𝓘(ℝ, ℂ) z z = (z : ℂ) := by simp
  rw [hchart, hlocal.fderiv_eq, (hasStrictFDerivAt_smul g z).hasFDerivAt.fderiv]

/-- The sign-conjugation `UpperHalfPlane.σ g` preserves the Euclidean inner product on `ℂ`. -/
theorem inner_σ (g : GL (Fin 2) ℝ) (u w : ℂ) :
    inner ℝ (σ g u) (σ g w) = inner ℝ u w := by
  simp only [σ]
  split_ifs
  · rfl
  · simp [Complex.inner]

/-- The real Fréchet derivative `UpperHalfPlane.smulFDeriv g z` scales the Euclidean inner product
on `ℂ` by `(det g)² / |cz + d|⁴`. -/
theorem inner_smulFDeriv (g : GL (Fin 2) ℝ) (z u w : ℂ) :
    inner ℝ (smulFDeriv g z u) (smulFDeriv g z w) =
      (g.det.val ^ 2 / Complex.normSq (denom g z) ^ 2) * inner ℝ u w := by
  have happly (x : ℂ) : smulFDeriv g z x = σ g (x * (g.det.val / denom g z ^ 2)) := rfl
  rw [happly, happly, inner_σ]
  have hmul (c : ℂ) : inner ℝ (u * c) (w * c) = Complex.normSq c * inner ℝ u w := by
    simp [Complex.inner, Complex.normSq_apply]
    ring
  rw [hmul, map_div₀, map_pow, Complex.normSq_ofReal, ← sq]

/-- Every element of `GL(2, ℝ)` preserves the Poincaré inner product on tangent spaces of `ℍ`. -/
theorem inner_mfderiv_smul (g : GL (Fin 2) ℝ) (z : ℍ) (v w : TangentSpace 𝓘(ℝ, ℂ) z) :
    inner ℝ (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (g • ·) z v) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (g • ·) z w) =
      inner ℝ v w := by
  rw [inner_tangentSpace, inner_tangentSpace,
    tangentSpaceCastModel_mfderiv_smul, tangentSpaceCastModel_mfderiv_smul,
    inner_smulFDeriv, im_smul_eq_div_normSq]
  have hdet : g.det.val ≠ 0 := g.det.ne_zero
  have hden : Complex.normSq (denom g z) ≠ 0 := (normSq_denom_pos g z.im_ne_zero).ne'
  have him : z.im ≠ 0 := z.im_pos.ne'
  field_simp [hdet, hden, him]
  rw [sq_abs]
  ring

/-- Every element of `PGL(2, ℝ)` preserves the Poincaré inner product on tangent spaces of `ℍ`. -/
theorem inner_mfderiv_pgl_smul (q : PGL(2, ℝ)) (z : ℍ) (v w : TangentSpace 𝓘(ℝ, ℂ) z) :
    inner ℝ (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (q • ·) z v) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (q • ·) z w) =
      inner ℝ v w := by
  induction q using Matrix.ProjGenLinGroup.induction_on with | mk g =>
  have hfun : (fun x : ℍ ↦ Matrix.ProjGenLinGroup.mk g • x) = (g • ·) := funext (pglMk_smul g)
  rw [hfun]
  exact inner_mfderiv_smul g z v w

/-- Every element of `PSL(2, R)` (for any commutative ring `R` mapping to `ℝ`) preserves the
Poincaré inner product on tangent spaces of `ℍ`. -/
theorem inner_mfderiv_psl_smul {R : Type*} [CommRing R] [Algebra R ℝ]
    (q : PSL(2, R)) (z : ℍ) (v w : TangentSpace 𝓘(ℝ, ℂ) z) :
    inner ℝ (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (q • ·) z v) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (q • ·) z w) =
      inner ℝ v w := by
  induction q using QuotientGroup.induction_on with | _ g =>
  have hfun : (fun x : ℍ ↦ (↑g : PSL(2, R)) • x) =
      ((Matrix.SpecialLinearGroup.mapGL ℝ g) • ·) :=
    funext fun x ↦ by rw [pslMk_smul, MulAction.compHom_smul_def]
  rw [hfun]
  exact inner_mfderiv_smul (Matrix.SpecialLinearGroup.mapGL ℝ g) z v w

end UpperHalfPlane

namespace TauCeti.UpperHalfPlane

/-! ### Homomorphisms into the Riemannian isometry group -/

/-- The Möbius action of `GL(2, ℝ)` as a homomorphism into the Riemannian isometry group of `ℍ`. -/
def glIsomHom : GL (Fin 2) ℝ →* Isom 𝓘(ℝ, ℂ) ℍ :=
  RiemannianIsometry.constSMulHom _root_.UpperHalfPlane.inner_mfderiv_smul

/-- `glIsomHom g` acts on `ℍ` as `g • ·`. -/
@[simp]
theorem glIsomHom_apply (g : GL (Fin 2) ℝ) (z : ℍ) : glIsomHom g z = g • z := by
  rw [glIsomHom, RiemannianIsometry.constSMulHom_apply, RiemannianIsometry.constSMul_apply]

/-- The Möbius action of `PGL(2, ℝ)` as a homomorphism into the Riemannian isometry group of
`ℍ`. -/
def pglIsomHom : PGL(2, ℝ) →* Isom 𝓘(ℝ, ℂ) ℍ :=
  RiemannianIsometry.constSMulHom _root_.UpperHalfPlane.inner_mfderiv_pgl_smul

/-- `pglIsomHom q` acts on `ℍ` as `q • ·`. -/
@[simp]
theorem pglIsomHom_apply (q : PGL(2, ℝ)) (z : ℍ) : pglIsomHom q z = q • z := by
  rw [pglIsomHom, RiemannianIsometry.constSMulHom_apply, RiemannianIsometry.constSMul_apply]

/-- Evaluating `pglIsomHom` on a matrix representative recovers `glIsomHom`. -/
@[simp]
theorem pglIsomHom_mk (g : GL (Fin 2) ℝ) :
    pglIsomHom (Matrix.ProjGenLinGroup.mk g) = glIsomHom g :=
  RiemannianIsometry.ext fun z ↦ by simp

/-- The homomorphism `PGL(2, ℝ) →* Isom 𝓘(ℝ, ℂ) ℍ` is injective, since `PGL(2, ℝ)` acts
faithfully on `ℍ`. -/
theorem pglIsomHom_injective : Function.Injective pglIsomHom :=
  RiemannianIsometry.constSMulHom_injective _

/-- The orientation-preserving Möbius action of `PSL(2, ℝ)` as a homomorphism into the Riemannian
isometry group of `ℍ`. -/
def pslIsomHom : PSL(2, ℝ) →* Isom 𝓘(ℝ, ℂ) ℍ :=
  pglIsomHom.comp Matrix.ProjectiveSpecialLinearGroup.toPGL

/-- `pslIsomHom q` acts on `ℍ` as `q • ·`. -/
@[simp]
theorem pslIsomHom_apply (q : PSL(2, ℝ)) (z : ℍ) : pslIsomHom q z = q • z := by
  simp [pslIsomHom]

/-- `pslIsomHom` is the restriction of `pglIsomHom` along `toPGL`. -/
@[simp]
theorem pglIsomHom_toPGL (q : PSL(2, ℝ)) :
    pglIsomHom (Matrix.ProjectiveSpecialLinearGroup.toPGL q) = pslIsomHom q := by
  rw [pslIsomHom, MonoidHom.comp_apply]

/-- The homomorphism `PSL(2, ℝ) →* Isom 𝓘(ℝ, ℂ) ℍ` is injective. -/
theorem pslIsomHom_injective : Function.Injective pslIsomHom :=
  pglIsomHom_injective.comp Matrix.ProjectiveSpecialLinearGroup.toPGL_injective

/-- The Riemannian isometry group of the Poincaré upper half-plane acts transitively. -/
instance isPretransitive_isom : MulAction.IsPretransitive (Isom 𝓘(ℝ, ℂ) ℍ) ℍ where
  exists_smul_eq x y := by
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq SL(2, ℝ) x y
    exact ⟨pslIsomHom g, by simpa only [RiemannianIsometry.smul_def, pslIsomHom_apply,
      _root_.UpperHalfPlane.pslMk_smul] using hg⟩

end TauCeti.UpperHalfPlane

end

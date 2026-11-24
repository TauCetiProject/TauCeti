/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.Manifold
public import TauCeti.Analysis.Complex.UpperHalfPlane.PSL.Manifold
public import TauCeti.Analysis.Complex.UpperHalfPlane.Riemannian.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Action
import Mathlib.Analysis.Complex.UpperHalfPlane.FixedPoints
import TauCeti.Analysis.Complex.UpperHalfPlane.SmulDeriv

/-!
# Riemannian isometries of the Poincaré upper half-plane

Mathlib's action `UpperHalfPlane.glAction` of `GL(2, ℝ)` on the complex upper half-plane `ℍ` sends
`z` to `(a z + b) / (c z + d)` when `det g > 0` and to `(a conj z + b) / (c conj z + d)` when
`det g < 0`. Every element of `GL(2, ℝ)` acts on `ℍ` by a real-analytic diffeomorphism for the
real manifold structure `𝓘(ℝ, ℂ)` (`TauCeti.UpperHalfPlane.instContMDiffConstSMulGLReal`).

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

* `TauCeti.UpperHalfPlane.glToIsom`, `TauCeti.UpperHalfPlane.pglToIsom`,
  `TauCeti.UpperHalfPlane.slToIsom`, `TauCeti.UpperHalfPlane.pslToIsom`: group homomorphisms from
  `GL(2, ℝ)`, `PGL(2, ℝ)`, `SL(2, R)`, and `PSL(2, R)` into `Isom 𝓘(ℝ, ℂ) ℍ`.

## Main results

* `UpperHalfPlane.inner_mfderiv_smul`: the differential of `z ↦ g • z` preserves the Poincaré
  metric for every `g ∈ GL(2, ℝ)`.
* `TauCeti.UpperHalfPlane.ker_glToIsom`: the elements of `GL(2, ℝ)` acting trivially are the
  scalar matrices.
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
open scoped ContDiff Manifold MatrixGroups UpperHalfPlane

noncomputable section

namespace TauCeti.UpperHalfPlane

open _root_.UpperHalfPlane

/-- The differential of `z ↦ g • z` preserves the Poincaré metric: every element of `GL(2, ℝ)`
acts on the upper half-plane by a Riemannian isometry. -/
theorem _root_.UpperHalfPlane.inner_mfderiv_smul (g : GL (Fin 2) ℝ) (z : ℍ)
    (v w : TangentSpace 𝓘(ℝ, ℂ) z) :
    inner ℝ (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (g • ·) z v) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (g • ·) z w) =
      inner ℝ v w := by
  rw [(g • z).inner_tangentSpace, z.inner_tangentSpace,
    Matrix.GeneralLinearGroup.tangentSpaceCastModel_mfderiv_smul g z v,
    Matrix.GeneralLinearGroup.tangentSpaceCastModel_mfderiv_smul g z w,
    Matrix.GeneralLinearGroup.inner_smulFDeriv_apply]
  have hz := z.im_pos.ne'
  field_simp

/-- The group homomorphism sending each element of `GL(2, ℝ)` to the Riemannian isometry it induces
on the Poincaré upper half-plane `ℍ`. Positive-determinant matrices act holomorphically and
negative-determinant matrices act antiholomorphically. -/
def glToIsom : GL (Fin 2) ℝ →* Isom 𝓘(ℝ, ℂ) ℍ where
  toFun g :=
    { toDiffeomorph := Diffeomorph.constSmul 𝓘(ℝ, ℂ) ∞ g
      inner_mfderiv' z v w := by
        rw [Diffeomorph.coe_constSmul]
        exact inner_mfderiv_smul g z v w }
  map_one' := by
    ext z
    simp [← RiemannianIsometry.coe_toDiffeomorph]
  map_mul' g h := by
    ext z
    simp [← RiemannianIsometry.coe_toDiffeomorph, mul_smul]

/-- The underlying diffeomorphism of `glToIsom g` is `Diffeomorph.constSmul 𝓘(ℝ, ℂ) ∞ g`. -/
@[simp]
theorem toDiffeomorph_glToIsom (g : GL (Fin 2) ℝ) :
    (glToIsom g).toDiffeomorph = Diffeomorph.constSmul 𝓘(ℝ, ℂ) ∞ g := (rfl)

/-- `glToIsom g` acts on `ℍ` by `g • z`. -/
@[simp]
theorem glToIsom_apply (g : GL (Fin 2) ℝ) (z : ℍ) : glToIsom g z = g • z := by
  rw [← RiemannianIsometry.coe_toDiffeomorph, toDiffeomorph_glToIsom]
  exact Diffeomorph.constSmul_apply (I := 𝓘(ℝ, ℂ)) (n := ∞) g z

/-- The inverse of `glToIsom g` acts on `ℍ` by `g⁻¹ • z`. -/
@[simp]
theorem glToIsom_symm_apply (g : GL (Fin 2) ℝ) (z : ℍ) : (glToIsom g).symm z = g⁻¹ • z := by
  rw [← RiemannianIsometry.inv_apply, ← map_inv, glToIsom_apply]

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

/-- The underlying diffeomorphism of `pglToIsom q` is `Diffeomorph.constSmul 𝓘(ℝ, ℂ) ∞ q`. -/
@[simp]
theorem toDiffeomorph_pglToIsom (q : PGL(2, ℝ)) :
    (pglToIsom q).toDiffeomorph = Diffeomorph.constSmul 𝓘(ℝ, ℂ) ∞ q := by
  ext z
  simp

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

/-- The underlying diffeomorphism of `slToIsom g` is `Diffeomorph.constSmul 𝓘(ℝ, ℂ) ∞ g`. -/
@[simp]
theorem toDiffeomorph_slToIsom {R : Type*} [CommRing R] [Algebra R ℝ] (g : SL(2, R)) :
    (slToIsom g).toDiffeomorph = Diffeomorph.constSmul 𝓘(ℝ, ℂ) ∞ g := by
  ext z
  simp

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

/-- The underlying diffeomorphism of `pslToIsom q` is `Diffeomorph.constSmul 𝓘(ℝ, ℂ) ∞ q`. -/
@[simp]
theorem toDiffeomorph_pslToIsom {R : Type*} [CommRing R] [Algebra R ℝ] (q : PSL(2, R)) :
    (pslToIsom q).toDiffeomorph = Diffeomorph.constSmul 𝓘(ℝ, ℂ) ∞ q := by
  ext z
  simp

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

/-- As a function, the Riemannian isometry attached to `g ∈ GL(2, ℝ)` is `(g • ·)`. -/
theorem coe_glToIsom (g : GL (Fin 2) ℝ) : ⇑(glToIsom g) = (g • ·) :=
  funext (glToIsom_apply g)

/-- As a function, the inverse of the Riemannian isometry attached to `g ∈ GL(2, ℝ)` is
`(g⁻¹ • ·)`. -/
theorem coe_glToIsom_symm (g : GL (Fin 2) ℝ) : ⇑(glToIsom g).symm = (g⁻¹ • ·) :=
  funext (glToIsom_symm_apply g)

/-- Nonzero scalar matrices act on `ℍ` by the identity isometry. -/
@[simp]
theorem glToIsom_scalar (u : ℝˣ) : glToIsom (Matrix.GeneralLinearGroup.scalar (Fin 2) u) = 1 :=
  RiemannianIsometry.ext fun z ↦ by
    rw [glToIsom_apply, glScalar_smul, RiemannianIsometry.one_apply]

/-- As a function, the Riemannian isometry attached to `q ∈ PGL(2, ℝ)` is `(q • ·)`. -/
theorem coe_pglToIsom (q : PGL(2, ℝ)) : ⇑(pglToIsom q) = (q • ·) :=
  funext (pglToIsom_apply q)

/-- As a function, the inverse of the Riemannian isometry attached to `q ∈ PGL(2, ℝ)` is
`(q⁻¹ • ·)`. -/
theorem coe_pglToIsom_symm (q : PGL(2, ℝ)) : ⇑(pglToIsom q).symm = (q⁻¹ • ·) :=
  funext (pglToIsom_symm_apply q)

/-- The elements of `GL(2, ℝ)` acting on `ℍ` by the identity isometry are the scalar matrices,
which form the centre. -/
@[simp]
theorem ker_glToIsom : glToIsom.ker = Subgroup.center (GL (Fin 2) ℝ) := by
  rw [← pglToIsom_comp_mk, MonoidHom.ker_comp_of_injective _ _ pglToIsom_injective,
    Matrix.ProjGenLinGroup.ker_mk]


/-- The Riemannian isometry group of the Poincaré upper half-plane acts transitively on `ℍ`, so `ℍ`
is a homogeneous Riemannian manifold. -/
instance isPretransitive_isom : MulAction.IsPretransitive (Isom 𝓘(ℝ, ℂ) ℍ) ℍ :=
  .of_smul_eq glToIsom fun {g z} ↦ glToIsom_apply g z

end TauCeti.UpperHalfPlane

end

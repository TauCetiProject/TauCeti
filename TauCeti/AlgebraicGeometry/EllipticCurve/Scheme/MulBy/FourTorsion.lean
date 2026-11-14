/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Smooth.StandardSmooth
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.MulBy
public import TauCeti.AlgebraicGeometry.EllipticCurve.TateNormalForm
import TauCeti.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.ZeroSection

/-!
# Points killed by `2`, and the `4`-torsion locus on the Tate normal form

Let `W` be an elliptic Weierstrass curve over a commutative ring `R`, with projective model
`E = projModel W` over `Spec R`, and let `(x, y)` be a solution of the affine Weierstrass equation
over `R`. This file shows first that the point `P = [x : y : 1]` of `E` is killed by multiplication
by `2`, as a morphism `Spec R ⟶ E`, if and only if the `2`-division polynomial `ψ₂ = 2y + a₁x + a₃`
vanishes at `(x, y)`
(`WeierstrassCurve.projModelAffinePoint_projModelMulBy_two_eq_projModelZero_iff`).
Indeed `2P = 0` means `P = -P = [x : -y - a₁x - a₃ : 1]`, which is the equation `2y + a₁x + a₃ = 0`
with no division by `2` and no reducedness assumption on `R`.

Specialising to an elliptic Tate normal form `Y² + aXY + bY = X³ + bX²`, where `b` is a unit, the
second Bosma–Lenstra addition law computes the double of `(0, 0)` on the projective model as
`2 • (0, 0) = [-b : b(a - 1) : 1]` (`WeierstrassCurve.tateNormalForm_projModelMulBy_two_zero`).
At `(-b, b(a - 1))` the `2`-division polynomial takes the value `2b(a - 1) - ab + b = b(a - 1)`,
without a factor of `2`. Since `b` is a unit, it follows over any commutative ring `R` that
`4 • (0, 0) = 0` on an elliptic Tate normal form if and only if `a = 1`
(`WeierstrassCurve.tateNormalForm_projModelMulBy_four_eq_projModelZero_iff`).

Setting `a = 1` gives the one-parameter family `Y² + XY + bY = X³ + bX²`, whose discriminant is
`b⁴(1 - 16b)` (`WeierstrassCurve.tateNormalForm_one_Δ`). Over `ℤ[B, (B(1 - 16B))⁻¹]`
(`WeierstrassCurve.UniversalGammaOneFour.Ring`), a localization of a one-variable polynomial ring
and therefore standard smooth of relative dimension `1` over `ℤ`, this produces the universal
elliptic Tate normal form with `4 • (0, 0) = 0` (`WeierstrassCurve.UniversalGammaOneFour.curve`).

## Main results

* `WeierstrassCurve.projModelMulBy_mul`: `[m * n] = [n] ≫ [m]` on the projective model.
* `WeierstrassCurve.projModelAffinePoint_projModelMulBy_two_eq_projModelZero_iff`: the point
  `[x : y : 1]` is killed by `2` if and only if `ψ₂(x, y) = 0`.
* `WeierstrassCurve.tateNormalForm_projModelMulBy_two_zero`: on an elliptic Tate normal form
  `Y² + aXY + bY = X³ + bX²`, doubling `[0 : 0 : 1]` gives `[-b : b(a - 1) : 1]`.
* `WeierstrassCurve.tateNormalForm_projModelMulBy_four_eq_projModelZero_iff`: on an elliptic Tate
  normal form, `[0 : 0 : 1]` is killed by `4` if and only if `a = 1`.
* `WeierstrassCurve.UniversalGammaOneFour.isStandardSmoothOfRelativeDimension`: the ring
  `ℤ[B, (B(1 - 16B))⁻¹]` is standard smooth of relative dimension `1` over `ℤ`.

## References

* D. S. Kubert, *Universal bounds on the torsion of elliptic curves*, Proc. London Math. Soc. (3)
  33 (1976), 193–237, Table 3 (`X₁(4)`).
* D. Loeffler, *Modular Curves*, lecture notes, §3.3.
-/

public section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj Polynomial
  TauCeti.AlgebraicGeometry

universe u

namespace WeierstrassCurve

section TwoTorsion

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) [W.IsElliptic]

/-- Multiplication by a product `m * n` on the projective model is multiplication by `n` followed
by multiplication by `m`. -/
@[reassoc]
theorem projModelMulBy_mul (m n : ℤ) :
    W.projModelMulBy (m * n) = W.projModelMulBy n ≫ W.projModelMulBy m := by
  simp only [projModelMulBy_eq, EllipticCurveGeom.mulBy_mul, Over.comp_left, Category.assoc,
    Iso.hom_inv_id_assoc]

/-- Multiplication by `n` commutes with the base change morphism of projective Weierstrass
models. -/
@[reassoc]
theorem projModelMulBy_projModelBaseChange {R' : Type u} [CommRing R'] (f : R →+* R') (n : ℤ) :
    (W.map f).projModelMulBy n ≫ W.projModelBaseChange f =
      W.projModelBaseChange f ≫ W.projModelMulBy n := by
  have hpb : IsPullback ((toEllipticCurveGeomIso (W.map f)).hom ≫ W.projModelBaseChange f)
      (toEllipticCurveGeom (W.map f)).structureMap W.projModelOver
      (Spec.map (CommRingCat.ofHom f)) := by
    simpa using (IsPullback.of_horiz_isIso (fst := (toEllipticCurveGeomIso (W.map f)).hom)
      (snd := (toEllipticCurveGeom (W.map f)).structureMap) (f := (W.map f).projModelOver)
      (g := 𝟙 _) ⟨by simp⟩).paste_horiz (W.isPullback_projModelBaseChange f)
  have h := comp_projModelMulBy_of_isPullback W hpb (by simp) n
  simp only [Category.assoc] at h
  rw [(W.map f).projModelMulBy_eq, Category.assoc, Category.assoc, ← h, Iso.inv_hom_id_assoc]

variable {W}

/-- **Points killed by `2`.** Let `W` be an elliptic Weierstrass curve over a commutative ring `R`
and `(x, y)` a solution of its affine equation over `R`. The point `[x : y : 1]` of the projective
model with values in `R` is killed by multiplication by `2`, as a morphism `Spec R ⟶ projModel W`,
if and only if `ψ₂(x, y) = 2y + a₁x + a₃ = 0`. -/
theorem projModelAffinePoint_projModelMulBy_two_eq_projModelZero_iff {x y : R}
    (h : W.toAffine.Equation x y) :
    W.projModelAffinePoint h ≫ W.projModelMulBy 2 = W.projModelZero ↔
      W.ψ₂.evalEval x y = 0 := by
  rw [show (2 : ℤ) = 1 + 1 by norm_num,
    comp_projModelMulBy_add_one_eq_projModelZero_iff (projModelAffinePoint_projModelOver h),
    show W.projModelMulBy 1 = 𝟙 _ by simp [projModelMulBy_eq], Category.comp_id,
    projModelAffinePoint_projModelNeg, projModelAffinePoint_inj]
  simp only [true_and, Affine.negY, ψ₂, Affine.evalEval_polynomialY]
  exact ⟨fun hy ↦ by linear_combination hy, fun hψ ↦ by linear_combination hψ⟩

end TwoTorsion

section TateNormalForm

variable {R : Type*} [CommRing R]

/-- The point `(-b, b(a - 1))` lies on the Tate normal form `Y² + aXY + bY = X³ + bX²`. -/
theorem equation_tateNormalForm_neg_mul_sub_one (a b : R) :
    (tateNormalForm a b).toAffine.Equation (-b) (b * (a - 1)) := by
  rw [Affine.equation_iff]
  simp only [tateNormalForm_a₁, tateNormalForm_a₂, tateNormalForm_a₃, tateNormalForm_a₄,
    tateNormalForm_a₆]
  ring

/-- On the Tate normal form `Y² + aXY + bY = X³ + bX²`, the `2`-division polynomial `ψ₂` takes the
value `b(a - 1)` at `(-b, b(a - 1))`. -/
@[simp]
theorem evalEval_ψ₂_tateNormalForm_neg_mul_sub_one (a b : R) :
    (tateNormalForm a b).ψ₂.evalEval (-b) (b * (a - 1)) = b * (a - 1) := by
  simp only [ψ₂, Affine.evalEval_polynomialY, tateNormalForm_a₁, tateNormalForm_a₃]
  ring

/-- The discriminant of the specialized Tate normal form `Y² + XY + bY = X³ + bX²` is
`b⁴(1 - 16b)`. -/
theorem tateNormalForm_one_Δ (b : R) :
    (tateNormalForm 1 b).Δ = b ^ 4 * (1 - 16 * b) := by
  rw [tateNormalForm_Δ]
  ring

/-- The specialized Tate normal form `Y² + XY + bY = X³ + bX²` is elliptic if and only if
`b(1 - 16b)` is a unit. -/
theorem isUnit_tateNormalForm_one_Δ_iff {b : R} :
    IsUnit (tateNormalForm 1 b).Δ ↔ IsUnit (b * (1 - 16 * b)) := by
  rw [tateNormalForm_one_Δ, IsUnit.mul_iff, IsUnit.mul_iff, isUnit_pow_iff four_ne_zero]

end TateNormalForm

section TateNormalFormScheme

variable {R : Type u} [CommRing R] {a b : R} [(tateNormalForm a b).IsElliptic]

/-- **Doubling `(0, 0)` on an elliptic Tate normal form.** On `Y² + aXY + bY = X³ + bX²`, doubling
the section `[0 : 0 : 1]` of the projective model yields `[-b : b(a - 1) : 1]`. -/
theorem tateNormalForm_projModelMulBy_two_zero :
    (tateNormalForm a b).projModelAffinePoint (equation_tateNormalForm_zero a b) ≫
        (tateNormalForm a b).projModelMulBy 2 =
      (tateNormalForm a b).projModelAffinePoint (equation_tateNormalForm_neg_mul_sub_one a b) := by
  set W := tateNormalForm a b
  have hb : IsUnit b := isUnit_of_isUnit_tateNormalForm_Δ W.isUnit_Δ
  have h₀ : W.toAffine.Equation 0 0 := equation_tateNormalForm_zero a b
  have hW : W.toProjective.map (RingHom.id R) = W.toProjective := W.map_id
  have hE : W.toProjective.Equation ![0, 0, 1] := (Projective.equation_some _ _).mpr h₀
  have hdbl : (W.toProjective.map (RingHom.id R)).dblAddXYZ ![0, 0, 1] ![0, 0, 1] =
      W.toProjective.dblXYZ ![0, 0, 1] := by
    rw [Projective.dblAddXYZ_self (hW ▸ hE), hW]
  have hm : IsUnit ((W.toProjective.map (RingHom.id R)).dblAddXYZ ![0, 0, 1] ![0, 0, 1] 2) := by
    rw [hdbl, Projective.dblXYZ_some h₀]
    simpa [W] using hb.pow 3
  rw [comp_projModelMulBy_two, projModelAffinePoint_def, projModelAffinePoint_def,
    lift_projModelPoint_additionMorphism_of_isUnit_dblAddXYZ (hm := hm),
    projModelPoint_eq_projModelPoint_iff, hdbl, Projective.dblXYZ_some h₀]
  refine ⟨rfl, (hb.pow 3).unit, ?_⟩
  ext i
  fin_cases i <;>
    simp [W, Affine.negY, Affine.evalEval_polynomialX, Units.smul_def]
  ring

/-- **The `4`-torsion locus of `(0, 0)` on an elliptic Tate normal form.** Over any commutative
ring `R`, the point `[0 : 0 : 1]` of an elliptic Tate normal form `Y² + aXY + bY = X³ + bX²` is
killed by multiplication by `4` if and only if `a = 1`. -/
theorem tateNormalForm_projModelMulBy_four_eq_projModelZero_iff :
    (tateNormalForm a b).projModelAffinePoint (equation_tateNormalForm_zero a b) ≫
        (tateNormalForm a b).projModelMulBy 4 = (tateNormalForm a b).projModelZero ↔
      a = 1 := by
  have hb : IsUnit b := isUnit_of_isUnit_tateNormalForm_Δ (tateNormalForm a b).isUnit_Δ
  rw [show (4 : ℤ) = 2 * 2 by norm_num, projModelMulBy_mul, ← Category.assoc,
    tateNormalForm_projModelMulBy_two_zero,
    projModelAffinePoint_projModelMulBy_two_eq_projModelZero_iff,
    evalEval_ψ₂_tateNormalForm_neg_mul_sub_one, hb.mul_right_eq_zero, sub_eq_zero]

end TateNormalFormScheme

/-! ### The universal Tate normal form with `4 • (0, 0) = 0` -/

namespace UniversalGammaOneFour

open MvPolynomial (X)

/-- The polynomial `B(1 - 16B)` in `ℤ[B]`, inverted to form the base ring of `Y₁(4)`. -/
noncomputable abbrev discrFactor : MvPolynomial (Fin 1) ℤ :=
  X 0 * (1 - 16 * X 0)

/-- The coordinate ring `ℤ[B, (B(1 - 16B))⁻¹]` of `Y₁(4)`: a localization of the polynomial ring
in one variable over `ℤ`. -/
abbrev Ring : Type :=
  Localization.Away discrFactor

/-- The ring `ℤ[B, (B(1 - 16B))⁻¹]` is standard smooth of relative dimension `1` over `ℤ`: it is a
localization away from one element of a polynomial ring in one variable over `ℤ`. -/
instance isStandardSmoothOfRelativeDimension :
    Algebra.IsStandardSmoothOfRelativeDimension 1 ℤ Ring := by
  have : Algebra.IsStandardSmoothOfRelativeDimension 0 (MvPolynomial (Fin 1) ℤ) Ring :=
    Algebra.IsStandardSmoothOfRelativeDimension.localization_away discrFactor
  exact Algebra.IsStandardSmoothOfRelativeDimension.trans 1 0 ℤ (MvPolynomial (Fin 1) ℤ) Ring

/-- The parameter `B` in `ℤ[B, (B(1 - 16B))⁻¹]`. -/
noncomputable def param : Ring :=
  algebraMap (MvPolynomial (Fin 1) ℤ) Ring (X 0)

/-- Two ring homomorphisms out of `ℤ[B, (B(1 - 16B))⁻¹]` are equal as soon as they agree on `B`. -/
@[ext high]
theorem Ring.ringHom_ext {S : Type*} [Semiring S] {f g : Ring →+* S}
    (h : f param = g param) : f = g :=
  IsLocalization.ringHom_ext (.powers discrFactor) <|
    MvPolynomial.ringHom_ext' (RingHom.ext_int _ _) <| Fin.forall_fin_one.mpr h

/-- The universal elliptic Tate normal form `Y² + XY + BY = X³ + BX²` with `4 • (0, 0) = 0`, over
`ℤ[B, (B(1 - 16B))⁻¹]`. -/
noncomputable def curve : WeierstrassCurve Ring :=
  tateNormalForm 1 param

/-- The curve `Y² + XY + BY = X³ + BX²` over `ℤ[B, (B(1 - 16B))⁻¹]` is elliptic. -/
instance isElliptic_curve : curve.IsElliptic where
  isUnit := isUnit_tateNormalForm_one_Δ_iff.mpr <| by
    simpa [param, discrFactor, map_ofNat] using
      IsLocalization.Away.algebraMap_isUnit (S := Ring) discrFactor

/-- The classifying homomorphism `ℤ[B, (B(1 - 16B))⁻¹] →+* R` sending `B` to `b`, for `b : R` with
`tateNormalForm 1 b` elliptic. -/
noncomputable def lift {R : Type*} [CommRing R] {b : R} (h : IsUnit (tateNormalForm 1 b).Δ) :
    Ring →+* R :=
  IsLocalization.Away.lift discrFactor
    (g := MvPolynomial.eval₂Hom (Int.castRingHom R) ![b]) <| by
    simpa [discrFactor] using isUnit_tateNormalForm_one_Δ_iff.mp h

/-- `lift h` maps the parameter `B` to `b`. -/
@[simp]
theorem lift_param {R : Type*} [CommRing R] {b : R} (h : IsUnit (tateNormalForm 1 b).Δ) :
    lift h param = b := by
  simp [lift, param]

/-- Every elliptic Tate normal form with `a = 1` is the base change of `UniversalGammaOneFour.curve`
along `lift h`. -/
@[simp]
theorem map_lift {R : Type*} [CommRing R] {b : R} (h : IsUnit (tateNormalForm 1 b).Δ) :
    curve.map (lift h) = tateNormalForm 1 b := by
  simp [curve]

/-- The homomorphism `ℤ[A, B][Δ⁻¹] →+* ℤ[B, (B(1 - 16B))⁻¹]` specializing the universal Tate normal
form to `A = 1`, `B = param`. -/
noncomputable def toUniversalTate : UniversalTate.Ring →+* Ring :=
  UniversalTate.lift curve.isUnit_Δ

/-- `toUniversalTate` sends the first parameter `A` of the universal Tate normal form to `1`. -/
@[simp]
theorem toUniversalTate_X_zero :
    toUniversalTate (algebraMap (MvPolynomial (Fin 2) ℤ) UniversalTate.Ring (X 0)) = 1 :=
  UniversalTate.lift_algebraMap_X_zero _

/-- `toUniversalTate` sends the second parameter `B` of the universal Tate normal form to
`param`. -/
@[simp]
theorem toUniversalTate_X_one :
    toUniversalTate (algebraMap (MvPolynomial (Fin 2) ℤ) UniversalTate.Ring (X 1)) = param :=
  UniversalTate.lift_algebraMap_X_one _

/-- Composing `lift h` with `toUniversalTate` recovers `UniversalTate.lift h`. -/
@[simp]
theorem lift_comp_toUniversalTate {R : Type*} [CommRing R] {b : R}
    (h : IsUnit (tateNormalForm 1 b).Δ) :
    (lift h).comp toUniversalTate = UniversalTate.lift h := by
  ext <;> simp

end UniversalGammaOneFour

end WeierstrassCurve

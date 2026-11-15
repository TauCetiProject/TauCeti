/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Pointed
public import TauCeti.AlgebraicGeometry.EllipticCurve.TateNormalForm
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.TwoTorsion
import TauCeti.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.ZSMul

/-!
# Pointed curves in Tate normal form

Over a field `F`, let `(W, P)` be a Weierstrass curve with a marked point `P` such that
`2 • P ≠ 0` and `3 • P ≠ 0`. Then `P = (x, y)` is affine, the `2`-division polynomial `ψ₂` does
not vanish at `(x, y)` and the `3`-division polynomial `Ψ₃` does not vanish at `x`, so a change of
variables carries `(W, P)` to the Tate normal form `Y² + aXY + bY = X³ + bX²` with the point
`(0, 0)` (`WeierstrassCurve.toTateNormalForm`). The coefficients are

`a = Ψ₃(x) ψ₂(x, y)⁻³ (a₁ + 2 s)`  and  `b = Ψ₃(x)³ ψ₂(x, y)⁻⁸`,

where `s = (a₄ + 2 a₂ x - a₁ y + 3 x²) / ψ₂(x, y)` is the slope of the tangent line at `(x, y)`
(`TauCeti.PointedWeierstrassCurve.tateNormalFormCoeffs`). Two pointed Tate normal forms are
isomorphic only when they are equal, so these coefficients are invariants of the isomorphism class
of `(W, P)`, and they classify it.

For `N ≥ 4` a point of exact order `N` satisfies both conditions. Hence the isomorphism classes of
elliptic curves over `F` with a point of exact order `N` are in bijection with the pairs `(a, b)`
for which the Tate normal form is elliptic and `(0, 0)` has exact order `N`
(`TauCeti.PointedWeierstrassCurve.exactOrderQuotientEquivTateNormalForm`). Read in the coordinates
`A = a`, `B = b` of `Spec ℤ[A, B][Δ⁻¹]`, these pairs describe the `F`-points of the fine moduli
scheme `Y₁(N)` (`TauCeti.AlgebraicGeometry.EllObj.yOne`), and the bijection is the field-valued
form of its universal property; the comparison with the scheme is not made here.

## Main definitions

* `TauCeti.PointedWeierstrassCurve.tateNormalForm a hb`: the Tate normal form
  `Y² + aXY + bY = X³ + bX²` with the point `(0, 0)`, for `b ≠ 0`.
* `TauCeti.PointedWeierstrassCurve.tateNormalFormCoeffs`: the coefficients `(a, b)` of the Tate
  normal form of a pointed curve.
* `TauCeti.PointedWeierstrassCurve.tateNormalFormExactOrder F N`: the pairs `(a, b)` whose Tate
  normal form is elliptic with `(0, 0)` of exact order `N`.
* `TauCeti.PointedWeierstrassCurve.exactOrderQuotientEquivTateNormalForm`: for `N ≥ 4`, the
  bijection from the isomorphism classes of elliptic curves with a point of exact order `N` to
  these pairs.

## Main results

* `TauCeti.PointedWeierstrassCurve.exists_smul_eq_tateNormalForm`: a pointed curve with
  `2 • P ≠ 0` and `3 • P ≠ 0` is isomorphic to the Tate normal form with its coefficients.
* `TauCeti.PointedWeierstrassCurve.exists_smul_tateNormalForm_eq_iff`: two pointed Tate normal forms
  are isomorphic exactly when their coefficients agree.
* `TauCeti.PointedWeierstrassCurve.tateNormalFormCoeffs_smul`: the coefficients are invariant under
  changes of variables.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], Exercise 8.13.
* D. S. Kubert, *Universal bounds on the torsion of elliptic curves*, Proc. London Math. Soc. (3)
  33 (1976), 193–237.
-/

public section

namespace TauCeti

open WeierstrassCurve.Affine.Point

namespace PointedWeierstrassCurve

section Field

variable {F : Type*} [Field F]

/-- The **pointed Tate normal form**: the curve `Y² + aXY + bY = X³ + bX²` with the point
`(0, 0)`, which is nonsingular since `b ≠ 0`. -/
noncomputable def tateNormalForm (a : F) {b : F} (hb : b ≠ 0) : PointedWeierstrassCurve F :=
  ⟨WeierstrassCurve.tateNormalForm a b,
    .some 0 0 (WeierstrassCurve.nonsingular_tateNormalForm_zero a hb)⟩

@[simp]
theorem tateNormalForm_curve (a : F) {b : F} (hb : b ≠ 0) :
    (tateNormalForm a hb).curve = WeierstrassCurve.tateNormalForm a b :=
  (rfl)

/-- The **coefficients of the Tate normal form** of a pointed curve `(W, (x, y))`:
`a = Ψ₃(x) ψ₂(x, y)⁻³ (a₁ + 2 s)` and `b = Ψ₃(x)³ ψ₂(x, y)⁻⁸`, where
`s = (a₄ + 2 a₂ x - a₁ y + 3 x²) / ψ₂(x, y)`. When `2 • P ≠ 0` and `3 • P ≠ 0` the pointed curve is
isomorphic to the Tate normal form with these coefficients
(`PointedWeierstrassCurve.exists_smul_eq_tateNormalForm`). The value `(0, 0)` at the point at
infinity carries no meaning. -/
noncomputable def tateNormalFormCoeffs : PointedWeierstrassCurve F → F × F
  | ⟨W, .some x y _⟩ =>
    (W.Ψ₃.eval x * (W.ψ₂.evalEval x y)⁻¹ ^ 3 *
        (W.a₁ + 2 * ((W.a₄ + 2 * x * W.a₂ - y * W.a₁ + 3 * x ^ 2) * (W.ψ₂.evalEval x y)⁻¹)),
      W.Ψ₃.eval x ^ 3 * (W.ψ₂.evalEval x y)⁻¹ ^ 8)
  | ⟨_, .zero⟩ => (0, 0)

@[simp]
theorem tateNormalFormCoeffs_mk_some {W : WeierstrassCurve F} {x y : F}
    (h : W.toAffine.Nonsingular x y) :
    tateNormalFormCoeffs ⟨W, .some x y h⟩ =
      (W.Ψ₃.eval x * (W.ψ₂.evalEval x y)⁻¹ ^ 3 *
          (W.a₁ + 2 * ((W.a₄ + 2 * x * W.a₂ - y * W.a₁ + 3 * x ^ 2) * (W.ψ₂.evalEval x y)⁻¹)),
        W.Ψ₃.eval x ^ 3 * (W.ψ₂.evalEval x y)⁻¹ ^ 8) :=
  (rfl)

/-- The coefficients of a pointed Tate normal form are its own coefficients `(a, b)`. -/
@[simp]
theorem tateNormalFormCoeffs_tateNormalForm (a : F) {b : F} (hb : b ≠ 0) :
    (tateNormalForm a hb).tateNormalFormCoeffs = (a, b) := by
  rw [tateNormalForm, tateNormalFormCoeffs_mk_some,
    WeierstrassCurve.eval_Ψ₃_tateNormalForm_zero, WeierstrassCurve.evalEval_ψ₂_tateNormalForm_zero]
  simp only [WeierstrassCurve.tateNormalForm_a₁, WeierstrassCurve.tateNormalForm_a₂,
    WeierstrassCurve.tateNormalForm_a₄, Prod.mk.injEq]
  constructor
  · field_simp
    ring
  · field_simp

/-- **Pointed Tate normal forms are rigid.** Two pointed Tate normal forms are isomorphic exactly
when their coefficients agree: a change of variables between them fixes `(0, 0)`, so it is the
change of variables to Tate normal form, which is the identity. -/
theorem exists_smul_tateNormalForm_eq_iff {a a' b b' : F} (hb : b ≠ 0) (hb' : b' ≠ 0) :
    (∃ C : WeierstrassCurve.VariableChange F, C • tateNormalForm a hb = tateNormalForm a' hb') ↔
      a = a' ∧ b = b' := by
  refine ⟨fun ⟨C, hC⟩ ↦ ?_, fun ⟨ha, hbb⟩ ↦ ⟨1, by subst ha hbb; exact one_smul _ _⟩⟩
  rw [tateNormalForm, tateNormalForm, smul_mk_some_eq_mk_some_iff] at hC
  obtain ⟨hC, hr, ht⟩ := hC
  simp only [mul_zero, zero_add] at hr ht
  have hψ₂ : IsUnit ((WeierstrassCurve.tateNormalForm a b).ψ₂.evalEval 0 0) := by
    simpa using hb.isUnit
  have hΨ₃ : IsUnit ((WeierstrassCurve.tateNormalForm a b).Ψ₃.eval 0) := by
    simpa using (hb.isUnit.pow 3)
  -- both `C` and the identity are the change of variables to Tate normal form at `(0, 0)`
  have h₁ : C = 1 :=
    (WeierstrassCurve.eq_toTateNormalForm hψ₂ hΨ₃ hr ht hC).trans
      (WeierstrassCurve.eq_toTateNormalForm hψ₂ hΨ₃ rfl rfl (one_smul _ _)).symm
  rw [h₁, one_smul] at hC
  exact ⟨by simpa using congrArg WeierstrassCurve.a₁ hC,
    by simpa using congrArg WeierstrassCurve.a₂ hC⟩

variable [DecidableEq F]

/-- **Every pointed curve with `2 • P ≠ 0` and `3 • P ≠ 0` has a Tate normal form**: it is
isomorphic to the pointed Tate normal form with the coefficients
`PointedWeierstrassCurve.tateNormalFormCoeffs`, whose second coefficient is nonzero. -/
theorem exists_smul_eq_tateNormalForm (X : PointedWeierstrassCurve F) (h₂ : 2 • X.point ≠ 0)
    (h₃ : 3 • X.point ≠ 0) :
    ∃ (hb : X.tateNormalFormCoeffs.2 ≠ 0) (C : WeierstrassCurve.VariableChange F),
      C • X = tateNormalForm X.tateNormalFormCoeffs.1 hb := by
  obtain ⟨W, _ | ⟨x, y, h⟩⟩ := X
  · exact absurd (nsmul_zero 2) h₂
  -- `2 • P ≠ 0` and `3 • P ≠ 0` say that `ψ₂` and `Ψ₃` do not vanish at `P`
  have hψ₂ : W.ψ₂.evalEval x y ≠ 0 := by
    rwa [Ne, WeierstrassCurve.ψ₂, ← some_add_self_eq_zero_iff h, ← two_nsmul]
  have hΨ₃ : W.Ψ₃.eval x ≠ 0 := by
    rwa [Ne, ← pow_eq_zero_iff two_ne_zero, ← Polynomial.eval_pow, ← WeierstrassCurve.ΨSq_three,
      WeierstrassCurve.eval_ΨSq_eq_zero_iff_zsmul_eq_zero W h,
      show (3 : ℤ) = ((3 : ℕ) : ℤ) from rfl, WeierstrassCurve.zsmul_fromAffine_eq_zero_iff]
  refine ⟨by simp [hψ₂, hΨ₃], WeierstrassCurve.toTateNormalForm hψ₂.isUnit hΨ₃.isUnit, ?_⟩
  rw [tateNormalForm, smul_mk_some_eq_mk_some_iff,
    WeierstrassCurve.toTateNormalForm_smul hψ₂.isUnit hΨ₃.isUnit h.1]
  simp [Units.val_inv_eq_inv_val]

/-- **The coefficients of the Tate normal form are isomorphism invariants**: a change of variables
does not change them, for a pointed curve with `2 • P ≠ 0` and `3 • P ≠ 0`. -/
theorem tateNormalFormCoeffs_smul (C : WeierstrassCurve.VariableChange F)
    (X : PointedWeierstrassCurve F) (h₂ : 2 • X.point ≠ 0) (h₃ : 3 • X.point ≠ 0) :
    (C • X).tateNormalFormCoeffs = X.tateNormalFormCoeffs := by
  obtain ⟨hb, C₁, hC₁⟩ := exists_smul_eq_tateNormalForm X h₂ h₃
  obtain ⟨hb', C₂, hC₂⟩ := exists_smul_eq_tateNormalForm (C • X)
    ((nsmul_smul_point_eq_zero_iff C X 2).not.mpr h₂)
    ((nsmul_smul_point_eq_zero_iff C X 3).not.mpr h₃)
  have h := (exists_smul_tateNormalForm_eq_iff hb' hb).mp
    ⟨C₁ * C⁻¹ * C₂⁻¹, by rw [← hC₂, mul_smul, mul_smul, inv_smul_smul, inv_smul_smul, hC₁]⟩
  exact Prod.ext h.1 h.2

variable (F) in
/-- The pairs `(a, b)` for which the Tate normal form `Y² + aXY + bY = X³ + bX²` is an elliptic
curve on which `(0, 0)` has exact order `N`. -/
def tateNormalFormExactOrder (N : ℕ) : Set (F × F) :=
  {p | ∃ hb : p.2 ≠ 0, tateNormalForm p.1 hb ∈ exactOrder F N}

theorem mem_tateNormalFormExactOrder_iff {N : ℕ} {p : F × F} :
    p ∈ tateNormalFormExactOrder F N ↔ ∃ hb : p.2 ≠ 0, tateNormalForm p.1 hb ∈ exactOrder F N :=
  Iff.rfl

/-- For `N ≥ 4`, a point of exact order `N` is killed neither by `2` nor by `3`. -/
private theorem nsmul_point_ne_zero_of_mem_exactOrder {N : ℕ} (hN : 4 ≤ N)
    {X : PointedWeierstrassCurve F} (hX : X ∈ exactOrder F N) {n : ℕ} (hn₀ : n ≠ 0)
    (hn : n < 4) : n • X.point ≠ 0 := by
  rw [Ne, ← addOrderOf_dvd_iff_nsmul_eq_zero, ((mem_exactOrder_iff X).mp hX).2]
  exact fun h ↦ by have := Nat.le_of_dvd (Nat.pos_of_ne_zero hn₀) h; omega

/-- For `N ≥ 4`, the coefficients of the Tate normal form of an elliptic curve with a point of
exact order `N` lie in `tateNormalFormExactOrder F N`. -/
theorem tateNormalFormCoeffs_mem_tateNormalFormExactOrder {N : ℕ} (hN : 4 ≤ N)
    {X : PointedWeierstrassCurve F} (hX : X ∈ exactOrder F N) :
    X.tateNormalFormCoeffs ∈ tateNormalFormExactOrder F N := by
  obtain ⟨hb, C, hC⟩ := exists_smul_eq_tateNormalForm X
    (nsmul_point_ne_zero_of_mem_exactOrder hN hX two_ne_zero (by norm_num))
    (nsmul_point_ne_zero_of_mem_exactOrder hN hX three_ne_zero (by norm_num))
  exact ⟨hb, hC ▸ (exactOrder F N).smul_mem C hX⟩

variable (F) in
/-- **Tate normal form classifies points of order `N ≥ 4`.** For `N ≥ 4`, the coefficients of the
Tate normal form give a bijection from the isomorphism classes of elliptic curves over `F` with a
point of exact order `N` to the pairs `(a, b)` for which `Y² + aXY + bY = X³ + bX²` is elliptic and
`(0, 0)` has exact order `N`. -/
noncomputable def exactOrderQuotientEquivTateNormalForm {N : ℕ} (hN : 4 ≤ N) :
    MulAction.orbitRel.Quotient (WeierstrassCurve.VariableChange F) (exactOrder F N) ≃
      tateNormalFormExactOrder F N where
  toFun := Quotient.lift
    (fun X ↦ ⟨X.1.tateNormalFormCoeffs, tateNormalFormCoeffs_mem_tateNormalFormExactOrder hN X.2⟩)
    fun X Y h ↦ by
      obtain ⟨C, hC⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp h)
      refine Subtype.ext ?_
      dsimp only
      rw [← hC, SubMulAction.val_smul, tateNormalFormCoeffs_smul _ _
        (nsmul_point_ne_zero_of_mem_exactOrder hN Y.2 two_ne_zero (by norm_num))
        (nsmul_point_ne_zero_of_mem_exactOrder hN Y.2 three_ne_zero (by norm_num))]
  invFun p := ⟦⟨tateNormalForm p.1.1 p.2.1, p.2.2⟩⟧
  left_inv q := Quotient.inductionOn q fun X ↦ by
    obtain ⟨hb, C, hC⟩ := exists_smul_eq_tateNormalForm X.1
      (nsmul_point_ne_zero_of_mem_exactOrder hN X.2 two_ne_zero (by norm_num))
      (nsmul_point_ne_zero_of_mem_exactOrder hN X.2 three_ne_zero (by norm_num))
    exact Quotient.sound (MulAction.orbitRel_apply.mpr
      (MulAction.mem_orbit_iff.mpr ⟨C, Subtype.ext (by rw [SubMulAction.val_smul]; exact hC)⟩))
  right_inv p := Subtype.ext (tateNormalFormCoeffs_tateNormalForm p.1.1 p.2.1)

@[simp]
theorem exactOrderQuotientEquivTateNormalForm_mk {N : ℕ} (hN : 4 ≤ N) (X : exactOrder F N) :
    (exactOrderQuotientEquivTateNormalForm F hN ⟦X⟧ : F × F) = X.1.tateNormalFormCoeffs :=
  (rfl)

end Field

end PointedWeierstrassCurve

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Pointed.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.TateNormalForm
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
scheme `Y₁(N)` (`TauCeti.AlgebraicGeometry.UniversalTate.yOne`), and the bijection is the
field-valued form of its universal property; the comparison with the scheme is not made here.

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
* `TauCeti.PointedWeierstrassCurve.existsUnique_smul_eq_tateNormalForm`: the change of variables
  to the Tate normal form is unique.
* `TauCeti.PointedWeierstrassCurve.smul_tateNormalForm_eq_iff`: the only change of variables between
  two pointed Tate normal forms is the identity, between equal ones.
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

namespace PointedWeierstrassCurve

section CommRing

variable {R : Type*} [CommRing R]

/-- The **pointed Tate normal form**: the curve `Y² + aXY + bY = X³ + bX²` with the point
`(0, 0)`, which is nonsingular since `b ≠ 0`. -/
noncomputable def tateNormalForm (a : R) {b : R} (hb : b ≠ 0) : PointedWeierstrassCurve R :=
  ⟨WeierstrassCurve.tateNormalForm a b,
    .some 0 0 (WeierstrassCurve.nonsingular_tateNormalForm_zero a hb)⟩

theorem tateNormalForm_def (a : R) {b : R} (hb : b ≠ 0) :
    tateNormalForm a hb = ⟨WeierstrassCurve.tateNormalForm a b,
      .some 0 0 (WeierstrassCurve.nonsingular_tateNormalForm_zero a hb)⟩ :=
  (rfl)

@[simp]
theorem tateNormalForm_curve (a : R) {b : R} (hb : b ≠ 0) :
    (tateNormalForm a hb).curve = WeierstrassCurve.tateNormalForm a b :=
  (rfl)

/-- Pointed Tate normal forms are equal exactly when their coefficients are. -/
@[simp]
theorem tateNormalForm_inj {a a' b b' : R} (hb : b ≠ 0) (hb' : b' ≠ 0) :
    tateNormalForm a hb = tateNormalForm a' hb' ↔ a = a' ∧ b = b' := by
  refine ⟨fun h ↦ ?_, fun ⟨ha, hbb⟩ ↦ by subst ha hbb; rfl⟩
  have h := congrArg PointedWeierstrassCurve.curve h
  exact ⟨by simpa using congrArg WeierstrassCurve.a₁ h,
    by simpa using congrArg WeierstrassCurve.a₂ h⟩

end CommRing

section Field

variable {F : Type*} [Field F]

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

@[simp]
theorem tateNormalFormCoeffs_mk_zero (W : WeierstrassCurve F) :
    tateNormalFormCoeffs ⟨W, 0⟩ = (0, 0) :=
  (rfl)

/-- The coefficients of a pointed Tate normal form are its own coefficients `(a, b)`. -/
@[simp]
theorem tateNormalFormCoeffs_tateNormalForm (a : F) {b : F} (hb : b ≠ 0) :
    (tateNormalForm a hb).tateNormalFormCoeffs = (a, b) := by
  rw [tateNormalForm_def, tateNormalFormCoeffs_mk_some,
    WeierstrassCurve.eval_Ψ₃_tateNormalForm_zero, WeierstrassCurve.evalEval_ψ₂_tateNormalForm_zero]
  simp only [WeierstrassCurve.tateNormalForm_a₁, WeierstrassCurve.tateNormalForm_a₂,
    WeierstrassCurve.tateNormalForm_a₄, Prod.mk.injEq]
  constructor
  · field_simp
    ring
  · field_simp

/-- **Rigidity of the pointed Tate normal form**: the only change of variables between two pointed
Tate normal forms is the identity, and it relates them only when their coefficients agree. -/
@[simp]
theorem smul_tateNormalForm_eq_iff {C : WeierstrassCurve.VariableChange F} {a a' b b' : F}
    (hb : b ≠ 0) (hb' : b' ≠ 0) :
    C • tateNormalForm a hb = tateNormalForm a' hb' ↔ C = 1 ∧ a = a' ∧ b = b' := by
  refine ⟨fun hC ↦ ?_, fun ⟨hC, ha, hbb⟩ ↦ by subst hC ha hbb; exact one_smul _ _⟩
  have hC' := hC
  rw [tateNormalForm_def, tateNormalForm_def, smul_mk_some_eq_mk_some_iff] at hC'
  obtain ⟨hC', hr, ht⟩ := hC'
  simp only [mul_zero, zero_add] at hr ht
  have hψ₂ : IsUnit ((WeierstrassCurve.tateNormalForm a b).ψ₂.evalEval 0 0) := by
    simpa using hb.isUnit
  have hΨ₃ : IsUnit ((WeierstrassCurve.tateNormalForm a b).Ψ₃.eval 0) := by
    simpa using (hb.isUnit.pow 3)
  -- both `C` and the identity are the change of variables to Tate normal form at `(0, 0)`
  have h₁ : C = 1 :=
    (WeierstrassCurve.eq_toTateNormalForm hψ₂ hΨ₃ hr ht hC').trans
      (WeierstrassCurve.eq_toTateNormalForm hψ₂ hΨ₃ rfl rfl (one_smul _ _)).symm
  rw [h₁, one_smul, tateNormalForm_inj] at hC
  exact ⟨h₁, hC⟩

/-- Two pointed Tate normal forms are isomorphic exactly when their coefficients agree. -/
theorem exists_smul_tateNormalForm_eq_iff {a a' b b' : F} (hb : b ≠ 0) (hb' : b' ≠ 0) :
    (∃ C : WeierstrassCurve.VariableChange F, C • tateNormalForm a hb = tateNormalForm a' hb') ↔
      a = a' ∧ b = b' := by
  simp

/-- The coefficients vanish when the marked point is killed by `2` or by `3`. -/
private theorem tateNormalFormCoeffs_eq_zero [DecidableEq F] {X : PointedWeierstrassCurve F}
    (h : 2 • X.point = 0 ∨ 3 • X.point = 0) : X.tateNormalFormCoeffs = (0, 0) := by
  obtain ⟨W, _ | ⟨x, y, hxy⟩⟩ := X
  · rfl
  rcases h with h | h
  · simp [(WeierstrassCurve.evalEval_ψ₂_eq_zero_iff_nsmul_eq_zero W hxy).mpr h]
  · simp [(WeierstrassCurve.eval_Ψ₃_eq_zero_iff_nsmul_eq_zero W hxy).mpr h]

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
  have hψ₂ : W.ψ₂.evalEval x y ≠ 0 :=
    (WeierstrassCurve.evalEval_ψ₂_eq_zero_iff_nsmul_eq_zero W h).not.mpr h₂
  have hΨ₃ : W.Ψ₃.eval x ≠ 0 := (WeierstrassCurve.eval_Ψ₃_eq_zero_iff_nsmul_eq_zero W h).not.mpr h₃
  refine ⟨by simp [hψ₂, hΨ₃], WeierstrassCurve.toTateNormalForm hψ₂.isUnit hΨ₃.isUnit, ?_⟩
  rw [tateNormalForm_def, smul_mk_some_eq_mk_some_iff,
    WeierstrassCurve.toTateNormalForm_smul hψ₂.isUnit hΨ₃.isUnit h.1]
  simp [Units.val_inv_eq_inv_val]

/-- **The change of variables to Tate normal form is unique**: for a pointed curve with
`2 • P ≠ 0` and `3 • P ≠ 0`, exactly one change of variables carries it to its Tate normal form. -/
theorem existsUnique_smul_eq_tateNormalForm (X : PointedWeierstrassCurve F)
    (h₂ : 2 • X.point ≠ 0) (h₃ : 3 • X.point ≠ 0) :
    ∃ hb : X.tateNormalFormCoeffs.2 ≠ 0, ∃! C : WeierstrassCurve.VariableChange F,
      C • X = tateNormalForm X.tateNormalFormCoeffs.1 hb := by
  obtain ⟨hb, C, hC⟩ := exists_smul_eq_tateNormalForm X h₂ h₃
  refine ⟨hb, C, hC, fun C' hC' ↦ ?_⟩
  have h : (C' * C⁻¹) • (C • X) = C' • X := by rw [mul_smul, inv_smul_smul]
  rw [hC, hC'] at h
  exact mul_inv_eq_one.mp ((smul_tateNormalForm_eq_iff hb hb).mp h).1

omit [DecidableEq F] in
/-- **The coefficients of the Tate normal form are isomorphism invariants**: a change of variables
does not change them. -/
@[simp]
theorem tateNormalFormCoeffs_smul (C : WeierstrassCurve.VariableChange F)
    (X : PointedWeierstrassCurve F) : (C • X).tateNormalFormCoeffs = X.tateNormalFormCoeffs := by
  classical
  by_cases h : 2 • X.point = 0 ∨ 3 • X.point = 0
  · rw [tateNormalFormCoeffs_eq_zero h,
      tateNormalFormCoeffs_eq_zero (by simpa only [nsmul_smul_point_eq_zero_iff] using h)]
  rw [not_or] at h
  obtain ⟨hb, C₁, hC₁⟩ := exists_smul_eq_tateNormalForm X h.1 h.2
  obtain ⟨hb', C₂, hC₂⟩ := exists_smul_eq_tateNormalForm (C • X)
    ((nsmul_smul_point_eq_zero_iff C X 2).not.mpr h.1)
    ((nsmul_smul_point_eq_zero_iff C X 3).not.mpr h.2)
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
    (hn : n < 4) : n • X.point ≠ 0 :=
  nsmul_ne_zero_of_lt_addOrderOf hn₀ (((mem_exactOrder_iff X).mp hX).2 ▸ hn.trans_le hN)

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
    (fun X ↦ ⟨X.val.tateNormalFormCoeffs, tateNormalFormCoeffs_mem_tateNormalFormExactOrder hN
        X.property⟩)
    fun X Y h ↦ by
      obtain ⟨C, hC⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp h)
      refine Subtype.ext ?_
      dsimp only
      rw [← hC, SubMulAction.val_smul, tateNormalFormCoeffs_smul]
  invFun p := ⟦⟨tateNormalForm p.val.1 p.property.1, p.property.2⟩⟧
  left_inv q := Quotient.inductionOn q fun X ↦ by
    obtain ⟨hb, C, hC⟩ := exists_smul_eq_tateNormalForm X.val
      (nsmul_point_ne_zero_of_mem_exactOrder hN X.property two_ne_zero (by norm_num))
      (nsmul_point_ne_zero_of_mem_exactOrder hN X.property three_ne_zero (by norm_num))
    exact Quotient.sound (MulAction.orbitRel_apply.mpr
      (MulAction.mem_orbit_iff.mpr ⟨C, Subtype.ext (by rw [SubMulAction.val_smul]; exact hC)⟩))
  right_inv p := Subtype.ext (tateNormalFormCoeffs_tateNormalForm p.val.1 p.property.1)

@[simp]
theorem coe_exactOrderQuotientEquivTateNormalForm_mk {N : ℕ} (hN : 4 ≤ N) (X : exactOrder F N) :
    (exactOrderQuotientEquivTateNormalForm F hN ⟦X⟧ : F × F) = X.val.tateNormalFormCoeffs :=
  (rfl)

@[simp]
theorem exactOrderQuotientEquivTateNormalForm_symm_apply {N : ℕ} (hN : 4 ≤ N)
    (p : tateNormalFormExactOrder F N) :
    (exactOrderQuotientEquivTateNormalForm F hN).symm p =
      ⟦⟨tateNormalForm p.val.1 (mem_tateNormalFormExactOrder_iff.mp p.property).1,
        (mem_tateNormalFormExactOrder_iff.mp p.property).2⟩⟧ :=
  (rfl)

end Field

end PointedWeierstrassCurve

end TauCeti

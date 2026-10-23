/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.AlgebraicGeometry.EllipticCurve.Jacobian.Point
public import Mathlib.Algebra.Module.Torsion.Basic
-- Proof-only: a vanishing `ψₙ` annihilates the point, and conversely.
import TauCeti.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.ZSMul
-- Proof-only: over an algebraically closed field every `x` is the abscissa of a point.
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.IsAlgClosed

/-!
# The roots of `ΨSqₙ` are the abscissae of the nonzero `n`-torsion

`ΨSqₙ` is the square of the `n`-division polynomial, pushed down to a polynomial in `x` alone. Its
roots are exactly the `x`-coordinates of the affine points killed by `n`: one direction holds over
any field, the other needs the base field algebraically closed, so that the `y` completing a root
to a point exists.

This is the dictionary the `n`-torsion is counted through — the kernel of `[n]` maps to the roots
of `ΨSqₙ` two-to-one away from the `2`-torsion, which is what matches `#ker [n] = n ²` against
`deg preΨₙ`.

## Main results

* `WeierstrassCurve.eval_ΨSq_eq_zero_iff_exists_zsmul_eq_zero`: over an algebraically closed
  field, the roots of `ΨSqₙ` are exactly the abscissae of the `n`-torsion points. The pointwise
  form, for a supplied `y`, is `eval_ΨSq_eq_zero_iff_zsmul_eq_zero` in
  `DivisionPolynomial/ZSMul.lean`; only the existence of `y` needs the closure assumption.
* `WeierstrassCurve.torsionBy_eq_bot_iff_forall_eval_ΨSq_ne_zero`: over an algebraically closed
  field, the `n`-torsion subgroup is trivial exactly when `ΨSqₙ` has no root.
* `WeierstrassCurve.torsionBy_two_eq_bot_iff_of_char_two` and
  `WeierstrassCurve.torsionBy_three_eq_bot_iff_of_char_three`: over an algebraically closed field
  of characteristic `2`, respectively `3`, the `2`-torsion is trivial exactly when `a₁ = 0`, and
  the `3`-torsion exactly when `b₂ = 0`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.6.4(b).
-/

public section

open Polynomial

namespace WeierstrassCurve

variable {F : Type*} [Field F] (W : WeierstrassCurve F)

/-- **Over an algebraically closed field the roots of `ΨSqₙ` are exactly the abscissae of the
`n`-torsion points.** Solving the Weierstrass equation for `y` gives a point over a root, and
`ΨSqₙ(x) = 0` makes `ψₙ` vanish there, which annihilates it; the converse needs no closure, since
the `y` is supplied. -/
theorem eval_ΨSq_eq_zero_iff_exists_zsmul_eq_zero [IsAlgClosed F] [W.IsElliptic] {n : ℤ} {x : F} :
    (W.ΨSq n).eval x = 0 ↔ ∃ y, ∃ hns : W.toAffine.Nonsingular x y,
      n • Jacobian.Point.fromAffine (Affine.Point.some _ _ hns) = 0 := by
  refine ⟨fun hx ↦ ?_, fun ⟨_, hns, h⟩ ↦ (eval_ΨSq_eq_zero_iff_zsmul_eq_zero W hns n).mpr h⟩
  obtain ⟨y, hy⟩ := W.toAffine.exists_point_on_curve x
  have hns : W.toAffine.Nonsingular x y := Affine.equation_iff_nonsingular.mp hy
  exact ⟨y, hns, (eval_ΨSq_eq_zero_iff_zsmul_eq_zero W hns n).mp hx⟩

/-- **Over an algebraically closed field the `n`-torsion is trivial exactly when `ΨSqₙ` has no
root**: a root is the abscissa of a nonzero affine `n`-torsion point, and the point at infinity is
the only point with no abscissa. -/
theorem torsionBy_eq_bot_iff_forall_eval_ΨSq_ne_zero [IsAlgClosed F] [W.IsElliptic] [DecidableEq F]
    {n : ℤ} : AddSubgroup.torsionBy W.toAffine.Point n = ⊥ ↔ ∀ x, (W.ΨSq n).eval x ≠ 0 := by
  simp only [AddSubgroup.eq_bot_iff_forall, Submodule.mem_toAddSubgroup,
    Submodule.mem_torsionBy_iff]
  refine ⟨fun h x hx ↦ ?_, ?_⟩
  · obtain ⟨y, hns, htors⟩ := W.eval_ΨSq_eq_zero_iff_exists_zsmul_eq_zero.mp hx
    exact Affine.Point.some_ne_zero hns (h _ (zsmul_fromAffine_eq_zero_iff_zsmul_eq_zero.mp htors))
  · rintro h (_ | ⟨x, y, hns⟩) hP
    · rfl
    · exact absurd ((eval_ΨSq_eq_zero_iff_zsmul_eq_zero W hns n).mpr
        (zsmul_fromAffine_eq_zero_iff_zsmul_eq_zero.mpr hP)) (h x)

/-! ### Characteristic two and three -/

/-- In characteristic `2` the `2`-torsion of an elliptic curve over an algebraically closed field
is trivial exactly when `a₁ = 0`: then `ΨSq₂ = a₃²` is a nonzero constant, and otherwise
`x = a₃ / a₁` is a root of `ΨSq₂ = a₁² x² + a₃²`. -/
theorem torsionBy_two_eq_bot_iff_of_char_two [IsAlgClosed F] [W.IsElliptic] [DecidableEq F]
    [CharP F 2] :
    AddSubgroup.torsionBy W.toAffine.Point 2 = ⊥ ↔ W.a₁ = 0 := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have heval (x : F) : (W.ΨSq 2).eval x = W.a₁ ^ 2 * x ^ 2 + W.a₃ ^ 2 := by
    rw [ΨSq_two, Ψ₂Sq, ← b₂_of_char_two, ← b₆_of_char_two]
    simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X]
    linear_combination (2 * x ^ 3 + W.b₄ * x) * h2
  rw [torsionBy_eq_bot_iff_forall_eval_ΨSq_ne_zero]
  simp only [heval]
  refine ⟨fun h ↦ by_contra fun ha ↦ h (W.a₃ / W.a₁) ?_, fun ha x ↦ ?_⟩
  · field_simp
    linear_combination W.a₃ ^ 2 * h2
  · have hΔ := W.isUnit_Δ.ne_zero
    rw [Δ_of_char_two, ha] at hΔ
    simpa [ha] using hΔ

/-- In characteristic `3` the `3`-torsion of an elliptic curve over an algebraically closed field
is trivial exactly when `b₂ = 0`: there `ψ₃ = b₂ x³ + b₈`, whose constant term `b₈` cannot vanish
together with `b₂`, and which has a root as soon as `b₂ ≠ 0`. -/
theorem torsionBy_three_eq_bot_iff_of_char_three [IsAlgClosed F] [W.IsElliptic] [DecidableEq F]
    [CharP F 3] :
    AddSubgroup.torsionBy W.toAffine.Point 3 = ⊥ ↔ W.b₂ = 0 := by
  have h3 : (3 : F) = 0 := CharP.cast_eq_zero F 3
  have heval (x : F) : (W.ΨSq 3).eval x = (W.b₂ * x ^ 3 + W.b₈) ^ 2 := by
    rw [ΨSq_three, Ψ₃]
    simp only [eval_pow, eval_add, eval_mul, eval_C, eval_X, eval_ofNat]
    linear_combination (x ^ 4 + W.b₄ * x ^ 2 + W.b₆ * x) *
      (3 * x ^ 4 + 2 * W.b₂ * x ^ 3 + 3 * W.b₄ * x ^ 2 + 3 * W.b₆ * x + 2 * W.b₈) * h3
  rw [torsionBy_eq_bot_iff_forall_eval_ΨSq_ne_zero]
  simp only [heval, ne_eq, pow_eq_zero_iff two_ne_zero]
  refine ⟨fun h ↦ by_contra fun hb ↦ ?_, fun hb x hx ↦ ?_⟩
  · obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (-W.b₈ / W.b₂) three_pos
    exact h z (by rw [hz]; field_simp; ring)
  · rw [hb, zero_mul, zero_add] at hx
    have hb₄ : W.b₄ = 0 := by
      have := W.b_relation_of_char_three
      rw [hx, hb, zero_mul, zero_sub, zero_eq_neg] at this
      exact pow_eq_zero_iff two_ne_zero |>.mp this
    exact W.isUnit_Δ.ne_zero (by rw [Δ_of_char_three, hb, hb₄]; ring)

end WeierstrassCurve

end

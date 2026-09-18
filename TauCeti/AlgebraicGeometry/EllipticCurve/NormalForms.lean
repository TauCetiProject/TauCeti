/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms

/-!
# Normal forms: transport, changes of variables, and elementary consequences

Mathlib's `WeierstrassCurve.IsCharNeTwoNF` asserts `a₁ = a₃ = 0` and its
`WeierstrassCurve.IsShortNF` asserts `a₁ = a₂ = a₃ = 0`, and its `NormalForms` file proves a
great deal from those hypotheses. This file collects three things it does not record.

**Transport.** Both conditions are preserved by `map` and `baseChange` — the coefficients of
`W.map f` are the images of `W`'s, so a vanishing coefficient stays vanishing.

**Changes of variables between short normal forms.** When `2` and `3` are non-zero-divisors, a
change of variables carrying one short equation to another is a pure scaling
`(x, y) ↦ (u²x, u³y)`: its `r`, `s` and `t` vanish, so it acts on the coefficients by
`(a₄, a₆) ↦ (u⁻⁴a₄, u⁻⁶a₆)`. This is the only freedom left in a short equation, and it is what a
canonical short equation has to normalise away.

**Elementary consequences.** Facts that follow from `a₁ = a₃ = 0` alone, by unfolding `negY`, with
no further machinery. `y_eq_zero_of_order_two` is the current example: negation is `(x, y) ↦
(x, -y)`, so a `2`-torsion point has `y = 0`. It lives here rather than with the division-polynomial
material that first proved it because it needs none of that — this module's closure is one file,
against thirty-three for `DivisionPolynomial/ShortNagellLutz.lean` — and its consumers, Nagell–Lutz
and the `2`-descent torsion count, sit in unrelated parts of the library.

That gap matters as soon as a statement is about a curve over `ℤ` and a point over `ℚ`, which is
the shape of the classical Nagell–Lutz theorem: the hypothesis is natural on the integral model,
while the point lives on the base change, and without these instances the class has to be
re-established by hand at every such crossing.

## Main results

* `WeierstrassCurve.isCharNeTwoNF_map`: `a₁ = a₃ = 0` is preserved by a ring hom.
* `WeierstrassCurve.isCharNeTwoNF_baseChange`: the same for a base change, which is the spelling
  consumers hold. Both are instances, so the crossing is silent.
* `WeierstrassCurve.isShortNF_map` and `WeierstrassCurve.isShortNF_baseChange`: the same two
  statements for short normal form.
* `WeierstrassCurve.VariableChange.r_eq_zero_of_isShortNF`, `…s_eq_zero_of_isShortNF` and
  `…t_eq_zero_of_isShortNF`: a change of variables between short normal forms is a scaling.
* `WeierstrassCurve.variableChange_a₄_of_isShortNF` and
  `WeierstrassCurve.variableChange_a₆_of_isShortNF`: it acts on the coefficients by
  `(a₄, a₆) ↦ (u⁻⁴a₄, u⁻⁶a₆)`.
* `WeierstrassCurve.y_eq_zero_of_order_two`: in a characteristic-≠-2 normal form, an affine
  point killed by `2` has `y = 0`.
-/

public section

namespace WeierstrassCurve

variable {R S : Type*} [CommRing R] [CommRing S] (W : WeierstrassCurve R)

/-- **Characteristic-≠-2 normal form is preserved by a ring hom.** `(W.map f).a₁` is `f W.a₁`, and
a hom sends `0` to `0`, so the vanishing survives.

As an `instance`, this is what lets typeclass search carry `IsCharNeTwoNF` across `W.map f`: a
caller who has the hypothesis on `W` and a statement about `W.map f` needs no bridging term. -/
instance isCharNeTwoNF_map (f : R →+* S) [W.IsCharNeTwoNF] : (W.map f).IsCharNeTwoNF :=
  ⟨by simp, by simp⟩

/-- **Characteristic-≠-2 normal form is preserved by a base change.** This is
`isCharNeTwoNF_map` at `algebraMap R S`, stated separately because `baseChange` is the spelling a
caller holds and instance search does not unfold it. -/
instance isCharNeTwoNF_baseChange [Algebra R S] [W.IsCharNeTwoNF] :
    (W.baseChange S).IsCharNeTwoNF :=
  W.isCharNeTwoNF_map (algebraMap R S)

/-- **Short normal form is preserved by a ring hom.** `(W.map f).a₂` is `f W.a₂`, and a hom sends
`0` to `0`, so the vanishing survives; likewise for `a₁` and `a₃`. As an instance, it carries
`IsShortNF` across `W.map f` in typeclass search. -/
instance isShortNF_map (f : R →+* S) [W.IsShortNF] : (W.map f).IsShortNF :=
  ⟨by simp, by simp, by simp⟩

/-- **Short normal form is preserved by a base change.** This is `isShortNF_map` at
`algebraMap R S`, stated separately because `baseChange` is the spelling a caller holds and
instance search does not unfold it. -/
instance isShortNF_baseChange [Algebra R S] [W.IsShortNF] : (W.baseChange S).IsShortNF :=
  W.isShortNF_map (algebraMap R S)

/-! ### Changes of variables between short normal forms

The coefficients `a₁`, `a₃` and `a₂` of `C • W` are `u⁻¹ · 2s`, `u⁻³ · 2t` and `u⁻² · 3r` when `W`
is short, so if `C • W` is short as well and `2` and `3` are non-zero-divisors then
`r = s = t = 0`, and `C` is the scaling `(x, y) ↦ (u²x, u³y)`. -/

section ShortNF

variable (C : VariableChange R) [W.IsShortNF] [(C • W).IsShortNF]
include W

/-- A change of variables between short normal forms has `s = 0`, when `2` is a
non-zero-divisor. -/
lemma VariableChange.s_eq_zero_of_isShortNF (h2 : IsRegular (2 : R)) : C.s = 0 := by
  have h := (C • W).a₁_of_isShortNF
  rw [variableChange_a₁, W.a₁_of_isShortNF, C.u⁻¹.isUnit.mul_right_eq_zero] at h
  exact h2.left (by simp only [mul_zero]; linear_combination h)

/-- A change of variables between short normal forms has `t = 0`, when `2` is a
non-zero-divisor. -/
lemma VariableChange.t_eq_zero_of_isShortNF (h2 : IsRegular (2 : R)) : C.t = 0 := by
  have h := (C • W).a₃_of_isShortNF
  rw [variableChange_a₃, W.a₁_of_isShortNF, W.a₃_of_isShortNF,
    (C.u⁻¹.isUnit.pow 3).mul_right_eq_zero] at h
  exact h2.left (by simp only [mul_zero]; linear_combination h)

/-- A change of variables between short normal forms has `r = 0`, when `2` and `3` are
non-zero-divisors. -/
lemma VariableChange.r_eq_zero_of_isShortNF (h2 : IsRegular (2 : R)) (h3 : IsRegular (3 : R)) :
    C.r = 0 := by
  have h := (C • W).a₂_of_isShortNF
  rw [variableChange_a₂, W.a₁_of_isShortNF, W.a₂_of_isShortNF, C.s_eq_zero_of_isShortNF W h2,
    (C.u⁻¹.isUnit.pow 2).mul_right_eq_zero] at h
  exact h3.left (by simp only [mul_zero]; linear_combination h)

/-- Between short normal forms, a change of variables scales `a₄` by `u⁻⁴`, when `2` and `3` are
non-zero-divisors. -/
@[simp]
lemma variableChange_a₄_of_isShortNF (h2 : IsRegular (2 : R)) (h3 : IsRegular (3 : R)) :
    (C • W).a₄ = C.u⁻¹ ^ 4 * W.a₄ := by
  rw [variableChange_a₄, C.r_eq_zero_of_isShortNF W h2 h3, C.s_eq_zero_of_isShortNF W h2,
    C.t_eq_zero_of_isShortNF W h2, W.a₁_of_isShortNF, W.a₂_of_isShortNF, W.a₃_of_isShortNF]
  ring

/-- Between short normal forms, a change of variables scales `a₆` by `u⁻⁶`, when `2` and `3` are
non-zero-divisors. -/
@[simp]
lemma variableChange_a₆_of_isShortNF (h2 : IsRegular (2 : R)) (h3 : IsRegular (3 : R)) :
    (C • W).a₆ = C.u⁻¹ ^ 6 * W.a₆ := by
  rw [variableChange_a₆, C.r_eq_zero_of_isShortNF W h2 h3, C.t_eq_zero_of_isShortNF W h2,
    W.a₁_of_isShortNF, W.a₂_of_isShortNF, W.a₃_of_isShortNF]
  ring

end ShortNF

/-- **In characteristic-≠-2 normal form, a two-torsion point has `y = 0`.** Negation is
`(x, y) ↦ (x, -y)`, so a point equal to its own negative has `2y = 0`; cancelling `2` finishes it.

Nothing here sees `ℤ` or `ℚ`, and nothing needs `a₂ = 0`: the argument is the normal-form identity
plus the ability to cancel `2` in the point's own field, so those are exactly the hypotheses.

The hypothesis is annihilation by `2` rather than `addOrderOf P = 2`, which is what the proof and
every caller actually have. For an *affine* point the two are equivalent — `Point.some _ _ _` is
never `0` — so the name remains exact; the weaker form simply spares callers the reconstruction. -/
lemma y_eq_zero_of_order_two {F : Type*} [Field F] [DecidableEq F]
    {E : WeierstrassCurve F} [E.IsCharNeTwoNF] (h2F : (2 : F) ≠ 0)
    {x y : F} (hns : E.toAffine.Nonsingular x y)
    (h2 : (2 : ℕ) • (Affine.Point.some _ _ hns) = 0) : y = 0 := by
  rw [two_nsmul, add_eq_zero_iff_eq_neg, Affine.Point.neg_some, Affine.Point.some.injEq] at h2
  have hneg : E.toAffine.negY x y = -y := by
    simp [Affine.negY, a₁_of_isCharNeTwoNF, a₃_of_isCharNeTwoNF]
  have hy : 2 * y = 0 := by linear_combination h2.2.trans hneg
  exact (mul_eq_zero.mp hy).resolve_left h2F

end WeierstrassCurve

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
public import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass

/-!
# Complements on Weierstrass curves

Facts about the invariants of an elliptic curve, complementing
`Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass.lean`:

* `WeierstrassCurve.a₁_ne_zero_or_a₃_ne_zero_of_Δ_ne_zero_of_two_eq_zero`: where `2 = 0`, a curve
  with `Δ ≠ 0`
  has `a₁ ≠ 0` or `a₃ ≠ 0`;
* `WeierstrassCurve.Δ_eq_of_c₄_eq_of_c₆_eq`: two equations with the same `c`-invariants have the
  same discriminant, wherever `1728` is a regular element, by `WeierstrassCurve.c_relation`;
* `WeierstrassCurve.Δ_eq_of_a₃_eq_zero_of_a₄_eq_zero`: an equation with `a₃ = a₄ = 0` has
  `Δ = -a₆ (b₂³ + 432 a₆)`, the form in which a node at the origin is studied;
* `WeierstrassCurve.j_eq_1728_iff`: `j = 1728 ↔ c₆ = 0`, the analogue for `j = 1728` of Mathlib's
  `WeierstrassCurve.j_eq_zero_iff` (`j = 0 ↔ c₄ = 0`), together with its unreduced companion
  `WeierstrassCurve.j_eq_1728_iff'` mirroring `WeierstrassCurve.j_eq_zero_iff'`;
* `WeierstrassCurve.baseChange_c₄_ne_zero` and `WeierstrassCurve.baseChange_c₆_ne_zero`: the two
  corollaries of those criteria that say `j ≠ 0` and `j ≠ 1728` survive base change along an
  injection, in the `c₄`/`c₆` form the automorphism criterion consumes.
* `WeierstrassCurve.algebraMap_Δ_of_baseChange_eq`,
  `WeierstrassCurve.algebraMap_c₄_of_baseChange_eq` and
  `WeierstrassCurve.algebraMap_c₆_of_baseChange_eq`: the invariants of an equation known to be a
  base change are the images of the original invariants.
* `WeierstrassCurve.cusp`: the cusp curve `Y² = X³`, its coefficient projections, and the point
  `(1, 1)` on it (`WeierstrassCurve.equation_cusp_one_one`). It depends on nothing beyond a
  Weierstrass equation, and is the specialization target used to retract the universal ring onto
  `ℤ`.

All are stated over a commutative ring, matching the generality of the Mathlib results they
complement.

Adapted from the FLT project (`ImperialCollegeLondon/FLT`,
`FLT/Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass.lean` at commit `bc2fe8ff7396`
(FLT PR #1088), Apache 2.0, by Kevin Buzzard and Claude). Every result here except the cusp curve
and `WeierstrassCurve.Δ_eq_of_a₃_eq_zero_of_a₄_eq_zero` is adapted from that file, and all are
generalised from FLT's field-level statements to a commutative ring: the two `j`-criteria, and the
base-change pair `baseChange_c₄_ne_zero` / `baseChange_c₆_ne_zero`, which FLT states only for a
field extension.
-/

public section

namespace WeierstrassCurve

section Invariants

variable {R : Type*} [CommRing R]

/-- The discriminant is determined by the `c`-invariants, wherever `1728` can be cancelled:
`WeierstrassCurve.c_relation` pins `1728 * Δ` down to `c₄³ - c₆²`. -/
theorem Δ_eq_of_c₄_eq_of_c₆_eq (h1728 : IsRegular (1728 : R)) {W W' : WeierstrassCurve R}
    (h₄ : W.c₄ = W'.c₄) (h₆ : W.c₆ = W'.c₆) : W.Δ = W'.Δ := by
  have h : (1728 : R) * W.Δ = 1728 * W'.Δ := by rw [c_relation, c_relation, h₄, h₆]
  exact h1728.left h

/-- **The discriminant of an equation with `a₃ = a₄ = 0`** is `-a₆ (b₂³ + 432 a₆)`: here `b₄ = 0`,
`b₆ = 4 a₆` and `b₈ = b₂ a₆`. When the reduction is singular at the origin and `b₂` is a unit, the
second factor is a unit, so `a₆` and `Δ` have the same valuation. -/
theorem Δ_eq_of_a₃_eq_zero_of_a₄_eq_zero {W : WeierstrassCurve R} (h₃ : W.a₃ = 0)
    (h₄ : W.a₄ = 0) : W.Δ = -W.a₆ * (W.b₂ ^ 3 + 432 * W.a₆) := by
  simp only [Δ, b₂, b₄, b₆, b₈, h₃, h₄]
  ring

variable (E : WeierstrassCurve R)

/-- Where `2 = 0`, a curve with nonzero discriminant has `a₁ ≠ 0` or `a₃ ≠ 0`: otherwise
`a₁ = a₃ = 0` makes the partial derivative `∂/∂y = 2y + a₁x + a₃` vanish identically, so
`Δ = 0`. -/
theorem a₁_ne_zero_or_a₃_ne_zero_of_Δ_ne_zero_of_two_eq_zero (hΔ : E.Δ ≠ 0) (h2 : (2 : R) = 0) :
    E.a₁ ≠ 0 ∨ E.a₃ ≠ 0 := by
  by_contra! h
  exact hΔ (by rw [Δ, b₈, b₆, b₄, b₂, h.1, h.2]; grobner)

section

variable [E.IsElliptic]

/-- `j(E) = 1728` if and only if `c₆(E)² = 0`, by the relation `1728·Δ = c₄³ - c₆²`. This is the
analogue for `j = 1728` of `WeierstrassCurve.j_eq_zero_iff'` (`j = 0 ↔ c₄³ = 0`). -/
theorem j_eq_1728_iff' : E.j = 1728 ↔ E.c₆ ^ 2 = 0 := by
  have h : E.c₆ ^ 2 = E.c₄ ^ 3 - 1728 * E.Δ := by linear_combination E.c_relation
  rw [h, sub_eq_zero, j, Units.inv_mul_eq_iff_eq_mul, coe_Δ', mul_comm E.Δ 1728]

/-- `j(E) = 1728` if and only if `c₆(E) = 0`, by the relation `1728·Δ = c₄³ - c₆²`. This is the
analogue for `j = 1728` of `WeierstrassCurve.j_eq_zero_iff` (`j = 0 ↔ c₄ = 0`). -/
theorem j_eq_1728_iff [IsReduced R] : E.j = 1728 ↔ E.c₆ = 0 := by
  rw [j_eq_1728_iff', pow_eq_zero_iff two_ne_zero]

end

section BaseChange

variable {A : Type*} [CommRing A] [Algebra R A]

/-- Base change preserves ellipticity. Mathlib's instance is stated for
`WeierstrassCurve.map`, which instance search does not see through the plain `def`
`WeierstrassCurve.baseChange`. -/
instance isElliptic_baseChange [E.IsElliptic] : (E.baseChange A).IsElliptic :=
  inferInstanceAs (E.map _).IsElliptic

/-- `c₄ ≠ 0` survives base change along an injection, since `c₄` of the base change is the
image of `c₄`. Stated on `c₄` rather than on `j`: nothing here needs `[IsReduced R]` or the
`j`-criterion — nor even that `E` be elliptic — and a caller with `j ≠ 0` gets the hypothesis from
`j_eq_zero_iff`. -/
theorem baseChange_c₄_ne_zero (hRA : Function.Injective (algebraMap R A)) (hc₄ : E.c₄ ≠ 0) :
    (E.baseChange A).c₄ ≠ 0 := by
  simp only [baseChange, map_c₄]
  exact (map_ne_zero_iff _ hRA).mpr hc₄

/-- `c₆ ≠ 0` survives base change along an injection. The companion of
`baseChange_c₄_ne_zero`; a caller with `j ≠ 1728` gets the hypothesis from `j_eq_1728_iff`. -/
theorem baseChange_c₆_ne_zero (hRA : Function.Injective (algebraMap R A)) (hc₆ : E.c₆ ≠ 0) :
    (E.baseChange A).c₆ ≠ 0 := by
  simp only [baseChange, map_c₆]
  exact (map_ne_zero_iff _ hRA).mpr hc₆

/-- The discriminant of a base change is the image of the discriminant, stated against an
equation `W` known to be the base change of `W₀`. -/
theorem algebraMap_Δ_of_baseChange_eq {W₀ : WeierstrassCurve R} {W : WeierstrassCurve A}
    (h : W₀.baseChange A = W) : algebraMap R A W₀.Δ = W.Δ := by
  rw [← h, baseChange, map_Δ]

/-- The invariant `c₄` of a base change is the image of `c₄`, stated against an equation `W`
known to be the base change of `W₀`. -/
theorem algebraMap_c₄_of_baseChange_eq {W₀ : WeierstrassCurve R} {W : WeierstrassCurve A}
    (h : W₀.baseChange A = W) : algebraMap R A W₀.c₄ = W.c₄ := by
  rw [← h, baseChange, map_c₄]

/-- The invariant `c₆` of a base change is the image of `c₆`, stated against an equation `W`
known to be the base change of `W₀`. -/
theorem algebraMap_c₆_of_baseChange_eq {W₀ : WeierstrassCurve R} {W : WeierstrassCurve A}
    (h : W₀.baseChange A = W) : algebraMap R A W₀.c₆ = W.c₆ := by
  rw [← h, baseChange, map_c₆]

end BaseChange

end Invariants

/-! ## The cusp curve -/

variable (R : Type*)

section Zero

variable [Zero R]

/-- The cusp curve `Y² = X³` over a commutative ring `R`. -/
def cusp : Affine R := { a₁ := 0, a₂ := 0, a₃ := 0, a₄ := 0, a₆ := 0 }

/-- Every coefficient of the cusp curve vanishes, and likewise for `cusp_a₂` through `cusp_a₆`.
The definition body is unexposed, so these are how a consumer projects out of `cusp` — for instance
when specialising the universal curve along it. -/
@[simp] theorem cusp_a₁ : (cusp R).a₁ = 0 := by rfl
/-- The `a₂` coefficient of the cusp curve vanishes. -/
@[simp] theorem cusp_a₂ : (cusp R).a₂ = 0 := by rfl
/-- The `a₃` coefficient of the cusp curve vanishes. -/
@[simp] theorem cusp_a₃ : (cusp R).a₃ = 0 := by rfl
/-- The `a₄` coefficient of the cusp curve vanishes. -/
@[simp] theorem cusp_a₄ : (cusp R).a₄ = 0 := by rfl
/-- The `a₆` coefficient of the cusp curve vanishes. -/
@[simp] theorem cusp_a₆ : (cusp R).a₆ = 0 := by rfl

end Zero

/-- `(1, 1)` lies on the cusp curve `Y² = X³`, over any commutative ring.

The case `R = ℤ` is the one the universal curve uses: specializing along that point is the cheap
route to nonvanishing statements, since `ψₙ(1,1) = n`, so a universal quantity that vanished would
have to vanish in `ℤ`. -/
theorem equation_cusp_one_one [CommRing R] : (cusp R).Equation 1 1 := by
  simp [Affine.Equation, Affine.polynomial, cusp, Polynomial.evalEval]

end WeierstrassCurve

end

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.SingularReduction
public import TauCeti.AlgebraicGeometry.EllipticCurve.TateAlgorithm.Terminal
-- Proof-only: the residue quadratic at an odd stage of the `Iₙ*` subprocedure.
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.StarredReduction
-- Proof-only: index two from sums of outside elements.
import TauCeti.GroupTheory.Index.Two
-- Proof-only: Hensel's lemma for a polynomial that is not monic.
import TauCeti.RingTheory.Henselian.Basic
-- Proof-only: units and the maximal ideal of a local ring with principal maximal ideal.
import TauCeti.RingTheory.LocalRing.MaximalIdeal.Generator
-- Proof-only: a root of a quadratic with unit discriminant is simple.
import TauCeti.RingTheory.LocalRing.QuadraticDoubleRoot

/-!
# Points with singular reduction at the symbols `Iₙ*`

Let `v` be a valuation on a field `F`, with valuation ring `O`, maximal ideal `𝔪 = (ϖ)` and
residue field `k`, and let `W` be a Weierstrass curve over `F` with an integral model `W_O` over
`O`. The points with nonsingular reduction form the subgroup `E₀(F)` of `W(F)`
(`WeierstrassCurve.Affine.nonsingularReduction`). When `F` is complete for a discrete valuation
with perfect residue field and the equation is minimal, the index `[E(F) : E₀(F)]` is the local
index `c_v` that Tate's algorithm computes (Silverman, *Advanced Topics*, IV.9, Table 4.1). This
file computes the index at the reduction symbols `Iₙ*` with `n ≥ 1`, which Tate's algorithm reaches
through the subprocedure of its Step 7 (`WeierstrassCurve.IsTateOddStage`,
`WeierstrassCurve.IsTateEvenStage`). The subprocedure stops at stage `n` when a quadratic over
`k` has distinct roots:

* at `n = 2k + 1`, with `a₃ = ϖ^(k+2) A₃` and `a₆ = ϖ^(2k+4) A₆`, the quadratic `T² + A₃ T − A₆`;
* at `n = 2k + 2`, with `a₂ = ϖ A₂`, `a₄ = ϖ^(k+3) A₄` and `a₆ = ϖ^(2k+5) A₆`, the quadratic
  `A₂ T² + A₄ T + A₆`.

Table 4.1 reports `c_v = 4` when this quadratic has a root in `k`, and `c_v = 2` otherwise. This
file proves that over a Henselian valuation ring, and that the index divides `4` in general.

Every stage of the subprocedure satisfies the normal form `ϖ ∣ a₁`, `ϖ ∥ a₂`, `ϖ² ∣ a₃`,
`ϖ³ ∣ a₄`, `ϖ⁴ ∣ a₆` of stage `1`, where the residue cubic is `T² (T + A₂)` with `A₂ = a₂ / ϖ` a
unit. A point with singular reduction is `(x, y)` with `x, y ∈ 𝔪`. If `ϖ² ∤ x`, the Weierstrass
equation divided by `ϖ²` and `ϖ³` shows that `ϖ² ∣ y` and `x = ϖ X` with `X ≡ −A₂`: the point
reduces to the simple root of the residue cubic. If `ϖ² ∣ x`, then `ϖ² ∣ y` as well. Let `S` be the
set of points `(ϖ² X, ϖ² Y)` with `X` and `Y` integral. Along the chord through two points the
Weierstrass cubic factors as `−(X − x₁)(X − x₂)(X − x₃)`, so that `x₁ + x₂ + x₃ = ℓ² + a₁ ℓ − a₂`
and `x₁ x₂ x₃ = ν² + a₃ ν − a₆` for the line `y = ℓ x + ν`. Comparing powers of `ϖ` in these two
identities shows:

* two points with singular reduction outside `S` add to a point with nonsingular reduction;
* a point with singular reduction outside `S` plus a point of `S` has singular reduction;
* two points of `S` do not add to a point of `S`.

Hence the points outside `S` form a subgroup `H` of `W(F)` containing `E₀(F)`, and both
`[H : E₀(F)]` and `[W(F) : H]` divide `2`. Over a Henselian valuation ring the simple root of the
residue cubic lifts to a point of `H` outside `E₀(F)`, so `[H : E₀(F)] = 2`. Following the
subprocedure on the coordinates of a point of `S` shows that it is `(ϖ^(k+2) X, ϖ^(k+2) Y)` with
`Y` (at `n = 2k + 1`) or `X` (at `n = 2k + 2`) a root of the quadratic above modulo `ϖ`. So `S` is
empty when the quadratic has no root in `k`. Conversely, over a Henselian valuation ring a root,
which is simple, lifts to a point of `S`, and then `[W(F) : H] = 2`.

No discreteness, completeness, minimality or perfectness is assumed. Only the existence of points
with singular reduction uses the Henselian hypothesis.

## Main results

All in the namespace `WeierstrassCurve.Affine`:

* `index_nonsingularReduction_dvd_four_of_isTateTerminal_IStar`: at `Iₙ*` with `n ≥ 1`, the index
  `[E(F) : E₀(F)]` divides `4`.
* `index_nonsingularReduction_dvd_two_of_isTateTerminal_IStar_two_mul_add_one` and
  `index_nonsingularReduction_dvd_two_of_isTateTerminal_IStar_two_mul_add_two`: if the quadratic
  of the last stage has no root in `k`, the index divides `2`.
* `index_nonsingularReduction_eq_two_of_isTateTerminal_IStar_two_mul_add_one` and
  `index_nonsingularReduction_eq_two_of_isTateTerminal_IStar_two_mul_add_two`: over a Henselian
  valuation ring, if the quadratic has no root in `k`, the index is `2`.
* `index_nonsingularReduction_eq_four_of_isTateTerminal_IStar_two_mul_add_one` and
  `index_nonsingularReduction_eq_four_of_isTateTerminal_IStar_two_mul_add_two`: over a Henselian
  valuation ring, if the quadratic has a root in `k`, the index is `4`.

## References

* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, GTM 151, IV.9.
* J. Tate, *Algorithm for determining the type of a singular fibre in an elliptic pencil*, in
  *Modular Functions of One Variable IV*, LNM 476 (1975), 33–52.
-/

public section

open IsLocalRing Polynomial
open TauCeti.IsLocalRing (isUnit_add_of_dvd isUnit_iff_not_dvd mem_maximalIdeal_iff_dvd)

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] [IsDomain R] (W : WeierstrassCurve R) {π : R}

/-- On the normal form `π ∣ a₁`, `a₂ = π A₂`, `π² ∣ a₃`, `π³ ∣ a₄`, `π⁴ ∣ a₆` of Step 7 of Tate's
algorithm, a solution `(π X, π Y)` with `π ∤ X` has `π ∣ Y` and `X ≡ −A₂` modulo `π`: the residue
of `X` is the simple root of the residue cubic `T² (T + A₂)`. -/
private theorem dvd_and_dvd_add_of_equation (hπ : Prime π) (h₁ : π ∣ W.a₁) {A₂ : R}
    (h₂ : W.a₂ = π * A₂) (h₃ : π ^ 2 ∣ W.a₃) (h₄ : π ^ 3 ∣ W.a₄) (h₆ : π ^ 4 ∣ W.a₆) {X Y : R}
    (hX : ¬ π ∣ X) (h : W.toAffine.Equation (π * X) (π * Y)) : π ∣ Y ∧ π ∣ X + A₂ := by
  obtain ⟨α₁, hα₁⟩ := h₁
  obtain ⟨α₃, hα₃⟩ := h₃
  obtain ⟨α₄, hα₄⟩ := h₄
  obtain ⟨α₆, hα₆⟩ := h₆
  rw [Affine.equation_iff, hα₁, h₂, hα₃, hα₄, hα₆] at h
  -- the equation divided by `π²` gives `π ∣ Y²`
  obtain ⟨Y, rfl⟩ : π ∣ Y := hπ.dvd_of_dvd_pow (n := 2)
    ⟨X ^ 3 + A₂ * X ^ 2 + π * α₄ * X + π * α₆ - α₁ * X * Y - α₃ * Y,
      mul_left_cancel₀ (pow_ne_zero 2 hπ.ne_zero) (by linear_combination h)⟩
  -- then the equation divided by `π³` gives `π ∣ X² (X + A₂)`
  refine ⟨dvd_mul_right π Y, (hπ.dvd_or_dvd (a := X ^ 2) ?_).resolve_left fun h' ↦
    hX (hπ.dvd_of_dvd_pow h')⟩
  exact ⟨Y ^ 2 + α₁ * X * Y + α₃ * Y - α₄ * X - α₆,
    mul_left_cancel₀ (pow_ne_zero 3 hπ.ne_zero) (by linear_combination -h)⟩

/-- If `π² ∣ a₃`, `π ∣ a₄` and `π³ ∣ a₆`, a solution `(π² X, π Y)` has `π ∣ Y`. -/
private theorem dvd_of_equation_sq_mul (hπ : Prime π) (h₃ : π ^ 2 ∣ W.a₃) (h₄ : π ∣ W.a₄)
    (h₆ : π ^ 3 ∣ W.a₆) {X Y : R} (h : W.toAffine.Equation (π ^ 2 * X) (π * Y)) : π ∣ Y := by
  obtain ⟨α₃, hα₃⟩ := h₃
  obtain ⟨α₄, hα₄⟩ := h₄
  obtain ⟨α₆, hα₆⟩ := h₆
  rw [Affine.equation_iff, hα₃, hα₄, hα₆] at h
  exact hπ.dvd_of_dvd_pow (n := 2)
    ⟨π ^ 3 * X ^ 3 + π * W.a₂ * X ^ 2 + α₄ * X + α₆ - W.a₁ * X * Y - α₃ * Y,
      mul_left_cancel₀ (pow_ne_zero 2 hπ.ne_zero) (by linear_combination h)⟩

/-- **One stage of the `Iₙ*` subprocedure, on points.** With `π ∣ a₁`, `a₂ = π A₂`, `π ∤ A₂`, and
`π^(j+1) ∣ a₃`, `π^(j+2) ∣ a₄`, `π^(2j+2) ∣ a₆` for `j = i + 2`, a solution `(π^j X, π^j Y)` has
`π ∣ X` and `π ∣ Y`: the equation divided by `π^(2j)` forces `π ∣ Y`, and then divided by
`π^(2j+1)` it forces `π ∣ A₂ X²`. -/
private theorem dvd_and_dvd_of_equation_pow (hπ : Prime π) (i : ℕ) (h₁ : π ∣ W.a₁) {A₂ : R}
    (h₂ : W.a₂ = π * A₂) (hA₂ : ¬ π ∣ A₂) (h₃ : π ^ (i + 3) ∣ W.a₃) (h₄ : π ^ (i + 4) ∣ W.a₄)
    (h₆ : π ^ (2 * i + 6) ∣ W.a₆) {X Y : R}
    (h : W.toAffine.Equation (π ^ (i + 2) * X) (π ^ (i + 2) * Y)) : π ∣ X ∧ π ∣ Y := by
  obtain ⟨α₁, hα₁⟩ := h₁
  obtain ⟨α₃, hα₃⟩ := h₃
  obtain ⟨α₄, hα₄⟩ := h₄
  obtain ⟨α₆, hα₆⟩ := h₆
  rw [Affine.equation_iff, hα₁, h₂, hα₃, hα₄, hα₆] at h
  obtain ⟨Y, rfl⟩ : π ∣ Y := hπ.dvd_of_dvd_pow (n := 2)
    ⟨π ^ (i + 1) * X ^ 3 + A₂ * X ^ 2 + π * α₄ * X + π * α₆ - α₁ * X * Y - α₃ * Y,
      mul_left_cancel₀ (pow_ne_zero (2 * i + 4) hπ.ne_zero) (by linear_combination h)⟩
  refine ⟨hπ.dvd_of_dvd_pow (n := 2) ((hπ.dvd_or_dvd (a := A₂) ?_).resolve_left hA₂),
    dvd_mul_right π Y⟩
  exact ⟨Y ^ 2 + α₁ * X * Y + α₃ * Y - π ^ i * X ^ 3 - α₄ * X - α₆,
    mul_left_cancel₀ (pow_ne_zero (2 * i + 5) hπ.ne_zero) (by linear_combination -h)⟩

/-- **The `Iₙ*` subprocedure, on points.** With `π ∣ a₁`, `a₂ = π A₂`, `π ∤ A₂`,
`π^(k+2) ∣ a₃`, `π^(k+3) ∣ a₄` and `π^(2k+4) ∣ a₆`, a solution `(x, y)` with `π² ∣ x` and `π² ∣ y`
has `π^(k+2) ∣ x` and `π^(k+2) ∣ y`. -/
private theorem pow_dvd_and_pow_dvd_of_equation (hπ : Prime π) {k : ℕ} (h₁ : π ∣ W.a₁) {A₂ : R}
    (h₂ : W.a₂ = π * A₂) (hA₂ : ¬ π ∣ A₂) (h₃ : π ^ (k + 2) ∣ W.a₃) (h₄ : π ^ (k + 3) ∣ W.a₄)
    (h₆ : π ^ (2 * k + 4) ∣ W.a₆) {x y : R} (h : W.toAffine.Equation x y) (hx : π ^ 2 ∣ x)
    (hy : π ^ 2 ∣ y) : π ^ (k + 2) ∣ x ∧ π ^ (k + 2) ∣ y := by
  suffices ∀ i ≤ k, π ^ (i + 2) ∣ x ∧ π ^ (i + 2) ∣ y from this k le_rfl
  intro i hi
  induction i with
  | zero => exact ⟨hx, hy⟩
  | succ i ih =>
    obtain ⟨⟨X, rfl⟩, ⟨Y, rfl⟩⟩ := ih (by omega)
    obtain ⟨⟨X, rfl⟩, ⟨Y, rfl⟩⟩ := W.dvd_and_dvd_of_equation_pow hπ i h₁ h₂ hA₂
      ((pow_dvd_pow π (by omega)).trans h₃) ((pow_dvd_pow π (by omega)).trans h₄)
      ((pow_dvd_pow π (by omega)).trans h₆) h
    exact ⟨⟨X, by ring⟩, ⟨Y, by ring⟩⟩

/-- **The last stage `n = 2k + 2` of the `Iₙ*` subprocedure, on points.** With `π ∣ a₁`,
`a₂ = π A₂`, `π^(k+3) ∣ a₃`, `a₄ = π^(k+3) A₄` and `a₆ = π^(2k+5) A₆`, a solution
`(π^(k+2) X, π^(k+2) Y)` makes `X` a root of `A₂ T² + A₄ T + A₆` modulo `π`. -/
private theorem dvd_quadratic_of_equation_even (hπ : Prime π) {k : ℕ} (h₁ : π ∣ W.a₁)
    {A₂ A₄ A₆ : R} (h₂ : W.a₂ = π * A₂) (h₃ : π ^ (k + 3) ∣ W.a₃)
    (h₄ : W.a₄ = π ^ (k + 3) * A₄) (h₆ : W.a₆ = π ^ (2 * k + 5) * A₆) {X Y : R}
    (h : W.toAffine.Equation (π ^ (k + 2) * X) (π ^ (k + 2) * Y)) :
    π ∣ A₂ * X ^ 2 + A₄ * X + A₆ := by
  obtain ⟨α₁, hα₁⟩ := h₁
  obtain ⟨α₃, hα₃⟩ := h₃
  rw [Affine.equation_iff, hα₁, h₂, hα₃, h₄, h₆] at h
  obtain ⟨Y, rfl⟩ : π ∣ Y := hπ.dvd_of_dvd_pow (n := 2)
    ⟨π ^ (k + 1) * X ^ 3 + A₂ * X ^ 2 + A₄ * X + A₆ - α₁ * X * Y - α₃ * Y,
      mul_left_cancel₀ (pow_ne_zero (2 * k + 4) hπ.ne_zero) (by linear_combination h)⟩
  exact ⟨Y ^ 2 + α₁ * X * Y + α₃ * Y - π ^ k * X ^ 3,
    mul_left_cancel₀ (pow_ne_zero (2 * k + 5) hπ.ne_zero) (by linear_combination -h)⟩

namespace Affine

variable {F Γ₀ : Type*} [Field F] [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation F Γ₀)
  {W : Affine F} [IsIntegral v.valuationSubring W]

/-- The valuation ring of `v`. -/
local notation "𝒪" => v.valuationSubring

/-! ### The normal form of the stopping test -/

/-- Both branches of the stopping test for `Iₙ*` satisfy the normal form of stage `1` of the
subprocedure: `ϖ ∣ a₁`, `ϖ ∥ a₂`, `ϖ² ∣ a₃`, `ϖ³ ∣ a₄` and `ϖ⁴ ∣ a₆`. -/
private theorem isTateOddStage_zero_of_isTateTerminal_IStar {ϖ : v.valuationSubring} {n : ℕ}
    (h : (integralModel v.valuationSubring W).IsTateTerminal ϖ (.IStar (n + 1))) :
    IsTateOddStage ϖ 0 (integralModel v.valuationSubring W) := by
  rcases isTateTerminal_IStar_add_one.1 h with ⟨k, -, hs, -⟩ | ⟨k, -, hs, -⟩
  · obtain ⟨h₁, h₂, h₂', h₃, h₄, h₆⟩ := isTateOddStage_iff.1 hs
    exact isTateOddStage_iff.2 ⟨h₁, h₂, h₂', (pow_dvd_pow ϖ (by omega)).trans h₃,
      (pow_dvd_pow ϖ (by omega)).trans h₄, (pow_dvd_pow ϖ (by omega)).trans h₆⟩
  · obtain ⟨h₁, h₂, h₂', h₃, h₄, h₆⟩ := isTateEvenStage_iff.1 hs
    exact isTateOddStage_iff.2 ⟨h₁, h₂, h₂', (pow_dvd_pow ϖ (by omega)).trans h₃,
      (pow_dvd_pow ϖ (by omega)).trans h₄, (pow_dvd_pow ϖ (by omega)).trans h₆⟩

/-- The stopping test at `I*_{2k+1}` is the odd stage `k` with `ϖ^(2k+5) ∤ b₆`. -/
private theorem isTateOddStage_of_isTateTerminal_IStar {ϖ : v.valuationSubring} {k : ℕ}
    (h : (integralModel v.valuationSubring W).IsTateTerminal ϖ (.IStar (2 * k + 1))) :
    IsTateOddStage ϖ k (integralModel v.valuationSubring W) ∧
      ¬ ϖ ^ (2 * k + 5) ∣ (integralModel v.valuationSubring W).b₆ := by
  rcases isTateTerminal_IStar_add_one.1 h with ⟨k', hk, hs, hb⟩ | ⟨k', hk, -, -⟩
  · obtain rfl : k' = k := by omega
    exact ⟨hs, hb⟩
  · omega

/-- The stopping test at `I*_{2k+2}` is the even stage `k` with
`ϖ^(2k+7) ∤ a₄² − 4 a₂ a₆`. -/
private theorem isTateEvenStage_of_isTateTerminal_IStar {ϖ : v.valuationSubring} {k : ℕ}
    (h : (integralModel v.valuationSubring W).IsTateTerminal ϖ (.IStar (2 * k + 2))) :
    IsTateEvenStage ϖ k (integralModel v.valuationSubring W) ∧
      ¬ ϖ ^ (2 * k + 7) ∣ discrim (integralModel v.valuationSubring W).a₂
        (integralModel v.valuationSubring W).a₄ (integralModel v.valuationSubring W).a₆ := by
  rcases isTateTerminal_IStar_add_one.1 h with ⟨k', hk, -, -⟩ | ⟨k', hk, hs, hb⟩
  · omega
  · obtain rfl : k' = k := by omega
    exact ⟨hs, hb⟩

/-- The data of the normal form of stage `1`: `ϖ` is prime, the reduction is singular at the
origin, and `a₂ = ϖ A₂` with `A₂` a unit. -/
private theorem stage_data {ϖ : v.valuationSubring}
    (hϖ : maximalIdeal v.valuationSubring = Ideal.span {ϖ})
    (hst : IsTateOddStage ϖ 0 (integralModel v.valuationSubring W)) :
    Prime ϖ ∧ (integralModel v.valuationSubring W).a₃ ∈ maximalIdeal v.valuationSubring ∧
      (integralModel v.valuationSubring W).a₄ ∈ maximalIdeal v.valuationSubring ∧
      (integralModel v.valuationSubring W).a₆ ∈ maximalIdeal v.valuationSubring ∧
      ∃ A₂ : v.valuationSubring, (integralModel v.valuationSubring W).a₂ = ϖ * A₂ ∧ ¬ ϖ ∣ A₂ := by
  obtain ⟨-, ⟨A₂, hA₂⟩, h₂', h₃, h₄, h₆⟩ := isTateOddStage_iff.1 hst
  have hϖ0 : ϖ ≠ 0 := by
    rintro rfl
    exact h₂' (by simp [hA₂])
  refine ⟨(Ideal.span_singleton_prime hϖ0).mp (hϖ ▸ (maximalIdeal.isMaximal _).isPrime),
    (mem_maximalIdeal_iff_dvd hϖ).2 ((dvd_pow_self ϖ (by norm_num)).trans h₃),
    (mem_maximalIdeal_iff_dvd hϖ).2 ((dvd_pow_self ϖ (by norm_num)).trans h₄),
    (mem_maximalIdeal_iff_dvd hϖ).2 ((dvd_pow_self ϖ (by norm_num)).trans h₆), A₂, hA₂,
    fun hd ↦ h₂' ?_⟩
  rw [hA₂, pow_two]
  exact mul_dvd_mul_left ϖ hd

/-! ### The points with both coordinates divisible by `ϖ²` -/

/-- The affine points `(x, y)` of `W(F)` with `x` and `y` integral and divisible by `ϖ²`. In the
`Iₙ*` branch of Tate's algorithm these are the points with singular reduction whose `x`-coordinate
does not reduce, after division by `ϖ`, to the simple root of the residue cubic. -/
private def farPoints (ϖ : v.valuationSubring) : Set W.Point :=
  {P | ∃ (x y : v.valuationSubring) (h : W.Nonsingular (x : F) (y : F)), P = .some _ _ h ∧
    ϖ ^ 2 ∣ x ∧ ϖ ^ 2 ∣ y}

/-- The negative of a point `(ϖ² X, ϖ² Y)` is again of this form, when `ϖ² ∣ a₃`. -/
private theorem neg_mem_farPoints {ϖ : v.valuationSubring}
    (h₃ : ϖ ^ 2 ∣ (integralModel v.valuationSubring W).a₃) {P : W.Point}
    (hP : P ∈ farPoints v ϖ) : -P ∈ farPoints v ϖ := by
  obtain ⟨x, y, h, rfl, hx, hy⟩ := hP
  have hnegY : W.negY (x : F) (y : F) =
      ((-y - (integralModel v.valuationSubring W).a₁ * x -
        (integralModel v.valuationSubring W).a₃ : v.valuationSubring) : F) := by
    rw [negY, ← coe_integralModel_a₁ v, ← coe_integralModel_a₃ v]
    push_cast
    ring
  refine ⟨x, _, hnegY ▸ (nonsingular_neg ..).2 h, ?_, hx,
    dvd_sub (dvd_sub (dvd_neg.2 hy) (hx.mul_left _)) h₃⟩
  rw [Point.neg_some, Point.some.injEq]
  exact ⟨rfl, hnegY⟩

/-- **A point with singular reduction not of the form `(ϖ² X, ϖ² Y)` reduces to the simple root.**
On the normal form of stage `1`, it is `(ϖ X, ϖ² Y)` with `X ≡ −A₂` modulo `ϖ`, where
`a₂ = ϖ A₂`; in particular `X` is a unit. -/
private theorem exists_eq_of_notMem_farPoints {ϖ : v.valuationSubring}
    (hp : Prime ϖ) (hst : IsTateOddStage ϖ 0 (integralModel v.valuationSubring W))
    {A₂ : v.valuationSubring} (hA₂ : (integralModel v.valuationSubring W).a₂ = ϖ * A₂)
    {x y : v.valuationSubring} (h : W.Nonsingular (x : F) (y : F)) (hx : ϖ ∣ x) (hy : ϖ ∣ y)
    (hF : Point.some _ _ h ∉ farPoints v ϖ) :
    ∃ X Y : v.valuationSubring, x = ϖ * X ∧ y = ϖ ^ 2 * Y ∧ ¬ ϖ ∣ X ∧ ϖ ∣ X + A₂ := by
  obtain ⟨h₁, -, -, h₃, h₄, h₆⟩ := isTateOddStage_iff.1 hst
  obtain ⟨X, rfl⟩ := hx
  obtain ⟨Y, rfl⟩ := hy
  have hE := (equation_integralModel_iff v).2 h.left
  by_cases hX : ϖ ∣ X
  · obtain ⟨X, rfl⟩ := hX
    have hY := (integralModel _ W).dvd_of_equation_sq_mul hp h₃
      ((dvd_pow_self ϖ (by norm_num)).trans h₄) ((pow_dvd_pow ϖ (by norm_num)).trans h₆)
      (X := X) (Y := Y) (by rwa [pow_two, mul_assoc])
    exact absurd ⟨_, _, h, rfl, ⟨X, by ring⟩, by rw [pow_two]; exact mul_dvd_mul_left ϖ hY⟩ hF
  obtain ⟨⟨Y, rfl⟩, hXA⟩ := (integralModel _ W).dvd_and_dvd_add_of_equation hp h₁ hA₂ h₃ h₄ h₆ hX hE
  exact ⟨X, Y, rfl, by ring, hX, hXA⟩

/-- At `I*_{2k+1}`, with `a₃ = ϖ^(k+2) A₃` and `a₆ = ϖ^(2k+4) A₆`, a point `(ϖ² X, ϖ² Y)` is
`(ϖ^(k+2) X', ϖ^(k+2) Y')` with `Y'` a root of `T² + A₃ T − A₆` modulo `ϖ`. -/
private theorem exists_root_of_mem_farPoints_odd {ϖ : v.valuationSubring}
    (hϖ : maximalIdeal v.valuationSubring = Ideal.span {ϖ}) {k : ℕ}
    (h : (integralModel v.valuationSubring W).IsTateTerminal ϖ (.IStar (2 * k + 1)))
    {A₃ A₆ : v.valuationSubring} (h₃ : (integralModel v.valuationSubring W).a₃ = ϖ ^ (k + 2) * A₃)
    (h₆ : (integralModel v.valuationSubring W).a₆ = ϖ ^ (2 * k + 4) * A₆) {P : W.Point}
    (hP : P ∈ farPoints v ϖ) :
    ∃ t : ResidueField v.valuationSubring, t ^ 2 + residue _ A₃ * t - residue _ A₆ = 0 := by
  obtain ⟨hp, -, -, -, A₂, hA₂, hA₂'⟩ :=
    stage_data v hϖ (isTateOddStage_zero_of_isTateTerminal_IStar v h)
  obtain ⟨h₁, h₂, -, h₃', h₄, h₆'⟩ :=
    isTateOddStage_iff.1 (isTateOddStage_of_isTateTerminal_IStar v h).1
  obtain ⟨x, y, hxy, -, hx, hy⟩ := hP
  have hE := (equation_integralModel_iff v).2 hxy.left
  obtain ⟨⟨X, rfl⟩, ⟨Y, rfl⟩⟩ := (integralModel _ W).pow_dvd_and_pow_dvd_of_equation hp h₁ hA₂
    hA₂' h₃' h₄ h₆' hE hx hy
  have hq := (integralModel _ W).dvd_quadratic_of_equation_odd hp.ne_zero h₁ h₂ h₃ h₄ h₆ hE
  exact ⟨residue _ Y,
    by simpa using (residue_eq_zero_iff _).2 ((mem_maximalIdeal_iff_dvd hϖ).2 hq)⟩

/-- At `I*_{2k+1}`, with `a₃ = ϖ^(k+2) A₃` and `a₆ = ϖ^(2k+4) A₆`, a root `t` of the residue
quadratic `T² + A₃ T − A₆` gives a point `(0, ϖ^(k+2) Y)`, when the valuation ring is Henselian:
the root is simple, since the discriminant `A₃² + 4 A₆` is `b₆ / ϖ^(2k+4)`, a unit by the stopping
test, so it lifts to a root `Y` of `T² + A₃ T − A₆`. -/
private theorem exists_mem_farPoints_odd [HenselianLocalRing v.valuationSubring]
    {ϖ : v.valuationSubring} (hϖ : maximalIdeal v.valuationSubring = Ideal.span {ϖ}) {k : ℕ}
    (h : (integralModel v.valuationSubring W).IsTateTerminal ϖ (.IStar (2 * k + 1)))
    {A₃ A₆ : v.valuationSubring} (h₃ : (integralModel v.valuationSubring W).a₃ = ϖ ^ (k + 2) * A₃)
    (h₆ : (integralModel v.valuationSubring W).a₆ = ϖ ^ (2 * k + 4) * A₆)
    {t : ResidueField v.valuationSubring} (ht : t ^ 2 + residue _ A₃ * t - residue _ A₆ = 0) :
    ∃ P : W.Point, P ∈ farPoints v ϖ := by
  set Wo := integralModel v.valuationSubring W
  obtain ⟨hp, -⟩ := stage_data v hϖ (isTateOddStage_zero_of_isTateTerminal_IStar v h)
  obtain ⟨-, hb₆⟩ := isTateOddStage_of_isTateTerminal_IStar v h
  have hD : IsUnit (A₃ ^ 2 + 4 * A₆) := by
    rw [isUnit_iff_not_dvd hϖ]
    rintro ⟨e, he⟩
    exact hb₆ ⟨e, by rw [b₆, h₃, h₆]; linear_combination ϖ ^ (2 * k + 4) * he⟩
  -- lift the root `t` to a root `Y` of `T² + A₃ T − A₆`
  obtain ⟨Y₀, rfl⟩ := residue_surjective t
  set f : v.valuationSubring[X] := X ^ 2 + C A₃ * X - C A₆ with hf
  have hmon : f.Monic := by
    rw [hf]
    monicity!
  have hf₀ : f.eval Y₀ ∈ maximalIdeal v.valuationSubring := by
    rw [← residue_eq_zero_iff]
    simpa [hf] using ht
  have hf₁ : IsUnit (f.derivative.eval Y₀) := by
    have hd : f.derivative.eval Y₀ = 2 * Y₀ + A₃ := by
      simp [hf, one_add_one_eq_two]
    rw [hd]
    exact TauCeti.IsLocalRing.isUnit_two_mul_add_of_isUnit_sq_add_four_mul hD
      (by simpa [hf] using hf₀)
  obtain ⟨Y, hY, -⟩ := HenselianLocalRing.is_henselian f hmon Y₀ hf₀ hf₁
  have hY' : Y ^ 2 + A₃ * Y - A₆ = 0 := by simpa [hf] using hY.eq_zero
  have hu : IsUnit (2 * Y + A₃) :=
    TauCeti.IsLocalRing.isUnit_two_mul_add_of_isUnit_sq_add_four_mul hD
      (by rw [hY']; exact zero_mem _)
  -- the point `(0, ϖ^(k+2) Y)`
  have hns : Wo.toAffine.Nonsingular 0 (ϖ ^ (k + 2) * Y) := by
    rw [nonsingular_iff']
    refine ⟨by rw [equation_iff, h₃, h₆]; linear_combination ϖ ^ (2 * k + 4) * hY', .inr ?_⟩
    rw [h₃]
    exact fun h0 ↦ mul_ne_zero (pow_ne_zero (k + 2) hp.ne_zero) hu.ne_zero
      (by linear_combination h0)
  have hF : W.Nonsingular ((0 : v.valuationSubring) : F)
      ((ϖ ^ (k + 2) * Y : v.valuationSubring) : F) :=
    (nonsingular_integralModel_iff v).1 hns
  exact ⟨Point.some _ _ hF, _, _, hF, rfl, dvd_zero _,
    ((pow_dvd_pow ϖ (by omega)).mul_right Y)⟩

/-- At `I*_{2k+2}`, with `a₂ = ϖ A₂`, `a₄ = ϖ^(k+3) A₄` and `a₆ = ϖ^(2k+5) A₆`, a point
`(ϖ² X, ϖ² Y)` is `(ϖ^(k+2) X', ϖ^(k+2) Y')` with `X'` a root of `A₂ T² + A₄ T + A₆` modulo
`ϖ`. -/
private theorem exists_root_of_mem_farPoints_even {ϖ : v.valuationSubring}
    (hϖ : maximalIdeal v.valuationSubring = Ideal.span {ϖ}) {k : ℕ}
    (h : (integralModel v.valuationSubring W).IsTateTerminal ϖ (.IStar (2 * k + 2)))
    {A₂ A₄ A₆ : v.valuationSubring} (h₂ : (integralModel v.valuationSubring W).a₂ = ϖ * A₂)
    (h₄ : (integralModel v.valuationSubring W).a₄ = ϖ ^ (k + 3) * A₄)
    (h₆ : (integralModel v.valuationSubring W).a₆ = ϖ ^ (2 * k + 5) * A₆) {P : W.Point}
    (hP : P ∈ farPoints v ϖ) : ∃ t : ResidueField v.valuationSubring,
      residue _ A₂ * t ^ 2 + residue _ A₄ * t + residue _ A₆ = 0 := by
  obtain ⟨h₁, -, h₂', h₃, -, -⟩ :=
    isTateEvenStage_iff.1 (isTateEvenStage_of_isTateTerminal_IStar v h).1
  obtain ⟨hp, -⟩ := stage_data v hϖ (isTateOddStage_zero_of_isTateTerminal_IStar v h)
  have hA₂ : ¬ ϖ ∣ A₂ := fun hd ↦ h₂' (by rw [h₂, pow_two]; exact mul_dvd_mul_left ϖ hd)
  obtain ⟨x, y, hxy, -, hx, hy⟩ := hP
  have hE := (equation_integralModel_iff v).2 hxy.left
  obtain ⟨⟨X, rfl⟩, ⟨Y, rfl⟩⟩ := (integralModel _ W).pow_dvd_and_pow_dvd_of_equation hp h₁ h₂ hA₂
    ((pow_dvd_pow ϖ (by omega)).trans h₃) ⟨A₄, h₄⟩ ⟨ϖ * A₆, by rw [h₆]; ring⟩ hE hx hy
  have hq := (integralModel _ W).dvd_quadratic_of_equation_even hp h₁ h₂ h₃ h₄ h₆ hE
  exact ⟨residue _ X,
    by simpa using (residue_eq_zero_iff _).2 ((mem_maximalIdeal_iff_dvd hϖ).2 hq)⟩

/-- At `I*_{2k+2}`, with `a₂ = ϖ A₂`, `a₄ = ϖ^(k+3) A₄` and `a₆ = ϖ^(2k+5) A₆`, a root `t` of the
residue quadratic `A₂ T² + A₄ T + A₆` gives a point `(ϖ^(k+2) X, 0)`, when the valuation ring is
Henselian: the discriminant `A₄² − 4 A₂ A₆` is `(a₄² − 4 a₂ a₆) / ϖ^(2k+6)`, a unit by the stopping
test, so `t` is a simple root and lifts to a root `X` of `ϖ^(k+1) T³ + A₂ T² + A₄ T + A₆`. -/
private theorem exists_mem_farPoints_even [HenselianLocalRing v.valuationSubring]
    {ϖ : v.valuationSubring} (hϖ : maximalIdeal v.valuationSubring = Ideal.span {ϖ}) {k : ℕ}
    (h : (integralModel v.valuationSubring W).IsTateTerminal ϖ (.IStar (2 * k + 2)))
    {A₂ A₄ A₆ : v.valuationSubring} (h₂ : (integralModel v.valuationSubring W).a₂ = ϖ * A₂)
    (h₄ : (integralModel v.valuationSubring W).a₄ = ϖ ^ (k + 3) * A₄)
    (h₆ : (integralModel v.valuationSubring W).a₆ = ϖ ^ (2 * k + 5) * A₆)
    {t : ResidueField v.valuationSubring}
    (ht : residue _ A₂ * t ^ 2 + residue _ A₄ * t + residue _ A₆ = 0) :
    ∃ P : W.Point, P ∈ farPoints v ϖ := by
  set Wo := integralModel v.valuationSubring W
  obtain ⟨hp, -⟩ := stage_data v hϖ (isTateOddStage_zero_of_isTateTerminal_IStar v h)
  obtain ⟨-, hdisc⟩ := isTateEvenStage_of_isTateTerminal_IStar v h
  -- the discriminant `A₄² − 4 A₂ A₆` is a unit, so `2 A₂ z + A₄` is a unit at a root `z`
  have hD : ¬ ϖ ∣ A₄ ^ 2 - 4 * A₂ * A₆ := by
    rintro ⟨e, he⟩
    exact hdisc ⟨e, by rw [discrim, h₂, h₄, h₆]; linear_combination ϖ ^ (2 * k + 6) * he⟩
  have hsimple (z : v.valuationSubring) (hz : ϖ ∣ A₂ * z ^ 2 + A₄ * z + A₆) :
      IsUnit (2 * A₂ * z + A₄) := by
    rw [isUnit_iff_not_dvd hϖ]
    intro hd
    refine hD (hp.dvd_of_dvd_pow (n := 1) ?_)
    rw [pow_one]
    exact (dvd_sub (dvd_pow hd two_ne_zero) (hz.mul_left (4 * A₂))).trans (dvd_of_eq (by ring))
  -- the cubic `ϖ^(k+1) T³ + A₂ T² + A₄ T + A₆` and its derivative
  set f : v.valuationSubring[X] := C (ϖ ^ (k + 1)) * X ^ 3 + C A₂ * X ^ 2 + C A₄ * X + C A₆ with hf
  have heval (z : v.valuationSubring) :
      f.eval z = ϖ * (ϖ ^ k * z ^ 3) + (A₂ * z ^ 2 + A₄ * z + A₆) := by
    simp only [hf, eval_add, eval_mul, eval_pow, eval_C, eval_X]
    ring
  have hder (z : v.valuationSubring) :
      f.derivative.eval z = 2 * A₂ * z + A₄ + ϖ * (3 * ϖ ^ k * z ^ 2) := by
    simp only [hf, derivative_add, derivative_C_mul_X_pow, derivative_C_mul_X, derivative_C,
      eval_add, eval_mul, eval_C, eval_pow, eval_X, eval_zero]
    push_cast
    ring
  obtain ⟨X₀, rfl⟩ := residue_surjective t
  have hX₀ : ϖ ∣ A₂ * X₀ ^ 2 + A₄ * X₀ + A₆ := by
    rw [← mem_maximalIdeal_iff_dvd hϖ, ← residue_eq_zero_iff]
    simpa using ht
  obtain ⟨X, hX, -⟩ := TauCeti.HenselianLocalRing.exists_isRoot_sub_mem_maximalIdeal f
    (a₀ := X₀) (by rw [heval, mem_maximalIdeal_iff_dvd hϖ]; exact dvd_add (dvd_mul_right _ _) hX₀)
    (by rw [hder]; exact isUnit_add_of_dvd hϖ (hsimple X₀ hX₀) (dvd_mul_right _ _))
  have hroot := hX.eq_zero
  rw [heval] at hroot
  have hu : IsUnit (2 * A₂ * X + A₄ + ϖ * (3 * ϖ ^ k * X ^ 2)) :=
    isUnit_add_of_dvd hϖ (hsimple X ⟨-(ϖ ^ k * X ^ 3), by linear_combination hroot⟩)
      (dvd_mul_right _ _)
  -- the point `(ϖ^(k+2) X, 0)`
  have hns : Wo.toAffine.Nonsingular (ϖ ^ (k + 2) * X) 0 := by
    rw [nonsingular_iff']
    refine ⟨by rw [equation_iff, h₂, h₄, h₆]; linear_combination (-ϖ ^ (2 * k + 5)) * hroot,
      .inl ?_⟩
    rw [h₂, h₄]
    exact fun h0 ↦ mul_ne_zero (neg_ne_zero.2 (pow_ne_zero (k + 3) hp.ne_zero)) hu.ne_zero
      (by linear_combination h0)
  have hF : W.Nonsingular ((ϖ ^ (k + 2) * X : v.valuationSubring) : F)
      ((0 : v.valuationSubring) : F) :=
    (nonsingular_integralModel_iff v).1 hns
  exact ⟨Point.some _ _ hF, _, _, hF, rfl, (pow_dvd_pow ϖ (by omega)).mul_right X, dvd_zero _⟩

/-! ### Points with singular reduction -/

variable [DecidableEq F]

/-- A point `(ϖ² X, ϖ² Y)` has singular reduction. -/
private theorem notMem_of_mem_farPoints {ϖ : v.valuationSubring}
    (hϖ : maximalIdeal v.valuationSubring = Ideal.span {ϖ})
    (hm₃ : (integralModel v.valuationSubring W).a₃ ∈ maximalIdeal v.valuationSubring)
    (hm₄ : (integralModel v.valuationSubring W).a₄ ∈ maximalIdeal v.valuationSubring)
    (hm₆ : (integralModel v.valuationSubring W).a₆ ∈ maximalIdeal v.valuationSubring)
    {P : W.Point} (hP : P ∈ farPoints v ϖ) : P ∉ W.nonsingularReduction v := by
  obtain ⟨x, y, h, rfl, hx, hy⟩ := hP
  exact (some_coe_notMem_nonsingularReduction_iff v hm₃ hm₄ hm₆ h).2
    ⟨(mem_maximalIdeal_iff_dvd hϖ).2 ((dvd_pow_self ϖ two_ne_zero).trans hx),
      (mem_maximalIdeal_iff_dvd hϖ).2 ((dvd_pow_self ϖ two_ne_zero).trans hy)⟩

/-- **Two points with singular reduction, neither of the form `(ϖ² X, ϖ² Y)`, add to a point
with nonsingular reduction.** Both are `(ϖ Xᵢ, ϖ² Yᵢ)` with `Xᵢ ≡ −A₂`. If their sum `(x₃, y₃)` had
singular reduction, the chord slope `ℓ` would be divisible by `ϖ`, so `x₁ x₂ x₃ = ν² + a₃ ν − a₆`
would force `ϖ² ∣ x₃`, and then `x₁ + x₂ + x₃ = ℓ² + a₁ ℓ − a₂` would read `−2 A₂ ≡ −A₂` modulo
`ϖ`. -/
private theorem add_mem_of_notMem_farPoints {ϖ : v.valuationSubring}
    (hϖ : maximalIdeal v.valuationSubring = Ideal.span {ϖ})
    (hst : IsTateOddStage ϖ 0 (integralModel v.valuationSubring W)) {P Q : W.Point}
    (hP : P ∉ W.nonsingularReduction v) (hQ : Q ∉ W.nonsingularReduction v)
    (hPF : P ∉ farPoints v ϖ) (hQF : Q ∉ farPoints v ϖ) : P + Q ∈ W.nonsingularReduction v := by
  obtain ⟨hp, hm₃, hm₄, hm₆, A₂, hA₂, hA₂'⟩ := stage_data v hϖ hst
  obtain ⟨⟨α₁, hα₁⟩, -, -, ⟨α₃, hα₃⟩, -, ⟨α₆, hα₆⟩⟩ := isTateOddStage_iff.1 hst
  obtain ⟨x₁, y₁, h₁, rfl, hx₁, hy₁⟩ :=
    exists_eq_some_of_notMem_nonsingularReduction v hm₃ hm₄ hm₆ hP
  obtain ⟨x₂, y₂, h₂, rfl, hx₂, hy₂⟩ :=
    exists_eq_some_of_notMem_nonsingularReduction v hm₃ hm₄ hm₆ hQ
  obtain ⟨X₁, Y₁, rfl, rfl, hX₁, ⟨c₁, hc₁⟩⟩ := exists_eq_of_notMem_farPoints v hp hst hA₂ h₁
    ((mem_maximalIdeal_iff_dvd hϖ).1 hx₁) ((mem_maximalIdeal_iff_dvd hϖ).1 hy₁) hPF
  obtain ⟨X₂, Y₂, rfl, rfl, hX₂, ⟨c₂, hc₂⟩⟩ := exists_eq_of_notMem_farPoints v hp hst hA₂ h₂
    ((mem_maximalIdeal_iff_dvd hϖ).1 hx₂) ((mem_maximalIdeal_iff_dvd hϖ).1 hy₂) hQF
  by_contra hPQ
  obtain ⟨x₃, -, L, -, -, -, hx₃, -, he₁, -, -, he₃⟩ :=
    exists_chord_of_add_notMem_nonsingularReduction v hm₃ hm₄ hm₆ hPQ
  obtain ⟨X₃, rfl⟩ := (mem_maximalIdeal_iff_dvd hϖ).1 hx₃
  -- `ϖ ∣ ℓ`
  obtain ⟨L, rfl⟩ : ϖ ∣ L := hp.dvd_of_dvd_pow (n := 2)
    ⟨X₁ + X₂ + X₃ - α₁ * L + A₂, by rw [hα₁, hA₂] at he₁; linear_combination he₁⟩
  -- `ϖ² ∣ x₃`
  have hu : IsUnit (X₁ * X₂) :=
    ((isUnit_iff_not_dvd hϖ).2 hX₁).mul ((isUnit_iff_not_dvd hϖ).2 hX₂)
  obtain ⟨X₃, rfl⟩ : ϖ ∣ X₃ := by
    refine (hu.dvd_mul_left).1 ⟨(Y₁ - L * X₁) ^ 2 + α₃ * (Y₁ - L * X₁) - α₆, ?_⟩
    refine mul_left_cancel₀ (pow_ne_zero 3 hp.ne_zero) ?_
    rw [hα₃, hα₆] at he₃
    linear_combination he₃
  -- `ϖ ∣ A₂`
  rw [hα₁, hA₂] at he₁
  refine hA₂' ⟨c₁ + c₂ - L ^ 2 - α₁ * L + X₃, mul_left_cancel₀ hp.ne_zero ?_⟩
  linear_combination he₁ + ϖ * hc₁ + ϖ * hc₂

/-- **A point with singular reduction not of the form `(ϖ² X, ϖ² Y)`, plus a point of that form,
has singular reduction.** The first is `(ϖ X₁, ϖ² Y₁)` with `X₁` a unit and the second is
`(ϖ² X₂, ϖ² Y₂)`, so the chord has slope `ϖ (Y₁ − Y₂) / (X₁ − ϖ X₂)`, divisible by `ϖ`, and the
sum has both coordinates in the maximal ideal. -/
private theorem add_notMem_of_mem_farPoints {ϖ : v.valuationSubring}
    (hϖ : maximalIdeal v.valuationSubring = Ideal.span {ϖ})
    (hst : IsTateOddStage ϖ 0 (integralModel v.valuationSubring W)) {P Q : W.Point}
    (hP : P ∉ W.nonsingularReduction v) (hPF : P ∉ farPoints v ϖ) (hQ : Q ∈ farPoints v ϖ) :
    P + Q ∉ W.nonsingularReduction v := by
  obtain ⟨hp, hm₃, hm₄, hm₆, A₂, hA₂, -⟩ := stage_data v hϖ hst
  obtain ⟨x₁, y₁, h₁, rfl, hx₁, hy₁⟩ :=
    exists_eq_some_of_notMem_nonsingularReduction v hm₃ hm₄ hm₆ hP
  obtain ⟨X₁, Y₁, rfl, rfl, hX₁, -⟩ := exists_eq_of_notMem_farPoints v hp hst hA₂ h₁
    ((mem_maximalIdeal_iff_dvd hϖ).1 hx₁) ((mem_maximalIdeal_iff_dvd hϖ).1 hy₁) hPF
  obtain ⟨x₂, y₂, h₂, rfl, ⟨X₂, rfl⟩, ⟨Y₂, rfl⟩⟩ := hQ
  -- `x₁ − x₂ = ϖ u` with `u = X₁ − ϖ X₂` a unit
  have hu : IsUnit (X₁ - ϖ * X₂) := (isUnit_iff_not_dvd hϖ).2 fun hd ↦
    hX₁ (by simpa using dvd_add hd (dvd_mul_right ϖ X₂))
  obtain ⟨i, hi⟩ := hu.exists_right_inv
  have hi' : ((X₁ - ϖ * X₂ : v.valuationSubring) : F) * (i : F) = 1 := by
    exact_mod_cast congrArg ((↑) : v.valuationSubring → F) hi
  have hx : ((ϖ * X₁ : v.valuationSubring) : F) ≠ ((ϖ ^ 2 * X₂ : v.valuationSubring) : F) :=
    fun he ↦ mul_ne_zero hp.ne_zero hu.ne_zero (Subtype.val_injective (by
      push_cast at he ⊢
      linear_combination he))
  have hxy : ¬(((ϖ * X₁ : v.valuationSubring) : F) = ((ϖ ^ 2 * X₂ : v.valuationSubring) : F) ∧
      ((ϖ ^ 2 * Y₁ : v.valuationSubring) : F) =
        W.negY ((ϖ ^ 2 * X₂ : v.valuationSubring) : F) ((ϖ ^ 2 * Y₂ : v.valuationSubring) : F)) :=
    fun hn ↦ hx hn.1
  -- the slope is `L = ϖ (Y₁ − Y₂) / u`
  set L : v.valuationSubring := ϖ * ((Y₁ - Y₂) * i) with hL
  have hℓ : W.slope ((ϖ * X₁ : v.valuationSubring) : F) ((ϖ ^ 2 * X₂ : v.valuationSubring) : F)
      ((ϖ ^ 2 * Y₁ : v.valuationSubring) : F) ((ϖ ^ 2 * Y₂ : v.valuationSubring) : F) = L := by
    rw [slope_of_X_ne hx, div_eq_iff (sub_ne_zero.2 hx), hL]
    push_cast at hi' ⊢
    linear_combination (-(ϖ : F) ^ 2 * ((Y₁ : F) - Y₂)) * hi'
  rw [Point.add_some hxy, some_notMem_nonsingularReduction_iff v hm₃ hm₄ hm₆, hℓ]
  set X₃ := L ^ 2 + (integralModel v.valuationSubring W).a₁ * L -
    (integralModel v.valuationSubring W).a₂ - ϖ * X₁ - ϖ ^ 2 * X₂ with hX₃
  have hdX₃ : ϖ ∣ X₃ := by
    rw [hX₃, hA₂, hL]
    exact ⟨ϖ * ((Y₁ - Y₂) * i) ^ 2 + (integralModel v.valuationSubring W).a₁ * ((Y₁ - Y₂) * i) -
      A₂ - X₁ - ϖ * X₂, by ring⟩
  have hx₃ : W.addX ((ϖ * X₁ : v.valuationSubring) : F) ((ϖ ^ 2 * X₂ : v.valuationSubring) : F)
      (L : F) = ((X₃ : v.valuationSubring) : F) := by
    rw [addX, ← coe_integralModel_a₁ v, ← coe_integralModel_a₂ v, hX₃]
    push_cast
    ring
  have hy₃ : W.addY ((ϖ * X₁ : v.valuationSubring) : F) ((ϖ ^ 2 * X₂ : v.valuationSubring) : F)
      ((ϖ ^ 2 * Y₁ : v.valuationSubring) : F) (L : F) =
        ((-(L * (X₃ - ϖ * X₁) + ϖ ^ 2 * Y₁) - (integralModel v.valuationSubring W).a₁ * X₃ -
          (integralModel v.valuationSubring W).a₃ : v.valuationSubring) : F) := by
    rw [addY, negAddY, hx₃, negY, ← coe_integralModel_a₁ v, ← coe_integralModel_a₃ v]
    push_cast
    ring
  rw [hx₃, hy₃, ← Valuation.mem_maximalIdeal_iff, ← Valuation.mem_maximalIdeal_iff,
    mem_maximalIdeal_iff_dvd hϖ, mem_maximalIdeal_iff_dvd hϖ]
  refine ⟨hdX₃, ?_⟩
  refine dvd_sub (dvd_sub (dvd_neg.2 (dvd_add ?_ ?_)) (hdX₃.mul_left _))
    ((mem_maximalIdeal_iff_dvd hϖ).1 hm₃)
  · exact (dvd_mul_right ϖ _).mul_right _
  · exact (dvd_pow_self ϖ two_ne_zero).mul_right _

/-- **Two points of the form `(ϖ² X, ϖ² Y)` do not add to a point of that form.** If they did,
all three would have singular reduction, and `x₁ + x₂ + x₃ = ℓ² + a₁ ℓ − a₂` would force first
`ϖ ∣ ℓ` and then `ϖ² ∣ a₂`. -/
private theorem add_notMem_farPoints {ϖ : v.valuationSubring}
    (hϖ : maximalIdeal v.valuationSubring = Ideal.span {ϖ})
    (hst : IsTateOddStage ϖ 0 (integralModel v.valuationSubring W)) {P Q : W.Point}
    (hP : P ∈ farPoints v ϖ) (hQ : Q ∈ farPoints v ϖ) : P + Q ∉ farPoints v ϖ := by
  intro hPQ
  obtain ⟨hp, hm₃, hm₄, hm₆, A₂, hA₂, hA₂'⟩ := stage_data v hϖ hst
  obtain ⟨⟨α₁, hα₁⟩, -⟩ := isTateOddStage_iff.1 hst
  have hPQb := notMem_of_mem_farPoints v hϖ hm₃ hm₄ hm₆ hPQ
  obtain ⟨x₁, y₁, h₁, rfl, ⟨X₁, rfl⟩, -⟩ := hP
  obtain ⟨x₂, y₂, h₂, rfl, ⟨X₂, rfl⟩, -⟩ := hQ
  obtain ⟨x₃, y₃, L, h₃, heq, -, -, -, he₁, -, -, -⟩ :=
    exists_chord_of_add_notMem_nonsingularReduction v hm₃ hm₄ hm₆ hPQb
  obtain ⟨x₃', y₃', h₃', he, ⟨X₃, rfl⟩, -⟩ := hPQ
  obtain rfl : x₃ = ϖ ^ 2 * X₃ :=
    Subtype.val_injective (Point.some.inj (heq.symm.trans he)).1
  rw [hα₁, hA₂] at he₁
  obtain ⟨L, rfl⟩ : ϖ ∣ L := hp.dvd_of_dvd_pow (n := 2)
    ⟨ϖ * X₁ + ϖ * X₂ + ϖ * X₃ - α₁ * L + A₂, by linear_combination he₁⟩
  exact hA₂' ⟨L ^ 2 + α₁ * L - X₁ - X₂ - X₃,
    mul_left_cancel₀ hp.ne_zero (by linear_combination -he₁)⟩

/-! ### The subgroup of points not of the form `(ϖ² X, ϖ² Y)` -/

/-- On the normal form of stage `1`, the points not of the form `(ϖ² X, ϖ² Y)`, namely `E₀(F)` and
the points reducing to the simple root of the residue cubic, form a subgroup of `W(F)`. -/
private def nearSubgroup {ϖ : v.valuationSubring}
    (hϖ : maximalIdeal v.valuationSubring = Ideal.span {ϖ})
    (hst : IsTateOddStage ϖ 0 (integralModel v.valuationSubring W)) : AddSubgroup W.Point where
  carrier := (farPoints v ϖ)ᶜ
  zero_mem' hF := by
    obtain ⟨-, hm₃, hm₄, hm₆, -⟩ := stage_data v hϖ hst
    exact notMem_of_mem_farPoints v hϖ hm₃ hm₄ hm₆ hF (zero_mem _)
  add_mem' {P Q} hP hQ hF := by
    obtain ⟨-, hm₃, hm₄, hm₆, -⟩ := stage_data v hϖ hst
    have h₃ : ϖ ^ 2 ∣ (integralModel v.valuationSubring W).a₃ := (isTateOddStage_iff.1 hst).2.2.2.1
    by_cases hP0 : P ∈ W.nonsingularReduction v <;> by_cases hQ0 : Q ∈ W.nonsingularReduction v
    · exact notMem_of_mem_farPoints v hϖ hm₃ hm₄ hm₆ hF (add_mem hP0 hQ0)
    · refine add_notMem_of_mem_farPoints v hϖ hst hQ0 hQ (neg_mem_farPoints v h₃ hF) ?_
      simpa using hP0
    · refine add_notMem_of_mem_farPoints v hϖ hst hP0 hP (neg_mem_farPoints v h₃ hF) ?_
      simpa [add_neg_cancel_comm] using hQ0
    · exact notMem_of_mem_farPoints v hϖ hm₃ hm₄ hm₆ hF
        (add_mem_of_notMem_farPoints v hϖ hst hP0 hQ0 hP hQ)
  neg_mem' {P} hP hF :=
    hP (by simpa using neg_mem_farPoints v (isTateOddStage_iff.1 hst).2.2.2.1 hF)

private theorem mem_nearSubgroup {ϖ : v.valuationSubring}
    (hϖ : maximalIdeal v.valuationSubring = Ideal.span {ϖ})
    (hst : IsTateOddStage ϖ 0 (integralModel v.valuationSubring W)) {P : W.Point} :
    P ∈ nearSubgroup v hϖ hst ↔ P ∉ farPoints v ϖ :=
  Iff.rfl

/-- Two points of the form `(ϖ² X, ϖ² Y)` add to a point not of that form. -/
private theorem add_mem_nearSubgroup {ϖ : v.valuationSubring}
    (hϖ : maximalIdeal v.valuationSubring = Ideal.span {ϖ})
    (hst : IsTateOddStage ϖ 0 (integralModel v.valuationSubring W)) {P Q : W.Point}
    (hP : P ∉ nearSubgroup v hϖ hst) (hQ : Q ∉ nearSubgroup v hϖ hst) :
    P + Q ∈ nearSubgroup v hϖ hst :=
  (mem_nearSubgroup v hϖ hst).2 <| add_notMem_farPoints v hϖ hst
    (not_not.1 ((mem_nearSubgroup v hϖ hst).not.1 hP))
    (not_not.1 ((mem_nearSubgroup v hϖ hst).not.1 hQ))

/-- `E₀(F)` lies in the subgroup of points not of the form `(ϖ² X, ϖ² Y)`. -/
private theorem le_nearSubgroup {ϖ : v.valuationSubring}
    (hϖ : maximalIdeal v.valuationSubring = Ideal.span {ϖ})
    (hst : IsTateOddStage ϖ 0 (integralModel v.valuationSubring W)) :
    W.nonsingularReduction v ≤ nearSubgroup v hϖ hst := fun _ hP ↦ by
  obtain ⟨-, hm₃, hm₄, hm₆, -⟩ := stage_data v hϖ hst
  exact (mem_nearSubgroup v hϖ hst).2 fun hF ↦ notMem_of_mem_farPoints v hϖ hm₃ hm₄ hm₆ hF hP

/-- Two points not of the form `(ϖ² X, ϖ² Y)` and outside `E₀(F)` add into `E₀(F)`. -/
private theorem add_mem_addSubgroupOf_nearSubgroup {ϖ : v.valuationSubring}
    (hϖ : maximalIdeal v.valuationSubring = Ideal.span {ϖ})
    (hst : IsTateOddStage ϖ 0 (integralModel v.valuationSubring W)) {P Q : nearSubgroup v hϖ hst}
    (hP : P ∉ (W.nonsingularReduction v).addSubgroupOf (nearSubgroup v hϖ hst))
    (hQ : Q ∉ (W.nonsingularReduction v).addSubgroupOf (nearSubgroup v hϖ hst)) :
    P + Q ∈ (W.nonsingularReduction v).addSubgroupOf (nearSubgroup v hϖ hst) := by
  rw [AddSubgroup.mem_addSubgroupOf] at hP hQ ⊢
  exact add_mem_of_notMem_farPoints v hϖ hst hP hQ ((mem_nearSubgroup v hϖ hst).1 P.2)
    ((mem_nearSubgroup v hϖ hst).1 Q.2)

/-- `E₀(F)` has index dividing `2` in the subgroup of points not of the form `(ϖ² X, ϖ² Y)`. -/
private theorem relIndex_nearSubgroup_dvd_two {ϖ : v.valuationSubring}
    (hϖ : maximalIdeal v.valuationSubring = Ideal.span {ϖ})
    (hst : IsTateOddStage ϖ 0 (integralModel v.valuationSubring W)) :
    (W.nonsingularReduction v).relIndex (nearSubgroup v hϖ hst) ∣ 2 :=
  AddSubgroup.index_dvd_two_of_add_mem fun _ _ ↦ add_mem_addSubgroupOf_nearSubgroup v hϖ hst

/-- The subgroup of points not of the form `(ϖ² X, ϖ² Y)` has index dividing `2`. -/
private theorem index_nearSubgroup_dvd_two {ϖ : v.valuationSubring}
    (hϖ : maximalIdeal v.valuationSubring = Ideal.span {ϖ})
    (hst : IsTateOddStage ϖ 0 (integralModel v.valuationSubring W)) :
    (nearSubgroup v hϖ hst).index ∣ 2 :=
  AddSubgroup.index_dvd_two_of_add_mem fun _ _ ↦ add_mem_nearSubgroup v hϖ hst

/-- If some point has the form `(ϖ² X, ϖ² Y)`, the subgroup of the other points has index `2`. -/
private theorem index_nearSubgroup_eq_two {ϖ : v.valuationSubring}
    (hϖ : maximalIdeal v.valuationSubring = Ideal.span {ϖ})
    (hst : IsTateOddStage ϖ 0 (integralModel v.valuationSubring W)) {P : W.Point}
    (hP : P ∈ farPoints v ϖ) : (nearSubgroup v hϖ hst).index = 2 :=
  AddSubgroup.index_eq_two_of_add_mem (fun _ _ ↦ add_mem_nearSubgroup v hϖ hst) (a := P)
    fun hK ↦ (mem_nearSubgroup v hϖ hst).1 hK hP

/-- If no point has the form `(ϖ² X, ϖ² Y)`, the subgroup of the other points is everything. -/
private theorem index_nearSubgroup_eq_one {ϖ : v.valuationSubring}
    (hϖ : maximalIdeal v.valuationSubring = Ideal.span {ϖ})
    (hst : IsTateOddStage ϖ 0 (integralModel v.valuationSubring W))
    (hF : ∀ P : W.Point, P ∉ farPoints v ϖ) : (nearSubgroup v hϖ hst).index = 1 :=
  AddSubgroup.index_eq_one.2 ((AddSubgroup.eq_top_iff' _).2 fun P ↦
    (mem_nearSubgroup v hϖ hst).2 (hF P))

/-- **On the normal form of stage `1`, some point reduces to the simple root of the residue cubic**,
when the valuation ring is Henselian. With `a₂ = ϖ A₂`, `a₄ = ϖ³ α₄` and `a₆ = ϖ⁴ α₆`, the simple
root `−A₂` of the reduction of `T³ + A₂ T² + ϖ α₄ T + ϖ α₆` lifts to a root `X`, and `(ϖ X, 0)` is a
point with singular reduction that is not of the form `(ϖ² X, ϖ² Y)`. -/
private theorem exists_notMem_notMem_farPoints [HenselianLocalRing v.valuationSubring]
    {ϖ : v.valuationSubring} (hϖ : maximalIdeal v.valuationSubring = Ideal.span {ϖ})
    (hst : IsTateOddStage ϖ 0 (integralModel v.valuationSubring W)) :
    ∃ P : W.Point, P ∉ W.nonsingularReduction v ∧ P ∉ farPoints v ϖ := by
  obtain ⟨hp, hm₃, hm₄, hm₆, A₂, hA₂, hA₂'⟩ := stage_data v hϖ hst
  obtain ⟨-, -, -, -, ⟨α₄, hα₄⟩, ⟨α₆, hα₆⟩⟩ := isTateOddStage_iff.1 hst
  set Wo := integralModel v.valuationSubring W
  set f : v.valuationSubring[X] := X ^ 3 + C A₂ * X ^ 2 + C (ϖ * α₄) * X + C (ϖ * α₆) with hf
  have hmon : f.Monic := by
    rw [hf]
    monicity!
  -- the derivative `3 z² + 2 A₂ z + ϖ α₄` is a unit at every `z ≡ −A₂`
  have hder (z : v.valuationSubring) :
      f.derivative.eval z = 3 * z ^ 2 + 2 * A₂ * z + ϖ * α₄ := by
    simp only [hf, derivative_add, derivative_X_pow, derivative_C_mul_X_pow, derivative_C_mul_X,
      derivative_C, eval_add, eval_mul, eval_C, eval_pow, eval_X, eval_zero]
    push_cast
    ring
  have hunit (z : v.valuationSubring) (hz : ϖ ∣ z + A₂) :
      IsUnit (3 * z ^ 2 + 2 * A₂ * z + ϖ * α₄) := by
    obtain ⟨m, hm⟩ := hz
    have hz' : 3 * z ^ 2 + 2 * A₂ * z + ϖ * α₄ =
        A₂ ^ 2 + ϖ * (3 * ϖ * m ^ 2 - 4 * A₂ * m + α₄) := by
      linear_combination (3 * z - A₂ + 3 * ϖ * m) * hm
    rw [hz']
    exact isUnit_add_of_dvd hϖ (((isUnit_iff_not_dvd hϖ).2 hA₂').pow 2) (dvd_mul_right ϖ _)
  have hf₀ : f.eval (-A₂) ∈ maximalIdeal v.valuationSubring := by
    rw [mem_maximalIdeal_iff_dvd hϖ]
    exact ⟨α₆ - α₄ * A₂, by
      simp only [hf, eval_add, eval_mul, eval_pow, eval_C, eval_X]
      ring⟩
  obtain ⟨X₀, hX₀, hX₀A⟩ :=
    HenselianLocalRing.is_henselian f hmon (-A₂) hf₀ (hder _ ▸ hunit _ (by simp))
  rw [sub_neg_eq_add, mem_maximalIdeal_iff_dvd hϖ] at hX₀A
  have hroot : X₀ ^ 3 + A₂ * X₀ ^ 2 + ϖ * α₄ * X₀ + ϖ * α₆ = 0 := by
    simpa [hf] using hX₀.eq_zero
  -- the point `(ϖ X₀, 0)`
  have hns : Wo.toAffine.Nonsingular (ϖ * X₀) 0 := by
    rw [nonsingular_iff']
    refine ⟨by rw [equation_iff, hA₂, hα₄, hα₆]; linear_combination (-ϖ ^ 3) * hroot, .inl ?_⟩
    rw [hA₂, hα₄]
    exact fun h0 ↦ mul_ne_zero (neg_ne_zero.2 (pow_ne_zero 2 hp.ne_zero)) (hunit X₀ hX₀A).ne_zero
      (by linear_combination h0)
  have hF : W.Nonsingular ((ϖ * X₀ : v.valuationSubring) : F) ((0 : v.valuationSubring) : F) :=
    (nonsingular_integralModel_iff v).1 hns
  refine ⟨Point.some _ _ hF, (some_coe_notMem_nonsingularReduction_iff v hm₃ hm₄ hm₆ hF).2
    ⟨(mem_maximalIdeal_iff_dvd hϖ).2 (dvd_mul_right ϖ X₀), zero_mem _⟩, ?_⟩
  rintro ⟨x, y, h, he, ⟨X, rfl⟩, -⟩
  have hx : ϖ * X₀ = ϖ ^ 2 * X := Subtype.val_injective (Point.some.inj he).1
  have hX₀ : ϖ ∣ X₀ := ⟨X, mul_left_cancel₀ hp.ne_zero (by rw [hx]; ring)⟩
  exact hA₂' (by simpa using dvd_sub hX₀A hX₀)

/-- `E₀(F)` has index `2` in the subgroup of points not of the form `(ϖ² X, ϖ² Y)`, when the
valuation ring is Henselian. -/
private theorem relIndex_nearSubgroup_eq_two [HenselianLocalRing v.valuationSubring]
    {ϖ : v.valuationSubring} (hϖ : maximalIdeal v.valuationSubring = Ideal.span {ϖ})
    (hst : IsTateOddStage ϖ 0 (integralModel v.valuationSubring W)) :
    (W.nonsingularReduction v).relIndex (nearSubgroup v hϖ hst) = 2 := by
  obtain ⟨P, hP, hPF⟩ := exists_notMem_notMem_farPoints v hϖ hst
  exact AddSubgroup.index_eq_two_of_add_mem
    (fun _ _ ↦ add_mem_addSubgroupOf_nearSubgroup v hϖ hst)
    (a := ⟨P, (mem_nearSubgroup v hϖ hst).2 hPF⟩) (by rwa [AddSubgroup.mem_addSubgroupOf])

/-! ### The index at the symbol `Iₙ*` -/

/-- **At the symbol `Iₙ*`, `[E(F) : E₀(F)]` divides `4`.** Here `ϖ` generates the maximal ideal and
Tate's algorithm stops at `Iₙ*` with `n ≥ 1` on the integral model. The points not of the form
`(ϖ² X, ϖ² Y)` form a subgroup containing `E₀(F)` with index dividing `2`, and of index dividing
`2` in `W(F)`. -/
theorem index_nonsingularReduction_dvd_four_of_isTateTerminal_IStar {ϖ : v.valuationSubring}
    (hϖ : maximalIdeal v.valuationSubring = Ideal.span {ϖ}) {n : ℕ}
    (h : (integralModel v.valuationSubring W).IsTateTerminal ϖ (.IStar (n + 1))) :
    (W.nonsingularReduction v).index ∣ 4 := by
  have hst := isTateOddStage_zero_of_isTateTerminal_IStar v h
  rw [← AddSubgroup.relIndex_mul_index (le_nearSubgroup v hϖ hst)]
  exact mul_dvd_mul (relIndex_nearSubgroup_dvd_two v hϖ hst) (index_nearSubgroup_dvd_two v hϖ hst)

/-- **At the symbol `I*_{2k+1}` with no rational root of the residue quadratic,
`[E(F) : E₀(F)]` divides `2`.** Here `ϖ` generates the maximal ideal, Tate's algorithm stops at
`I*_{2k+1}` on the integral model, and with `a₃ = ϖ^(k+2) A₃` and `a₆ = ϖ^(2k+4) A₆` the
quadratic `T² + A₃ T − A₆` of the last stage of the subprocedure has no root in the residue
field. -/
theorem index_nonsingularReduction_dvd_two_of_isTateTerminal_IStar_two_mul_add_one
    {ϖ : v.valuationSubring} (hϖ : maximalIdeal v.valuationSubring = Ideal.span {ϖ}) {k : ℕ}
    (h : (integralModel v.valuationSubring W).IsTateTerminal ϖ (.IStar (2 * k + 1)))
    {A₃ A₆ : v.valuationSubring} (h₃ : (integralModel v.valuationSubring W).a₃ = ϖ ^ (k + 2) * A₃)
    (h₆ : (integralModel v.valuationSubring W).a₆ = ϖ ^ (2 * k + 4) * A₆)
    (hroot : ∀ t : ResidueField v.valuationSubring,
      t ^ 2 + residue _ A₃ * t - residue _ A₆ ≠ 0) :
    (W.nonsingularReduction v).index ∣ 2 := by
  have hst := isTateOddStage_zero_of_isTateTerminal_IStar v h
  rw [← AddSubgroup.relIndex_mul_index (le_nearSubgroup v hϖ hst),
    index_nearSubgroup_eq_one v hϖ hst fun P hP ↦
      (exists_root_of_mem_farPoints_odd v hϖ h h₃ h₆ hP).elim hroot, mul_one]
  exact relIndex_nearSubgroup_dvd_two v hϖ hst

/-- **At the symbol `I*_{2k+1}` with no rational root of the residue quadratic,
`[E(F) : E₀(F)] = 2`**, when the valuation ring is Henselian, for instance complete. This is the
local index `c_v = 2` that Tate's algorithm reports at `I*_{2k+1}` in that case. Here `ϖ`
generates the maximal ideal, Tate's algorithm stops at `I*_{2k+1}` on the integral model, and with
`a₃ = ϖ^(k+2) A₃` and `a₆ = ϖ^(2k+4) A₆` the quadratic `T² + A₃ T − A₆` has no root in the residue
field. -/
theorem index_nonsingularReduction_eq_two_of_isTateTerminal_IStar_two_mul_add_one
    [HenselianLocalRing v.valuationSubring] {ϖ : v.valuationSubring}
    (hϖ : maximalIdeal v.valuationSubring = Ideal.span {ϖ}) {k : ℕ}
    (h : (integralModel v.valuationSubring W).IsTateTerminal ϖ (.IStar (2 * k + 1)))
    {A₃ A₆ : v.valuationSubring} (h₃ : (integralModel v.valuationSubring W).a₃ = ϖ ^ (k + 2) * A₃)
    (h₆ : (integralModel v.valuationSubring W).a₆ = ϖ ^ (2 * k + 4) * A₆)
    (hroot : ∀ t : ResidueField v.valuationSubring,
      t ^ 2 + residue _ A₃ * t - residue _ A₆ ≠ 0) :
    (W.nonsingularReduction v).index = 2 := by
  have hst := isTateOddStage_zero_of_isTateTerminal_IStar v h
  rw [← AddSubgroup.relIndex_mul_index (le_nearSubgroup v hϖ hst),
    index_nearSubgroup_eq_one v hϖ hst fun P hP ↦
      (exists_root_of_mem_farPoints_odd v hϖ h h₃ h₆ hP).elim hroot, mul_one]
  exact relIndex_nearSubgroup_eq_two v hϖ hst

/-- **At the symbol `I*_{2k+1}` with a rational root of the residue quadratic,
`[E(F) : E₀(F)] = 4`**, when the valuation ring is Henselian, for instance complete. This is the
local index `c_v = 4` that Tate's algorithm reports at `I*_{2k+1}` in that case. Here `ϖ`
generates the maximal ideal, Tate's algorithm stops at `I*_{2k+1}` on the integral model, and with
`a₃ = ϖ^(k+2) A₃` and `a₆ = ϖ^(2k+4) A₆` the quadratic `T² + A₃ T − A₆` has a root `t` in the
residue field. -/
theorem index_nonsingularReduction_eq_four_of_isTateTerminal_IStar_two_mul_add_one
    [HenselianLocalRing v.valuationSubring] {ϖ : v.valuationSubring}
    (hϖ : maximalIdeal v.valuationSubring = Ideal.span {ϖ}) {k : ℕ}
    (h : (integralModel v.valuationSubring W).IsTateTerminal ϖ (.IStar (2 * k + 1)))
    {A₃ A₆ : v.valuationSubring} (h₃ : (integralModel v.valuationSubring W).a₃ = ϖ ^ (k + 2) * A₃)
    (h₆ : (integralModel v.valuationSubring W).a₆ = ϖ ^ (2 * k + 4) * A₆)
    {t : ResidueField v.valuationSubring} (ht : t ^ 2 + residue _ A₃ * t - residue _ A₆ = 0) :
    (W.nonsingularReduction v).index = 4 := by
  have hst := isTateOddStage_zero_of_isTateTerminal_IStar v h
  obtain ⟨P, hP⟩ := exists_mem_farPoints_odd v hϖ h h₃ h₆ ht
  rw [← AddSubgroup.relIndex_mul_index (le_nearSubgroup v hϖ hst),
    relIndex_nearSubgroup_eq_two v hϖ hst, index_nearSubgroup_eq_two v hϖ hst hP]

/-- **At the symbol `I*_{2k+2}` with no rational root of the residue quadratic,
`[E(F) : E₀(F)]` divides `2`.** Here `ϖ` generates the maximal ideal, Tate's algorithm stops at
`I*_{2k+2}` on the integral model, and with `a₂ = ϖ A₂`, `a₄ = ϖ^(k+3) A₄` and
`a₆ = ϖ^(2k+5) A₆` the quadratic `A₂ T² + A₄ T + A₆` of the last stage of the subprocedure has no
root in the residue field. -/
theorem index_nonsingularReduction_dvd_two_of_isTateTerminal_IStar_two_mul_add_two
    {ϖ : v.valuationSubring} (hϖ : maximalIdeal v.valuationSubring = Ideal.span {ϖ}) {k : ℕ}
    (h : (integralModel v.valuationSubring W).IsTateTerminal ϖ (.IStar (2 * k + 2)))
    {A₂ A₄ A₆ : v.valuationSubring} (h₂ : (integralModel v.valuationSubring W).a₂ = ϖ * A₂)
    (h₄ : (integralModel v.valuationSubring W).a₄ = ϖ ^ (k + 3) * A₄)
    (h₆ : (integralModel v.valuationSubring W).a₆ = ϖ ^ (2 * k + 5) * A₆)
    (hroot : ∀ t : ResidueField v.valuationSubring,
      residue _ A₂ * t ^ 2 + residue _ A₄ * t + residue _ A₆ ≠ 0) :
    (W.nonsingularReduction v).index ∣ 2 := by
  have hst := isTateOddStage_zero_of_isTateTerminal_IStar v h
  rw [← AddSubgroup.relIndex_mul_index (le_nearSubgroup v hϖ hst),
    index_nearSubgroup_eq_one v hϖ hst fun P hP ↦
      (exists_root_of_mem_farPoints_even v hϖ h h₂ h₄ h₆ hP).elim hroot, mul_one]
  exact relIndex_nearSubgroup_dvd_two v hϖ hst

/-- **At the symbol `I*_{2k+2}` with no rational root of the residue quadratic,
`[E(F) : E₀(F)] = 2`**, when the valuation ring is Henselian, for instance complete. This is the
local index `c_v = 2` that Tate's algorithm reports at `I*_{2k+2}` in that case. Here `ϖ`
generates the maximal ideal, Tate's algorithm stops at `I*_{2k+2}` on the integral model, and with
`a₂ = ϖ A₂`, `a₄ = ϖ^(k+3) A₄` and `a₆ = ϖ^(2k+5) A₆` the quadratic `A₂ T² + A₄ T + A₆` has no
root in the residue field. -/
theorem index_nonsingularReduction_eq_two_of_isTateTerminal_IStar_two_mul_add_two
    [HenselianLocalRing v.valuationSubring] {ϖ : v.valuationSubring}
    (hϖ : maximalIdeal v.valuationSubring = Ideal.span {ϖ}) {k : ℕ}
    (h : (integralModel v.valuationSubring W).IsTateTerminal ϖ (.IStar (2 * k + 2)))
    {A₂ A₄ A₆ : v.valuationSubring} (h₂ : (integralModel v.valuationSubring W).a₂ = ϖ * A₂)
    (h₄ : (integralModel v.valuationSubring W).a₄ = ϖ ^ (k + 3) * A₄)
    (h₆ : (integralModel v.valuationSubring W).a₆ = ϖ ^ (2 * k + 5) * A₆)
    (hroot : ∀ t : ResidueField v.valuationSubring,
      residue _ A₂ * t ^ 2 + residue _ A₄ * t + residue _ A₆ ≠ 0) :
    (W.nonsingularReduction v).index = 2 := by
  have hst := isTateOddStage_zero_of_isTateTerminal_IStar v h
  rw [← AddSubgroup.relIndex_mul_index (le_nearSubgroup v hϖ hst),
    index_nearSubgroup_eq_one v hϖ hst fun P hP ↦
      (exists_root_of_mem_farPoints_even v hϖ h h₂ h₄ h₆ hP).elim hroot, mul_one]
  exact relIndex_nearSubgroup_eq_two v hϖ hst

/-- **At the symbol `I*_{2k+2}` with a rational root of the residue quadratic,
`[E(F) : E₀(F)] = 4`**, when the valuation ring is Henselian, for instance complete. This is the
local index `c_v = 4` that Tate's algorithm reports at `I*_{2k+2}` in that case. Here `ϖ`
generates the maximal ideal, Tate's algorithm stops at `I*_{2k+2}` on the integral model, and with
`a₂ = ϖ A₂`, `a₄ = ϖ^(k+3) A₄` and `a₆ = ϖ^(2k+5) A₆` the quadratic `A₂ T² + A₄ T + A₆` has a root
`t` in the residue field. -/
theorem index_nonsingularReduction_eq_four_of_isTateTerminal_IStar_two_mul_add_two
    [HenselianLocalRing v.valuationSubring] {ϖ : v.valuationSubring}
    (hϖ : maximalIdeal v.valuationSubring = Ideal.span {ϖ}) {k : ℕ}
    (h : (integralModel v.valuationSubring W).IsTateTerminal ϖ (.IStar (2 * k + 2)))
    {A₂ A₄ A₆ : v.valuationSubring} (h₂ : (integralModel v.valuationSubring W).a₂ = ϖ * A₂)
    (h₄ : (integralModel v.valuationSubring W).a₄ = ϖ ^ (k + 3) * A₄)
    (h₆ : (integralModel v.valuationSubring W).a₆ = ϖ ^ (2 * k + 5) * A₆)
    {t : ResidueField v.valuationSubring}
    (ht : residue _ A₂ * t ^ 2 + residue _ A₄ * t + residue _ A₆ = 0) :
    (W.nonsingularReduction v).index = 4 := by
  have hst := isTateOddStage_zero_of_isTateTerminal_IStar v h
  obtain ⟨P, hP⟩ := exists_mem_farPoints_even v hϖ h h₂ h₄ h₆ ht
  rw [← AddSubgroup.relIndex_mul_index (le_nearSubgroup v hϖ hst),
    relIndex_nearSubgroup_eq_two v hϖ hst, index_nearSubgroup_eq_two v hϖ hst hP]

end Affine

end WeierstrassCurve

end

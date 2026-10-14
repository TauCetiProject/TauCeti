/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Henselian
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.SingularReduction
public import TauCeti.AlgebraicGeometry.EllipticCurve.TateAlgorithm.Terminal
-- Proof-only: the chord through two points with singular reduction.
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.IndexTwo
-- Proof-only: `E₀(F) = W(F)` when no integral solution is divisible by `ϖ`.
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.StarredReduction
-- Proof-only: index three from three covering cosets.
import TauCeti.GroupTheory.Index.Three
-- Proof-only: units and the maximal ideal of a local ring with principal maximal ideal.
import TauCeti.RingTheory.LocalRing.MaximalIdeal.Generator
-- Proof-only: a root of a quadratic with unit discriminant is simple.
import TauCeti.RingTheory.LocalRing.QuadraticDoubleRoot

/-!
# Points with singular reduction at the symbol `IV`

Let `v` be a valuation on a field `F`, with valuation ring `O`, maximal ideal `𝔪 = (ϖ)` and
residue field `k`, and let `W` be a Weierstrass curve over `F` with an integral model `W_O` over
`O`. The points with nonsingular reduction form the subgroup `E₀(F)` of `W(F)`
(`WeierstrassCurve.Affine.nonsingularReduction`). When `F` is complete for a discrete valuation
with perfect residue field and the equation is minimal, the index `[E(F) : E₀(F)]` is the local
index `c_v` that Tate's algorithm computes (Silverman, *Advanced Topics*, IV.9, Table 4.1). This
file computes the index at the reduction symbol `IV`, where Tate's algorithm stops when
`ϖ ∣ b₂`, `ϖ ∣ a₃`, `ϖ ∣ a₄`, `ϖ² ∣ a₆`, `ϖ³ ∣ b₈` and `ϖ³ ∤ b₆`. Writing `a₃ = ϖ A₃` and
`a₆ = ϖ² A₆`, the algorithm reports `c_v = 3` when the residue quadratic `T² + A₃ T − A₆` has a
root in `k`, and `c_v = 1` otherwise. The last stopping condition says that this quadratic has
the unit discriminant `A₃² + 4 A₆`, so its roots are distinct.

The reduced curve has a cusp at the origin, whose tangent cone is the double line `y = s x`, for
`s` a lift of the double root of the tangent quadratic `T² + a₁ T − a₂`. Such a lift exists over
any residue field: `s = −a₁ / 2` when `2` is a unit, and `s = a₄ / a₃` when `a₃ / ϖ` is a unit,
which is the case when `2 ∈ 𝔪` because the discriminant `A₃² + 4 A₆` is a unit. The condition
`ϖ³ ∣ b₈` then says that `a₄ / ϖ ≡ s a₃ / ϖ` modulo `𝔪`.

A point with singular reduction is `(ϖ X, ϖ Y)` with `X, Y ∈ O`, and the Weierstrass equation
divided by `ϖ²` says that `Y − s X` reduces to a root of the residue quadratic. Negation exchanges
the two roots. The slope `ℓ` of the chord through two points `P` and `Q` with singular reduction,
when `P + Q` also has singular reduction, is integral with `ℓ ≡ s` modulo `𝔪`, so
`Y₁ − Y₂ = ℓ (X₁ − X₂)` shows that `P` and `Q` reduce to the same root. The tangent at a point
with singular reduction has slope `≡ s` as well, its denominator being `ϖ` times the unit
`2 (Y − s X) + A₃` up to `𝔪`, so `2 P` again has singular reduction. Hence, if `P` has singular
reduction, the three cosets of `E₀(F)` are `E₀(F)`, `P + E₀(F)` and `−P + E₀(F)`, and the index
is `3`. Over a Henselian valuation ring a root `t` of the residue quadratic lifts to a root `Y` of
`T² + A₃ T − A₆`, and `(0, ϖ Y)` is a point with singular reduction.

No discreteness, completeness, minimality or perfectness is assumed. Only the existence of a point
with singular reduction uses the Henselian hypothesis.

## Main results

* `WeierstrassCurve.dvd_residueQuadratic_of_equation`: over a domain, with `a₃ = ϖ A₃`,
  `a₄ = ϖ A₄`, `a₆ = ϖ² A₆` and `s` a lift of the double root of the tangent quadratic with
  `A₄ ≡ s A₃`, a solution `(ϖ X, ϖ Y)` makes `Y − s X` a root of `T² + A₃ T − A₆` modulo `ϖ`.
* `WeierstrassCurve.Affine.nonsingularReduction_eq_top_of_isTateTerminal_IV`: at `IV`, if the
  residue quadratic has no root in the residue field, every point has nonsingular reduction.
* `WeierstrassCurve.Affine.index_nonsingularReduction_eq_three_of_isTateTerminal_IV_of_notMem`:
  at `IV`, if some point has singular reduction, then `[E(F) : E₀(F)] = 3`.
* `WeierstrassCurve.Affine.index_nonsingularReduction_dvd_three_of_isTateTerminal_IV`: at `IV`,
  the index divides `3`.
* `WeierstrassCurve.Affine.exists_notMem_nonsingularReduction_of_isTateTerminal_IV` and
  `WeierstrassCurve.Affine.index_nonsingularReduction_eq_three_of_isTateTerminal_IV`: at `IV`
  over a Henselian valuation ring, if the residue quadratic has a root in the residue field, some
  point has singular reduction, and `[E(F) : E₀(F)] = 3`.

## References

* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, GTM 151, IV.9.
* J. Tate, *Algorithm for determining the type of a singular fibre in an elliptic pencil*, in
  *Modular Functions of One Variable IV*, LNM 476 (1975), 33–52.
-/

public section

open IsLocalRing Polynomial
open TauCeti.IsLocalRing (isUnit_iff_not_dvd isUnit_two_mul_add_of_isUnit_sq_add_four_mul
  mem_maximalIdeal_iff_dvd)

namespace WeierstrassCurve

/-- On an equation with `a₃ = ϖ A₃`, `a₄ = ϖ A₄` and `a₆ = ϖ² A₆`, let `s` lift a double root of
the tangent quadratic modulo `ϖ`, with `A₄ ≡ s A₃`. Then a solution `(ϖ X, ϖ Y)` makes `Y − s X` a
root of the residue quadratic `T² + A₃ T − A₆` modulo `ϖ`. -/
theorem dvd_residueQuadratic_of_equation {R : Type*} [CommRing R] [IsDomain R]
    (W : WeierstrassCurve R) {ϖ A₃ A₄ A₆ s : R} (hϖ : ϖ ≠ 0) (h₃ : W.a₃ = ϖ * A₃)
    (h₄ : W.a₄ = ϖ * A₄) (h₆ : W.a₆ = ϖ ^ 2 * A₆) (hs₁ : ϖ ∣ 2 * s + W.a₁)
    (hs₂ : ϖ ∣ s ^ 2 + W.a₁ * s - W.a₂) (hs₄ : ϖ ∣ A₄ - s * A₃) {X Y : R}
    (h : W.toAffine.Equation (ϖ * X) (ϖ * Y)) :
    ϖ ∣ (Y - s * X) ^ 2 + A₃ * (Y - s * X) - A₆ := by
  rw [Affine.equation_iff, h₃, h₄, h₆] at h
  -- the Weierstrass equation divided by `ϖ²`
  have hG : Y ^ 2 + W.a₁ * X * Y + A₃ * Y - ϖ * X ^ 3 - W.a₂ * X ^ 2 - A₄ * X - A₆ = 0 := by
    refine (mul_eq_zero.mp ?_).resolve_left (pow_ne_zero 2 hϖ)
    linear_combination h
  obtain ⟨c₁, hc₁⟩ := hs₁
  obtain ⟨c₂, hc₂⟩ := hs₂
  obtain ⟨c₄, hc₄⟩ := hs₄
  exact ⟨X ^ 3 - c₁ * X * Y + (s * c₁ - c₂) * X ^ 2 + c₄ * X, by
    linear_combination hG - X * Y * hc₁ + s * X ^ 2 * hc₁ - X ^ 2 * hc₂ + X * hc₄⟩

namespace Affine

variable {F Γ₀ : Type*} [Field F] [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation F Γ₀)
  {W : Affine F} [IsIntegral v.valuationSubring W]

/-- The valuation ring of `v`. -/
local notation "𝒪" => v.valuationSubring

/-! ### Numerals -/

/-- A numeral of the valuation ring, coerced to `F`, is the numeral of `F`. -/
private theorem coe_ofNat (n : ℕ) [n.AtLeastTwo] :
    ((ofNat(n) : v.valuationSubring) : F) = ofNat(n) := by
  simpa using map_ofNat (algebraMap v.valuationSubring F) n

/-! ### The data of the stopping test -/

/-- The stopping test for `IV`, with `a₃ = ϖ A₃`, `a₄ = ϖ A₄` and `a₆ = ϖ² A₆`: the reduction is
singular at the origin, `ϖ` is prime, the discriminant `A₃² + 4 A₆` of the residue quadratic is a
unit, and the double root of the tangent quadratic `T² + a₁ T − a₂` lifts to some `s` with
`A₄ ≡ s A₃` modulo `ϖ`. -/
private theorem isTateTerminal_IV_data {ϖ : v.valuationSubring}
    (hϖ : maximalIdeal v.valuationSubring = Ideal.span {ϖ})
    (h : (integralModel v.valuationSubring W).IsTateTerminal ϖ .IV)
    {A₃ A₄ A₆ : v.valuationSubring} (h₃ : (integralModel v.valuationSubring W).a₃ = ϖ * A₃)
    (h₄ : (integralModel v.valuationSubring W).a₄ = ϖ * A₄)
    (h₆ : (integralModel v.valuationSubring W).a₆ = ϖ ^ 2 * A₆) :
    (integralModel v.valuationSubring W).a₃ ∈ maximalIdeal v.valuationSubring ∧
      (integralModel v.valuationSubring W).a₄ ∈ maximalIdeal v.valuationSubring ∧
      (integralModel v.valuationSubring W).a₆ ∈ maximalIdeal v.valuationSubring ∧
      Prime ϖ ∧ IsUnit (A₃ ^ 2 + 4 * A₆) ∧ ∃ s : v.valuationSubring,
      ϖ ∣ 2 * s + (integralModel v.valuationSubring W).a₁ ∧
      ϖ ∣ s ^ 2 + (integralModel v.valuationSubring W).a₁ * s -
        (integralModel v.valuationSubring W).a₂ ∧ ϖ ∣ A₄ - s * A₃ := by
  set Wo := integralModel 𝒪 W
  obtain ⟨⟨d, hd⟩, -, -, -, ⟨c, hc⟩, hb₆⟩ := isTateTerminal_IV.1 h
  rw [b₂] at hd
  have hϖ0 : ϖ ≠ 0 := h.ne_zero (by simp)
  have hp : Prime ϖ :=
    (Ideal.span_singleton_prime hϖ0).mp (hϖ ▸ (maximalIdeal.isMaximal 𝒪).isPrime)
  -- `b₆ = ϖ² (A₃² + 4 A₆)`
  have hD : IsUnit (A₃ ^ 2 + 4 * A₆) := by
    rw [isUnit_iff_not_dvd hϖ]
    rintro ⟨e, he⟩
    exact hb₆ ⟨e, by rw [b₆, h₃, h₆]; linear_combination ϖ ^ 2 * he⟩
  -- `b₈ = b₂ a₆ − ϖ² (a₁ A₃ A₄ − a₂ A₃² + A₄²)`
  have hE : ϖ ∣ Wo.a₁ * A₃ * A₄ - Wo.a₂ * A₃ ^ 2 + A₄ ^ 2 := by
    rw [b₈, h₃, h₄, h₆] at hc
    refine (mul_dvd_mul_iff_left (pow_ne_zero 2 hϖ0)).mp ⟨d * A₆ - c, ?_⟩
    linear_combination ϖ ^ 2 * A₆ * hd - hc
  -- a root of the tangent quadratic modulo `ϖ`
  obtain ⟨s, hs₂⟩ : ∃ s : 𝒪, ϖ ∣ s ^ 2 + Wo.a₁ * s - Wo.a₂ := by
    by_cases hA₃ : IsUnit A₃
    · -- `s = A₄ / A₃`
      obtain ⟨i, hi⟩ := hA₃.exists_right_inv
      obtain ⟨e, he⟩ := hE
      exact ⟨A₄ * i, e * i ^ 2, by
        linear_combination i ^ 2 * he - (Wo.a₁ * A₄ * i - Wo.a₂ * (1 + A₃ * i)) * hi⟩
    · -- `ϖ ∣ A₃`, so `4 A₆` and hence `2` are units: `s = −a₁ / 2`
      rw [isUnit_iff_not_dvd hϖ, not_not] at hA₃
      have h4 : IsUnit (2 * (2 * A₆)) := by
        rw [isUnit_iff_not_dvd hϖ] at hD ⊢
        exact fun h4 ↦ hD (by
          rw [show A₃ ^ 2 + 4 * A₆ = A₃ * A₃ + 2 * (2 * A₆) by ring]
          exact dvd_add (hA₃.mul_right A₃) h4)
      obtain ⟨i, hi⟩ := (isUnit_of_mul_isUnit_left h4).exists_right_inv
      exact ⟨-Wo.a₁ * i, -d * i ^ 2, by
        linear_combination -(i ^ 2) * hd + (Wo.a₁ ^ 2 * i + Wo.a₂ * (2 * i + 1)) * hi⟩
  -- the root is double, since the discriminant of the tangent quadratic is `b₂`
  have hs₁ : ϖ ∣ 2 * s + Wo.a₁ := hp.dvd_of_dvd_pow (n := 2) <| by
    obtain ⟨e, he⟩ := hs₂
    exact ⟨4 * e + d, by linear_combination 4 * he + hd⟩
  refine ⟨(mem_maximalIdeal_iff_dvd hϖ).2 ⟨A₃, h₃⟩, (mem_maximalIdeal_iff_dvd hϖ).2 ⟨A₄, h₄⟩,
    (mem_maximalIdeal_iff_dvd hϖ).2 ⟨ϖ * A₆, by rw [h₆]; ring⟩, hp, hD, s, hs₁, hs₂,
    hp.dvd_of_dvd_pow (n := 2) ?_⟩
  -- `(A₄ − s A₃)² ≡ a₁ A₃ A₄ − a₂ A₃² + A₄²`
  obtain ⟨e₁, he₁⟩ := hs₁
  obtain ⟨e₂, he₂⟩ := hs₂
  obtain ⟨e, he⟩ := hE
  exact ⟨e - e₁ * A₃ * A₄ + (s * e₁ - e₂) * A₃ ^ 2, by
    linear_combination he - A₃ * A₄ * he₁ + s * A₃ ^ 2 * he₁ - A₃ ^ 2 * he₂⟩

/-! ### Points with singular reduction -/

variable [DecidableEq F]

/-- **A point with singular reduction is `(ϖ X, ϖ Y)`** with `X` and `Y` integral, when the
reduction is singular at the origin and `ϖ` generates the maximal ideal. -/
private theorem exists_eq_some_of_notMem {ϖ : v.valuationSubring}
    (hϖ : maximalIdeal v.valuationSubring = Ideal.span {ϖ})
    (h₃ : (integralModel v.valuationSubring W).a₃ ∈ maximalIdeal v.valuationSubring)
    (h₄ : (integralModel v.valuationSubring W).a₄ ∈ maximalIdeal v.valuationSubring)
    (h₆ : (integralModel v.valuationSubring W).a₆ ∈ maximalIdeal v.valuationSubring)
    {P : W.Point} (hP : P ∉ W.nonsingularReduction v) :
    ∃ (X Y : v.valuationSubring)
      (h : W.Nonsingular ((ϖ * X : v.valuationSubring) : F) ((ϖ * Y : v.valuationSubring) : F)),
      P = .some _ _ h := by
  obtain ⟨x, y, hxy, rfl, hx, hy⟩ := exists_eq_some_of_notMem_nonsingularReduction v h₃ h₄ h₆ hP
  obtain ⟨X, rfl⟩ := (mem_maximalIdeal_iff_dvd hϖ).1 hx
  obtain ⟨Y, rfl⟩ := (mem_maximalIdeal_iff_dvd hϖ).1 hy
  exact ⟨X, Y, hxy, rfl⟩

/-- **If two points and their sum all have singular reduction, they reduce to the same root of the
residue quadratic.** Here `P = (ϖ X₁, ϖ Y₁)` and `Q = (ϖ X₂, ϖ Y₂)`, and `s` lifts the double root
of the tangent quadratic: the slope `ℓ` of the chord is integral with `ℓ ≡ s`, and
`Y₁ − Y₂ = ℓ (X₁ − X₂)`. -/
private theorem dvd_sub_of_add_notMem {ϖ : v.valuationSubring}
    (hϖ : maximalIdeal v.valuationSubring = Ideal.span {ϖ}) (hp : Prime ϖ)
    (h₃ : (integralModel v.valuationSubring W).a₃ ∈ maximalIdeal v.valuationSubring)
    (h₄ : (integralModel v.valuationSubring W).a₄ ∈ maximalIdeal v.valuationSubring)
    (h₆ : (integralModel v.valuationSubring W).a₆ ∈ maximalIdeal v.valuationSubring)
    {s : v.valuationSubring} (hs₁ : ϖ ∣ 2 * s + (integralModel v.valuationSubring W).a₁)
    (hs₂ : ϖ ∣ s ^ 2 + (integralModel v.valuationSubring W).a₁ * s -
      (integralModel v.valuationSubring W).a₂)
    {X₁ Y₁ X₂ Y₂ : v.valuationSubring}
    (h₁ : W.Nonsingular ((ϖ * X₁ : v.valuationSubring) : F) ((ϖ * Y₁ : v.valuationSubring) : F))
    (h₂ : W.Nonsingular ((ϖ * X₂ : v.valuationSubring) : F) ((ϖ * Y₂ : v.valuationSubring) : F))
    (h : Point.some _ _ h₁ + Point.some _ _ h₂ ∉ W.nonsingularReduction v) :
    ϖ ∣ (Y₁ - s * X₁) - (Y₂ - s * X₂) := by
  by_cases hX : X₁ = X₂
  · -- `P + Q ≠ 0`, so `P = Q`
    subst hX
    obtain hY | hY := Y_eq_of_X_eq h₁.1 h₂.1 rfl
    · rw [mul_left_cancel₀ hp.ne_zero (Subtype.val_injective hY), sub_self]
      exact dvd_zero ϖ
    · exact absurd (by rw [Point.add_of_Y_eq rfl hY]; exact zero_mem _) h
  have hx : ((ϖ * X₁ : 𝒪) : F) ≠ ((ϖ * X₂ : 𝒪) : F) :=
    fun he ↦ hX (mul_left_cancel₀ hp.ne_zero (Subtype.val_injective he))
  -- the chord has an integral slope `ℓ` with `ℓ² + a₁ ℓ − a₂ ∈ 𝔪`
  have hns {X Y : 𝒪} (hXY : W.Nonsingular ((ϖ * X : 𝒪) : F) ((ϖ * Y : 𝒪) : F)) :
      Point.some _ _ hXY ∉ W.nonsingularReduction v :=
    (some_coe_notMem_nonsingularReduction_iff v h₃ h₄ h₆ hXY).2
      ⟨(mem_maximalIdeal_iff_dvd hϖ).2 (dvd_mul_right ϖ X),
        (mem_maximalIdeal_iff_dvd hϖ).2 (dvd_mul_right ϖ Y)⟩
  obtain ⟨L, -, hℓ, -, hm, -⟩ :=
    exists_slope_of_notMem_nonsingularReduction v h₃ h₄ h₆ (hns h₁) (hns h₂) h
  -- `ℓ (X₁ − X₂) = Y₁ − Y₂`
  have hslope : L * (X₁ - X₂) = Y₁ - Y₂ := by
    have hℓ' : (L : F) * (((ϖ * X₁ : 𝒪) : F) - ((ϖ * X₂ : 𝒪) : F)) =
        ((ϖ * Y₁ : 𝒪) : F) - ((ϖ * Y₂ : 𝒪) : F) := by
      rw [hℓ, slope_of_X_ne hx]
      exact div_mul_cancel₀ _ (sub_ne_zero.2 hx)
    refine mul_left_cancel₀ hp.ne_zero (Subtype.val_injective ?_)
    push_cast at hℓ' ⊢
    linear_combination hℓ'
  -- so `(ℓ − s)² ≡ 0`
  have hL : ϖ ∣ L - s := hp.dvd_of_dvd_pow (n := 2) <| by
    obtain ⟨c₁, hc₁⟩ := hs₁
    obtain ⟨c₂, hc₂⟩ := hs₂
    obtain ⟨c, hc⟩ := (mem_maximalIdeal_iff_dvd hϖ).1 hm
    exact ⟨c - c₂ - c₁ * (L - s), by linear_combination hc - hc₂ - (L - s) * hc₁⟩
  rw [show Y₁ - s * X₁ - (Y₂ - s * X₂) = (L - s) * (X₁ - X₂) by linear_combination -hslope]
  exact hL.mul_right _

/-- **The tangent at a point with singular reduction has integral slope `≡ s`.** Here
`P = (ϖ X, ϖ Y)`, and `s` lifts the double root of the tangent quadratic with `A₄ ≡ s A₃`. The
denominator `2 y + a₁ x + a₃` of the slope is `ϖ` times `2 Y + a₁ X + A₃ ≡ 2 (Y − s X) + A₃`, a
unit since `Y − s X` is a simple root of the residue quadratic, and its numerator
`3 x² + 2 a₂ x + a₄ − a₁ y` is `ϖ` times a lift of `s (2 Y + a₁ X + A₃)`. -/
private theorem exists_slope_self_eq {ϖ : v.valuationSubring}
    (hϖ : maximalIdeal v.valuationSubring = Ideal.span {ϖ}) (hp : Prime ϖ)
    {A₃ A₄ A₆ : v.valuationSubring} (h₃ : (integralModel v.valuationSubring W).a₃ = ϖ * A₃)
    (h₄ : (integralModel v.valuationSubring W).a₄ = ϖ * A₄)
    (h₆ : (integralModel v.valuationSubring W).a₆ = ϖ ^ 2 * A₆) (hD : IsUnit (A₃ ^ 2 + 4 * A₆))
    {s : v.valuationSubring} (hs₁ : ϖ ∣ 2 * s + (integralModel v.valuationSubring W).a₁)
    (hs₂ : ϖ ∣ s ^ 2 + (integralModel v.valuationSubring W).a₁ * s -
      (integralModel v.valuationSubring W).a₂) (hs₄ : ϖ ∣ A₄ - s * A₃)
    {X Y : v.valuationSubring}
    (h : W.Nonsingular ((ϖ * X : v.valuationSubring) : F) ((ϖ * Y : v.valuationSubring) : F)) :
    ((ϖ * Y : 𝒪) : F) ≠ W.negY ((ϖ * X : 𝒪) : F) ((ϖ * Y : 𝒪) : F) ∧ ∃ L : 𝒪,
      W.slope ((ϖ * X : 𝒪) : F) ((ϖ * X : 𝒪) : F) ((ϖ * Y : 𝒪) : F) ((ϖ * Y : 𝒪) : F) = L ∧
        ϖ ∣ L - s := by
  -- `Y − s X` is a root of the residue quadratic, so `u = 2 Y + a₁ X + A₃` is a unit
  have hq := (integralModel 𝒪 W).dvd_residueQuadratic_of_equation hp.ne_zero h₃ h₄ h₆ hs₁ hs₂ hs₄
    ((equation_integralModel_iff v).2 h.1)
  set u := 2 * Y + (integralModel 𝒪 W).a₁ * X + A₃ with hu_def
  have hu : IsUnit u := by
    have ht :=
      isUnit_two_mul_add_of_isUnit_sq_add_four_mul hD ((mem_maximalIdeal_iff_dvd hϖ).2 hq)
    rw [← residue_ne_zero_iff_isUnit] at ht ⊢
    have hs : (2 * s + (integralModel 𝒪 W).a₁) * X ∈ maximalIdeal 𝒪 :=
      (mem_maximalIdeal_iff_dvd hϖ).2 (hs₁.mul_right X)
    rwa [show u = 2 * (Y - s * X) + A₃ + (2 * s + (integralModel 𝒪 W).a₁) * X by
      rw [hu_def]; ring, map_add, (residue_eq_zero_iff _).2 hs, add_zero]
  -- `y − (−y − a₁ x − a₃) = ϖ u ≠ 0`
  have hden : ((ϖ * Y : 𝒪) : F) - W.negY ((ϖ * X : 𝒪) : F) ((ϖ * Y : 𝒪) : F) =
      ((ϖ * u : 𝒪) : F) := by
    rw [negY, ← coe_integralModel_a₁ v, ← coe_integralModel_a₃ v, h₃, hu_def]
    push_cast [coe_ofNat v]
    ring
  have hy : ((ϖ * Y : 𝒪) : F) ≠ W.negY ((ϖ * X : 𝒪) : F) ((ϖ * Y : 𝒪) : F) := fun he ↦
    mul_ne_zero hp.ne_zero hu.ne_zero
      (Subtype.val_injective (by rw [← hden, ← he, sub_self, ZeroMemClass.coe_zero]))
  -- the slope is `ℓ = N / u` with `N = 3 ϖ X² + 2 a₂ X + A₄ − a₁ Y`
  obtain ⟨i, hi⟩ := hu.exists_right_inv
  refine ⟨hy, (3 * ϖ * X ^ 2 + 2 * (integralModel 𝒪 W).a₂ * X + A₄ - (integralModel 𝒪 W).a₁ * Y) *
    i, ?_, ?_⟩
  · have hi' : (u : F) * (i : F) = 1 := by exact_mod_cast congrArg ((↑) : 𝒪 → F) hi
    rw [slope_of_Y_ne rfl hy, hden,
      div_eq_iff (by exact_mod_cast mul_ne_zero hp.ne_zero hu.ne_zero), ← coe_integralModel_a₁ v,
      ← coe_integralModel_a₂ v, ← coe_integralModel_a₄ v, h₄]
    push_cast [coe_ofNat v]
    linear_combination (-(ϖ : F) * (3 * ϖ * X ^ 2 + 2 * (integralModel 𝒪 W).a₂ * X + A₄ -
      (integralModel 𝒪 W).a₁ * Y)) * hi'
  · obtain ⟨c₁, hc₁⟩ := hs₁
    obtain ⟨c₂, hc₂⟩ := hs₂
    obtain ⟨c₄, hc₄⟩ := hs₄
    exact ⟨(3 * X ^ 2 + (s * c₁ - 2 * c₂) * X + c₄ - c₁ * Y) * i, by
      linear_combination s * hi + i * (s * X * hc₁ - 2 * X * hc₂ + hc₄ - Y * hc₁)⟩

/-- **The double of a point with singular reduction has singular reduction.** Here
`P = (ϖ X, ϖ Y)`, and `s` lifts the double root of the tangent quadratic with `A₄ ≡ s A₃`. The
tangent at `P` has integral slope `ℓ ≡ s`, so `x(2 P) = ℓ² + a₁ ℓ − a₂ − 2 x ∈ 𝔪`, and then
`y(2 P) ∈ 𝔪` as well. -/
private theorem add_self_notMem {ϖ : v.valuationSubring}
    (hϖ : maximalIdeal v.valuationSubring = Ideal.span {ϖ}) (hp : Prime ϖ)
    (hm₃ : (integralModel v.valuationSubring W).a₃ ∈ maximalIdeal v.valuationSubring)
    (hm₄ : (integralModel v.valuationSubring W).a₄ ∈ maximalIdeal v.valuationSubring)
    (hm₆ : (integralModel v.valuationSubring W).a₆ ∈ maximalIdeal v.valuationSubring)
    {A₃ A₄ A₆ : v.valuationSubring} (h₃ : (integralModel v.valuationSubring W).a₃ = ϖ * A₃)
    (h₄ : (integralModel v.valuationSubring W).a₄ = ϖ * A₄)
    (h₆ : (integralModel v.valuationSubring W).a₆ = ϖ ^ 2 * A₆) (hD : IsUnit (A₃ ^ 2 + 4 * A₆))
    {s : v.valuationSubring} (hs₁ : ϖ ∣ 2 * s + (integralModel v.valuationSubring W).a₁)
    (hs₂ : ϖ ∣ s ^ 2 + (integralModel v.valuationSubring W).a₁ * s -
      (integralModel v.valuationSubring W).a₂) (hs₄ : ϖ ∣ A₄ - s * A₃)
    {X Y : v.valuationSubring}
    (h : W.Nonsingular ((ϖ * X : v.valuationSubring) : F) ((ϖ * Y : v.valuationSubring) : F)) :
    Point.some _ _ h + Point.some _ _ h ∉ W.nonsingularReduction v := by
  obtain ⟨hy, L, hℓ, ⟨e, he⟩⟩ :=
    exists_slope_self_eq v hϖ hp h₃ h₄ h₆ hD hs₁ hs₂ hs₄ h
  rw [Point.add_self_of_Y_ne hy, some_notMem_nonsingularReduction_iff v hm₃ hm₄ hm₆, hℓ]
  -- `x(2 P) = ℓ² + a₁ ℓ − a₂ − 2 x ≡ (ℓ − s)² ≡ 0`
  set X₃ := L ^ 2 + (integralModel 𝒪 W).a₁ * L - (integralModel 𝒪 W).a₂ - ϖ * X - ϖ * X with hX₃_def
  have hX₃ : ϖ ∣ X₃ := by
    obtain ⟨c₁, hc₁⟩ := hs₁
    obtain ⟨c₂, hc₂⟩ := hs₂
    exact ⟨ϖ * e ^ 2 + c₁ * L - s * c₁ + c₂ - 2 * X, by
      linear_combination (L - s + ϖ * e) * he + L * hc₁ - s * hc₁ + hc₂⟩
  have hx₃ : W.addX ((ϖ * X : 𝒪) : F) ((ϖ * X : 𝒪) : F) (L : F) = ((X₃ : 𝒪) : F) := by
    rw [addX, ← coe_integralModel_a₁ v, ← coe_integralModel_a₂ v, hX₃_def]
    push_cast
    ring
  have hy₃ : W.addY ((ϖ * X : 𝒪) : F) ((ϖ * X : 𝒪) : F) ((ϖ * Y : 𝒪) : F) (L : F) =
      ((-(L * (X₃ - ϖ * X) + ϖ * Y) - (integralModel 𝒪 W).a₁ * X₃ - ϖ * A₃ : 𝒪) : F) := by
    rw [addY, negAddY, hx₃, negY, ← coe_integralModel_a₁ v, ← coe_integralModel_a₃ v, h₃]
    push_cast
    ring
  rw [hx₃, hy₃, ← Valuation.mem_maximalIdeal_iff, ← Valuation.mem_maximalIdeal_iff,
    mem_maximalIdeal_iff_dvd hϖ, mem_maximalIdeal_iff_dvd hϖ]
  refine ⟨hX₃, ?_⟩
  obtain ⟨c, hc⟩ := hX₃
  exact ⟨-(L * (c - X) + Y) - (integralModel 𝒪 W).a₁ * c - A₃, by rw [hc]; ring⟩

/-! ### The index at the symbol `IV` -/

/-- **At the symbol `IV` with no rational root of the residue quadratic, every point has
nonsingular reduction**: `E₀(F) = W(F)`. Here `ϖ` generates the maximal ideal, Tate's algorithm
stops at `IV` on the integral model, and with `a₃ = ϖ A₃` and `a₆ = ϖ² A₆` the residue quadratic
`T² + A₃ T − A₆` has no root in the residue field. -/
theorem nonsingularReduction_eq_top_of_isTateTerminal_IV {ϖ : v.valuationSubring}
    (hϖ : maximalIdeal v.valuationSubring = Ideal.span {ϖ})
    (h : (integralModel v.valuationSubring W).IsTateTerminal ϖ .IV)
    {A₃ A₆ : v.valuationSubring} (h₃ : (integralModel v.valuationSubring W).a₃ = ϖ * A₃)
    (h₆ : (integralModel v.valuationSubring W).a₆ = ϖ ^ 2 * A₆)
    (hroot : ∀ t : ResidueField v.valuationSubring,
      t ^ 2 + residue _ A₃ * t - residue _ A₆ ≠ 0) :
    W.nonsingularReduction v = ⊤ := by
  obtain ⟨-, -, ⟨A₄, h₄⟩, -, -, -⟩ := isTateTerminal_IV.1 h
  obtain ⟨-, -, -, -, -, s, hs₁, hs₂, hs₄⟩ := isTateTerminal_IV_data v hϖ h h₃ h₄ h₆
  refine nonsingularReduction_eq_top_of_isTateTerminal v hϖ h (by simp) fun hp x y hx hy hE ↦ ?_
  obtain ⟨X, rfl⟩ := hx
  obtain ⟨Y, rfl⟩ := hy
  have hq := (integralModel 𝒪 W).dvd_residueQuadratic_of_equation hp.ne_zero h₃ h₄ h₆ hs₁ hs₂
    hs₄ hE
  exact hroot (residue _ (Y - s * X))
    (by simpa using (residue_eq_zero_iff _).2 ((mem_maximalIdeal_iff_dvd hϖ).2 hq))

/-- At the symbol `IV`, if `P` has singular reduction then so does `2 • P`, and every point lies
in `E₀(F)`, `P + E₀(F)` or `−P + E₀(F)`: a point with singular reduction reduces to one of the two
roots of the residue quadratic, `P` and `−P` reduce to different roots, and if `Q` and `±P` reduce
to the same root then `Q ∓ P` has nonsingular reduction. -/
private theorem two_nsmul_notMem_and_cosets_of_isTateTerminal_IV {ϖ : v.valuationSubring}
    (hϖ : maximalIdeal v.valuationSubring = Ideal.span {ϖ})
    (h : (integralModel v.valuationSubring W).IsTateTerminal ϖ .IV) {P : W.Point}
    (hP : P ∉ W.nonsingularReduction v) :
    2 • P ∉ W.nonsingularReduction v ∧ ∀ Q : W.Point, Q ∈ W.nonsingularReduction v ∨
      -P + Q ∈ W.nonsingularReduction v ∨ P + Q ∈ W.nonsingularReduction v := by
  obtain ⟨-, ⟨A₃, h₃⟩, ⟨A₄, h₄⟩, ⟨A₆, h₆⟩, -, -⟩ := isTateTerminal_IV.1 h
  obtain ⟨hm₃, hm₄, hm₆, hp, hD, s, hs₁, hs₂, hs₄⟩ := isTateTerminal_IV_data v hϖ h h₃ h₄ h₆
  -- a point `(ϖ X, ϖ Y)` with singular reduction makes `Y − s X` a root of the residue quadratic
  have hroot {X Y : 𝒪} (hXY : W.Nonsingular ((ϖ * X : 𝒪) : F) ((ϖ * Y : 𝒪) : F)) :
      ϖ ∣ (Y - s * X) ^ 2 + A₃ * (Y - s * X) - A₆ :=
    (integralModel 𝒪 W).dvd_residueQuadratic_of_equation hp.ne_zero h₃ h₄ h₆ hs₁ hs₂ hs₄
      ((equation_integralModel_iff v).2 hXY.1)
  obtain ⟨X₀, Y₀, h₀, rfl⟩ := exists_eq_some_of_notMem v hϖ hm₃ hm₄ hm₆ hP
  have hne (hd : ϖ ∣ 2 * (Y₀ - s * X₀) + A₃) : False :=
    hp.not_isUnit (isUnit_of_dvd_unit hd (isUnit_two_mul_add_of_isUnit_sq_add_four_mul hD
      ((mem_maximalIdeal_iff_dvd hϖ).2 (hroot h₀))))
  -- `−P = (ϖ X₀, ϖ Y₀')`, where `Y₀' − s X₀ ≡ −(Y₀ − s X₀) − A₃` is the other root
  set Y₀' := -Y₀ - (integralModel 𝒪 W).a₁ * X₀ - A₃ with hY₀'
  have hnegY : W.negY ((ϖ * X₀ : 𝒪) : F) ((ϖ * Y₀ : 𝒪) : F) = ((ϖ * Y₀' : 𝒪) : F) := by
    rw [negY, ← coe_integralModel_a₁ v, ← coe_integralModel_a₃ v, h₃, hY₀']
    push_cast
    ring
  have h₀' : W.Nonsingular ((ϖ * X₀ : 𝒪) : F) ((ϖ * Y₀' : 𝒪) : F) :=
    hnegY ▸ (nonsingular_neg ..).2 h₀
  have hneg : -Point.some _ _ h₀ = Point.some _ _ h₀' := by
    rw [Point.neg_some, Point.some.injEq]
    exact ⟨rfl, hnegY⟩
  refine ⟨by rw [two_nsmul]; exact add_self_notMem v hϖ hp hm₃ hm₄ hm₆ h₃ h₄ h₆ hD hs₁ hs₂ hs₄ h₀,
    fun Q ↦ ?_⟩
  -- `Q` lies in `E₀(F)`, `P + E₀(F)` or `−P + E₀(F)`, according to its root
  by_cases hQ : Q ∈ W.nonsingularReduction v
  · exact .inl hQ
  obtain ⟨X, Y, hXY, rfl⟩ := exists_eq_some_of_notMem v hϖ hm₃ hm₄ hm₆ hQ
  have hprod : ϖ ∣ ((Y - s * X) - (Y₀ - s * X₀)) * ((Y - s * X) + (Y₀ - s * X₀) + A₃) := by
    convert dvd_sub (hroot hXY) (hroot h₀) using 1
    ring
  obtain ⟨c₁, hc₁⟩ := hs₁
  rcases hp.dvd_or_dvd hprod with ⟨e, he⟩ | ⟨e, he⟩
  · refine .inr (.inl (Classical.byContradiction fun hn ↦ hne ?_))
    rw [hneg, add_comm] at hn
    obtain ⟨e', he'⟩ := dvd_sub_of_add_notMem v hϖ hp hm₃ hm₄ hm₆ ⟨c₁, hc₁⟩ hs₂ hXY h₀' hn
    rw [hY₀'] at he'
    exact ⟨e' - e - c₁ * X₀, by linear_combination he' - he - X₀ * hc₁⟩
  · refine .inr (.inr (Classical.byContradiction fun hn ↦ hne ?_))
    rw [add_comm] at hn
    obtain ⟨e', he'⟩ := dvd_sub_of_add_notMem v hϖ hp hm₃ hm₄ hm₆ ⟨c₁, hc₁⟩ hs₂ hXY h₀ hn
    exact ⟨e - e', by linear_combination he - he'⟩

/-- **At the symbol `IV`, if some point has singular reduction, then `[E(F) : E₀(F)] = 3`.** Here
`ϖ` generates the maximal ideal and Tate's algorithm stops at `IV` on the integral model. If `P`
has singular reduction, the cosets of `E₀(F)` are `E₀(F)`, `P + E₀(F)` and `−P + E₀(F)`. -/
theorem index_nonsingularReduction_eq_three_of_isTateTerminal_IV_of_notMem
    {ϖ : v.valuationSubring} (hϖ : maximalIdeal v.valuationSubring = Ideal.span {ϖ})
    (h : (integralModel v.valuationSubring W).IsTateTerminal ϖ .IV) {P : W.Point}
    (hP : P ∉ W.nonsingularReduction v) :
    (W.nonsingularReduction v).index = 3 := by
  obtain ⟨hdbl, hcos⟩ := two_nsmul_notMem_and_cosets_of_isTateTerminal_IV v hϖ h hP
  exact AddSubgroup.index_eq_three_of_two_nsmul_notMem hdbl hcos

/-- **At the symbol `IV`, `[E(F) : E₀(F)]` divides `3`.** Here `ϖ` generates the maximal ideal and
Tate's algorithm stops at `IV` on the integral model. The index is `3` when some point has singular
reduction, and `1` otherwise. -/
theorem index_nonsingularReduction_dvd_three_of_isTateTerminal_IV {ϖ : v.valuationSubring}
    (hϖ : maximalIdeal v.valuationSubring = Ideal.span {ϖ})
    (h : (integralModel v.valuationSubring W).IsTateTerminal ϖ .IV) :
    (W.nonsingularReduction v).index ∣ 3 := by
  by_cases hall : ∀ P, P ∈ W.nonsingularReduction v
  · rw [(AddSubgroup.eq_top_iff' _).2 hall, AddSubgroup.index_top]
    exact one_dvd 3
  · obtain ⟨P, hP⟩ := not_forall.1 hall
    rw [index_nonsingularReduction_eq_three_of_isTateTerminal_IV_of_notMem v hϖ h hP]

/-- **At the symbol `IV`, some point has singular reduction**, when the valuation ring is
Henselian, for instance complete, and the residue quadratic has a root. Here `ϖ` generates the
maximal ideal, Tate's algorithm stops at `IV` on the integral model, and with `a₃ = ϖ A₃` and
`a₆ = ϖ² A₆` the residue quadratic `T² + A₃ T − A₆` has a root `t` in the residue field. The root
is simple, so it lifts to a root `Y` of `T² + A₃ T − A₆`, and the point is `(0, ϖ Y)`. -/
theorem exists_notMem_nonsingularReduction_of_isTateTerminal_IV
    [HenselianLocalRing v.valuationSubring] {ϖ : v.valuationSubring}
    (hϖ : maximalIdeal v.valuationSubring = Ideal.span {ϖ})
    (h : (integralModel v.valuationSubring W).IsTateTerminal ϖ .IV)
    {A₃ A₆ : v.valuationSubring} (h₃ : (integralModel v.valuationSubring W).a₃ = ϖ * A₃)
    (h₆ : (integralModel v.valuationSubring W).a₆ = ϖ ^ 2 * A₆)
    {t : ResidueField v.valuationSubring} (ht : t ^ 2 + residue _ A₃ * t - residue _ A₆ = 0) :
    ∃ P : W.Point, P ∉ W.nonsingularReduction v := by
  set Wo := integralModel 𝒪 W
  obtain ⟨-, -, ⟨A₄, h₄⟩, -, -, -⟩ := isTateTerminal_IV.1 h
  obtain ⟨hm₃, hm₄, hm₆, hp, hD, -⟩ := isTateTerminal_IV_data v hϖ h h₃ h₄ h₆
  -- lift the root `t` to a root `Y` of `T² + A₃ T − A₆`
  obtain ⟨Y₀, rfl⟩ := residue_surjective t
  set f : 𝒪[X] := X ^ 2 + C A₃ * X - C A₆ with hf
  have hmon : f.Monic := by
    rw [hf]
    monicity!
  have hf₀ : f.eval Y₀ ∈ maximalIdeal 𝒪 := by
    rw [← residue_eq_zero_iff]
    simpa [hf] using ht
  have hf₁ : IsUnit (f.derivative.eval Y₀) := by
    have hd : f.derivative.eval Y₀ = 2 * Y₀ + A₃ := by
      simp [hf, one_add_one_eq_two]
    rw [hd]
    exact isUnit_two_mul_add_of_isUnit_sq_add_four_mul hD (by simpa [hf] using hf₀)
  obtain ⟨Y, hY, -⟩ := HenselianLocalRing.is_henselian f hmon Y₀ hf₀ hf₁
  have hY' : Y ^ 2 + A₃ * Y - A₆ = 0 := by simpa [hf] using hY.eq_zero
  have hu : IsUnit (2 * Y + A₃) :=
    isUnit_two_mul_add_of_isUnit_sq_add_four_mul hD (by rw [hY']; exact zero_mem _)
  -- the point `(0, ϖ Y)`
  have hns : Wo.toAffine.Nonsingular 0 (ϖ * Y) := by
    rw [nonsingular_iff']
    refine ⟨by rw [equation_iff, h₃, h₆]; linear_combination ϖ ^ 2 * hY', .inr ?_⟩
    rw [h₃, mul_zero, add_zero, show 2 * (ϖ * Y) + ϖ * A₃ = ϖ * (2 * Y + A₃) by ring]
    exact mul_ne_zero hp.ne_zero hu.ne_zero
  have hF : W.Nonsingular ((0 : 𝒪) : F) ((ϖ * Y : 𝒪) : F) := (nonsingular_integralModel_iff v).1 hns
  exact ⟨Point.some _ _ hF, (some_coe_notMem_nonsingularReduction_iff v hm₃ hm₄ hm₆ hF).2
    ⟨zero_mem _, (mem_maximalIdeal_iff_dvd hϖ).2 (dvd_mul_right ϖ Y)⟩⟩

/-- **At the symbol `IV`, `[E(F) : E₀(F)] = 3`**, when the valuation ring is Henselian, for
instance complete, and the residue quadratic has a root. This is the local index `c_v = 3` that
Tate's algorithm reports at `IV` in that case. Here `ϖ` generates the maximal ideal, Tate's
algorithm stops at `IV` on the integral model, and with `a₃ = ϖ A₃` and `a₆ = ϖ² A₆` the residue
quadratic `T² + A₃ T − A₆` has a root `t` in the residue field. -/
theorem index_nonsingularReduction_eq_three_of_isTateTerminal_IV
    [HenselianLocalRing v.valuationSubring] {ϖ : v.valuationSubring}
    (hϖ : maximalIdeal v.valuationSubring = Ideal.span {ϖ})
    (h : (integralModel v.valuationSubring W).IsTateTerminal ϖ .IV)
    {A₃ A₆ : v.valuationSubring} (h₃ : (integralModel v.valuationSubring W).a₃ = ϖ * A₃)
    (h₆ : (integralModel v.valuationSubring W).a₆ = ϖ ^ 2 * A₆)
    {t : ResidueField v.valuationSubring} (ht : t ^ 2 + residue _ A₃ * t - residue _ A₆ = 0) :
    (W.nonsingularReduction v).index = 3 := by
  obtain ⟨P, hP⟩ := exists_notMem_nonsingularReduction_of_isTateTerminal_IV v hϖ h h₃ h₆ ht
  exact index_nonsingularReduction_eq_three_of_isTateTerminal_IV_of_notMem v hϖ h hP

end Affine

end WeierstrassCurve

end

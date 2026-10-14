/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Henselian
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.SingularReduction
public import TauCeti.AlgebraicGeometry.EllipticCurve.TateAlgorithm.Terminal

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

namespace WeierstrassCurve

/-- On an equation with `a₃ = ϖ A₃`, `a₄ = ϖ A₄` and `a₆ = ϖ² A₆`, let `s` lift a double root of
the tangent quadratic modulo `ϖ`, with `A₄ ≡ s A₃`. Then a solution `(ϖ X, ϖ Y)` makes `Y − s X` a
root of the residue quadratic `T² + A₃ T − A₆` modulo `ϖ`. -/
private theorem dvd_residueQuadratic_of_equation {R : Type*} [CommRing R] [IsDomain R]
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

/-! ### The data of the stopping test -/

/-- The stopping test for `IV`, with `a₃ = ϖ A₃`, `a₄ = ϖ A₄` and `a₆ = ϖ² A₆`: `ϖ` is prime, the
discriminant `A₃² + 4 A₆` of the residue quadratic is a unit, and the double root of the tangent
quadratic `T² + a₁ T − a₂` lifts to some `s` with `A₄ ≡ s A₃` modulo `ϖ`. -/
private theorem isTateTerminal_IV_data {ϖ : v.valuationSubring}
    (hϖ : maximalIdeal v.valuationSubring = Ideal.span {ϖ})
    (h : (integralModel v.valuationSubring W).IsTateTerminal ϖ .IV)
    {A₃ A₄ A₆ : v.valuationSubring} (h₃ : (integralModel v.valuationSubring W).a₃ = ϖ * A₃)
    (h₄ : (integralModel v.valuationSubring W).a₄ = ϖ * A₄)
    (h₆ : (integralModel v.valuationSubring W).a₆ = ϖ ^ 2 * A₆) :
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
  have hunit (z : 𝒪) : IsUnit z ↔ ¬ ϖ ∣ z := by
    rw [← Ideal.mem_span_singleton, ← hϖ, mem_maximalIdeal, mem_nonunits_iff, not_not]
  -- `b₆ = ϖ² (A₃² + 4 A₆)`
  have hD : IsUnit (A₃ ^ 2 + 4 * A₆) := by
    rw [hunit]
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
      rw [hunit, not_not] at hA₃
      have h4 : IsUnit (2 * (2 * A₆)) := by
        rw [hunit] at hD ⊢
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
  refine ⟨hp, hD, s, hs₁, hs₂, hp.dvd_of_dvd_pow (n := 2) ?_⟩
  -- `(A₄ − s A₃)² ≡ a₁ A₃ A₄ − a₂ A₃² + A₄²`
  obtain ⟨e₁, he₁⟩ := hs₁
  obtain ⟨e₂, he₂⟩ := hs₂
  obtain ⟨e, he⟩ := hE
  exact ⟨e - e₁ * A₃ * A₄ + (s * e₁ - e₂) * A₃ ^ 2, by
    linear_combination he - A₃ * A₄ * he₁ + s * A₃ ^ 2 * he₁ - A₃ ^ 2 * he₂⟩

/-- A root `t` of the residue quadratic `T² + A₃ T − A₆` modulo `ϖ`, whose discriminant
`A₃² + 4 A₆` is a unit, is simple: `2 t + A₃` is a unit. -/
private theorem isUnit_two_mul_add {ϖ : v.valuationSubring}
    (hϖ : maximalIdeal v.valuationSubring = Ideal.span {ϖ}) {A₃ A₆ t : v.valuationSubring}
    (hD : IsUnit (A₃ ^ 2 + 4 * A₆)) (ht : ϖ ∣ t ^ 2 + A₃ * t - A₆) : IsUnit (2 * t + A₃) := by
  have hm : t ^ 2 + A₃ * t - A₆ ∈ maximalIdeal v.valuationSubring := by
    rwa [hϖ, Ideal.mem_span_singleton]
  rw [← isUnit_pow_iff two_ne_zero, ← residue_ne_zero_iff_isUnit,
    show (2 * t + A₃) ^ 2 = 4 * (t ^ 2 + A₃ * t - A₆) + (A₃ ^ 2 + 4 * A₆) by ring, map_add,
    map_mul, (residue_eq_zero_iff _).2 hm, mul_zero, zero_add, residue_ne_zero_iff_isUnit]
  exact hD

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
  rcases P with _ | ⟨x, y, hxy⟩
  · exact absurd (zero_mem _) hP
  obtain ⟨hx, hy⟩ := (some_notMem_nonsingularReduction_iff v h₃ h₄ h₆ hxy).1 hP
  have hmem {z : F} (hz : v z < 1) :
      (⟨z, (v.mem_valuationSubring_iff z).2 hz.le⟩ : v.valuationSubring) ∈
        Ideal.span {ϖ} :=
    hϖ ▸ (Valuation.mem_maximalIdeal_iff (v := v)).2 hz
  obtain ⟨X, hX⟩ := Ideal.mem_span_singleton'.1 (hmem hx)
  obtain ⟨Y, hY⟩ := Ideal.mem_span_singleton'.1 (hmem hy)
  obtain rfl : x = ((ϖ * X : v.valuationSubring) : F) := by rw [mul_comm, hX]
  obtain rfl : y = ((ϖ * Y : v.valuationSubring) : F) := by rw [mul_comm, hY]
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
  set Wo := integralModel 𝒪 W
  have hinj : Function.Injective ((↑) : 𝒪 → F) := Subtype.val_injective
  by_cases hX : X₁ = X₂
  · -- `P + Q ≠ 0`, so `P = Q`
    subst hX
    obtain hY | hY := Y_eq_of_X_eq h₁.1 h₂.1 rfl
    · rw [mul_left_cancel₀ hp.ne_zero (hinj hY), sub_self]
      exact dvd_zero ϖ
    · exact absurd (by rw [Point.add_of_Y_eq rfl hY]; exact zero_mem _) h
  have hx : ((ϖ * X₁ : 𝒪) : F) ≠ ((ϖ * X₂ : 𝒪) : F) :=
    fun he ↦ hX (mul_left_cancel₀ hp.ne_zero (hinj he))
  rw [Point.add_of_X_ne hx] at h
  obtain ⟨hx₃, -⟩ := (some_notMem_nonsingularReduction_iff v h₃ h₄ h₆ _).1 h
  set ℓ := W.slope ((ϖ * X₁ : 𝒪) : F) ((ϖ * X₂ : 𝒪) : F) ((ϖ * Y₁ : 𝒪) : F) ((ϖ * Y₂ : 𝒪) : F)
    with hℓ_def
  have hv (z : 𝒪) : v (z : F) ≤ 1 := (v.mem_valuationSubring_iff _).1 z.2
  set L : 𝒪 := ⟨ℓ, (v.mem_valuationSubring_iff ℓ).2
    (valuation_le_one_of_valuation_addX_le_one v (hv _) (hv _) hx₃.le)⟩
  set X₃ : 𝒪 := ⟨W.addX _ _ ℓ, (v.mem_valuationSubring_iff _).2 hx₃.le⟩
  have hX₃ : ϖ ∣ X₃ :=
    Ideal.mem_span_singleton.1 (hϖ ▸ (Valuation.mem_maximalIdeal_iff (v := v)).2 hx₃)
  have ha₁ : ((Wo.a₁ : 𝒪) : F) = W.a₁ := (integralModel_a₁_eq 𝒪 W :)
  have ha₂ : ((Wo.a₂ : 𝒪) : F) = W.a₂ := (integralModel_a₂_eq 𝒪 W :)
  -- the chord: `ℓ (X₁ − X₂) = Y₁ − Y₂`, and `ℓ² + a₁ ℓ − a₂ = x₁ + x₂ + x₃`
  have hslope : L * (X₁ - X₂) = Y₁ - Y₂ := by
    have hℓ : ℓ * (((ϖ * X₁ : 𝒪) : F) - ((ϖ * X₂ : 𝒪) : F)) =
        ((ϖ * Y₁ : 𝒪) : F) - ((ϖ * Y₂ : 𝒪) : F) := by
      rw [hℓ_def, slope_of_X_ne hx]
      exact div_mul_cancel₀ _ (sub_ne_zero.2 hx)
    refine mul_left_cancel₀ hp.ne_zero (hinj ?_)
    push_cast at hℓ ⊢
    linear_combination hℓ
  have hsum : L ^ 2 + Wo.a₁ * L - Wo.a₂ = ϖ * X₁ + ϖ * X₂ + X₃ := by
    apply hinj
    push_cast
    rw [ha₁, ha₂]
    simp only [L, X₃, addX]
    push_cast
    ring
  -- so `(ℓ − s)² ≡ 0`
  have hL : ϖ ∣ L - s := hp.dvd_of_dvd_pow (n := 2) <| by
    obtain ⟨c₁, hc₁⟩ := hs₁
    obtain ⟨c₂, hc₂⟩ := hs₂
    obtain ⟨c₃, hc₃⟩ := hX₃
    exact ⟨X₁ + X₂ + c₃ - c₁ * L + s * c₁ - c₂, by
      linear_combination hsum + hc₃ - L * hc₁ + s * hc₁ - hc₂⟩
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
  set Wo := integralModel 𝒪 W
  have hinj : Function.Injective ((↑) : 𝒪 → F) := Subtype.val_injective
  have ha₁ : ((Wo.a₁ : 𝒪) : F) = W.a₁ := (integralModel_a₁_eq 𝒪 W :)
  have ha₂ : ((Wo.a₂ : 𝒪) : F) = W.a₂ := (integralModel_a₂_eq 𝒪 W :)
  have ha₃ : ((Wo.a₃ : 𝒪) : F) = W.a₃ := (integralModel_a₃_eq 𝒪 W :)
  have ha₄ : ((Wo.a₄ : 𝒪) : F) = W.a₄ := (integralModel_a₄_eq 𝒪 W :)
  have h2 : ((2 : 𝒪) : F) = 2 := map_ofNat (algebraMap 𝒪 F) 2
  have h3 : ((3 : 𝒪) : F) = 3 := map_ofNat (algebraMap 𝒪 F) 3
  -- `Y − s X` is a root of the residue quadratic, so `u = 2 Y + a₁ X + A₃` is a unit
  have hq := Wo.dvd_residueQuadratic_of_equation hp.ne_zero h₃ h₄ h₆ hs₁ hs₂ hs₄
    ((equation_integralModel_iff v).2 h.1)
  set u := 2 * Y + Wo.a₁ * X + A₃ with hu_def
  have hu : IsUnit u := by
    have ht := isUnit_two_mul_add v hϖ hD hq
    rw [← residue_ne_zero_iff_isUnit] at ht ⊢
    have hs : (2 * s + Wo.a₁) * X ∈ maximalIdeal 𝒪 := by
      rw [hϖ, Ideal.mem_span_singleton]
      exact hs₁.mul_right X
    rwa [show u = 2 * (Y - s * X) + A₃ + (2 * s + Wo.a₁) * X by rw [hu_def]; ring, map_add,
      (residue_eq_zero_iff _).2 hs, add_zero]
  -- `y − (−y − a₁ x − a₃) = ϖ u ≠ 0`
  have hden : ((ϖ * Y : 𝒪) : F) - W.negY ((ϖ * X : 𝒪) : F) ((ϖ * Y : 𝒪) : F) =
      ((ϖ * u : 𝒪) : F) := by
    rw [negY, ← ha₁, ← ha₃, h₃, hu_def]
    push_cast [h2]
    ring
  have hy : ((ϖ * Y : 𝒪) : F) ≠ W.negY ((ϖ * X : 𝒪) : F) ((ϖ * Y : 𝒪) : F) := fun he ↦
    mul_ne_zero hp.ne_zero hu.ne_zero
      (hinj (by rw [← hden, ← he, sub_self, ZeroMemClass.coe_zero]))
  -- the slope is `ℓ = N / u` with `N = 3 ϖ X² + 2 a₂ X + A₄ − a₁ Y`
  obtain ⟨i, hi⟩ := hu.exists_right_inv
  refine ⟨hy, (3 * ϖ * X ^ 2 + 2 * Wo.a₂ * X + A₄ - Wo.a₁ * Y) * i, ?_, ?_⟩
  · have hi' : (u : F) * (i : F) = 1 := by exact_mod_cast congrArg ((↑) : 𝒪 → F) hi
    rw [slope_of_Y_ne rfl hy, hden,
      div_eq_iff (by exact_mod_cast mul_ne_zero hp.ne_zero hu.ne_zero), ← ha₁, ← ha₂, ← ha₄, h₄]
    push_cast [h2, h3]
    linear_combination (-(ϖ : F) * (3 * ϖ * X ^ 2 + 2 * Wo.a₂ * X + A₄ - Wo.a₁ * Y)) * hi'
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
    {A₃ A₄ A₆ : v.valuationSubring} (h₃ : (integralModel v.valuationSubring W).a₃ = ϖ * A₃)
    (h₄ : (integralModel v.valuationSubring W).a₄ = ϖ * A₄)
    (h₆ : (integralModel v.valuationSubring W).a₆ = ϖ ^ 2 * A₆) (hD : IsUnit (A₃ ^ 2 + 4 * A₆))
    {s : v.valuationSubring} (hs₁ : ϖ ∣ 2 * s + (integralModel v.valuationSubring W).a₁)
    (hs₂ : ϖ ∣ s ^ 2 + (integralModel v.valuationSubring W).a₁ * s -
      (integralModel v.valuationSubring W).a₂) (hs₄ : ϖ ∣ A₄ - s * A₃)
    {X Y : v.valuationSubring}
    (h : W.Nonsingular ((ϖ * X : v.valuationSubring) : F) ((ϖ * Y : v.valuationSubring) : F)) :
    Point.some _ _ h + Point.some _ _ h ∉ W.nonsingularReduction v := by
  set Wo := integralModel 𝒪 W
  have key (z : 𝒪) : z ∈ maximalIdeal 𝒪 ↔ ϖ ∣ z := by rw [hϖ, Ideal.mem_span_singleton]
  have ha₁ : ((Wo.a₁ : 𝒪) : F) = W.a₁ := (integralModel_a₁_eq 𝒪 W :)
  have ha₂ : ((Wo.a₂ : 𝒪) : F) = W.a₂ := (integralModel_a₂_eq 𝒪 W :)
  have ha₃ : ((Wo.a₃ : 𝒪) : F) = W.a₃ := (integralModel_a₃_eq 𝒪 W :)
  obtain ⟨hy, L, hℓ, ⟨e, he⟩⟩ :=
    exists_slope_self_eq v hϖ hp h₃ h₄ h₆ hD hs₁ hs₂ hs₄ h
  rw [Point.add_self_of_Y_ne hy, some_notMem_nonsingularReduction_iff v ((key _).2 ⟨A₃, h₃⟩)
    ((key _).2 ⟨A₄, h₄⟩) ((key _).2 ⟨ϖ * A₆, by rw [h₆]; ring⟩), hℓ]
  -- `x(2 P) = ℓ² + a₁ ℓ − a₂ − 2 x ≡ (ℓ − s)² ≡ 0`
  set X₃ := L ^ 2 + Wo.a₁ * L - Wo.a₂ - ϖ * X - ϖ * X with hX₃_def
  have hX₃ : ϖ ∣ X₃ := by
    obtain ⟨c₁, hc₁⟩ := hs₁
    obtain ⟨c₂, hc₂⟩ := hs₂
    exact ⟨ϖ * e ^ 2 + c₁ * L - s * c₁ + c₂ - 2 * X, by
      linear_combination (L - s + ϖ * e) * he + L * hc₁ - s * hc₁ + hc₂⟩
  have hx₃ : W.addX ((ϖ * X : 𝒪) : F) ((ϖ * X : 𝒪) : F) (L : F) = ((X₃ : 𝒪) : F) := by
    rw [addX, ← ha₁, ← ha₂, hX₃_def]
    push_cast
    ring
  have hy₃ : W.addY ((ϖ * X : 𝒪) : F) ((ϖ * X : 𝒪) : F) ((ϖ * Y : 𝒪) : F) (L : F) =
      ((-(L * (X₃ - ϖ * X) + ϖ * Y) - Wo.a₁ * X₃ - ϖ * A₃ : 𝒪) : F) := by
    rw [addY, negAddY, hx₃, negY, ← ha₁, ← ha₃, h₃]
    push_cast
    ring
  have hlt (z : 𝒪) (hz : ϖ ∣ z) : v (z : F) < 1 :=
    (Valuation.mem_maximalIdeal_iff (v := v)).1 ((key _).2 hz)
  rw [hx₃, hy₃]
  refine ⟨hlt _ hX₃, hlt _ ?_⟩
  obtain ⟨c, hc⟩ := hX₃
  exact ⟨-(L * (c - X) + Y) - Wo.a₁ * c - A₃, by rw [hc]; ring⟩

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
  obtain ⟨hp, -, s, hs₁, hs₂, hs₄⟩ := isTateTerminal_IV_data v hϖ h h₃ h₄ h₆
  have key (z : 𝒪) : z ∈ maximalIdeal 𝒪 ↔ ϖ ∣ z := by rw [hϖ, Ideal.mem_span_singleton]
  refine nonsingularReduction_eq_top_of_forall_mem_maximalIdeal_not_equation v
    ((key _).2 ⟨A₃, h₃⟩) ((key _).2 ⟨A₄, h₄⟩) ((key _).2 ⟨ϖ * A₆, by rw [h₆]; ring⟩)
    fun x y hx hy hE ↦ ?_
  obtain ⟨X, rfl⟩ := (key _).1 hx
  obtain ⟨Y, rfl⟩ := (key _).1 hy
  have hq := (integralModel 𝒪 W).dvd_residueQuadratic_of_equation hp.ne_zero h₃ h₄ h₆ hs₁ hs₂
    hs₄ hE
  exact hroot (residue _ (Y - s * X)) (by simpa using (residue_eq_zero_iff _).2 ((key _).2 hq))

/-- At the symbol `IV`, if `P` has singular reduction then so does `P + P`, and every point lies
in `E₀(F)`, `P + E₀(F)` or `−P + E₀(F)`: a point with singular reduction reduces to one of the two
roots of the residue quadratic, `P` and `−P` reduce to different roots, and if `Q` and `±P` reduce
to the same root then `Q ∓ P` has nonsingular reduction. -/
private theorem add_self_notMem_and_cosets_of_isTateTerminal_IV {ϖ : v.valuationSubring}
    (hϖ : maximalIdeal v.valuationSubring = Ideal.span {ϖ})
    (h : (integralModel v.valuationSubring W).IsTateTerminal ϖ .IV) {P : W.Point}
    (hP : P ∉ W.nonsingularReduction v) :
    P + P ∉ W.nonsingularReduction v ∧ ∀ Q : W.Point, Q ∈ W.nonsingularReduction v ∨
      Q + -P ∈ W.nonsingularReduction v ∨ Q + P ∈ W.nonsingularReduction v := by
  set Wo := integralModel 𝒪 W
  obtain ⟨-, ⟨A₃, h₃⟩, ⟨A₄, h₄⟩, ⟨A₆, h₆⟩, -, -⟩ := isTateTerminal_IV.1 h
  obtain ⟨hp, hD, s, hs₁, hs₂, hs₄⟩ := isTateTerminal_IV_data v hϖ h h₃ h₄ h₆
  have key (z : 𝒪) : z ∈ maximalIdeal 𝒪 ↔ ϖ ∣ z := by rw [hϖ, Ideal.mem_span_singleton]
  have hm₃ : Wo.a₃ ∈ maximalIdeal 𝒪 := (key _).2 ⟨A₃, h₃⟩
  have hm₄ : Wo.a₄ ∈ maximalIdeal 𝒪 := (key _).2 ⟨A₄, h₄⟩
  have hm₆ : Wo.a₆ ∈ maximalIdeal 𝒪 := (key _).2 ⟨ϖ * A₆, by rw [h₆]; ring⟩
  -- a point `(ϖ X, ϖ Y)` with singular reduction makes `Y − s X` a root of the residue quadratic
  have hroot {X Y : 𝒪} (hXY : W.Nonsingular ((ϖ * X : 𝒪) : F) ((ϖ * Y : 𝒪) : F)) :
      ϖ ∣ (Y - s * X) ^ 2 + A₃ * (Y - s * X) - A₆ :=
    Wo.dvd_residueQuadratic_of_equation hp.ne_zero h₃ h₄ h₆ hs₁ hs₂ hs₄
      ((equation_integralModel_iff v).2 hXY.1)
  obtain ⟨X₀, Y₀, h₀, rfl⟩ := exists_eq_some_of_notMem v hϖ hm₃ hm₄ hm₆ hP
  have hne (hd : ϖ ∣ 2 * (Y₀ - s * X₀) + A₃) : False :=
    hp.not_isUnit (isUnit_of_dvd_unit hd (isUnit_two_mul_add v hϖ hD (hroot h₀)))
  -- `−P = (ϖ X₀, ϖ Y₀')`, where `Y₀' − s X₀ ≡ −(Y₀ − s X₀) − A₃` is the other root
  set Y₀' := -Y₀ - Wo.a₁ * X₀ - A₃ with hY₀'
  have hnegY : W.negY ((ϖ * X₀ : 𝒪) : F) ((ϖ * Y₀ : 𝒪) : F) = ((ϖ * Y₀' : 𝒪) : F) := by
    have ha₁ : ((Wo.a₁ : 𝒪) : F) = W.a₁ := (integralModel_a₁_eq 𝒪 W :)
    have ha₃ : ((Wo.a₃ : 𝒪) : F) = W.a₃ := (integralModel_a₃_eq 𝒪 W :)
    rw [negY, ← ha₁, ← ha₃, h₃, hY₀']
    push_cast
    ring
  have h₀' : W.Nonsingular ((ϖ * X₀ : 𝒪) : F) ((ϖ * Y₀' : 𝒪) : F) :=
    hnegY ▸ (nonsingular_neg ..).2 h₀
  have hneg : -Point.some _ _ h₀ = Point.some _ _ h₀' := by
    rw [Point.neg_some, Point.some.injEq]
    exact ⟨rfl, hnegY⟩
  refine ⟨add_self_notMem v hϖ hp h₃ h₄ h₆ hD hs₁ hs₂ hs₄ h₀, fun Q ↦ ?_⟩
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
    rw [hneg] at hn
    obtain ⟨e', he'⟩ := dvd_sub_of_add_notMem v hϖ hp hm₃ hm₄ hm₆ ⟨c₁, hc₁⟩ hs₂ hXY h₀' hn
    rw [hY₀'] at he'
    exact ⟨e' - e - c₁ * X₀, by linear_combination he' - he - X₀ * hc₁⟩
  · refine .inr (.inr (Classical.byContradiction fun hn ↦ hne ?_))
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
  obtain ⟨hdbl, hcos⟩ := add_self_notMem_and_cosets_of_isTateTerminal_IV v hϖ h hP
  set H := W.nonsingularReduction v
  -- `0`, `P` and `−P` represent the three classes of `W(F) ⧸ H`
  have hf : Function.Bijective
      ![((0 : W.Point) : W.Point ⧸ H), (P : W.Point ⧸ H), ((-P : W.Point) : W.Point ⧸ H)] := by
    refine ⟨fun i j hij ↦ ?_, fun q ↦ ?_⟩
    · have h01 : -0 + P ∉ H := by rwa [neg_zero, zero_add]
      have h02 : -0 + -P ∉ H := by rwa [neg_zero, zero_add, neg_mem_iff]
      have h12 : -P + -P ∉ H := by rwa [← neg_add, neg_mem_iff]
      fin_cases i <;> fin_cases j
      all_goals first
        | rfl
        | exact absurd (QuotientAddGroup.eq.1 hij) h01
        | exact absurd (QuotientAddGroup.eq.1 hij) h02
        | exact absurd (QuotientAddGroup.eq.1 hij) h12
        | exact absurd (QuotientAddGroup.eq.1 hij.symm) h01
        | exact absurd (QuotientAddGroup.eq.1 hij.symm) h02
        | exact absurd (QuotientAddGroup.eq.1 hij.symm) h12
    · obtain ⟨Q, rfl⟩ := QuotientAddGroup.mk_surjective q
      rcases hcos Q with hQ | hQ | hQ
      · exact ⟨0, QuotientAddGroup.eq.2 (by rwa [neg_zero, zero_add])⟩
      · exact ⟨1, QuotientAddGroup.eq.2 (by rwa [add_comm])⟩
      · exact ⟨2, QuotientAddGroup.eq.2 (by rwa [neg_neg, add_comm])⟩
  rw [AddSubgroup.index, ← Nat.card_eq_of_bijective _ hf, Nat.card_eq_fintype_card,
    Fintype.card_fin]

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
  obtain ⟨hp, hD, -⟩ := isTateTerminal_IV_data v hϖ h h₃ h₄ h₆
  have key (z : 𝒪) : z ∈ maximalIdeal 𝒪 ↔ ϖ ∣ z := by rw [hϖ, Ideal.mem_span_singleton]
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
      simp only [hf, derivative_sub, derivative_add, derivative_mul, derivative_X_pow,
        derivative_C, derivative_X, eval_sub, eval_add, eval_mul, eval_C, eval_X, eval_pow]
      norm_num
    rw [hd]
    exact isUnit_two_mul_add v hϖ hD ((key _).1 (by simpa [hf] using hf₀))
  obtain ⟨Y, hY, -⟩ := HenselianLocalRing.is_henselian f hmon Y₀ hf₀ hf₁
  have hY' : Y ^ 2 + A₃ * Y - A₆ = 0 := by simpa [hf] using hY.eq_zero
  have hu : IsUnit (2 * Y + A₃) := isUnit_two_mul_add v hϖ hD ⟨0, by rw [hY', mul_zero]⟩
  -- the point `(0, ϖ Y)`
  have hns : Wo.toAffine.Nonsingular 0 (ϖ * Y) := by
    rw [nonsingular_iff']
    refine ⟨by rw [equation_iff, h₃, h₆]; linear_combination ϖ ^ 2 * hY', .inr ?_⟩
    rw [h₃, mul_zero, add_zero, show 2 * (ϖ * Y) + ϖ * A₃ = ϖ * (2 * Y + A₃) by ring]
    exact mul_ne_zero hp.ne_zero hu.ne_zero
  have hF : W.Nonsingular ((0 : 𝒪) : F) ((ϖ * Y : 𝒪) : F) := by
    have := (Wo.toAffine.map_nonsingular (IsFractionRing.injective _ F) _ _).mpr hns
    rwa [← baseChange_integralModel_eq 𝒪 W]
  have hlt (z : 𝒪) (hz : ϖ ∣ z) : v (z : F) < 1 :=
    (Valuation.mem_maximalIdeal_iff (v := v)).1 ((key _).2 hz)
  exact ⟨Point.some _ _ hF, (some_notMem_nonsingularReduction_iff v ((key _).2 ⟨A₃, h₃⟩)
    ((key _).2 ⟨A₄, h₄⟩) ((key _).2 ⟨ϖ * A₆, by rw [h₆]; ring⟩) hF).2
    ⟨hlt _ (dvd_zero ϖ), hlt _ (dvd_mul_right ϖ Y)⟩⟩

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

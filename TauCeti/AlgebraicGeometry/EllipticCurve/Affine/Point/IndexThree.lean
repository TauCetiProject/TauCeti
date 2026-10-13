/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.NonsingularReduction
public import TauCeti.AlgebraicGeometry.EllipticCurve.TateAlgorithm.Terminal
public import Mathlib.RingTheory.Henselian
-- Proof-only: the points with singular reduction when the reduction is singular at the origin.
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.SingularReduction
-- Proof-only: the chord through two points whose sum has singular reduction.
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.IndexTwo
-- Proof-only: index three from a covering by three cosets.
import TauCeti.GroupTheory.Index.Three

/-!
# Points with singular reduction: the index three case `IV*`

Let `v` be a valuation on a field `F` whose valuation ring `O` has maximal ideal `𝔪 = (ϖ)`, and
let `W` be a Weierstrass curve over `F` with an integral model `W_O` over `O`. The points with
nonsingular reduction form the subgroup `E₀(F)` of `W(F)`
(`WeierstrassCurve.Affine.nonsingularReduction`). When `F` is complete for a discrete valuation
with perfect residue field and the equation is minimal, the index `[E(F) : E₀(F)]` is the local
index `c_v` that Tate's algorithm computes (Silverman, *Advanced Topics*, IV.9, Table 4.1). This
file computes the index at the reduction symbol `IV*`, where `c_v` is `3` or `1` according to
whether the residue quadratic `T² + (a₃ / ϖ²) T − a₆ / ϖ⁴` has a root in the residue field.

Tate's algorithm stops at `IV*` on an equation with `ϖ ∣ a₁`, `ϖ² ∣ a₂`, `a₃ = ϖ² A₃`,
`ϖ³ ∣ a₄`, `a₆ = ϖ⁴ A₆` and `ϖ⁵ ∤ b₆ = ϖ⁴ (A₃² + 4 A₆)`, so that the residue quadratic
`T² + A₃ T − A₆` has distinct roots. A point `(x, y)` with singular reduction has `x, y ∈ 𝔪`;
comparing powers of `ϖ` in the Weierstrass equation gives `x = ϖ² X` and `y = ϖ² Y`, where the
residue of `Y` is a root of the residue quadratic. The two roots sort the points with singular
reduction into two classes, exchanged by negation, since `-(x, y) = (x, -y - a₁ x - a₃)` and the
two roots add up to `-A₃`.

* If `P` and `Q` have singular reduction in different classes, then `P + Q` has nonsingular
  reduction. Indeed, if `P`, `Q` and `P + Q` all have singular reduction, then the slope `ℓ` of the
  chord through `P` and `Q` lies in `𝔪` because `ℓ² + a₁ ℓ − a₂ = x₁ + x₂ + x₃`, so
  `y₁ − y₂ = ℓ (x₁ − x₂)` is divisible by `ϖ³`, and `P` and `Q` are in the same class.
* If `P` has singular reduction, so does `2 P`: the tangent at `P` has slope
  `(3 x² + 2 a₂ x + a₄ − a₁ y) / (2 y + a₁ x + a₃)`, whose numerator is divisible by `ϖ³` and whose
  denominator is `ϖ²` times a unit, as the derivative `2 Y + A₃` of the residue quadratic at the
  simple root `Y` is a unit.

So if `P` has singular reduction, every point lies in `E₀(F)`, in `P + E₀(F)` or in
`-P + E₀(F)`, and these cosets are distinct since `2 P ∉ E₀(F)`: the index is `3`. Otherwise the
index is `1`. Over a Henselian valuation ring, a root of the residue quadratic lifts to a root `Y`
of `T² + A₃ T − A₆`, and `(0, ϖ² Y)` is a point with singular reduction.

In particular `[E(F) : E₀(F)]` divides `3` with no further hypothesis. No completeness,
discreteness, minimality or hypothesis on the residue field is needed except where stated.

## Main results

* `WeierstrassCurve.Affine.index_nonsingularReduction_eq_three_of_isTateTerminal_IVStar_of_notMem`:
  at the symbol `IV*`, if some point has singular reduction, then `[E(F) : E₀(F)] = 3`.
* `WeierstrassCurve.Affine.index_nonsingularReduction_dvd_three_of_isTateTerminal_IVStar`: at the
  symbol `IV*`, `[E(F) : E₀(F)]` divides `3`.
* `WeierstrassCurve.Affine.exists_notMem_nonsingularReduction_of_isTateTerminal_IVStar` and
  `WeierstrassCurve.Affine.index_nonsingularReduction_eq_three_of_isTateTerminal_IVStar`: at the
  symbol `IV*` over a Henselian valuation ring, if the residue quadratic has a root, some point has
  singular reduction, and `[E(F) : E₀(F)] = 3`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VII.6.
* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, GTM 151, IV.9.
* J. Tate, *Algorithm for determining the type of a singular fibre in an elliptic pencil*, in
  *Modular Functions of One Variable IV*, LNM 476 (1975), 33–52.
-/

public section

open IsLocalRing Polynomial

namespace WeierstrassCurve

section CommRing

variable {R : Type*} [CommRing R] {ϖ : R}

/-- On the normal form of Tate's algorithm at the symbol `IV*`, where `ϖ ∣ a₁`, `ϖ² ∣ a₂`,
`a₃ = ϖ² A₃`, `ϖ³ ∣ a₄` and `a₆ = ϖ⁴ A₆`, a solution with both coordinates divisible by the prime
`ϖ` is `(ϖ² X, ϖ² Y)` with `Y² + A₃ Y − A₆` divisible by `ϖ`. -/
private theorem exists_eq_sq_mul_of_equation [IsDomain R] (W : WeierstrassCurve R)
    (hϖ : Prime ϖ) (h₁ : ϖ ∣ W.a₁) (h₂ : ϖ ^ 2 ∣ W.a₂) {A₃ A₆ : R} (h₃ : W.a₃ = ϖ ^ 2 * A₃)
    (h₄ : ϖ ^ 3 ∣ W.a₄) (h₆ : W.a₆ = ϖ ^ 4 * A₆) {x y : R} (h : W.toAffine.Equation x y)
    (hx : ϖ ∣ x) (hy : ϖ ∣ y) :
    ∃ X Y, x = ϖ ^ 2 * X ∧ y = ϖ ^ 2 * Y ∧ ϖ ∣ Y ^ 2 + A₃ * Y - A₆ := by
  obtain ⟨A₁, hA₁⟩ := h₁
  obtain ⟨A₂, hA₂⟩ := h₂
  obtain ⟨A₄, hA₄⟩ := h₄
  obtain ⟨X, rfl⟩ := hx
  obtain ⟨Y, rfl⟩ := hy
  rw [Affine.equation_iff, hA₁, hA₂, h₃, hA₄, h₆] at h
  have hϖ0 := hϖ.ne_zero
  -- comparing powers of `ϖ` in the equation gives `ϖ ∣ Y`, then `ϖ ∣ X`
  obtain ⟨Y, rfl⟩ : ϖ ∣ Y := hϖ.dvd_of_dvd_pow (n := 2)
    ⟨X ^ 3 + ϖ * A₂ * X ^ 2 + ϖ * A₄ * X + ϖ * A₆ - A₁ * X * Y - A₃ * Y,
      mul_left_cancel₀ (pow_ne_zero 2 hϖ0) (by linear_combination h)⟩
  obtain ⟨X, rfl⟩ : ϖ ∣ X := hϖ.dvd_of_dvd_pow (n := 3)
    ⟨Y ^ 2 + A₁ * X * Y + A₃ * Y - A₂ * X ^ 2 - A₄ * X - A₆,
      mul_left_cancel₀ (pow_ne_zero 3 hϖ0) (by linear_combination -h)⟩
  exact ⟨X, Y, by ring, by ring, ϖ * X ^ 3 + ϖ * A₂ * X ^ 2 + A₄ * X - A₁ * X * Y,
    mul_left_cancel₀ (pow_ne_zero 4 hϖ0) (by linear_combination h)⟩

/-- A root modulo the prime `ϖ` of `T² + A₃ T − A₆` is simple when `ϖ ∤ A₃² + 4 A₆`: the
derivative `2 Y + A₃` is not divisible by `ϖ`, since
`(2 Y + A₃)² = 4 (Y² + A₃ Y − A₆) + A₃² + 4 A₆`. -/
private theorem not_dvd_two_mul_add {A₃ A₆ Y : R} (hb : ¬ ϖ ∣ A₃ ^ 2 + 4 * A₆)
    (hY : ϖ ∣ Y ^ 2 + A₃ * Y - A₆) : ¬ ϖ ∣ 2 * Y + A₃ := fun hd ↦ hb <| by
  rw [show A₃ ^ 2 + 4 * A₆ = (2 * Y + A₃) ^ 2 - 4 * (Y ^ 2 + A₃ * Y - A₆) by ring]
  exact dvd_sub (dvd_pow hd two_ne_zero) (hY.mul_left 4)

/-- At the symbol `IV*`, the uniformiser is prime and `ϖ ∤ A₃² + 4 A₆`, where `a₃ = ϖ² A₃` and
`a₆ = ϖ⁴ A₆`. -/
private theorem IsTateTerminal.prime_and_not_dvd_of_IVStar {W : WeierstrassCurve R}
    (hϖ : (Ideal.span {ϖ}).IsPrime) (h : W.IsTateTerminal ϖ .IVStar) {A₃ A₆ : R}
    (h₃ : W.a₃ = ϖ ^ 2 * A₃) (h₆ : W.a₆ = ϖ ^ 4 * A₆) :
    Prime ϖ ∧ ¬ ϖ ∣ A₃ ^ 2 + 4 * A₆ := by
  obtain ⟨-, -, -, -, -, hb₆⟩ := isTateTerminal_IVStar.1 h
  have hb : W.b₆ = ϖ ^ 4 * (A₃ ^ 2 + 4 * A₆) := by
    rw [b₆, h₃, h₆]
    ring
  -- `ϖ ≠ 0`, since otherwise `b₆ = 0`
  have hϖ0 : ϖ ≠ 0 := by
    rintro rfl
    exact hb₆ (by simp [hb])
  refine ⟨(Ideal.span_singleton_prime hϖ0).1 hϖ, fun hd ↦ hb₆ ?_⟩
  rw [hb, pow_succ]
  exact mul_dvd_mul_left _ hd

end CommRing

namespace Affine

variable {F Γ₀ : Type*} [Field F] [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation F Γ₀)
  {W : Affine F} [IsIntegral v.valuationSubring W]

variable [DecidableEq F]

/-- At the symbol `IV*`, a point with singular reduction is `(ϖ² X, ϖ² Y)` with `X` and `Y`
integral and the residue of `Y` a root of the residue quadratic `T² + A₃ T − A₆`. -/
private theorem exists_eq_sq_mul_of_notMem_of_isTateTerminal_IVStar {ϖ : v.valuationSubring}
    (hϖ : maximalIdeal v.valuationSubring = Ideal.span {ϖ})
    (h : (integralModel v.valuationSubring W).IsTateTerminal ϖ .IVStar) {A₃ A₆ : v.valuationSubring}
    (h₃ : (integralModel v.valuationSubring W).a₃ = ϖ ^ 2 * A₃)
    (h₆ : (integralModel v.valuationSubring W).a₆ = ϖ ^ 4 * A₆) {x y : v.valuationSubring}
    {hxy : W.Nonsingular x y} (hP : Point.some _ _ hxy ∉ W.nonsingularReduction v) :
    ∃ X Y, x = ϖ ^ 2 * X ∧ y = ϖ ^ 2 * Y ∧ ϖ ∣ Y ^ 2 + A₃ * Y - A₆ := by
  obtain ⟨h₁, h₂, -, h₄, -, -⟩ := isTateTerminal_IVStar.1 h
  have key (z : v.valuationSubring) : z ∈ maximalIdeal v.valuationSubring ↔ ϖ ∣ z := by
    rw [hϖ, Ideal.mem_span_singleton]
  obtain ⟨hp, -⟩ := IsTateTerminal.prime_and_not_dvd_of_IVStar
    (hϖ ▸ (maximalIdeal.isMaximal _).isPrime) h h₃ h₆
  obtain ⟨hx, hy⟩ := (some_notMem_nonsingularReduction_iff v
    ((key _).2 ⟨ϖ * A₃, by rw [h₃]; ring⟩) ((key _).2 ((dvd_pow_self ϖ three_ne_zero).trans h₄))
    ((key _).2 ⟨ϖ ^ 3 * A₆, by rw [h₆]; ring⟩) hxy).1 hP
  exact exists_eq_sq_mul_of_equation _ hp h₁ h₂ h₃ h₄ h₆
    ((equation_integralModel_iff v).2 hxy.left)
    ((key _).1 ((Valuation.mem_maximalIdeal_iff (v := v)).2 hx))
    ((key _).1 ((Valuation.mem_maximalIdeal_iff (v := v)).2 hy))

/-- **At the symbol `IV*`, two points whose sum has singular reduction lie in the same class.** If
`(x₁, y₁)`, `(x₂, y₂)` and their sum all have singular reduction, then `ϖ³ ∣ y₁ − y₂`: the slope
`ℓ` of the chord lies in `𝔪` and `y₁ − y₂ = ℓ (x₁ − x₂)` with `ϖ² ∣ x₁, x₂`. -/
private theorem pow_three_dvd_sub_of_isTateTerminal_IVStar {ϖ : v.valuationSubring}
    (hϖ : maximalIdeal v.valuationSubring = Ideal.span {ϖ})
    (h : (integralModel v.valuationSubring W).IsTateTerminal ϖ .IVStar)
    {x₁ y₁ x₂ y₂ : v.valuationSubring} {h₁ : W.Nonsingular x₁ y₁} {h₂ : W.Nonsingular x₂ y₂}
    (hP : Point.some _ _ h₁ ∉ W.nonsingularReduction v)
    (hQ : Point.some _ _ h₂ ∉ W.nonsingularReduction v)
    (hPQ : Point.some _ _ h₁ + Point.some _ _ h₂ ∉ W.nonsingularReduction v) :
    ϖ ^ 3 ∣ y₁ - y₂ := by
  obtain ⟨ha₁, ha₂, ⟨A₃, h₃⟩, h₄, ⟨A₆, h₆⟩, -⟩ := isTateTerminal_IVStar.1 h
  have key (z : v.valuationSubring) : z ∈ maximalIdeal v.valuationSubring ↔ ϖ ∣ z := by
    rw [hϖ, Ideal.mem_span_singleton]
  obtain ⟨hp, -⟩ := IsTateTerminal.prime_and_not_dvd_of_IVStar
    (hϖ ▸ (maximalIdeal.isMaximal _).isPrime) h h₃ h₆
  obtain ⟨X₁, -, rfl, -, -⟩ := exists_eq_sq_mul_of_notMem_of_isTateTerminal_IVStar v hϖ h h₃ h₆ hP
  obtain ⟨X₂, -, rfl, -, -⟩ := exists_eq_sq_mul_of_notMem_of_isTateTerminal_IVStar v hϖ h h₃ h₆ hQ
  obtain ⟨x₃, -, ℓ, -, hx₃, -, hs, hL, -⟩ := exists_chord_of_add_notMem_nonsingularReduction v
    ((key _).2 ⟨ϖ * A₃, by rw [h₃]; ring⟩) ((key _).2 ((dvd_pow_self ϖ three_ne_zero).trans h₄))
    ((key _).2 ⟨ϖ ^ 3 * A₆, by rw [h₆]; ring⟩) hPQ
  -- the slope is divisible by `ϖ`, since `ℓ² = x₁ + x₂ + x₃ + a₂ − a₁ ℓ`
  have hℓ : ϖ ∣ ℓ := by
    refine hp.dvd_of_dvd_pow (n := 2) ?_
    rw [show ℓ ^ 2 = ϖ * (ϖ * X₁) + ϖ * (ϖ * X₂) + x₃ + (integralModel v.valuationSubring W).a₂ -
        (integralModel v.valuationSubring W).a₁ * ℓ by linear_combination hs]
    exact dvd_sub (dvd_add (dvd_add (dvd_add (dvd_mul_right _ _) (dvd_mul_right _ _))
      ((key _).1 hx₃)) ((dvd_pow_self ϖ two_ne_zero).trans ha₂)) (ha₁.mul_right ℓ)
  rw [hL, show ϖ ^ 2 * X₁ - ϖ ^ 2 * X₂ = ϖ ^ 2 * (X₁ - X₂) by ring, pow_succ']
  exact mul_dvd_mul hℓ (dvd_mul_right _ _)

/-- **Twice a point whose tangent slope lies in `𝔪` has singular reduction.** Here the reduction is
singular at the origin and `a₂ ∈ 𝔪` as well. If `(x, y)` has integral coordinates in `𝔪` and the
tangent there has slope `ℓ ∈ 𝔪`, that is `ℓ (2 y + a₁ x + a₃) = 3 x² + 2 a₂ x + a₄ − a₁ y` with
`2 y + a₁ x + a₃ ≠ 0`, then both coordinates of twice the point lie in `𝔪`. -/
private theorem two_nsmul_notMem_of_slope_mem
    (h₂ : (integralModel v.valuationSubring W).a₂ ∈ maximalIdeal v.valuationSubring)
    (h₃ : (integralModel v.valuationSubring W).a₃ ∈ maximalIdeal v.valuationSubring)
    (h₄ : (integralModel v.valuationSubring W).a₄ ∈ maximalIdeal v.valuationSubring)
    (h₆ : (integralModel v.valuationSubring W).a₆ ∈ maximalIdeal v.valuationSubring)
    {x y ℓ : v.valuationSubring} {hxy : W.Nonsingular x y}
    (hx : x ∈ maximalIdeal v.valuationSubring) (hy : y ∈ maximalIdeal v.valuationSubring)
    (hℓ : ℓ ∈ maximalIdeal v.valuationSubring)
    (hne : 2 * y + (integralModel v.valuationSubring W).a₁ * x +
      (integralModel v.valuationSubring W).a₃ ≠ 0)
    (hslope : ℓ * (2 * y + (integralModel v.valuationSubring W).a₁ * x +
      (integralModel v.valuationSubring W).a₃) = 3 * x ^ 2 +
        2 * (integralModel v.valuationSubring W).a₂ * x + (integralModel v.valuationSubring W).a₄ -
          (integralModel v.valuationSubring W).a₁ * y) :
    2 • Point.some _ _ hxy ∉ W.nonsingularReduction v := by
  set Wo := integralModel v.valuationSubring W
  have hneg : W.negY x y = ((Wo.toAffine.negY x y : v.valuationSubring) : F) := by
    conv_lhs => rw [← baseChange_integralModel_eq v.valuationSubring W]
    exact map_negY _ x y
  have hy' : (y : F) ≠ W.negY x y := by
    rw [hneg, Ne, Subtype.coe_inj]
    intro h
    exact hne (by rw [negY] at h; linear_combination h)
  -- the coefficients of `W` are those of `Wo`
  have ha₁ : ((Wo.a₁ : v.valuationSubring) : F) = W.a₁ := by
    simpa using integralModel_a₁_eq v.valuationSubring W
  have ha₂ : ((Wo.a₂ : v.valuationSubring) : F) = W.a₂ := by
    simpa using integralModel_a₂_eq v.valuationSubring W
  have ha₃ : ((Wo.a₃ : v.valuationSubring) : F) = W.a₃ := by
    simpa using integralModel_a₃_eq v.valuationSubring W
  have ha₄ : ((Wo.a₄ : v.valuationSubring) : F) = W.a₄ := by
    simpa using integralModel_a₄_eq v.valuationSubring W
  have h2 : ((2 : v.valuationSubring) : F) = 2 := by
    simpa using map_ofNat (algebraMap v.valuationSubring F) 2
  have h3 : ((3 : v.valuationSubring) : F) = 3 := by
    simpa using map_ofNat (algebraMap v.valuationSubring F) 3
  have hslopeF : W.slope (x : F) x y y = ℓ := by
    rw [slope_of_Y_ne rfl hy', div_eq_iff (sub_ne_zero.2 hy')]
    have := congrArg ((↑) : v.valuationSubring → F) hslope
    push_cast at this
    rw [ha₁, ha₂, ha₃, ha₄, h2, h3] at this
    rw [negY]
    linear_combination -this
  have hx₃ : Wo.toAffine.addX x x ℓ ∈ maximalIdeal v.valuationSubring :=
    sub_mem (sub_mem (sub_mem (add_mem (Ideal.pow_mem_of_mem _ hℓ 2 two_pos)
      (Ideal.mul_mem_left _ _ hℓ)) h₂) hx) hx
  have hy₃ : Wo.toAffine.addY x x y ℓ ∈ maximalIdeal v.valuationSubring :=
    sub_mem (sub_mem (neg_mem (add_mem (Ideal.mul_mem_right _ _ hℓ) hy))
      (Ideal.mul_mem_left _ _ hx₃)) h₃
  -- the coordinates of `2 P` are the images of those computed in the integral model
  have hX₃ : W.addX x x ℓ = ((Wo.toAffine.addX x x ℓ : v.valuationSubring) : F) := by
    conv_lhs => rw [← baseChange_integralModel_eq v.valuationSubring W]
    exact map_addX _ x x ℓ
  have hY₃ : W.addY x x y ℓ = ((Wo.toAffine.addY x x y ℓ : v.valuationSubring) : F) := by
    conv_lhs => rw [← baseChange_integralModel_eq v.valuationSubring W]
    exact map_addY _ x y x ℓ
  rw [two_nsmul, Point.add_self_of_Y_ne hy', some_notMem_nonsingularReduction_iff v h₃ h₄ h₆,
    hslopeF, hX₃, hY₃]
  exact ⟨(Valuation.mem_maximalIdeal_iff (v := v)).1 hx₃,
    (Valuation.mem_maximalIdeal_iff (v := v)).1 hy₃⟩

/-- **At the symbol `IV*`, twice a point with singular reduction has singular reduction.** At
`(ϖ² X, ϖ² Y)` the tangent has slope `(3 x² + 2 a₂ x + a₄ − a₁ y) / (2 y + a₁ x + a₃)`, whose
numerator is `ϖ³` times an integer and whose denominator is `ϖ²` times a unit, since the derivative
`2 Y + A₃` of the residue quadratic at its simple root `Y` is a unit. So the slope lies in `𝔪`. -/
private theorem two_nsmul_notMem_of_isTateTerminal_IVStar {ϖ : v.valuationSubring}
    (hϖ : maximalIdeal v.valuationSubring = Ideal.span {ϖ})
    (h : (integralModel v.valuationSubring W).IsTateTerminal ϖ .IVStar) {x y : v.valuationSubring}
    {hxy : W.Nonsingular x y} (hP : Point.some _ _ hxy ∉ W.nonsingularReduction v) :
    2 • Point.some _ _ hxy ∉ W.nonsingularReduction v := by
  obtain ⟨⟨A₁, hA₁⟩, ⟨A₂, hA₂⟩, ⟨A₃, h₃⟩, ⟨A₄, hA₄⟩, ⟨A₆, h₆⟩, -⟩ := isTateTerminal_IVStar.1 h
  have key (z : v.valuationSubring) : z ∈ maximalIdeal v.valuationSubring ↔ ϖ ∣ z := by
    rw [hϖ, Ideal.mem_span_singleton]
  obtain ⟨hp, hb⟩ := IsTateTerminal.prime_and_not_dvd_of_IVStar
    (hϖ ▸ (maximalIdeal.isMaximal _).isPrime) h h₃ h₆
  obtain ⟨X, Y, rfl, rfl, hY⟩ :=
    exists_eq_sq_mul_of_notMem_of_isTateTerminal_IVStar v hϖ h h₃ h₆ hP
  -- the denominator `2 y + a₁ x + a₃` of the tangent slope is `ϖ² D` with `D` a unit
  have hDu : IsUnit (2 * Y + A₃ + ϖ * A₁ * X) := by
    by_contra hn
    refine not_dvd_two_mul_add (ϖ := ϖ) hb hY ?_
    rw [show 2 * Y + A₃ = (2 * Y + A₃ + ϖ * A₁ * X) - ϖ * (A₁ * X) by ring]
    exact dvd_sub ((key _).1 ((mem_maximalIdeal _).2 hn)) (dvd_mul_right _ _)
  have hden : 2 * (ϖ ^ 2 * Y) + (integralModel v.valuationSubring W).a₁ * (ϖ ^ 2 * X) +
      (integralModel v.valuationSubring W).a₃ = ϖ ^ 2 * (2 * Y + A₃ + ϖ * A₁ * X) := by
    rw [hA₁, h₃]
    ring
  -- the slope is `ϖ N / D`, where the numerator `3 x² + 2 a₂ x + a₄ − a₁ y` is `ϖ³ N`
  refine two_nsmul_notMem_of_slope_mem v ((key _).2 ⟨ϖ * A₂, by rw [hA₂]; ring⟩)
    ((key _).2 ⟨ϖ * A₃, by rw [h₃]; ring⟩) ((key _).2 ⟨ϖ ^ 2 * A₄, by rw [hA₄]; ring⟩)
    ((key _).2 ⟨ϖ ^ 3 * A₆, by rw [h₆]; ring⟩) ((key _).2 ⟨ϖ * X, by ring⟩)
    ((key _).2 ⟨ϖ * Y, by ring⟩)
    (ℓ := ϖ * ((3 * ϖ * X ^ 2 + 2 * ϖ * A₂ * X + A₄ - A₁ * Y) * ↑hDu.unit⁻¹))
    ((key _).2 (dvd_mul_right _ _)) ?_ ?_
  · rw [hden]
    exact mul_ne_zero (pow_ne_zero 2 hp.ne_zero) hDu.ne_zero
  · rw [hden, hA₁, hA₂, hA₄]
    linear_combination (ϖ ^ 3 * (3 * ϖ * X ^ 2 + 2 * ϖ * A₂ * X + A₄ - A₁ * Y)) *
      hDu.val_inv_mul

/-! ### The index at `IV*` -/

/-- **At the reduction symbol `IV*`, if some point has singular reduction, then
`[E(F) : E₀(F)] = 3`.** Here `ϖ` generates the maximal ideal of the valuation ring, and Tate's
algorithm, run on the integral model with uniformiser `ϖ`, stops with the symbol `IV*`:
`ϖ ∣ a₁`, `ϖ² ∣ a₂`, `ϖ² ∣ a₃`, `ϖ³ ∣ a₄`, `ϖ⁴ ∣ a₆` and `ϖ⁵ ∤ b₆`. If `P` has singular reduction,
then `E₀(F)`, `P + E₀(F)` and `-P + E₀(F)` are the three cosets. -/
theorem index_nonsingularReduction_eq_three_of_isTateTerminal_IVStar_of_notMem
    {ϖ : v.valuationSubring} (hϖ : maximalIdeal v.valuationSubring = Ideal.span {ϖ})
    (h : (integralModel v.valuationSubring W).IsTateTerminal ϖ .IVStar) {P : W.Point}
    (hP : P ∉ W.nonsingularReduction v) : (W.nonsingularReduction v).index = 3 := by
  obtain ⟨ha₁, -, ⟨A₃, h₃⟩, h₄, ⟨A₆, h₆⟩, -⟩ := isTateTerminal_IVStar.1 h
  have key (z : v.valuationSubring) : z ∈ maximalIdeal v.valuationSubring ↔ ϖ ∣ z := by
    rw [hϖ, Ideal.mem_span_singleton]
  obtain ⟨hp, hb⟩ := IsTateTerminal.prime_and_not_dvd_of_IVStar
    (hϖ ▸ (maximalIdeal.isMaximal _).isPrime) h h₃ h₆
  have m₃ : (integralModel v.valuationSubring W).a₃ ∈ maximalIdeal v.valuationSubring :=
    (key _).2 ⟨ϖ * A₃, by rw [h₃]; ring⟩
  have m₄ : (integralModel v.valuationSubring W).a₄ ∈ maximalIdeal v.valuationSubring :=
    (key _).2 ((dvd_pow_self ϖ three_ne_zero).trans h₄)
  have m₆ : (integralModel v.valuationSubring W).a₆ ∈ maximalIdeal v.valuationSubring :=
    (key _).2 ⟨ϖ ^ 3 * A₆, by rw [h₆]; ring⟩
  obtain ⟨x₀, y₀, h₀, rfl, -, -⟩ := exists_eq_some_of_notMem_nonsingularReduction v m₃ m₄ m₆ hP
  obtain ⟨X₀, Y₀, hx₀, hy₀, hY₀⟩ :=
    exists_eq_sq_mul_of_notMem_of_isTateTerminal_IVStar v hϖ h h₃ h₆ hP
  -- the derivative `2 Y₀ + A₃` of the residue quadratic at `Y₀` is a unit
  have hY₀' : ¬ ϖ ∣ 2 * Y₀ + A₃ := not_dvd_two_mul_add hb hY₀
  refine AddSubgroup.index_eq_three_of_two_nsmul_notMem
    (two_nsmul_notMem_of_isTateTerminal_IVStar v hϖ h hP) fun Q ↦ ?_
  by_cases hQ : Q ∈ W.nonsingularReduction v
  · exact Or.inl hQ
  obtain ⟨x, y, hxy, rfl, -, -⟩ := exists_eq_some_of_notMem_nonsingularReduction v m₃ m₄ m₆ hQ
  obtain ⟨X, Y, -, hy, hY⟩ := exists_eq_sq_mul_of_notMem_of_isTateTerminal_IVStar v hϖ h h₃ h₆ hQ
  -- `Y` is congruent to one of the two roots `Y₀` and `-Y₀ - A₃` of the residue quadratic
  have hcancel {z : v.valuationSubring} (hz : ϖ ^ 3 ∣ ϖ ^ 2 * z) : ϖ ∣ z :=
    (mul_dvd_mul_iff_left (pow_ne_zero 2 hp.ne_zero)).1 (by rwa [← pow_succ])
  rcases hp.dvd_or_dvd (show ϖ ∣ (Y - Y₀) * (Y + Y₀ + A₃) by
    rw [show (Y - Y₀) * (Y + Y₀ + A₃) = (Y ^ 2 + A₃ * Y - A₆) - (Y₀ ^ 2 + A₃ * Y₀ - A₆) by ring]
    exact dvd_sub hY hY₀) with hd | hd
  · -- `Q` is in the class of `P`, so `-P + Q ∈ E₀(F)`
    refine Or.inr (Or.inl (by_contra fun hn ↦ hY₀' ?_))
    -- the point `-P` in integral coordinates
    set y₀' := (integralModel v.valuationSubring W).toAffine.negY x₀ y₀
    have hy₀' : W.negY x₀ y₀ = y₀' := by
      conv_lhs => rw [← baseChange_integralModel_eq v.valuationSubring W]
      exact map_negY _ x₀ y₀
    have h₀' : W.Nonsingular x₀ y₀' := hy₀' ▸ (nonsingular_neg ..).2 h₀
    have hneg : -Point.some _ _ h₀ = Point.some _ _ h₀' := by
      rw [Point.neg_some, Point.some.injEq]
      exact ⟨rfl, hy₀'⟩
    rw [hneg] at hn
    have hd' := pow_three_dvd_sub_of_isTateTerminal_IVStar v hϖ h
      (by rwa [← hneg, neg_mem_iff]) hQ hn
    -- so `ϖ³ ∣ y₀' - y = ϖ² (-Y₀ - A₃ - Y) - a₁ x₀`, with `ϖ³ ∣ a₁ x₀`
    have hax : ϖ ^ 3 ∣ (integralModel v.valuationSubring W).a₁ * x₀ := by
      rw [hx₀, pow_succ']
      exact mul_dvd_mul ha₁ (dvd_mul_right _ _)
    have hd'' := hcancel (show ϖ ^ 3 ∣ ϖ ^ 2 * (-Y₀ - A₃ - Y) by
      rw [show ϖ ^ 2 * (-Y₀ - A₃ - Y) = (y₀' - y) + (integralModel v.valuationSubring W).a₁ * x₀ by
        simp only [y₀', negY]
        rw [hy₀, hy, h₃]
        ring]
      exact dvd_add hd' hax)
    rw [show 2 * Y₀ + A₃ = -(-Y₀ - A₃ - Y) - (Y - Y₀) by ring]
    exact dvd_sub (dvd_neg.2 hd'') hd
  · -- `Q` is in the class of `-P`, so `P + Q ∈ E₀(F)`
    refine Or.inr (Or.inr (by_contra fun hn ↦ hY₀' ?_))
    have hd' := hcancel (show ϖ ^ 3 ∣ ϖ ^ 2 * (Y₀ - Y) by
      rw [mul_sub, ← hy₀, ← hy]
      exact pow_three_dvd_sub_of_isTateTerminal_IVStar v hϖ h hP hQ hn)
    rw [show 2 * Y₀ + A₃ = (Y + Y₀ + A₃) + (Y₀ - Y) by ring]
    exact dvd_add hd hd'

/-- **At the reduction symbol `IV*`, `[E(F) : E₀(F)]` divides `3`.** It is `3` when some point has
singular reduction, and `1` otherwise. Here `ϖ` generates the maximal ideal of the valuation ring,
and Tate's algorithm, run on the integral model with uniformiser `ϖ`, stops with the symbol
`IV*`. -/
theorem index_nonsingularReduction_dvd_three_of_isTateTerminal_IVStar {ϖ : v.valuationSubring}
    (hϖ : maximalIdeal v.valuationSubring = Ideal.span {ϖ})
    (h : (integralModel v.valuationSubring W).IsTateTerminal ϖ .IVStar) :
    (W.nonsingularReduction v).index ∣ 3 := by
  by_cases hP : ∃ P, P ∉ W.nonsingularReduction v
  · obtain ⟨P, hP⟩ := hP
    rw [index_nonsingularReduction_eq_three_of_isTateTerminal_IVStar_of_notMem v hϖ h hP]
  · push Not at hP
    rw [AddSubgroup.index_eq_one.2 (eq_top_iff.2 fun P _ ↦ hP P)]
    exact one_dvd 3

/-- **At the reduction symbol `IV*`, some point has singular reduction** when the valuation ring
is Henselian, for instance complete, and the residue quadratic `T² + A₃ T − A₆` has a root in the
residue field, where `a₃ = ϖ² A₃` and `a₆ = ϖ⁴ A₆`. Here `ϖ` generates the maximal ideal of the
valuation ring, and Tate's algorithm, run on the integral model with uniformiser `ϖ`, stops with
the symbol `IV*`. The root is simple, so it lifts to a root `Y` of `T² + A₃ T − A₆`, and the point
is `(0, ϖ² Y)`. -/
theorem exists_notMem_nonsingularReduction_of_isTateTerminal_IVStar
    [HenselianLocalRing v.valuationSubring] {ϖ : v.valuationSubring}
    (hϖ : maximalIdeal v.valuationSubring = Ideal.span {ϖ})
    (h : (integralModel v.valuationSubring W).IsTateTerminal ϖ .IVStar) {A₃ A₆ : v.valuationSubring}
    (h₃ : (integralModel v.valuationSubring W).a₃ = ϖ ^ 2 * A₃)
    (h₆ : (integralModel v.valuationSubring W).a₆ = ϖ ^ 4 * A₆)
    (hroot : ∃ t : ResidueField v.valuationSubring, t ^ 2 + residue _ A₃ * t - residue _ A₆ = 0) :
    ∃ P : W.Point, P ∉ W.nonsingularReduction v := by
  obtain ⟨-, -, -, h₄, -, -⟩ := isTateTerminal_IVStar.1 h
  have key (z : v.valuationSubring) : z ∈ maximalIdeal v.valuationSubring ↔ ϖ ∣ z := by
    rw [hϖ, Ideal.mem_span_singleton]
  obtain ⟨hp, hb⟩ := IsTateTerminal.prime_and_not_dvd_of_IVStar
    (hϖ ▸ (maximalIdeal.isMaximal _).isPrime) h h₃ h₆
  -- lift the root of the residue quadratic by Hensel's lemma
  obtain ⟨t, ht⟩ := hroot
  obtain ⟨t₀, rfl⟩ := residue_surjective t
  set f : v.valuationSubring[X] := X ^ 2 + C A₃ * X - C A₆ with hf
  have hmon : f.Monic := by
    rw [hf]
    monicity!
  have heval (z : v.valuationSubring) : f.eval z = z ^ 2 + A₃ * z - A₆ := by
    simp [hf]
  have hder (z : v.valuationSubring) : f.derivative.eval z = 2 * z + A₃ := by
    simp [hf, one_add_one_eq_two]
  have hq₀ : ϖ ∣ t₀ ^ 2 + A₃ * t₀ - A₆ :=
    (key _).1 ((residue_eq_zero_iff _).1 (by simpa using ht))
  obtain ⟨Y, hY, -⟩ := HenselianLocalRing.is_henselian f hmon t₀
    ((key _).2 (heval t₀ ▸ hq₀)) (by
      rw [hder, ← residue_ne_zero_iff_isUnit, Ne, residue_eq_zero_iff, key]
      exact not_dvd_two_mul_add hb hq₀)
  have hY : Y ^ 2 + A₃ * Y - A₆ = 0 := heval Y ▸ hY.eq_zero
  have hY' : ¬ ϖ ∣ 2 * Y + A₃ := not_dvd_two_mul_add hb (hY ▸ dvd_zero ϖ)
  have hns : (integralModel v.valuationSubring W).toAffine.Nonsingular 0 (ϖ ^ 2 * Y) := by
    rw [nonsingular_iff']
    refine ⟨by
      rw [equation_iff, h₃, h₆]
      linear_combination ϖ ^ 4 * hY, Or.inr ?_⟩
    rw [h₃, mul_zero, add_zero, show 2 * (ϖ ^ 2 * Y) + ϖ ^ 2 * A₃ = ϖ ^ 2 * (2 * Y + A₃) by ring]
    exact mul_ne_zero (pow_ne_zero 2 hp.ne_zero) fun h0 ↦ hY' (h0 ▸ dvd_zero ϖ)
  have hF :
      W.Nonsingular ((0 : v.valuationSubring) : F) ((ϖ ^ 2 * Y : v.valuationSubring) : F) := by
    have := ((integralModel v.valuationSubring W).toAffine.map_nonsingular
      (IsFractionRing.injective _ F) _ _).mpr hns
    rwa [← baseChange_integralModel_eq v.valuationSubring W]
  have hy : v ((ϖ ^ 2 * Y : v.valuationSubring) : F) < 1 :=
    (Valuation.mem_maximalIdeal_iff (v := v)).1 ((key _).2 (Dvd.intro (ϖ * Y) (by ring)))
  exact ⟨Point.some _ _ hF, (some_notMem_nonsingularReduction_iff v
    ((key _).2 ⟨ϖ * A₃, by rw [h₃]; ring⟩) ((key _).2 ((dvd_pow_self ϖ three_ne_zero).trans h₄))
    ((key _).2 ⟨ϖ ^ 3 * A₆, by rw [h₆]; ring⟩) hF).2 ⟨by simp, hy⟩⟩

/-- **At the reduction symbol `IV*`, `[E(F) : E₀(F)] = 3`** when the valuation ring is Henselian,
for instance complete, and the residue quadratic `T² + A₃ T − A₆` has a root in the residue field,
where `a₃ = ϖ² A₃` and `a₆ = ϖ⁴ A₆`. This is the local index `c_v = 3` that Tate's algorithm
reports at `IV*` in that case. Here `ϖ` generates the maximal ideal of the valuation ring, and
Tate's algorithm, run on the integral model with uniformiser `ϖ`, stops with the symbol `IV*`. -/
theorem index_nonsingularReduction_eq_three_of_isTateTerminal_IVStar
    [HenselianLocalRing v.valuationSubring] {ϖ : v.valuationSubring}
    (hϖ : maximalIdeal v.valuationSubring = Ideal.span {ϖ})
    (h : (integralModel v.valuationSubring W).IsTateTerminal ϖ .IVStar) {A₃ A₆ : v.valuationSubring}
    (h₃ : (integralModel v.valuationSubring W).a₃ = ϖ ^ 2 * A₃)
    (h₆ : (integralModel v.valuationSubring W).a₆ = ϖ ^ 4 * A₆)
    (hroot : ∃ t : ResidueField v.valuationSubring, t ^ 2 + residue _ A₃ * t - residue _ A₆ = 0) :
    (W.nonsingularReduction v).index = 3 := by
  obtain ⟨P, hP⟩ := exists_notMem_nonsingularReduction_of_isTateTerminal_IVStar v hϖ h h₃ h₆ hroot
  exact index_nonsingularReduction_eq_three_of_isTateTerminal_IVStar_of_notMem v hϖ h hP

end Affine

end WeierstrassCurve

end

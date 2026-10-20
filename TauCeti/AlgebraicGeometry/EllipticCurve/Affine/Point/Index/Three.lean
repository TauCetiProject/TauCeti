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
-- Proof-only: the coordinates of a solution in `(ϖ)` on the normal form at `IV*`.
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.StarredReduction
-- Proof-only: lifting roots of a quadratic with unit discriminant.
import TauCeti.RingTheory.LocalRing.QuadraticDoubleRoot
-- Proof-only: divisibility and the derivative of a quadratic.
import TauCeti.Algebra.QuadraticDiscriminant
-- Proof-only: index three from a covering by three cosets.
import TauCeti.GroupTheory.Index.Three
import TauCeti.RingTheory.LocalRing.MaximalIdeal.Generator

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

open IsLocalRing Polynomial TauCeti
open TauCeti.IsLocalRing (mem_maximalIdeal_iff_dvd)

namespace WeierstrassCurve

namespace Affine

variable {F Γ₀ : Type*} [Field F] [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation F Γ₀)
  {W : Affine F} [IsIntegral v.valuationSubring W]

/-- At the symbol `IV*`, the uniformiser is prime and the reduction is singular at the origin:
`a₃`, `a₄` and `a₆` lie in the maximal ideal. -/
private theorem prime_and_mem_maximalIdeal_of_isTateTerminal_IVStar {ϖ : v.valuationSubring}
    (hϖ : maximalIdeal v.valuationSubring = Ideal.span {ϖ})
    (h : (integralModel v.valuationSubring W).IsTateTerminal ϖ .IVStar) :
    Prime ϖ ∧ (integralModel v.valuationSubring W).a₃ ∈ maximalIdeal v.valuationSubring ∧
      (integralModel v.valuationSubring W).a₄ ∈ maximalIdeal v.valuationSubring ∧
      (integralModel v.valuationSubring W).a₆ ∈ maximalIdeal v.valuationSubring := by
  obtain ⟨-, -, ⟨A₃, h₃⟩, -, ⟨A₆, h₆⟩, -⟩ := isTateTerminal_IVStar.1 h
  obtain ⟨-, d₃, d₄, d₆⟩ := h.dvd_b₂_and_dvd_a₃_and_dvd_a₄_and_dvd_a₆ fun _ ↦ nofun
  refine ⟨(IsTateTerminal.prime_and_not_dvd_of_IVStar
    (hϖ ▸ (maximalIdeal.isMaximal _).isPrime) h h₃ h₆).1, ?_⟩
  simp only [hϖ, Ideal.mem_span_singleton]
  exact ⟨d₃, d₄, d₆⟩

/-- **At the symbol `IV*`, negation exchanges the two classes.** The negative of a point
`(ϖ² X, ϖ² Y)` is `(ϖ² X, ϖ² Y')` with `ϖ ∣ Y' + Y + A₃`, where `a₃ = ϖ² A₃`, since
`-(x, y) = (x, -y - a₁ x - a₃)` and `ϖ ∣ a₁`. -/
private theorem exists_neg_eq_of_isTateTerminal_IVStar {ϖ : v.valuationSubring}
    (h : (integralModel v.valuationSubring W).IsTateTerminal ϖ .IVStar) {A₃ : v.valuationSubring}
    (h₃ : (integralModel v.valuationSubring W).a₃ = ϖ ^ 2 * A₃) {x y X Y : v.valuationSubring}
    {hxy : W.Nonsingular x y} (hx : x = ϖ ^ 2 * X) (hy : y = ϖ ^ 2 * Y) :
    ∃ (Y' : v.valuationSubring) (h' : W.Nonsingular x ((ϖ ^ 2 * Y' : v.valuationSubring) : F)),
      -Point.some _ _ hxy = Point.some _ _ h' ∧ ϖ ∣ Y' + Y + A₃ := by
  obtain ⟨A₁, hA₁⟩ := (isTateTerminal_IVStar.1 h).1
  have hneg : W.negY x y = ((ϖ ^ 2 * (-Y - A₃ - ϖ * A₁ * X) : v.valuationSubring) : F) := by
    rw [← coe_negY_integralModel, negY, hx, hy, hA₁, h₃]
    congr 1
    ring
  refine ⟨_, hneg ▸ (nonsingular_neg ..).2 hxy, ?_, ⟨-(A₁ * X), by ring⟩⟩
  rw [Point.neg_some, Point.some.injEq]
  exact ⟨rfl, hneg⟩

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
  obtain ⟨hp, m₃, m₄, m₆⟩ := prime_and_mem_maximalIdeal_of_isTateTerminal_IVStar v hϖ h
  obtain ⟨hx, hy⟩ := (some_notMem_nonsingularReduction_iff v m₃ m₄ m₆ hxy).1 hP
  exact exists_eq_sq_mul_of_equation _ hp h₁ h₂ h₃ h₄ h₆
    ((equation_integralModel_iff v).2 hxy.left)
    ((mem_maximalIdeal_iff_dvd hϖ).1 ((Valuation.mem_maximalIdeal_iff (v := v)).2 hx))
    ((mem_maximalIdeal_iff_dvd hϖ).1 ((Valuation.mem_maximalIdeal_iff (v := v)).2 hy))

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
  obtain ⟨ha₁, ha₂, ⟨A₃, h₃⟩, -, ⟨A₆, h₆⟩, -⟩ := isTateTerminal_IVStar.1 h
  obtain ⟨hp, m₃, m₄, m₆⟩ := prime_and_mem_maximalIdeal_of_isTateTerminal_IVStar v hϖ h
  obtain ⟨X₁, -, rfl, -, -⟩ := exists_eq_sq_mul_of_notMem_of_isTateTerminal_IVStar v hϖ h h₃ h₆ hP
  obtain ⟨X₂, -, rfl, -, -⟩ := exists_eq_sq_mul_of_notMem_of_isTateTerminal_IVStar v hϖ h h₃ h₆ hQ
  obtain ⟨x₃, -, ℓ, -, -, -, hx₃, -, hs, hL, -⟩ :=
    exists_chord_of_add_notMem_nonsingularReduction v m₃ m₄ m₆ hPQ
  -- the slope is divisible by `ϖ`, since `ℓ² = x₁ + x₂ + x₃ + a₂ − a₁ ℓ`
  have hℓ : ϖ ∣ ℓ := by
    refine hp.dvd_of_dvd_pow (n := 2) ?_
    rw [show ℓ ^ 2 = ϖ * (ϖ * X₁) + ϖ * (ϖ * X₂) + x₃ + (integralModel v.valuationSubring W).a₂ -
        (integralModel v.valuationSubring W).a₁ * ℓ by linear_combination hs]
    exact dvd_sub (dvd_add (dvd_add (dvd_add (dvd_mul_right _ _) (dvd_mul_right _ _))
      ((mem_maximalIdeal_iff_dvd hϖ).1 hx₃)) ((dvd_pow_self ϖ two_ne_zero).trans ha₂))
      (ha₁.mul_right ℓ)
  rw [hL, show ϖ ^ 2 * X₁ - ϖ ^ 2 * X₂ = ϖ ^ 2 * (X₁ - X₂) by ring, pow_succ']
  exact mul_dvd_mul hℓ (dvd_mul_right _ _)

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
  obtain ⟨-, m₃, m₄, m₆⟩ := prime_and_mem_maximalIdeal_of_isTateTerminal_IVStar v hϖ h
  obtain ⟨hp, hb⟩ := IsTateTerminal.prime_and_not_dvd_of_IVStar
    (hϖ ▸ (maximalIdeal.isMaximal _).isPrime) h h₃ h₆
  obtain ⟨X, Y, rfl, rfl, hY⟩ :=
    exists_eq_sq_mul_of_notMem_of_isTateTerminal_IVStar v hϖ h h₃ h₆ hP
  -- the denominator `2 y + a₁ x + a₃` of the tangent slope is `ϖ² D` with `D` a unit
  have hDu : IsUnit (2 * Y + A₃ + ϖ * A₁ * X) := by
    by_contra hn
    refine not_dvd_two_mul_add_of_not_dvd_sq_add_four_mul (p := ϖ) hb hY ?_
    rw [show 2 * Y + A₃ = (2 * Y + A₃ + ϖ * A₁ * X) - ϖ * (A₁ * X) by ring]
    exact dvd_sub ((mem_maximalIdeal_iff_dvd hϖ).1 ((mem_maximalIdeal _).2 hn)) (dvd_mul_right _ _)
  have hden : 2 * (ϖ ^ 2 * Y) + (integralModel v.valuationSubring W).a₁ * (ϖ ^ 2 * X) +
      (integralModel v.valuationSubring W).a₃ = ϖ ^ 2 * (2 * Y + A₃ + ϖ * A₁ * X) := by
    rw [hA₁, h₃]
    ring
  -- the slope is `ϖ N / D`, where the numerator `3 x² + 2 a₂ x + a₄ − a₁ y` is `ϖ³ N`
  refine two_nsmul_notMem_of_slope_mem v
    ((mem_maximalIdeal_iff_dvd hϖ).2 ⟨ϖ * A₂, by rw [hA₂]; ring⟩) m₃ m₄ m₆
    ((mem_maximalIdeal_iff_dvd hϖ).2 ⟨ϖ * X, by ring⟩)
    ((mem_maximalIdeal_iff_dvd hϖ).2 ⟨ϖ * Y, by ring⟩)
    (ℓ := ϖ * ((3 * ϖ * X ^ 2 + 2 * ϖ * A₂ * X + A₄ - A₁ * Y) * ↑hDu.unit⁻¹))
    ((mem_maximalIdeal_iff_dvd hϖ).2 (dvd_mul_right _ _)) ?_ ?_
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
  obtain ⟨-, -, ⟨A₃, h₃⟩, -, ⟨A₆, h₆⟩, -⟩ := isTateTerminal_IVStar.1 h
  obtain ⟨hp, hb⟩ := IsTateTerminal.prime_and_not_dvd_of_IVStar
    (hϖ ▸ (maximalIdeal.isMaximal _).isPrime) h h₃ h₆
  obtain ⟨-, m₃, m₄, m₆⟩ := prime_and_mem_maximalIdeal_of_isTateTerminal_IVStar v hϖ h
  obtain ⟨x₀, y₀, h₀, rfl, -, -⟩ := exists_eq_some_of_notMem_nonsingularReduction v m₃ m₄ m₆ hP
  obtain ⟨X₀, Y₀, hx₀, hy₀, hY₀⟩ :=
    exists_eq_sq_mul_of_notMem_of_isTateTerminal_IVStar v hϖ h h₃ h₆ hP
  -- the derivative `2 Y₀ + A₃` of the residue quadratic at `Y₀` is a unit
  have hY₀' : ¬ ϖ ∣ 2 * Y₀ + A₃ := not_dvd_two_mul_add_of_not_dvd_sq_add_four_mul hb hY₀
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
    -- `-P = (x₀, ϖ² Y₀')` with `Y₀' ≡ -Y₀ - A₃`, and `-P`, `Q` are in the same class
    obtain ⟨Y₀', h₀', hneg, hY₀''⟩ :=
      exists_neg_eq_of_isTateTerminal_IVStar v h h₃ hx₀ hy₀ (hxy := h₀)
    rw [hneg] at hn
    have hd' := hcancel (show ϖ ^ 3 ∣ ϖ ^ 2 * (Y₀' - Y) by
      rw [mul_sub, ← hy]
      exact pow_three_dvd_sub_of_isTateTerminal_IVStar v hϖ h (by rwa [← hneg, neg_mem_iff]) hQ hn)
    rw [show 2 * Y₀ + A₃ = (Y₀' + Y₀ + A₃) - (Y₀' - Y) - (Y - Y₀) by ring]
    exact dvd_sub (dvd_sub hY₀'' hd') hd
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
  obtain ⟨-, m₃, m₄, m₆⟩ := prime_and_mem_maximalIdeal_of_isTateTerminal_IVStar v hϖ h
  obtain ⟨hp, hb⟩ := IsTateTerminal.prime_and_not_dvd_of_IVStar
    (hϖ ▸ (maximalIdeal.isMaximal _).isPrime) h h₃ h₆
  -- lift the root of the residue quadratic by Hensel's lemma
  obtain ⟨t, ht⟩ := hroot
  obtain ⟨t₀, rfl⟩ := residue_surjective t
  obtain ⟨Y, hY, -, hu⟩ := TauCeti.HenselianLocalRing.exists_quadratic_root_of_isUnit_discriminant
    ((TauCeti.IsLocalRing.isUnit_iff_not_dvd hϖ).2 hb)
    ((residue_eq_zero_iff _).1 (by simpa using ht))
  have hY' : ¬ ϖ ∣ 2 * Y + A₃ := (TauCeti.IsLocalRing.isUnit_iff_not_dvd hϖ).1 hu
  have hns : (integralModel v.valuationSubring W).toAffine.Nonsingular 0 (ϖ ^ 2 * Y) := by
    rw [nonsingular_iff']
    refine ⟨by
      rw [equation_iff, h₃, h₆]
      linear_combination ϖ ^ 4 * hY, Or.inr ?_⟩
    rw [h₃, mul_zero, add_zero, show 2 * (ϖ ^ 2 * Y) + ϖ ^ 2 * A₃ = ϖ ^ 2 * (2 * Y + A₃) by ring]
    exact mul_ne_zero (pow_ne_zero 2 hp.ne_zero) fun h0 ↦ hY' (h0 ▸ dvd_zero ϖ)
  have hF := (nonsingular_integralModel_iff v).1 hns
  have hy : v ((ϖ ^ 2 * Y : v.valuationSubring) : F) < 1 :=
    (Valuation.mem_maximalIdeal_iff (v := v)).1
      ((mem_maximalIdeal_iff_dvd hϖ).2 (Dvd.intro (ϖ * Y) (by ring)))
  exact ⟨Point.some _ _ hF, (some_notMem_nonsingularReduction_iff v m₃ m₄ m₆ hF).2 ⟨by simp, hy⟩⟩

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

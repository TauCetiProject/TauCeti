/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.StarredReduction
public import TauCeti.AlgebraicGeometry.EllipticCurve.TateAlgorithm.LocalIndex
import TauCeti.Algebra.Polynomial.Cubic.RepeatedRoot

/-!
# Points with singular reduction: the residue cubic at `I₀*`

Let `v` be a valuation on a field `F` whose valuation ring `O` has maximal ideal `𝔪 = (ϖ)`, and
let `W` be a Weierstrass curve over `F` with an integral model `W_O` over `O`. The points with
nonsingular reduction form the subgroup `E₀(F)` of `W(F)`
(`WeierstrassCurve.Affine.nonsingularReduction`). When `F` is complete for a discrete valuation
with perfect residue field and the equation is minimal, the index `[E(F) : E₀(F)]` is the local
index `c_v` that Tate's algorithm computes (Silverman, *Advanced Topics*, IV.9, Table 4.1). This
file computes the index at the reduction symbol `I₀*`, where `c_v = 1 + N` with `N` the number of
roots in the residue field of the residue cubic `P(T) = T³ + (a₂/ϖ) T² + (a₄/ϖ²) T + a₆/ϖ³`.

Tate's algorithm stops at `I₀*` on an equation with `ϖ ∣ a₁`, `a₂ = ϖ A₂`, `ϖ² ∣ a₃`,
`a₄ = ϖ² A₄`, `a₆ = ϖ³ A₆` and `P = T³ + A₂ T² + A₄ T + A₆` of nonzero discriminant modulo `ϖ`. A
point with singular reduction is `(ϖ X, ϖ² Y)` with `X` and `Y` integral and the residue of `X` a
root of `P` (`WeierstrassCurve.exists_eq_mul_and_eq_sq_mul_of_equation`). This root sorts the
points with singular reduction into classes, which are the nontrivial cosets of `E₀(F)`. Let
`P₁ = (ϖ X₁, ϖ² Y₁)` and `P₂ = (ϖ X₂, ϖ² Y₂)` have singular reduction.

* If `X₁ ≢ X₂` modulo `ϖ`, then `P₁ + P₂` has singular reduction. Indeed `x₁ − x₂` is `ϖ` times a
  unit and `ϖ² ∣ y₁ − y₂`, so the chord through `P₁` and `P₂` has slope in `𝔪`
  (`WeierstrassCurve.Affine.add_notMem_of_slope_mem`).
* If `X₁ ≡ X₂` modulo `ϖ`, then `P₁ + P₂` has nonsingular reduction. Otherwise
  `P₁ + P₂ = (ϖ X₃, ϖ² Y₃)` has singular reduction as well, the slope of the chord lies in `𝔪`, and
  comparing coefficients in the Weierstrass cubic restricted to the chord shows that
  `P ≡ (T − X₁) (T − X₂) (T − X₃)` modulo `ϖ`. Then `P` has a repeated root modulo `ϖ`, against
  its nonzero discriminant.

Since negation preserves the `x`-coordinate, two points with singular reduction lie in the same
coset of `E₀(F)` exactly when their roots agree. Over a Henselian valuation ring every root of the
residue cubic occurs: it is simple, so it lifts to a root `X` of `P`, and `(ϖ X, 0)` is a point
with singular reduction. The nontrivial cosets of `E₀(F)` are therefore in bijection with the roots
of the residue cubic, and `[E(F) : E₀(F)] = 1 + N`. No completeness, discreteness, minimality or
hypothesis on the residue field is needed beyond the Henselian property.

## Main results

* `index_nonsingularReduction_eq_one_add_natCard_of_isTateTerminal_IStar_zero`, in the namespace
  `WeierstrassCurve.Affine`: at the symbol `I₀*` over a Henselian valuation ring, `[E(F) : E₀(F)]`
  is one more than the number of roots of the residue cubic, counted as
  `WeierstrassCurve.tateCubicRoots` in `O ⧸ (ϖ)`.

## References

* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, GTM 151, IV.9.
* J. Tate, *Algorithm for determining the type of a singular fibre in an elliptic pencil*, in
  *Modular Functions of One Variable IV*, LNM 476 (1975), 33–52.
-/

public section

open IsLocalRing Polynomial TauCeti

namespace WeierstrassCurve

namespace Affine

variable {F Γ₀ : Type*} [Field F] [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation F Γ₀)
  {W : Affine F} [IsIntegral v.valuationSubring W]

/-- At the symbol `I₀*`, the uniformiser is prime and the reduction is singular at the origin:
`a₃`, `a₄` and `a₆` lie in the maximal ideal. -/
private theorem prime_and_mem_maximalIdeal_of_isTateTerminal_IStar_zero {ϖ : v.valuationSubring}
    (hϖ : maximalIdeal v.valuationSubring = Ideal.span {ϖ})
    (h : (integralModel v.valuationSubring W).IsTateTerminal ϖ (.IStar 0)) :
    Prime ϖ ∧ (integralModel v.valuationSubring W).a₃ ∈ maximalIdeal v.valuationSubring ∧
      (integralModel v.valuationSubring W).a₄ ∈ maximalIdeal v.valuationSubring ∧
      (integralModel v.valuationSubring W).a₆ ∈ maximalIdeal v.valuationSubring := by
  obtain ⟨-, d₃, d₄, d₆⟩ := h.dvd_b₂_and_dvd_a₃_and_dvd_a₄_and_dvd_a₆ (by simp)
  refine ⟨(Ideal.span_singleton_prime (h.ne_zero (by simp))).mp
    (hϖ ▸ (maximalIdeal.isMaximal _).isPrime), ?_⟩
  simp only [hϖ, Ideal.mem_span_singleton]
  exact ⟨d₃, d₄, d₆⟩

/-- At the symbol `I₀*`, with `a₂ = ϖ A₂`, `a₄ = ϖ² A₄` and `a₆ = ϖ³ A₆`, the discriminant of the
residue cubic `T³ + A₂ T² + A₄ T + A₆` is not divisible by `ϖ`: the discriminant of
`T³ + a₂ T² + a₄ T + a₆` is `ϖ⁶` times it, and is not divisible by `ϖ⁷`. -/
private theorem not_dvd_discr_of_isTateTerminal_IStar_zero {ϖ : v.valuationSubring}
    (h : (integralModel v.valuationSubring W).IsTateTerminal ϖ (.IStar 0))
    {A₂ A₄ A₆ : v.valuationSubring} (h₂ : (integralModel v.valuationSubring W).a₂ = ϖ * A₂)
    (h₄ : (integralModel v.valuationSubring W).a₄ = ϖ ^ 2 * A₄)
    (h₆ : (integralModel v.valuationSubring W).a₆ = ϖ ^ 3 * A₆) :
    ¬ ϖ ∣ (Cubic.mk 1 A₂ A₄ A₆).discr := by
  obtain ⟨-, -, -, -, -, hd⟩ := isTateTerminal_IStar_zero.1 h
  refine fun hD ↦ hd ?_
  rw [h₂, h₄, h₆, show (Cubic.mk 1 (ϖ * A₂) (ϖ ^ 2 * A₄) (ϖ ^ 3 * A₆)).discr =
      ϖ ^ 6 * (Cubic.mk 1 A₂ A₄ A₆).discr by simp only [Cubic.discr]; ring, pow_succ]
  exact mul_dvd_mul_left _ hD

variable [DecidableEq F]

/-- At the symbol `I₀*`, a point with singular reduction is `(ϖ X, ϖ² Y)` with `X` and `Y`
integral and the residue of `X` a root of the residue cubic `T³ + A₂ T² + A₄ T + A₆`. -/
private theorem exists_eq_mul_of_notMem_of_isTateTerminal_IStar_zero {ϖ : v.valuationSubring}
    (hϖ : maximalIdeal v.valuationSubring = Ideal.span {ϖ})
    (h : (integralModel v.valuationSubring W).IsTateTerminal ϖ (.IStar 0))
    {A₂ A₄ A₆ : v.valuationSubring} (h₂ : (integralModel v.valuationSubring W).a₂ = ϖ * A₂)
    (h₄ : (integralModel v.valuationSubring W).a₄ = ϖ ^ 2 * A₄)
    (h₆ : (integralModel v.valuationSubring W).a₆ = ϖ ^ 3 * A₆) {x y : v.valuationSubring}
    {hxy : W.Nonsingular x y} (hP : Point.some _ _ hxy ∉ W.nonsingularReduction v) :
    ∃ X Y, x = ϖ * X ∧ y = ϖ ^ 2 * Y ∧ ϖ ∣ X ^ 3 + A₂ * X ^ 2 + A₄ * X + A₆ := by
  obtain ⟨h₁, -, h₃, -, -, -⟩ := isTateTerminal_IStar_zero.1 h
  obtain ⟨hp, m₃, m₄, m₆⟩ := prime_and_mem_maximalIdeal_of_isTateTerminal_IStar_zero v hϖ h
  have key (z : v.valuationSubring) : z ∈ maximalIdeal v.valuationSubring ↔ ϖ ∣ z := by
    rw [hϖ, Ideal.mem_span_singleton]
  obtain ⟨hx, hy⟩ := (some_notMem_nonsingularReduction_iff v m₃ m₄ m₆ hxy).1 hP
  exact exists_eq_mul_and_eq_sq_mul_of_equation _ hp h₁ h₂ h₃ h₄ h₆
    ((equation_integralModel_iff v).2 hxy.left)
    ((key _).1 ((Valuation.mem_maximalIdeal_iff (v := v)).2 hx))
    ((key _).1 ((Valuation.mem_maximalIdeal_iff (v := v)).2 hy))

/-- **At the symbol `I₀*`, two points in the same class add up into `E₀(F)`.** If `(x₁, y₁)` and
`(x₂, y₂)` have singular reduction and `ϖ² ∣ x₁ − x₂`, then their sum has nonsingular reduction.
Otherwise the sum is `(ϖ X₃, ϖ² Y₃)` with singular reduction, and comparing coefficients in the
Weierstrass cubic restricted to the chord gives
`T³ + A₂ T² + A₄ T + A₆ ≡ (T − X₁) (T − X₂) (T − X₃)` modulo `ϖ`, a cubic with the repeated root
`X₁ ≡ X₂`; but its discriminant is nonzero modulo `ϖ`. -/
private theorem add_mem_of_isTateTerminal_IStar_zero {ϖ : v.valuationSubring}
    (hϖ : maximalIdeal v.valuationSubring = Ideal.span {ϖ})
    (h : (integralModel v.valuationSubring W).IsTateTerminal ϖ (.IStar 0))
    {x₁ y₁ x₂ y₂ : v.valuationSubring} {h₁ : W.Nonsingular x₁ y₁} {h₂ : W.Nonsingular x₂ y₂}
    (hP : Point.some _ _ h₁ ∉ W.nonsingularReduction v)
    (hQ : Point.some _ _ h₂ ∉ W.nonsingularReduction v) (hx : ϖ ^ 2 ∣ x₁ - x₂) :
    Point.some _ _ h₁ + Point.some _ _ h₂ ∈ W.nonsingularReduction v := by
  obtain ⟨⟨A₁, hA₁⟩, ⟨A₂, hA₂⟩, ⟨A₃, hA₃⟩, ⟨A₄, hA₄⟩, ⟨A₆, hA₆⟩, -⟩ :=
    isTateTerminal_IStar_zero.1 h
  obtain ⟨hp, m₃, m₄, m₆⟩ := prime_and_mem_maximalIdeal_of_isTateTerminal_IStar_zero v hϖ h
  have hϖ0 := hp.ne_zero
  by_contra hPQ
  obtain ⟨X₁, Y₁, rfl, rfl, -⟩ :=
    exists_eq_mul_of_notMem_of_isTateTerminal_IStar_zero v hϖ h hA₂ hA₄ hA₆ hP
  obtain ⟨X₂, Y₂, rfl, rfl, -⟩ :=
    exists_eq_mul_of_notMem_of_isTateTerminal_IStar_zero v hϖ h hA₂ hA₄ hA₆ hQ
  obtain ⟨x₃, y₃, ℓ, h₃, hsum, -, -, -, hs, -, hc⟩ :=
    exists_chord_of_add_notMem_nonsingularReduction v m₃ m₄ m₆ hPQ
  rw [hsum] at hPQ
  obtain ⟨X₃, Y₃, rfl, -, -⟩ :=
    exists_eq_mul_of_notMem_of_isTateTerminal_IStar_zero v hϖ h hA₂ hA₄ hA₆ hPQ
  have hE := (equation_integralModel_iff v).2 h₁.left
  rw [equation_iff, hA₁, hA₂, hA₃, hA₄, hA₆] at hE
  rw [hA₁, hA₂] at hs
  rw [hA₁, hA₃, hA₄] at hc
  -- the slope is divisible by `ϖ`, since `ℓ² = x₁ + x₂ + x₃ + a₂ − a₁ ℓ`
  obtain ⟨L, rfl⟩ : ϖ ∣ ℓ := hp.dvd_of_dvd_pow (n := 2)
    ⟨X₁ + X₂ + X₃ + A₂ - A₁ * ℓ, by linear_combination hs⟩
  -- the coefficients of the cubic are the elementary symmetric functions of `X₁, X₂, X₃` mod `ϖ`
  have e₂ : A₂ + (X₁ + X₂ + X₃) = ϖ * (L ^ 2 + A₁ * L) :=
    mul_left_cancel₀ hϖ0 (by linear_combination -hs)
  have e₄ : A₄ - (X₁ * X₂ + X₁ * X₃ + X₂ * X₃) =
      ϖ * (A₃ * L + (2 * L + A₁) * (Y₁ - L * X₁)) :=
    mul_left_cancel₀ (pow_ne_zero 2 hϖ0) (by linear_combination hc)
  have e₆ : A₆ + X₁ * X₂ * X₃ = ϖ * ((Y₁ - L * X₁) ^ 2 + A₃ * (Y₁ - L * X₁)) :=
    mul_left_cancel₀ (pow_ne_zero 3 hϖ0)
      (by linear_combination -hE + (ϖ * X₁) ^ 2 * hs - ϖ * X₁ * hc)
  rw [← mul_sub, pow_two, mul_dvd_mul_iff_left hϖ0] at hx
  obtain ⟨c, hc₁₂⟩ := hx
  -- the discriminant of the residue cubic is that of `(T − X₁)² (T − X₃)`, which vanishes
  refine not_dvd_discr_of_isTateTerminal_IStar_zero v h hA₂ hA₄ hA₆ ?_
  set q := Ideal.Quotient.mk (Ideal.span {ϖ})
  have hq {z : v.valuationSubring} (hz : ∃ w, z = ϖ * w) : q z = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
    exact hz
  have k₂ : q A₂ = -(q X₁ + q X₂ + q X₃) := by
    linear_combination (by simpa using hq ⟨_, e₂⟩ : q A₂ + (q X₁ + q X₂ + q X₃) = 0)
  have k₄ : q A₄ = q X₁ * q X₂ + q X₁ * q X₃ + q X₂ * q X₃ := by
    linear_combination (by simpa using hq ⟨_, e₄⟩ :
      q A₄ - (q X₁ * q X₂ + q X₁ * q X₃ + q X₂ * q X₃) = 0)
  have k₆ : q A₆ = -(q X₁ * q X₂ * q X₃) := by
    linear_combination (by simpa using hq ⟨_, e₆⟩ : q A₆ + q X₁ * q X₂ * q X₃ = 0)
  have k₁₂ : q X₂ = q X₁ := by
    linear_combination -(by simpa using hq ⟨_, hc₁₂⟩ : q X₁ - q X₂ = 0)
  rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem]
  simp only [Cubic.discr, map_add, map_sub, map_mul, map_pow, map_one, map_ofNat]
  rw [k₂, k₄, k₆, k₁₂]
  ring

/-- **At the symbol `I₀*`, two points in different classes add up to a point outside `E₀(F)`.**
If `(x₁, y₁)` and `(x₂, y₂)` have singular reduction and `ϖ² ∤ x₁ − x₂`, then `x₁ − x₂` is `ϖ`
times a unit while `ϖ² ∣ y₁ − y₂`, so the chord through them has slope in `𝔪` and their sum has
singular reduction. -/
private theorem add_notMem_of_isTateTerminal_IStar_zero {ϖ : v.valuationSubring}
    (hϖ : maximalIdeal v.valuationSubring = Ideal.span {ϖ})
    (h : (integralModel v.valuationSubring W).IsTateTerminal ϖ (.IStar 0))
    {x₁ y₁ x₂ y₂ : v.valuationSubring} {h₁ : W.Nonsingular x₁ y₁} {h₂ : W.Nonsingular x₂ y₂}
    (hP : Point.some _ _ h₁ ∉ W.nonsingularReduction v)
    (hQ : Point.some _ _ h₂ ∉ W.nonsingularReduction v) (hx : ¬ ϖ ^ 2 ∣ x₁ - x₂) :
    Point.some _ _ h₁ + Point.some _ _ h₂ ∉ W.nonsingularReduction v := by
  obtain ⟨-, ⟨A₂, hA₂⟩, -, ⟨A₄, hA₄⟩, ⟨A₆, hA₆⟩, -⟩ := isTateTerminal_IStar_zero.1 h
  obtain ⟨-, m₃, m₄, m₆⟩ := prime_and_mem_maximalIdeal_of_isTateTerminal_IStar_zero v hϖ h
  have key (z : v.valuationSubring) : z ∈ maximalIdeal v.valuationSubring ↔ ϖ ∣ z := by
    rw [hϖ, Ideal.mem_span_singleton]
  obtain ⟨X₁, Y₁, rfl, rfl, -⟩ :=
    exists_eq_mul_of_notMem_of_isTateTerminal_IStar_zero v hϖ h hA₂ hA₄ hA₆ hP
  obtain ⟨X₂, Y₂, rfl, rfl, -⟩ :=
    exists_eq_mul_of_notMem_of_isTateTerminal_IStar_zero v hϖ h hA₂ hA₄ hA₆ hQ
  -- `X₁ − X₂` is a unit, since `ϖ² ∤ ϖ (X₁ − X₂)`
  have hu : IsUnit (X₁ - X₂) := by
    by_contra hn
    obtain ⟨c, hc⟩ := (key _).1 ((mem_maximalIdeal _).2 hn)
    exact hx ⟨c, by rw [← mul_sub, hc]; ring⟩
  refine add_notMem_of_slope_mem v ((key _).2 ⟨A₂, hA₂⟩) m₃ m₄ m₆
    (ℓ := ϖ * ((Y₁ - Y₂) * ↑hu.unit⁻¹)) ((key _).2 (dvd_mul_right _ _))
    ((key _).2 ⟨ϖ * Y₁, by ring⟩) ((key _).2 (dvd_mul_right _ _))
    ((key _).2 (dvd_mul_right _ _)) (fun he ↦ hx (by rw [he, sub_self]; exact dvd_zero _)) ?_
  linear_combination (-(ϖ ^ 2 * (Y₁ - Y₂))) * hu.val_inv_mul

/-- **At the symbol `I₀*`, the class of a point with singular reduction is that of its root.** If
`(x₁, y₁)` and `(x₂, y₂)` have singular reduction, then `-(x₁, y₁) + (x₂, y₂)` has nonsingular
reduction exactly when `ϖ² ∣ x₁ − x₂`, that is when the residues of `x₁ / ϖ` and `x₂ / ϖ` agree.
Negation preserves the `x`-coordinate, so this follows from the two preceding statements. -/
private theorem neg_add_mem_iff_of_isTateTerminal_IStar_zero {ϖ : v.valuationSubring}
    (hϖ : maximalIdeal v.valuationSubring = Ideal.span {ϖ})
    (h : (integralModel v.valuationSubring W).IsTateTerminal ϖ (.IStar 0))
    {x₁ y₁ x₂ y₂ : v.valuationSubring} {h₁ : W.Nonsingular x₁ y₁} {h₂ : W.Nonsingular x₂ y₂}
    (hP : Point.some _ _ h₁ ∉ W.nonsingularReduction v)
    (hQ : Point.some _ _ h₂ ∉ W.nonsingularReduction v) :
    -Point.some _ _ h₁ + Point.some _ _ h₂ ∈ W.nonsingularReduction v ↔ ϖ ^ 2 ∣ x₁ - x₂ := by
  -- `-(x₁, y₁) = (x₁, y₁')`, with `y₁'` computed in the integral model
  have hnegY := coe_negY_integralModel (W := W) v x₁ y₁
  have h₁' : W.Nonsingular x₁
      (((integralModel v.valuationSubring W).toAffine.negY x₁ y₁ : v.valuationSubring) : F) :=
    hnegY ▸ (nonsingular_neg ..).2 h₁
  have hneg : -Point.some _ _ h₁ = Point.some _ _ h₁' := by
    rw [Point.neg_some, Point.some.injEq]
    exact ⟨rfl, hnegY.symm⟩
  have hP' : Point.some _ _ h₁' ∉ W.nonsingularReduction v := by rwa [← hneg, neg_mem_iff]
  rw [hneg]
  exact ⟨not_imp_not.1 (add_notMem_of_isTateTerminal_IStar_zero v hϖ h hP' hQ),
    add_mem_of_isTateTerminal_IStar_zero v hϖ h hP' hQ⟩

/-- **At the symbol `I₀*`, every root of the residue cubic comes from a point with singular
reduction** when the valuation ring is Henselian, for instance complete. Here `a₂ = ϖ A₂`,
`a₄ = ϖ² A₄` and `a₆ = ϖ³ A₆`, and `t₀` is a root of `T³ + A₂ T² + A₄ T + A₆` modulo `ϖ`. The root
is simple, as the discriminant of the residue cubic is nonzero, so it lifts to a root `X`, and
`(ϖ X, 0)` is a point with singular reduction. -/
private theorem exists_notMem_of_isTateTerminal_IStar_zero
    [HenselianLocalRing v.valuationSubring] {ϖ : v.valuationSubring}
    (hϖ : maximalIdeal v.valuationSubring = Ideal.span {ϖ})
    (h : (integralModel v.valuationSubring W).IsTateTerminal ϖ (.IStar 0))
    {A₂ A₄ A₆ : v.valuationSubring} (h₂ : (integralModel v.valuationSubring W).a₂ = ϖ * A₂)
    (h₄ : (integralModel v.valuationSubring W).a₄ = ϖ ^ 2 * A₄)
    (h₆ : (integralModel v.valuationSubring W).a₆ = ϖ ^ 3 * A₆) {t₀ : v.valuationSubring}
    (ht₀ : ϖ ∣ t₀ ^ 3 + A₂ * t₀ ^ 2 + A₄ * t₀ + A₆) :
    ∃ (X : v.valuationSubring) (hX : W.Nonsingular ((ϖ * X : v.valuationSubring) : F)
        ((0 : v.valuationSubring) : F)),
      ϖ ∣ X - t₀ ∧ Point.some _ _ hX ∉ W.nonsingularReduction v := by
  obtain ⟨hp, m₃, m₄, m₆⟩ := prime_and_mem_maximalIdeal_of_isTateTerminal_IStar_zero v hϖ h
  have key (z : v.valuationSubring) : z ∈ maximalIdeal v.valuationSubring ↔ ϖ ∣ z := by
    rw [hϖ, Ideal.mem_span_singleton]
  have hd' := not_dvd_discr_of_isTateTerminal_IStar_zero v h h₂ h₄ h₆
  -- lift the root of the residue cubic by Hensel's lemma
  set f := (Cubic.mk 1 A₂ A₄ A₆).toPoly
  have heval (z : v.valuationSubring) : f.eval z = z ^ 3 + A₂ * z ^ 2 + A₄ * z + A₆ := by
    simp [f, Cubic.toPoly]
  have hder (z : v.valuationSubring) : f.derivative.eval z = 3 * z ^ 2 + 2 * A₂ * z + A₄ := by
    simp [f, Cubic.toPoly]
    ring
  rw [← heval] at ht₀
  obtain ⟨X, hX, hXt⟩ := HenselianLocalRing.is_henselian f Cubic.monic_of_a_eq_one' t₀
    ((key _).2 ht₀) (by
      rw [← residue_ne_zero_iff_isUnit, Ne, residue_eq_zero_iff, key]
      exact Cubic.not_dvd_eval_derivative_of_not_dvd_discr hd' ht₀)
  have hX' : ¬ ϖ ∣ 3 * X ^ 2 + 2 * A₂ * X + A₄ := hder X ▸
    Cubic.not_dvd_eval_derivative_of_not_dvd_discr hd' (hX.eq_zero ▸ dvd_zero ϖ)
  replace hX : X ^ 3 + A₂ * X ^ 2 + A₄ * X + A₆ = 0 := heval X ▸ hX.eq_zero
  have hns : (integralModel v.valuationSubring W).toAffine.Nonsingular (ϖ * X) 0 := by
    rw [nonsingular_iff']
    refine ⟨by
      rw [equation_iff, h₂, h₄, h₆]
      linear_combination -ϖ ^ 3 * hX, Or.inl ?_⟩
    rw [h₂, h₄, show (integralModel v.valuationSubring W).a₁ * 0 -
        (3 * (ϖ * X) ^ 2 + 2 * (ϖ * A₂) * (ϖ * X) + ϖ ^ 2 * A₄) =
        -(ϖ ^ 2 * (3 * X ^ 2 + 2 * A₂ * X + A₄)) by ring, neg_ne_zero]
    exact mul_ne_zero (pow_ne_zero 2 hp.ne_zero) fun h0 ↦ hX' (h0 ▸ dvd_zero ϖ)
  have hF := (nonsingular_integralModel_iff v).1 hns
  have hx : v ((ϖ * X : v.valuationSubring) : F) < 1 :=
    (Valuation.mem_maximalIdeal_iff (v := v)).1 ((key _).2 (dvd_mul_right _ _))
  exact ⟨X, hF, (key _).1 hXt,
    (some_notMem_nonsingularReduction_iff v m₃ m₄ m₆ hF).2 ⟨hx, by simp⟩⟩

/-! ### The index at `I₀*` -/

/-- **At the reduction symbol `I₀*`, `[E(F) : E₀(F)]` is one more than the number of roots of the
residue cubic** when the valuation ring is Henselian, for instance complete. This is the local
index `c_v = 1 + N` that Tate's algorithm reports at `I₀*`. Here `ϖ` generates the maximal ideal
of the valuation ring, Tate's algorithm, run on the integral model with uniformiser `ϖ`, stops with
the symbol `I₀*`, and the roots of the residue cubic `T³ + (a₂/ϖ) T² + (a₄/ϖ²) T + a₆/ϖ³` are
counted in `O ⧸ (ϖ)` (`WeierstrassCurve.tateCubicRoots`). The nontrivial cosets of `E₀(F)`
correspond to these roots, through the residue of `x / ϖ` at a point with singular reduction. -/
theorem index_nonsingularReduction_eq_one_add_natCard_of_isTateTerminal_IStar_zero
    [HenselianLocalRing v.valuationSubring] {ϖ : v.valuationSubring}
    (hϖ : maximalIdeal v.valuationSubring = Ideal.span {ϖ})
    (h : (integralModel v.valuationSubring W).IsTateTerminal ϖ (.IStar 0)) :
    (W.nonsingularReduction v).index =
      1 + Nat.card ((integralModel v.valuationSubring W).tateCubicRoots ϖ) := by
  classical
  obtain ⟨-, ⟨A₂, hA₂⟩, -, ⟨A₄, hA₄⟩, ⟨A₆, hA₆⟩, -⟩ := isTateTerminal_IStar_zero.1 h
  obtain ⟨hp, m₃, m₄, m₆⟩ := prime_and_mem_maximalIdeal_of_isTateTerminal_IStar_zero v hϖ h
  set S := (integralModel v.valuationSubring W).tateCubicRoots ϖ
  set H := W.nonsingularReduction v
  have hmk {a b : v.valuationSubring} :
      Ideal.Quotient.mk (Ideal.span {ϖ}) a = Ideal.Quotient.mk _ b ↔ ϖ ∣ a - b := by
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]
  have : Finite S := (finite_tateCubicRoots hp ⟨A₂, hA₂⟩ ⟨A₄, hA₄⟩ ⟨A₆, hA₆⟩).to_subtype
  -- a point with singular reduction for each root
  have hlift (t : S) : ∃ (X : v.valuationSubring) (hX : W.Nonsingular
      ((ϖ * X : v.valuationSubring) : F) ((0 : v.valuationSubring) : F)),
      Ideal.Quotient.mk _ X = (t : v.valuationSubring ⧸ Ideal.span {ϖ}) ∧
        Point.some _ _ hX ∉ H := by
    obtain ⟨t, ht⟩ := t
    obtain ⟨t₀, rfl⟩ := Ideal.Quotient.mk_surjective t
    obtain ⟨X, hX, hXt, hXH⟩ := exists_notMem_of_isTateTerminal_IStar_zero v hϖ h hA₂ hA₄ hA₆
      ((mk_mem_tateCubicRoots_iff hp.ne_zero hA₂ hA₄ hA₆ t₀).1 ht)
    exact ⟨X, hX, hmk.2 hXt, hXH⟩
  choose X hX hXt hXH using hlift
  have hdvd (a b : v.valuationSubring) : ϖ ^ 2 ∣ ϖ * a - ϖ * b ↔ ϖ ∣ a - b := by
    rw [← mul_sub, pow_two, mul_dvd_mul_iff_left hp.ne_zero]
  -- the root of each class of points with singular reduction gives the cosets of `E₀(F)`
  let g : Option S → W.Point ⧸ H := fun o ↦ o.elim 0 fun t ↦ (Point.some _ _ (hX t) : W.Point)
  have hg : g.Bijective := by
    refine ⟨fun o o' hoo' ↦ ?_, fun p ↦ ?_⟩
    · rcases o with _ | t <;> rcases o' with _ | t'
      · rfl
      · exact absurd ((QuotientAddGroup.eq_zero_iff _).1 hoo'.symm) (hXH t')
      · exact absurd ((QuotientAddGroup.eq_zero_iff _).1 hoo') (hXH t)
      · refine congrArg some (Subtype.ext ?_)
        rw [← hXt t, ← hXt t', hmk, ← hdvd,
          ← neg_add_mem_iff_of_isTateTerminal_IStar_zero v hϖ h (hXH t) (hXH t')]
        exact QuotientAddGroup.eq.1 hoo'
    · induction p using QuotientAddGroup.induction_on with | H P => ?_
      by_cases hP : P ∈ H
      · exact ⟨none, ((QuotientAddGroup.eq_zero_iff _).2 hP).symm⟩
      obtain ⟨x, y, hxy, rfl, -, -⟩ := exists_eq_some_of_notMem_nonsingularReduction v m₃ m₄ m₆ hP
      obtain ⟨X₀, -, rfl, -, hX₀⟩ :=
        exists_eq_mul_of_notMem_of_isTateTerminal_IStar_zero v hϖ h hA₂ hA₄ hA₆ hP
      let t : S := ⟨_, (mk_mem_tateCubicRoots_iff hp.ne_zero hA₂ hA₄ hA₆ X₀).2 hX₀⟩
      refine ⟨some t, QuotientAddGroup.eq.2
        ((neg_add_mem_iff_of_isTateTerminal_IStar_zero v hϖ h (hXH t) hP).2 ?_)⟩
      rw [hdvd, ← hmk, hXt t]
  rw [AddSubgroup.index_eq_card, ← Nat.card_congr (Equiv.ofBijective g hg), Finite.card_option,
    add_comm]

end Affine

end WeierstrassCurve

end

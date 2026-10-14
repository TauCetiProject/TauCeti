/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.SingularReduction
public import TauCeti.AlgebraicGeometry.EllipticCurve.TateAlgorithm.Terminal

/-!
# Points with singular reduction at the symbols `I₀*`, `IV*` and `II*`

Let `v` be a valuation on a field `F`, with valuation ring `O`, maximal ideal `𝔪 = (ϖ)` and
residue field `k`, and let `W` be a Weierstrass curve over `F` with an integral model `W_O` over
`O`. The points with nonsingular reduction form the subgroup `E₀(F)` of `W(F)`
(`WeierstrassCurve.Affine.nonsingularReduction`). When `F` is complete for a discrete valuation with
perfect residue field and the equation is minimal, the index `[E(F) : E₀(F)]` is the local index
`c_v` that Tate's algorithm computes (Silverman, *Advanced Topics*, IV.9, Table 4.1). This file
shows that `E₀(F) = W(F)`, so that the index is one, at three of the symbols that Tate's algorithm
reaches from the normal form `ϖ ∣ a₁, a₂`, `ϖ² ∣ a₃, a₄`, `ϖ³ ∣ a₆` of its Step 6:

* at `I₀*`, when the residue cubic `T³ + (a₂/ϖ) T² + (a₄/ϖ²) T + a₆/ϖ³` has no root in `k`;
* at `IV*`, when the residue quadratic `T² + (a₃/ϖ²) T − a₆/ϖ⁴` has no root in `k`;
* at `II*`, always.

These are the cases in which Table 4.1 reports `c_v = 1` at these symbols. In general Tate's
algorithm reports `c_v = 1 + #{roots of the cubic in k}` at `I₀*` and `c_v = 3` at `IV*` when the
quadratic has a root in `k`.

The reduction of `W_O` is singular at the origin, so a point with singular reduction is an
integral solution `(x, y)` with `x, y ∈ 𝔪`
(`WeierstrassCurve.Affine.nonsingularReduction_eq_top_of_forall_mem_maximalIdeal_not_equation`).
Comparing powers of `ϖ` in the Weierstrass equation rules such solutions out. At `I₀*`, writing
`x = ϖ X` and `y = ϖ Y`, the equation divided by `ϖ²` forces `ϖ ∣ Y`, and then divided by `ϖ³`
forces `X` to reduce to a root of the residue cubic. From the normal form of Step 8, where
`ϖ ∣ a₁`, `ϖ² ∣ a₂, a₃`, `ϖ³ ∣ a₄` and `ϖ⁴ ∣ a₆`, the same comparison gives `x, y ∈ 𝔪²`, and
`y / ϖ²` reduces to a root of the residue quadratic. At `II*` that quadratic is `T²`, so
`y ∈ 𝔪³`, and the equation then forces `ϖ⁶ ∣ a₆`, which the stopping test for `II*` excludes.

## Main results

* `WeierstrassCurve.exists_dvd_cubic_of_equation` and
  `WeierstrassCurve.pow_six_dvd_a₆_of_equation`: over a domain with a prime `ϖ`, a solution with
  both coordinates divisible by `ϖ` on the normal forms of Steps 6 and 10 of Tate's algorithm
  gives a root of the residue cubic modulo `ϖ`, and `ϖ⁶ ∣ a₆`, respectively. On the normal form of
  Step 8 such a solution gives a root of the residue quadratic modulo `ϖ`
  (`WeierstrassCurve.exists_eq_sq_mul_of_equation`).
* `WeierstrassCurve.Affine.nonsingularReduction_eq_top_of_isTateTerminal_IStar_zero`: at `I₀*`, if
  the residue cubic has no root in `k`, then `E₀(F) = W(F)`.
* `WeierstrassCurve.Affine.nonsingularReduction_eq_top_of_isTateTerminal_IVStar`: at `IV*`, if the
  residue quadratic has no root in `k`, then `E₀(F) = W(F)`.
* `WeierstrassCurve.Affine.nonsingularReduction_eq_top_of_isTateTerminal_IIStar`: at `II*`,
  `E₀(F) = W(F)`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VII.6.
* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, GTM 151, IV.9.
* J. Tate, *Algorithm for determining the type of a singular fibre in an elliptic pencil*, in
  *Modular Functions of One Variable IV*, LNM 476 (1975), 33–52.
-/

public section

open IsLocalRing

namespace WeierstrassCurve

/-! ### Solutions with coordinates divisible by `ϖ` -/

section Domain

variable {R : Type*} [CommRing R] [IsDomain R] (W : WeierstrassCurve R) {ϖ : R}

/-- **On the normal form of Step 6 of Tate's algorithm, a solution divisible by `ϖ` reduces to a
root of the residue cubic.** Over a domain with a prime `ϖ`, suppose that `ϖ ∣ a₁`, `ϖ² ∣ a₃`,
`a₂ = ϖ A₂`, `a₄ = ϖ² A₄` and `a₆ = ϖ³ A₆`. If `(x, y)` is a solution with `ϖ ∣ x` and `ϖ ∣ y`, then
the cubic `T³ + A₂ T² + A₄ T + A₆` has a root modulo `ϖ`. -/
theorem exists_dvd_cubic_of_equation (hϖ : Prime ϖ) (h₁ : ϖ ∣ W.a₁) {A₂ A₄ A₆ : R}
    (h₂ : W.a₂ = ϖ * A₂) (h₃ : ϖ ^ 2 ∣ W.a₃) (h₄ : W.a₄ = ϖ ^ 2 * A₄) (h₆ : W.a₆ = ϖ ^ 3 * A₆)
    {x y : R} (h : W.toAffine.Equation x y) (hx : ϖ ∣ x) (hy : ϖ ∣ y) :
    ∃ t, ϖ ∣ t ^ 3 + A₂ * t ^ 2 + A₄ * t + A₆ := by
  obtain ⟨A₁, hA₁⟩ := h₁
  obtain ⟨A₃, hA₃⟩ := h₃
  obtain ⟨X, rfl⟩ := hx
  obtain ⟨Y, rfl⟩ := hy
  rw [Affine.equation_iff, hA₁, h₂, hA₃, h₄, h₆] at h
  -- `ϖ² Y² ≡ 0` modulo `ϖ³`
  obtain ⟨Y, rfl⟩ : ϖ ∣ Y := hϖ.dvd_of_dvd_pow (n := 2) <|
    (mul_dvd_mul_iff_left (pow_ne_zero 2 hϖ.ne_zero)).mp
      ⟨X ^ 3 + A₂ * X ^ 2 + A₄ * X + A₆ - A₁ * X * Y - A₃ * Y, by linear_combination h⟩
  -- `ϖ³ (X³ + A₂ X² + A₄ X + A₆) ≡ 0` modulo `ϖ⁴`
  exact ⟨X, (mul_dvd_mul_iff_left (pow_ne_zero 3 hϖ.ne_zero)).mp
    ⟨Y ^ 2 + A₁ * X * Y + A₃ * Y, by linear_combination -h⟩⟩

/-- **On the normal form of Step 10 of Tate's algorithm, a solution divisible by `ϖ` forces
`ϖ⁶ ∣ a₆`.** Over a domain with a prime `ϖ`, suppose that `ϖ ∣ a₁`, `ϖ² ∣ a₂`, `ϖ³ ∣ a₃`,
`ϖ⁴ ∣ a₄` and `ϖ⁵ ∣ a₆`. If `(x, y)` is a solution with `ϖ ∣ x` and `ϖ ∣ y`, then `ϖ⁶ ∣ a₆`. The
stopping test for `II*` asks for `ϖ⁶ ∤ a₆`, so there such a solution does not exist. -/
theorem pow_six_dvd_a₆_of_equation (hϖ : Prime ϖ) (h₁ : ϖ ∣ W.a₁) (h₂ : ϖ ^ 2 ∣ W.a₂)
    (h₃ : ϖ ^ 3 ∣ W.a₃) (h₄ : ϖ ^ 4 ∣ W.a₄) (h₆ : ϖ ^ 5 ∣ W.a₆) {x y : R}
    (h : W.toAffine.Equation x y) (hx : ϖ ∣ x) (hy : ϖ ∣ y) : ϖ ^ 6 ∣ W.a₆ := by
  obtain ⟨⟨X, rfl⟩, ⟨Y, rfl⟩⟩ := W.sq_dvd_and_pow_three_dvd_of_equation hϖ h₁ h₂ h₃
    ((pow_dvd_pow ϖ (by norm_num)).trans h₄) h₆ h hx hy
  obtain ⟨A₁, hA₁⟩ := h₁
  obtain ⟨A₂, hA₂⟩ := h₂
  obtain ⟨A₃, hA₃⟩ := h₃
  obtain ⟨A₄, hA₄⟩ := h₄
  obtain ⟨A₆, hA₆⟩ := h₆
  rw [Affine.equation_iff, hA₁, hA₂, hA₃, hA₄, hA₆] at h
  -- `ϖ⁵ A₆ ≡ 0` modulo `ϖ⁶`
  have hA : ϖ ^ 5 * ϖ ∣ ϖ ^ 5 * A₆ :=
    ⟨Y ^ 2 + A₁ * X * Y + A₃ * Y - X ^ 3 - A₂ * X ^ 2 - A₄ * X, by linear_combination -h⟩
  rw [hA₆, pow_succ]
  exact mul_dvd_mul_left _ ((mul_dvd_mul_iff_left (pow_ne_zero 5 hϖ.ne_zero)).mp hA)

end Domain

/-! ### Every point has nonsingular reduction -/

namespace Affine

variable {F Γ₀ : Type*} [Field F] [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation F Γ₀)
  {W : Affine F} [IsIntegral v.valuationSubring W] [DecidableEq F]

/-- If Tate's algorithm stops at an additive symbol on the integral model with a generator `ϖ` of
the maximal ideal, and no integral solution has both coordinates divisible by `ϖ`, then every point
has nonsingular reduction. The stopping test forces `ϖ ≠ 0`, so `ϖ` is prime, which the hypothesis
on solutions may use. -/
private theorem nonsingularReduction_eq_top_of_isTateTerminal {ϖ : v.valuationSubring}
    (hϖ : maximalIdeal v.valuationSubring = Ideal.span {ϖ})
    {s : TauCeti.ReductionSymbol} (hs : (integralModel v.valuationSubring W).IsTateTerminal ϖ s)
    (hsI : ∀ n, s ≠ .I n)
    (h : Prime ϖ → ∀ x y : v.valuationSubring, ϖ ∣ x → ϖ ∣ y →
      ¬ (integralModel v.valuationSubring W).toAffine.Equation x y) :
    W.nonsingularReduction v = ⊤ := by
  obtain ⟨-, h₃, h₄, h₆⟩ := hs.dvd_b₂_and_dvd_a₃_and_dvd_a₄_and_dvd_a₆ hsI
  have hmem {z : v.valuationSubring} : z ∈ maximalIdeal v.valuationSubring ↔ ϖ ∣ z := by
    rw [hϖ, Ideal.mem_span_singleton]
  have hp : Prime ϖ := (Ideal.span_singleton_prime (hs.ne_zero (hsI 0))).mp
    (hϖ ▸ (maximalIdeal.isMaximal _).isPrime)
  exact nonsingularReduction_eq_top_of_forall_mem_maximalIdeal_not_equation v (hmem.mpr h₃)
    (hmem.mpr h₄) (hmem.mpr h₆) fun x y hx hy ↦ h hp x y (hmem.mp hx) (hmem.mp hy)

/-- **At the symbol `I₀*` with no rational root of the residue cubic, every point has nonsingular
reduction**: `E₀(F) = W(F)`. Here `ϖ` generates the maximal ideal, Tate's algorithm stops at `I₀*`
on the integral model, and with `a₂ = ϖ A₂`, `a₄ = ϖ² A₄` and `a₆ = ϖ³ A₆` the residue cubic
`T³ + A₂ T² + A₄ T + A₆` has no root in the residue field. -/
theorem nonsingularReduction_eq_top_of_isTateTerminal_IStar_zero {ϖ : v.valuationSubring}
    (hϖ : maximalIdeal v.valuationSubring = Ideal.span {ϖ})
    (h : (integralModel v.valuationSubring W).IsTateTerminal ϖ (.IStar 0))
    {A₂ A₄ A₆ : v.valuationSubring} (h₂ : (integralModel v.valuationSubring W).a₂ = ϖ * A₂)
    (h₄ : (integralModel v.valuationSubring W).a₄ = ϖ ^ 2 * A₄)
    (h₆ : (integralModel v.valuationSubring W).a₆ = ϖ ^ 3 * A₆)
    (hroot : ∀ t : ResidueField v.valuationSubring,
      t ^ 3 + residue _ A₂ * t ^ 2 + residue _ A₄ * t + residue _ A₆ ≠ 0) :
    W.nonsingularReduction v = ⊤ := by
  obtain ⟨h₁, -, h₃, -, -, hd⟩ := isTateTerminal_IStar_zero.1 h
  refine nonsingularReduction_eq_top_of_isTateTerminal v hϖ h (by simp)
    fun hp x y hx hy hE ↦ ?_
  obtain ⟨t, ht⟩ := exists_dvd_cubic_of_equation _ hp h₁ h₂ h₃ h₄ h₆ hE hx hy
  have ht' : _ ∈ maximalIdeal v.valuationSubring := hϖ ▸ Ideal.mem_span_singleton.mpr ht
  exact hroot (residue _ t) (by simpa using (residue_eq_zero_iff _).mpr ht')

/-- **At the symbol `IV*` with no rational root of the residue quadratic, every point has
nonsingular reduction**: `E₀(F) = W(F)`. Here `ϖ` generates the maximal ideal, Tate's algorithm
stops at `IV*` on the integral model, and with `a₃ = ϖ² A₃` and `a₆ = ϖ⁴ A₆` the residue quadratic
`T² + A₃ T − A₆` has no root in the residue field. -/
theorem nonsingularReduction_eq_top_of_isTateTerminal_IVStar {ϖ : v.valuationSubring}
    (hϖ : maximalIdeal v.valuationSubring = Ideal.span {ϖ})
    (h : (integralModel v.valuationSubring W).IsTateTerminal ϖ .IVStar)
    {A₃ A₆ : v.valuationSubring} (h₃ : (integralModel v.valuationSubring W).a₃ = ϖ ^ 2 * A₃)
    (h₆ : (integralModel v.valuationSubring W).a₆ = ϖ ^ 4 * A₆)
    (hroot : ∀ t : ResidueField v.valuationSubring,
      t ^ 2 + residue _ A₃ * t - residue _ A₆ ≠ 0) :
    W.nonsingularReduction v = ⊤ := by
  obtain ⟨h₁, h₂, -, h₄, -, hb₆⟩ := isTateTerminal_IVStar.1 h
  refine nonsingularReduction_eq_top_of_isTateTerminal v hϖ h (by simp)
    fun hp x y hx hy hE ↦ ?_
  obtain ⟨-, t, -, -, ht⟩ := exists_eq_sq_mul_of_equation _ hp h₁ h₂ h₃ h₄ h₆ hE hx hy
  have ht' : _ ∈ maximalIdeal v.valuationSubring := hϖ ▸ Ideal.mem_span_singleton.mpr ht
  exact hroot (residue _ t) (by simpa using (residue_eq_zero_iff _).mpr ht')

/-- **At the symbol `II*`, every point has nonsingular reduction**: `E₀(F) = W(F)`. Here `ϖ`
generates the maximal ideal and Tate's algorithm stops at `II*` on the integral model. -/
theorem nonsingularReduction_eq_top_of_isTateTerminal_IIStar {ϖ : v.valuationSubring}
    (hϖ : maximalIdeal v.valuationSubring = Ideal.span {ϖ})
    (h : (integralModel v.valuationSubring W).IsTateTerminal ϖ .IIStar) :
    W.nonsingularReduction v = ⊤ := by
  obtain ⟨h₁, h₂, h₃, h₄, h₆, h₆'⟩ := isTateTerminal_IIStar.1 h
  exact nonsingularReduction_eq_top_of_isTateTerminal v hϖ h (by simp)
    fun hp x y hx hy hE ↦ h₆' (pow_six_dvd_a₆_of_equation _ hp h₁ h₂ h₃ h₄ h₆ hE hx hy)

end Affine

end WeierstrassCurve

end

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.NonsingularReduction
public import TauCeti.AlgebraicGeometry.EllipticCurve.TateAlgorithm.Terminal
-- Proof-only: the points with singular reduction when the reduction is singular at the origin, and
-- the solutions divisible by `ϖ` on the normal form of `I₀*`.
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.StarredReduction
-- Proof-only: a common root of a cubic and its derivative divides the discriminant.
import TauCeti.Algebra.CubicDiscriminant

/-!
# Points with singular reduction at the reduction symbol `I₀*`

Let `v` be a valuation on a field `F`, with valuation ring `O`, maximal ideal `𝔪 = (ϖ)` and residue
field `k`, and let `W` be a Weierstrass curve over `F` with an integral model `W_O` over `O`. The
points with nonsingular reduction form the subgroup `E₀(F)` of `W(F)`
(`WeierstrassCurve.Affine.nonsingularReduction`). When `F` is complete for a discrete valuation with
perfect residue field and the equation is minimal, the index `[E(F) : E₀(F)]` is the local index
`c_v` that Tate's algorithm computes (Silverman, *Advanced Topics*, IV.9, Table 4.1). This file
computes it at the reduction symbol `I₀*`, where Tate's algorithm reports
`c_v = 1 + #{roots of the residue cubic in k}`.

At `I₀*` the integral model is in the normal form `ϖ ∣ a₁`, `a₂ = ϖ A₂`, `ϖ² ∣ a₃`, `a₄ = ϖ² A₄`,
`a₆ = ϖ³ A₆`, and the **residue cubic** `T³ + A₂ T² + A₄ T + A₆` has nonzero discriminant over `k`
(`WeierstrassCurve.IsTateTerminal`). A point with singular reduction is an affine point `(x, y)`
with `x, y ∈ 𝔪` (`WeierstrassCurve.Affine.some_notMem_nonsingularReduction_iff`). Comparing powers
of `ϖ` in the Weierstrass equation shows `x = ϖ X` and `y = ϖ² Y` with `X, Y ∈ O`, and the residue
of `X` is a root of the residue cubic.

Two points `P = (ϖ X₁, y₁)` and `Q = (ϖ X₂, y₂)` with singular reduction are then congruent modulo
`E₀(F)` up to sign exactly when `X₁` and `X₂` have the same residue: `P + Q ∈ E₀(F)` if and only if
`X₁ ≡ X₂` (`WeierstrassCurve.Affine.add_mem_nonsingularReduction_iff_of_isTateTerminal_IStar_zero`).
If the residues differ, the line through `P` and `Q` has slope
`ℓ = (y₁ − y₂) / (x₁ − x₂) ∈ ϖ O`, since `v(x₁ − x₂) = v(ϖ)` and `ϖ² ∣ y₁ − y₂`, so the third
intersection point and with it `P + Q` has coordinates in `𝔪`. If the residues agree and
`P + Q = -(ϖ X₃, y₃)` has singular reduction as well, then `ℓ ∈ 𝔪`, and dividing the
factorisation

`x³ + a₂ x² + a₄ x + a₆ − (ℓ (x − x₁) + y₁)² − (a₁ x + a₃) (ℓ (x − x₁) + y₁)
  = (x − x₁) (x − x₂) (x − x₃)`

of the Weierstrass cubic along the line by `ϖ³` at `x = ϖ T` shows that the residue cubic is
`(T − X₁) (T − X₂) (T − X₃)` modulo `ϖ`. A repeated root would make its discriminant vanish, which
the stopping test for `I₀*` excludes.

So the cosets of `E₀(F)` other than `E₀(F)` itself correspond to the roots of the residue cubic in
`k` that some point with singular reduction reduces to. Over a Henselian valuation ring every root
`t` occurs: it lifts to a root `X` of `T³ + A₂ T² + A₄ T + A₆` in `O`, since the roots of the
residue cubic are simple, and `(ϖ X, 0)` is a point of `W` with singular reduction. Hence
`[E(F) : E₀(F)] = 1 + #{roots of the residue cubic in k}`, which is `1`, `2` or `4`.

## Main results

* `WeierstrassCurve.Affine.exists_xCoord_eq_of_isTateTerminal_IStar_zero`:
  a point with singular reduction has `x = ϖ X`, with the residue of `X` a root of the residue
  cubic.
* `WeierstrassCurve.Affine.exists_yCoord_eq_of_isTateTerminal_IStar_zero`:
  a point with singular reduction has `y = ϖ² Y`.
* `WeierstrassCurve.Affine.add_mem_nonsingularReduction_iff_of_isTateTerminal_IStar_zero`: for two
  points `(ϖ X₁, y₁)` and `(ϖ X₂, y₂)` with singular reduction, the sum has nonsingular reduction
  exactly when `X₁` and `X₂` have the same residue.
* `WeierstrassCurve.Affine.exists_notMem_nonsingularReduction_of_isTateTerminal_IStar_zero`: over a
  Henselian valuation ring, every root of the residue cubic is the residue of `x / ϖ` for some point
  with singular reduction.
* `WeierstrassCurve.Affine.index_nonsingularReduction_eq_of_isTateTerminal_IStar_zero`: over a
  Henselian valuation ring, `[E(F) : E₀(F)] = 1 + #{roots of the residue cubic in k}`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VII.6.
* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, GTM 151, IV.9.
* J. Tate, *Algorithm for determining the type of a singular fibre in an elliptic pencil*, in
  *Modular Functions of One Variable IV*, LNM 476 (1975), 33–52.
-/

public section

open IsLocalRing Polynomial

namespace WeierstrassCurve

namespace Affine

variable {F Γ₀ : Type*} [Field F] [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation F Γ₀)
  {W : Affine F} [IsIntegral v.valuationSubring W] [DecidableEq F]

omit [DecidableEq F] in
/-- The consequences of the stopping test for `I₀*` used below, given `a₂ = ϖ A₂`, `a₄ = ϖ² A₄` and
`a₆ = ϖ³ A₆`: `ϖ` is prime, `ϖ ∣ a₁`, `ϖ² ∣ a₃`, and `ϖ` does not divide the discriminant of the
residue cubic `T³ + A₂ T² + A₄ T + A₆`. -/
private theorem prime_and_dvd_and_not_dvd_discr_of_isTateTerminal_IStar_zero
    {ϖ : v.valuationSubring} (hϖ : maximalIdeal v.valuationSubring = Ideal.span {ϖ})
    (h : (integralModel v.valuationSubring W).IsTateTerminal ϖ (.IStar 0))
    {A₂ A₄ A₆ : v.valuationSubring} (h₂ : (integralModel v.valuationSubring W).a₂ = ϖ * A₂)
    (h₄ : (integralModel v.valuationSubring W).a₄ = ϖ ^ 2 * A₄)
    (h₆ : (integralModel v.valuationSubring W).a₆ = ϖ ^ 3 * A₆) :
    Prime ϖ ∧ ϖ ∣ (integralModel v.valuationSubring W).a₁ ∧
      ϖ ^ 2 ∣ (integralModel v.valuationSubring W).a₃ ∧ ¬ ϖ ∣ (Cubic.mk 1 A₂ A₄ A₆).discr := by
  obtain ⟨h₁, -, h₃, -, -, hD⟩ := isTateTerminal_IStar_zero.1 h
  -- The discriminant is homogeneous of weight `6` in `(a₂, a₄, a₆)`.
  have hdiscr : (Cubic.mk 1 (integralModel v.valuationSubring W).a₂
      (integralModel v.valuationSubring W).a₄ (integralModel v.valuationSubring W).a₆).discr =
      ϖ ^ 6 * (Cubic.mk 1 A₂ A₄ A₆).discr := by
    simp only [h₂, h₄, h₆, Cubic.discr]
    ring
  have hϖ0 : ϖ ≠ 0 := by
    rintro rfl
    exact hD (by simp [hdiscr])
  refine ⟨(Ideal.span_singleton_prime hϖ0).mp (hϖ ▸ (maximalIdeal.isMaximal _).isPrime), h₁, h₃,
    fun hd ↦ hD ?_⟩
  rw [hdiscr, pow_succ]
  exact mul_dvd_mul_left _ hd

/-- A point with singular reduction at `I₀*`, with `x = ϖ X`, has `y = ϖ² Y`, and `X` is a root of
the residue cubic modulo `ϖ`. -/
private theorem exists_yCoord_eq_and_dvd_cubic {ϖ : v.valuationSubring}
    (hϖ : maximalIdeal v.valuationSubring = Ideal.span {ϖ})
    (h : (integralModel v.valuationSubring W).IsTateTerminal ϖ (.IStar 0))
    {A₂ A₄ A₆ : v.valuationSubring} (h₂ : (integralModel v.valuationSubring W).a₂ = ϖ * A₂)
    (h₄ : (integralModel v.valuationSubring W).a₄ = ϖ ^ 2 * A₄)
    (h₆ : (integralModel v.valuationSubring W).a₆ = ϖ ^ 3 * A₆) {P : W.Point}
    (hP : P ∉ W.nonsingularReduction v) {X : v.valuationSubring}
    (hX : P.xCoord = ((ϖ * X : v.valuationSubring) : F)) :
    ∃ Y : v.valuationSubring, P.yCoord = ((ϖ ^ 2 * Y : v.valuationSubring) : F) ∧
      ϖ ∣ X ^ 3 + A₂ * X ^ 2 + A₄ * X + A₆ := by
  obtain ⟨hp, h₁, h₃, -⟩ :=
    prime_and_dvd_and_not_dvd_discr_of_isTateTerminal_IStar_zero v hϖ h h₂ h₄ h₆
  obtain ⟨-, -, -, h₄', h₆', -⟩ := isTateTerminal_IStar_zero.1 h
  have hmem (z : v.valuationSubring) : z ∈ maximalIdeal v.valuationSubring ↔ ϖ ∣ z := by
    rw [hϖ, Ideal.mem_span_singleton]
  rcases P with _ | ⟨x, y, hxy⟩
  · exact absurd (zero_mem _) hP
  obtain ⟨-, hy⟩ := (some_notMem_nonsingularReduction_iff v ((hmem _).2 (dvd_pow_self ϖ
    two_ne_zero |>.trans h₃)) ((hmem _).2 (dvd_pow_self ϖ two_ne_zero |>.trans h₄'))
    ((hmem _).2 (dvd_pow_self ϖ three_ne_zero |>.trans h₆')) hxy).1 hP
  rw [Point.xCoord_some] at hX
  subst hX
  set y₀ : v.valuationSubring := ⟨y, (v.mem_valuationSubring_iff y).2 hy.le⟩
  have hE : (integralModel v.valuationSubring W).toAffine.Equation (ϖ * X) y₀ :=
    (equation_integralModel_iff v).2 hxy.left
  obtain ⟨⟨Y, hY⟩, hX⟩ := (integralModel v.valuationSubring W).sq_dvd_and_dvd_cubic_of_equation hp
    h₁ h₂ h₃ h₄ h₆ hE ((hmem _).1 ((Valuation.mem_maximalIdeal_iff (v := v)).2 hy))
  exact ⟨Y, by rw [Point.yCoord_some, ← hY], hX⟩

/-- **At `I₀*`, a point with singular reduction has `x = ϖ X`, with the residue of `X` a root of the
residue cubic.** Here `ϖ` generates the maximal ideal of the valuation ring, Tate's algorithm stops
at `I₀*` on the integral model, and `a₂ = ϖ A₂`, `a₄ = ϖ² A₄`, `a₆ = ϖ³ A₆`, so that the residue
cubic is `T³ + A₂ T² + A₄ T + A₆` over the residue field. -/
theorem exists_xCoord_eq_of_isTateTerminal_IStar_zero
    {ϖ : v.valuationSubring} (hϖ : maximalIdeal v.valuationSubring = Ideal.span {ϖ})
    (h : (integralModel v.valuationSubring W).IsTateTerminal ϖ (.IStar 0))
    {A₂ A₄ A₆ : v.valuationSubring} (h₂ : (integralModel v.valuationSubring W).a₂ = ϖ * A₂)
    (h₄ : (integralModel v.valuationSubring W).a₄ = ϖ ^ 2 * A₄)
    (h₆ : (integralModel v.valuationSubring W).a₆ = ϖ ^ 3 * A₆) {P : W.Point}
    (hP : P ∉ W.nonsingularReduction v) :
    ∃ X : v.valuationSubring, P.xCoord = ((ϖ * X : v.valuationSubring) : F) ∧
      residue _ X ^ 3 + residue _ A₂ * residue _ X ^ 2 + residue _ A₄ * residue _ X +
        residue _ A₆ = 0 := by
  obtain ⟨-, -, -, h₄', h₆', -⟩ := isTateTerminal_IStar_zero.1 h
  have hmem (z : v.valuationSubring) : z ∈ maximalIdeal v.valuationSubring ↔ ϖ ∣ z := by
    rw [hϖ, Ideal.mem_span_singleton]
  obtain ⟨h₃, -⟩ := (prime_and_dvd_and_not_dvd_discr_of_isTateTerminal_IStar_zero v hϖ h h₂ h₄
    h₆).2.2
  rcases P with _ | ⟨x, y, hxy⟩
  · exact absurd (zero_mem _) hP
  obtain ⟨hx, -⟩ := (some_notMem_nonsingularReduction_iff v ((hmem _).2 (dvd_pow_self ϖ
    two_ne_zero |>.trans h₃)) ((hmem _).2 (dvd_pow_self ϖ two_ne_zero |>.trans h₄'))
    ((hmem _).2 (dvd_pow_self ϖ three_ne_zero |>.trans h₆')) hxy).1 hP
  obtain ⟨X, hX⟩ := (hmem ⟨x, (v.mem_valuationSubring_iff x).2 hx.le⟩).1
    ((Valuation.mem_maximalIdeal_iff (v := v)).2 hx)
  have hX' : (Point.some x y hxy).xCoord = ((ϖ * X : v.valuationSubring) : F) := by
    rw [Point.xCoord_some, ← hX]
  obtain ⟨-, -, hc⟩ := exists_yCoord_eq_and_dvd_cubic v hϖ h h₂ h₄ h₆ hP hX'
  refine ⟨X, hX', ?_⟩
  simpa using (residue_eq_zero_iff _).2 ((hmem _).2 hc)

/-- **At `I₀*`, a point with singular reduction has `y = ϖ² Y`.** Here `ϖ` generates the maximal
ideal of the valuation ring and Tate's algorithm stops at `I₀*` on the integral model. -/
theorem exists_yCoord_eq_of_isTateTerminal_IStar_zero
    {ϖ : v.valuationSubring} (hϖ : maximalIdeal v.valuationSubring = Ideal.span {ϖ})
    (h : (integralModel v.valuationSubring W).IsTateTerminal ϖ (.IStar 0)) {P : W.Point}
    (hP : P ∉ W.nonsingularReduction v) :
    ∃ Y : v.valuationSubring, P.yCoord = ((ϖ ^ 2 * Y : v.valuationSubring) : F) := by
  obtain ⟨-, ⟨A₂, h₂⟩, -, ⟨A₄, h₄⟩, ⟨A₆, h₆⟩, -⟩ := isTateTerminal_IStar_zero.1 h
  obtain ⟨X, hX, -⟩ := exists_xCoord_eq_of_isTateTerminal_IStar_zero v hϖ h h₂ h₄ h₆ hP
  obtain ⟨Y, hY, -⟩ := exists_yCoord_eq_and_dvd_cubic v hϖ h h₂ h₄ h₆ hP hX
  exact ⟨Y, hY⟩

/-! ### Sums of points with singular reduction -/

/-- **At `I₀*`, three collinear points with singular reduction reduce to the three roots of the
residue cubic.** If `P = (ϖ X₁, y₁)`, `Q = (ϖ X₂, y₂)` and `P + Q = -(ϖ X₃, y₃)` all have singular
reduction, then `T³ + A₂ T² + A₄ T + A₆ ≡ (T − X₁) (T − X₂) (T − X₃)` modulo `ϖ`: this is the
factorisation of the Weierstrass cubic along the line through `P` and `Q`, divided by `ϖ³`. -/
private theorem exists_dvd_of_add_notMem_nonsingularReduction {ϖ : v.valuationSubring}
    (hϖ : maximalIdeal v.valuationSubring = Ideal.span {ϖ})
    (h : (integralModel v.valuationSubring W).IsTateTerminal ϖ (.IStar 0))
    {A₂ A₄ A₆ : v.valuationSubring} (h₂ : (integralModel v.valuationSubring W).a₂ = ϖ * A₂)
    (h₄ : (integralModel v.valuationSubring W).a₄ = ϖ ^ 2 * A₄)
    (h₆ : (integralModel v.valuationSubring W).a₆ = ϖ ^ 3 * A₆) {P Q : W.Point}
    (hP : P ∉ W.nonsingularReduction v) (hQ : Q ∉ W.nonsingularReduction v)
    (hPQ : P + Q ∉ W.nonsingularReduction v) {X₁ X₂ : v.valuationSubring}
    (hX₁ : P.xCoord = ((ϖ * X₁ : v.valuationSubring) : F))
    (hX₂ : Q.xCoord = ((ϖ * X₂ : v.valuationSubring) : F)) :
    ∃ X₃ : v.valuationSubring, ϖ ∣ X₁ + X₂ + X₃ + A₂ ∧
      ϖ ∣ X₁ * X₂ + X₁ * X₃ + X₂ * X₃ - A₄ ∧ ϖ ∣ X₁ * X₂ * X₃ + A₆ := by
  obtain ⟨hp, ⟨A₁, hA₁⟩, ⟨A₃, hA₃⟩, -⟩ :=
    prime_and_dvd_and_not_dvd_discr_of_isTateTerminal_IStar_zero v hϖ h h₂ h₄ h₆
  have hϖF : (ϖ : F) ≠ 0 := by simpa using hp.ne_zero
  obtain ⟨Y₁, hY₁, -⟩ := exists_yCoord_eq_and_dvd_cubic v hϖ h h₂ h₄ h₆ hP hX₁
  obtain ⟨X₃, hX₃, -⟩ :=
    exists_xCoord_eq_of_isTateTerminal_IStar_zero v hϖ h h₂ h₄ h₆ hPQ
  rcases P with _ | ⟨x₁, y₁, h₁⟩
  · exact absurd (zero_mem _) hP
  rcases Q with _ | ⟨x₂, y₂, h₂'⟩
  · exact absurd (zero_mem _) hQ
  have hxy : ¬(x₁ = x₂ ∧ y₁ = W.negY x₂ y₂) := by
    rintro ⟨rfl, rfl⟩
    exact hPQ (by rw [Point.add_of_Y_eq rfl rfl]; exact zero_mem _)
  rw [Point.add_some hxy, Point.xCoord_some] at hX₃
  rw [Point.xCoord_some] at hX₁ hX₂
  rw [Point.yCoord_some] at hY₁
  -- the coefficients of `W`, in terms of those of the normal form
  have ha₁ : W.a₁ = ϖ * A₁ := by
    rw [← integralModel_a₁_eq v.valuationSubring W, hA₁]; simp
  have ha₂ : W.a₂ = ϖ * A₂ := by
    rw [← integralModel_a₂_eq v.valuationSubring W, h₂]; simp
  have ha₃ : W.a₃ = ϖ ^ 2 * A₃ := by
    rw [← integralModel_a₃_eq v.valuationSubring W, hA₃]; simp
  have ha₄ : W.a₄ = ϖ ^ 2 * A₄ := by
    rw [← integralModel_a₄_eq v.valuationSubring W, h₄]; simp
  have ha₆ : W.a₆ = ϖ ^ 3 * A₆ := by
    rw [← integralModel_a₆_eq v.valuationSubring W, h₆]; simp
  -- the Weierstrass cubic along the line through `P` and `Q` is `−(X − x₁) (X − x₂) (X − x₃)`
  set ℓ := W.slope x₁ x₂ y₁ y₂
  have key := W.addPolynomial_slope h₁.left h₂'.left hxy
  rw [addPolynomial_eq, Cubic.prod_X_sub_C_eq, neg_inj, Cubic.toPoly_injective] at key
  have hb : -ℓ ^ 2 - W.a₁ * ℓ + W.a₂ = -(x₁ + x₂ + W.addX x₁ x₂ ℓ) := congrArg Cubic.b key
  have hc : 2 * x₁ * ℓ ^ 2 + (W.a₁ * x₁ - 2 * y₁ - W.a₃) * ℓ + (-W.a₁ * y₁ + W.a₄) =
      x₁ * x₂ + x₁ * W.addX x₁ x₂ ℓ + x₂ * W.addX x₁ x₂ ℓ := congrArg Cubic.c key
  have hd : -x₁ ^ 2 * ℓ ^ 2 + (2 * x₁ * y₁ + W.a₃ * x₁) * ℓ - (y₁ ^ 2 + W.a₃ * y₁ - W.a₆) =
      -(x₁ * x₂ * W.addX x₁ x₂ ℓ) := congrArg Cubic.d key
  -- the slope lies in `𝔪`: `ℓ (ℓ + a₁) = x₁ + x₂ + x₃ + a₂`
  have hℓO : ℓ ∈ v.valuationSubring := (v.mem_valuationSubring_iff ℓ).2
    (valuation_le_one_of_valuation_addX_le_one v (x₁ := x₁) (x₂ := x₂)
      (hX₁ ▸ (v.mem_valuationSubring_iff _).1 (ϖ * X₁).2)
      (hX₂ ▸ (v.mem_valuationSubring_iff _).1 (ϖ * X₂).2)
      (hX₃ ▸ (v.mem_valuationSubring_iff _).1 (ϖ * X₃).2))
  obtain ⟨L, hL⟩ : ϖ ∣ (⟨ℓ, hℓO⟩ : v.valuationSubring) := by
    have hprod : (⟨ℓ, hℓO⟩ : v.valuationSubring) * (⟨ℓ, hℓO⟩ + ϖ * A₁) =
        ϖ * (X₁ + X₂ + X₃ + A₂) := by
      have h₃ := hX₃
      rw [addX, ha₁, ha₂, hX₁, hX₂] at h₃
      apply Subtype.val_injective
      push_cast at h₃ ⊢
      linear_combination h₃
    rcases hp.dvd_or_dvd ⟨_, hprod⟩ with hℓ | hℓ
    · exact hℓ
    · simpa using (dvd_add_left (dvd_mul_right ϖ A₁)).1 hℓ
  replace hL : ℓ = ((ϖ * L : v.valuationSubring) : F) := congrArg Subtype.val hL
  rw [hX₃] at hb hc hd
  simp only [hL, ha₁, ha₂, ha₃, ha₄, ha₆, hX₁, hX₂, hY₁] at hb hc hd
  push_cast at hb hc hd
  have h2 : ((2 : v.valuationSubring) : F) = 2 := by
    simpa using map_ofNat (algebraMap v.valuationSubring F) 2
  -- divide the three coefficient identities by `ϖ`, `ϖ²` and `ϖ³`
  refine ⟨X₃, ⟨L ^ 2 + A₁ * L, ?_⟩,
    ⟨2 * X₁ * L ^ 2 + (A₁ * X₁ - 2 * Y₁ - A₃) * L - A₁ * Y₁, ?_⟩,
    ⟨X₁ ^ 2 * L ^ 2 - (2 * X₁ * Y₁ + A₃ * X₁) * L + Y₁ ^ 2 + A₃ * Y₁, ?_⟩⟩ <;>
    apply Subtype.val_injective <;> push_cast [h2]
  · apply mul_left_cancel₀ hϖF
    linear_combination hb
  · apply mul_left_cancel₀ (pow_ne_zero 2 hϖF)
    linear_combination -hc
  · apply mul_left_cancel₀ (pow_ne_zero 3 hϖF)
    linear_combination hd

/-- **At `I₀*`, two points with singular reduction whose `x / ϖ` have different residues add up
to a point with singular reduction.** The line through `P = (ϖ X₁, ϖ² Y₁)` and
`Q = (ϖ X₂, ϖ² Y₂)` has slope `ϖ (Y₁ − Y₂) / (X₁ − X₂)` with `X₁ − X₂` a unit, so the coordinates
of `P + Q` lie in `𝔪`. -/
private theorem add_notMem_nonsingularReduction_of_not_dvd_sub {ϖ : v.valuationSubring}
    (hϖ : maximalIdeal v.valuationSubring = Ideal.span {ϖ})
    (h : (integralModel v.valuationSubring W).IsTateTerminal ϖ (.IStar 0))
    {A₂ A₄ A₆ : v.valuationSubring} (h₂ : (integralModel v.valuationSubring W).a₂ = ϖ * A₂)
    (h₄ : (integralModel v.valuationSubring W).a₄ = ϖ ^ 2 * A₄)
    (h₆ : (integralModel v.valuationSubring W).a₆ = ϖ ^ 3 * A₆) {P Q : W.Point}
    (hP : P ∉ W.nonsingularReduction v) (hQ : Q ∉ W.nonsingularReduction v)
    {X₁ X₂ : v.valuationSubring} (hX₁ : P.xCoord = ((ϖ * X₁ : v.valuationSubring) : F))
    (hX₂ : Q.xCoord = ((ϖ * X₂ : v.valuationSubring) : F)) (hX : ¬ ϖ ∣ X₁ - X₂) :
    P + Q ∉ W.nonsingularReduction v := by
  obtain ⟨hp, ⟨A₁, hA₁⟩, ⟨A₃, hA₃⟩, -⟩ :=
    prime_and_dvd_and_not_dvd_discr_of_isTateTerminal_IStar_zero v hϖ h h₂ h₄ h₆
  have hmem (z : v.valuationSubring) : z ∈ maximalIdeal v.valuationSubring ↔ ϖ ∣ z := by
    rw [hϖ, Ideal.mem_span_singleton]
  obtain ⟨Y₁, hY₁, -⟩ := exists_yCoord_eq_and_dvd_cubic v hϖ h h₂ h₄ h₆ hP hX₁
  obtain ⟨Y₂, hY₂, -⟩ := exists_yCoord_eq_and_dvd_cubic v hϖ h h₂ h₄ h₆ hQ hX₂
  rcases P with _ | ⟨x₁, y₁, h₁⟩
  · exact absurd (zero_mem _) hP
  rcases Q with _ | ⟨x₂, y₂, h₂'⟩
  · exact absurd (zero_mem _) hQ
  rw [Point.xCoord_some] at hX₁ hX₂
  rw [Point.yCoord_some] at hY₁ hY₂
  -- `X₁ − X₂` is a unit, so `x₁ ≠ x₂`
  have hu : IsUnit (X₁ - X₂) := notMem_maximalIdeal.1 fun hm ↦ hX ((hmem _).1 hm)
  have hx : x₁ ≠ x₂ := by
    intro hx
    rw [hX₁, hX₂] at hx
    have : X₁ - X₂ = 0 := by
      rw [sub_eq_zero]
      exact mul_left_cancel₀ hp.ne_zero (Subtype.val_injective hx)
    exact hX (this ▸ dvd_zero ϖ)
  have hxy : ¬(x₁ = x₂ ∧ y₁ = W.negY x₂ y₂) := fun hxy ↦ hx hxy.1
  have ha₁ : W.a₁ = ϖ * A₁ := by
    rw [← integralModel_a₁_eq v.valuationSubring W, hA₁]; simp
  have ha₂ : W.a₂ = ϖ * A₂ := by
    rw [← integralModel_a₂_eq v.valuationSubring W, h₂]; simp
  have ha₃ : W.a₃ = ϖ ^ 2 * A₃ := by
    rw [← integralModel_a₃_eq v.valuationSubring W, hA₃]; simp
  -- the slope is `ϖ L` with `L = (Y₁ − Y₂) / (X₁ − X₂)`
  set L : v.valuationSubring := (Y₁ - Y₂) * ↑hu.unit⁻¹
  have hinv : ((↑hu.unit⁻¹ : v.valuationSubring) : F) * ((X₁ : F) - X₂) = 1 := by
    have h := congrArg (fun z : v.valuationSubring ↦ (z : F)) hu.val_inv_mul
    push_cast at h
    exact h
  have hℓ : W.slope x₁ x₂ y₁ y₂ = ((ϖ * L : v.valuationSubring) : F) := by
    rw [slope_of_X_ne hx, div_eq_iff (sub_ne_zero.2 hx), hX₁, hX₂, hY₁, hY₂]
    push_cast [L]
    linear_combination (-(ϖ : F) ^ 2 * ((Y₁ : F) - Y₂)) * hinv
  -- the coordinates of `P + Q`, as elements of `𝔪`
  set X₃ : v.valuationSubring := (ϖ * L) ^ 2 + ϖ * A₁ * (ϖ * L) - ϖ * A₂ - ϖ * X₁ - ϖ * X₂
  set Y₃ : v.valuationSubring := -((ϖ * L) * (X₃ - ϖ * X₁) + ϖ ^ 2 * Y₁) - ϖ * A₁ * X₃ - ϖ ^ 2 * A₃
  have hX₃ : X₃ ∈ maximalIdeal v.valuationSubring :=
    (hmem _).2 ⟨ϖ * L ^ 2 + ϖ * A₁ * L - A₂ - X₁ - X₂, by ring⟩
  have hY₃ : Y₃ ∈ maximalIdeal v.valuationSubring :=
    (hmem _).2 ⟨-(L * (X₃ - ϖ * X₁) + ϖ * Y₁) - A₁ * X₃ - ϖ * A₃, by ring⟩
  rw [Point.add_some hxy]
  refine (some_notMem_nonsingularReduction_iff v ((hmem _).2 (dvd_pow_self ϖ two_ne_zero |>.trans
    ⟨A₃, hA₃⟩)) ((hmem _).2 (dvd_pow_self ϖ two_ne_zero |>.trans ⟨A₄, h₄⟩))
    ((hmem _).2 (dvd_pow_self ϖ three_ne_zero |>.trans ⟨A₆, h₆⟩)) _).2 ⟨?_, ?_⟩
  · convert (Valuation.mem_maximalIdeal_iff (v := v)).1 hX₃ using 2
    rw [addX, hℓ, ha₁, ha₂, hX₁, hX₂]
    simp only [X₃]
    push_cast
    ring
  · convert (Valuation.mem_maximalIdeal_iff (v := v)).1 hY₃ using 2
    rw [addY, negY, negAddY, addX, hℓ, ha₁, ha₂, ha₃, hX₁, hX₂, hY₁]
    simp only [Y₃, X₃]
    push_cast
    ring

/-- **At `I₀*`, two points with singular reduction add up to a point with nonsingular reduction
exactly when their values of `x / ϖ` have the same residue.** Here `P = (ϖ X₁, y₁)` and
`Q = (ϖ X₂, y₂)` have singular reduction, `ϖ` generates the maximal ideal of the valuation ring,
Tate's algorithm stops at `I₀*` on the integral model, and `a₂ = ϖ A₂`, `a₄ = ϖ² A₄`,
`a₆ = ϖ³ A₆`. So the cosets of `E₀(F)` other than `E₀(F)` itself are classified by roots of the
residue cubic `T³ + A₂ T² + A₄ T + A₆`, since `-Q = (ϖ X₂, -y₂ - a₁ x₂ - a₃)`. -/
theorem add_mem_nonsingularReduction_iff_of_isTateTerminal_IStar_zero {ϖ : v.valuationSubring}
    (hϖ : maximalIdeal v.valuationSubring = Ideal.span {ϖ})
    (h : (integralModel v.valuationSubring W).IsTateTerminal ϖ (.IStar 0))
    {A₂ A₄ A₆ : v.valuationSubring} (h₂ : (integralModel v.valuationSubring W).a₂ = ϖ * A₂)
    (h₄ : (integralModel v.valuationSubring W).a₄ = ϖ ^ 2 * A₄)
    (h₆ : (integralModel v.valuationSubring W).a₆ = ϖ ^ 3 * A₆) {P Q : W.Point}
    (hP : P ∉ W.nonsingularReduction v) (hQ : Q ∉ W.nonsingularReduction v)
    {X₁ X₂ : v.valuationSubring} (hX₁ : P.xCoord = ((ϖ * X₁ : v.valuationSubring) : F))
    (hX₂ : Q.xCoord = ((ϖ * X₂ : v.valuationSubring) : F)) :
    P + Q ∈ W.nonsingularReduction v ↔ residue _ X₁ = residue _ X₂ := by
  have hmem (z : v.valuationSubring) : z ∈ maximalIdeal v.valuationSubring ↔ ϖ ∣ z := by
    rw [hϖ, Ideal.mem_span_singleton]
  have hres : residue _ X₁ = residue _ X₂ ↔ ϖ ∣ X₁ - X₂ := by
    rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff, hmem]
  rw [hres]
  constructor
  · intro hPQ
    by_contra hX
    exact add_notMem_nonsingularReduction_of_not_dvd_sub v hϖ h h₂ h₄ h₆ hP hQ hX₁ hX₂ hX hPQ
  · intro hX
    by_contra hPQ
    obtain ⟨X₃, hs₁, hs₂, hs₃⟩ :=
      exists_dvd_of_add_notMem_nonsingularReduction v hϖ h h₂ h₄ h₆ hP hQ hPQ hX₁ hX₂
    exact (prime_and_dvd_and_not_dvd_discr_of_isTateTerminal_IStar_zero v hϖ h h₂ h₄ h₆).2.2.2
      (TauCeti.Cubic.dvd_discr_of_dvd_sub hs₁ hs₂ hs₃ hX)

/-! ### Over a Henselian valuation ring -/

/-- **At `I₀*` over a Henselian valuation ring, every root of the residue cubic comes from a point
with singular reduction.** Here `ϖ` generates the maximal ideal of the valuation ring, Tate's
algorithm stops at `I₀*` on the integral model, and `a₂ = ϖ A₂`, `a₄ = ϖ² A₄`, `a₆ = ϖ³ A₆`. A root
`t` of the residue cubic `T³ + A₂ T² + A₄ T + A₆` is simple, since the cubic has nonzero
discriminant, so it lifts to a root `X` of `T³ + A₂ T² + A₄ T + A₆` in the valuation ring, and
`(ϖ X, 0)` is a point of `W` with singular reduction. -/
theorem exists_notMem_nonsingularReduction_of_isTateTerminal_IStar_zero
    [HenselianLocalRing v.valuationSubring] {ϖ : v.valuationSubring}
    (hϖ : maximalIdeal v.valuationSubring = Ideal.span {ϖ})
    (h : (integralModel v.valuationSubring W).IsTateTerminal ϖ (.IStar 0))
    {A₂ A₄ A₆ : v.valuationSubring} (h₂ : (integralModel v.valuationSubring W).a₂ = ϖ * A₂)
    (h₄ : (integralModel v.valuationSubring W).a₄ = ϖ ^ 2 * A₄)
    (h₆ : (integralModel v.valuationSubring W).a₆ = ϖ ^ 3 * A₆)
    {t : ResidueField v.valuationSubring}
    (ht : t ^ 3 + residue _ A₂ * t ^ 2 + residue _ A₄ * t + residue _ A₆ = 0) :
    ∃ P : W.Point, P ∉ W.nonsingularReduction v ∧ ∃ X : v.valuationSubring,
      P.xCoord = ((ϖ * X : v.valuationSubring) : F) ∧ residue _ X = t := by
  obtain ⟨hp, ⟨A₁, hA₁⟩, ⟨A₃, hA₃⟩, hD⟩ :=
    prime_and_dvd_and_not_dvd_discr_of_isTateTerminal_IStar_zero v hϖ h h₂ h₄ h₆
  have hmem (z : v.valuationSubring) : z ∈ maximalIdeal v.valuationSubring ↔ ϖ ∣ z := by
    rw [hϖ, Ideal.mem_span_singleton]
  -- a root of `T³ + A₂ T² + A₄ T + A₆` modulo `ϖ` is simple
  have hsimple (z : v.valuationSubring) (hz : ϖ ∣ z ^ 3 + A₂ * z ^ 2 + A₄ * z + A₆) :
      IsUnit (3 * z ^ 2 + 2 * A₂ * z + A₄) :=
    notMem_maximalIdeal.1 fun hm ↦ hD (TauCeti.Cubic.dvd_discr hz (dvd_pow ((hmem _).1 hm)
      two_ne_zero))
  -- lift `t` to a root `X` by Hensel's lemma
  set p : (v.valuationSubring)[X] := (Cubic.mk 1 A₂ A₄ A₆).toPoly
  have heval (z : v.valuationSubring) : p.eval z = z ^ 3 + A₂ * z ^ 2 + A₄ * z + A₆ := by
    simp [p, Cubic.toPoly]
  have hder (z : v.valuationSubring) : p.derivative.eval z = 3 * z ^ 2 + 2 * A₂ * z + A₄ := by
    simp [p, Cubic.toPoly]
    ring
  obtain ⟨t₀, rfl⟩ := residue_surjective t
  have ht₀ : ϖ ∣ t₀ ^ 3 + A₂ * t₀ ^ 2 + A₄ * t₀ + A₆ :=
    (hmem _).1 ((residue_eq_zero_iff _).1 (by simpa using ht))
  obtain ⟨X, hX, hXt⟩ := HenselianLocalRing.is_henselian p Cubic.monic_of_a_eq_one' t₀
    ((hmem _).2 (heval t₀ ▸ ht₀)) (hder t₀ ▸ hsimple t₀ ht₀)
  have hX0 : X ^ 3 + A₂ * X ^ 2 + A₄ * X + A₆ = 0 := heval X ▸ hX.eq_zero
  -- the point `(ϖ X, 0)`
  have hns : (integralModel v.valuationSubring W).toAffine.Nonsingular (ϖ * X) 0 := by
    rw [nonsingular_iff']
    refine ⟨by rw [equation_iff, h₂, h₄, h₆]; linear_combination -ϖ ^ 3 * hX0, Or.inl ?_⟩
    rw [h₂, h₄]
    have hne : 3 * X ^ 2 + 2 * A₂ * X + A₄ ≠ 0 := (hsimple X (hX0 ▸ dvd_zero ϖ)).ne_zero
    have hϖ2 : ϖ ^ 2 ≠ 0 := pow_ne_zero 2 hp.ne_zero
    contrapose! hne
    exact (mul_eq_zero.1 (by linear_combination -hne)).resolve_left hϖ2
  have hF : W.Nonsingular ((ϖ * X : v.valuationSubring) : F) ((0 : v.valuationSubring) : F) := by
    have := ((integralModel v.valuationSubring W).toAffine.map_nonsingular
      (IsFractionRing.injective _ F) _ _).mpr hns
    rwa [← baseChange_integralModel_eq v.valuationSubring W]
  have hlt (z : v.valuationSubring) (hz : ϖ ∣ z) : v (z : F) < 1 :=
    (Valuation.mem_maximalIdeal_iff (v := v)).1 ((hmem _).2 hz)
  exact ⟨.some _ _ hF, (some_notMem_nonsingularReduction_iff v ((hmem _).2 ⟨ϖ * A₃, by
    rw [hA₃]; ring⟩) ((hmem _).2 ⟨ϖ * A₄, by rw [h₄]; ring⟩) ((hmem _).2 ⟨ϖ ^ 2 * A₆, by
    rw [h₆]; ring⟩) hF).2 ⟨hlt _ (dvd_mul_right ϖ X), hlt _ (dvd_zero ϖ)⟩, X,
    Point.xCoord_some hF, by rwa [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]⟩

/-- **At `I₀*` over a Henselian valuation ring, `[E(F) : E₀(F)]` is one more than the number of
roots of the residue cubic.** Here `ϖ` generates the maximal ideal of the valuation ring, Tate's
algorithm stops at `I₀*` on the integral model, and `a₂ = ϖ A₂`, `a₄ = ϖ² A₄`, `a₆ = ϖ³ A₆`, so
that the residue cubic is `T³ + A₂ T² + A₄ T + A₆` over the residue field. Since the residue cubic
has nonzero discriminant, the index is `1`, `2` or `4`. When `F` is complete for a discrete
valuation with perfect residue field and the equation is minimal, this is the local index `c_v` that
Tate's algorithm reports at `I₀*`. -/
theorem index_nonsingularReduction_eq_of_isTateTerminal_IStar_zero
    [HenselianLocalRing v.valuationSubring] {ϖ : v.valuationSubring}
    (hϖ : maximalIdeal v.valuationSubring = Ideal.span {ϖ})
    (h : (integralModel v.valuationSubring W).IsTateTerminal ϖ (.IStar 0))
    {A₂ A₄ A₆ : v.valuationSubring} (h₂ : (integralModel v.valuationSubring W).a₂ = ϖ * A₂)
    (h₄ : (integralModel v.valuationSubring W).a₄ = ϖ ^ 2 * A₄)
    (h₆ : (integralModel v.valuationSubring W).a₆ = ϖ ^ 3 * A₆) :
    (W.nonsingularReduction v).index = 1 + Nat.card {t : ResidueField v.valuationSubring |
      t ^ 3 + residue _ A₂ * t ^ 2 + residue _ A₄ * t + residue _ A₆ = 0} := by
  classical
  set S := {t : ResidueField v.valuationSubring |
    t ^ 3 + residue _ A₂ * t ^ 2 + residue _ A₄ * t + residue _ A₆ = 0}
  have hϖ0 : ϖ ≠ 0 :=
    (prime_and_dvd_and_not_dvd_discr_of_isTateTerminal_IStar_zero v hϖ h h₂ h₄ h₆).1.ne_zero
  -- the residue of `x / ϖ` at a point with singular reduction
  choose X hX hroot using fun (P : W.Point) (hP : P ∉ W.nonsingularReduction v) ↦
    exists_xCoord_eq_of_isTateTerminal_IStar_zero v hϖ h h₂ h₄ h₆ hP
  let g (P : W.Point) : Option S :=
    if hP : P ∈ W.nonsingularReduction v then none else some ⟨residue _ (X P hP), hroot P hP⟩
  -- two points lie in the same coset of `E₀(F)` exactly when they have the same value of `g`
  have key (P Q : W.Point) : g P = g Q ↔ -P + Q ∈ W.nonsingularReduction v := by
    by_cases hP : P ∈ W.nonsingularReduction v <;> by_cases hQ : Q ∈ W.nonsingularReduction v
    · simp only [g, hP, hQ, dite_true, true_iff]
      exact add_mem (neg_mem hP) hQ
    · simp only [g, hP, hQ, dite_true, dite_false, reduceCtorEq, false_iff]
      exact fun hPQ ↦ hQ (by simpa using add_mem hP hPQ)
    · simp only [g, hP, hQ, dite_true, dite_false, reduceCtorEq, false_iff]
      exact fun hPQ ↦ hP (by simpa using neg_mem (sub_mem hPQ hQ))
    · simp only [g, hP, hQ, dite_false, Option.some.injEq, Subtype.mk.injEq]
      rw [add_mem_nonsingularReduction_iff_of_isTateTerminal_IStar_zero v hϖ h h₂ h₄ h₆
        ((neg_mem_iff (H := W.nonsingularReduction v)).not.2 hP) hQ
        (by rw [Point.xCoord_neg]; exact hX P hP) (hX Q hQ)]
  -- so `g` induces a bijection from `W(F) ⧸ E₀(F)` onto `Option S`
  let ĝ : W.Point ⧸ W.nonsingularReduction v → Option S :=
    Quotient.lift g fun P Q hPQ ↦ (key P Q).2 (QuotientAddGroup.leftRel_apply.1 hPQ)
  have hĝ : Function.Bijective ĝ := by
    refine ⟨fun a b hab ↦ ?_, fun s ↦ ?_⟩
    · induction a using QuotientAddGroup.induction_on
      induction b using QuotientAddGroup.induction_on
      exact QuotientAddGroup.eq.2 ((key _ _).1 hab)
    · rcases s with _ | ⟨t, ht⟩
      · refine ⟨(0 : W.Point), ?_⟩
        simp only [ĝ, g, QuotientAddGroup.mk, Quotient.lift_mk, zero_mem, dite_true]
      · obtain ⟨P, hP, Y, hY, rfl⟩ :=
          exists_notMem_nonsingularReduction_of_isTateTerminal_IStar_zero v hϖ h h₂ h₄ h₆ ht
        refine ⟨P, ?_⟩
        simp only [ĝ, g, QuotientAddGroup.mk, Quotient.lift_mk, hP, dite_false, Option.some.injEq,
          Subtype.mk.injEq]
        exact congrArg _ (mul_left_cancel₀ hϖ0 (Subtype.val_injective ((hX P hP).symm.trans hY)))
  -- `S` is finite, being the set of roots of a nonzero polynomial
  have : Finite S := by
    refine Set.Finite.to_subtype ((Polynomial.finite_setOfPred_isRoot
      (Cubic.ne_zero_of_a_ne_zero (P := Cubic.mk 1 (residue _ A₂) (residue _ A₄) (residue _ A₆))
        one_ne_zero)).subset fun t ht ↦ ?_)
    simpa [S, Cubic.toPoly] using ht
  rw [AddSubgroup.index_eq_card, Nat.card_congr (Equiv.ofBijective ĝ hĝ), Finite.card_option,
    add_comm]

end Affine

end WeierstrassCurve

end

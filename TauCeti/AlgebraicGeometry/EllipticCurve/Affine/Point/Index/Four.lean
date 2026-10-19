/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.NonsingularReduction
public import TauCeti.AlgebraicGeometry.EllipticCurve.TateAlgorithm.LocalIndex
public import TauCeti.AlgebraicGeometry.EllipticCurve.TateAlgorithm.Terminal
public import Mathlib.RingTheory.Henselian
-- Proof-only: the points with singular reduction when the reduction is singular at the origin.
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.SingularReduction
-- Proof-only: a root modulo `ϖ` of a quadratic with discriminant prime to `ϖ` is simple.
import TauCeti.Algebra.QuadraticDiscriminant
-- Proof-only: index two from the sums of points outside a subgroup.
import TauCeti.GroupTheory.Index.Two
-- Proof-only: index four from four covering cosets.
import TauCeti.GroupTheory.Index.Four
-- Proof-only: Hensel's lemma for a polynomial that is not monic.
import TauCeti.RingTheory.Henselian.Basic

/-!
# Points with singular reduction: the symbols `Iₙ*`

Let `v` be a valuation on a field `F` whose valuation ring `O` has maximal ideal `𝔪 = (ϖ)`, and
let `W` be a Weierstrass curve over `F` with an integral model `W_O` over `O`. The points with
nonsingular reduction form the subgroup `E₀(F)` of `W(F)`
(`WeierstrassCurve.Affine.nonsingularReduction`). When `F` is complete for a discrete valuation
with perfect residue field and the equation is minimal, the index `[E(F) : E₀(F)]` is the local
index `c_v` that Tate's algorithm computes (Silverman, *Advanced Topics*, IV.9, Table 4.1). This
file proves that equality at the reduction symbols `Iₙ*` with `n ≥ 1`, where `c_v` is `4` or `2`
according as the quadratic at which the subprocedure of Step 7 stops has a root in the residue
field.

Tate's algorithm stops at `Iₙ*` on an equation at a stage of that subprocedure
(`WeierstrassCurve.IsTateOddStage`, `WeierstrassCurve.IsTateEvenStage`). With `m = k + 2`, the odd
stage `n = 2k + 1` has `ϖ ∣ a₁`, `a₂ = ϖ A₂` with `ϖ ∤ A₂`, `a₃ = ϖ^m A₃`, `ϖ^(m+1) ∣ a₄`,
`a₆ = ϖ^(2m) A₆` and `ϖ ∤ A₃² + 4 A₆`; the even stage `n = 2k + 2` has moreover `ϖ^(m+1) ∣ a₃`,
`a₄ = ϖ^(m+1) A₄`, `a₆ = ϖ^(2m+1) A₆` and `ϖ ∤ A₄² − 4 A₂ A₆` in place of the last condition. In
both cases the residue cubic of Step 6 is `T² (T + A₂)`, and comparing powers of `ϖ` in the
Weierstrass equation sorts the points `(x, y)` with singular reduction into

* the points **near the simple root** `−A₂` of the residue cubic: `ϖ² ∣ x + a₂` and `ϖ² ∣ y`;
* the **deep** points: `ϖ^m ∣ x` and `ϖ^m ∣ y`. At the odd stage `y / ϖ^m` reduces to a root of
  `Y² + A₃ Y − A₆`, and at the even stage `ϖ^(m+1) ∣ y` and `x / ϖ^m` reduces to a root of
  `A₂ X² + A₄ X + A₆`. These are the quadratics of the tests `WeierstrassCurve.HasTateYRoot` and
  `WeierstrassCurve.HasTateXRoot` in the definition of `WeierstrassCurve.tateLocalIndex`.

The chord through two points whose sum has singular reduction has slope `ℓ ∈ 𝔪`, and comparing the
coefficients of the Weierstrass cubic restricted to it gives:

* two points near the simple root add up into `E₀(F)`, since otherwise `ϖ³ ∣ a₂²`;
* at the odd stage, two deep points whose roots are exchanged by negation, `Y₁ + Y₂ + A₃ ≡ 0`,
  add up into `E₀(F)`, since otherwise `ϖ ∣ Y₁ − Y₂` and `ϖ` divides the derivative `2 Y₁ + A₃`;
* at the even stage, two deep points with the same root add up into `E₀(F)`, since otherwise
  `ϖ ∣ A₄ + A₂ (X₁ + X₂)` and `ϖ` divides the derivative `2 A₂ X₁ + A₄`;
* a point near the simple root plus a deep point has singular reduction, as the chord through them
  has slope in `𝔪`.

Over a Henselian valuation ring the simple root `−A₂` lifts to a point near it, and a root of the
residue quadratic lifts to a deep point. If the quadratic has a root, the points near the simple
root, the deep points of each root, and `E₀(F)` give four cosets, so the index is `4`; otherwise
every point outside `E₀(F)` is near the simple root and the index is `2`.

## Main result

* `index_nonsingularReduction_eq_tateLocalIndex_of_isTateTerminal_IStar_add_one`, in the namespace
  `WeierstrassCurve.Affine`: over a Henselian valuation ring, at the symbol `Iₙ*` with `n ≥ 1`, the
  point-group index is the local index reported by Tate's algorithm.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VII.6.
* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, GTM 151, IV.9.
* J. Tate, *Algorithm for determining the type of a singular fibre in an elliptic pencil*, in
  *Modular Functions of One Variable IV*, LNM 476 (1975), 33–52.
-/

public section

open IsLocalRing Polynomial TauCeti

namespace WeierstrassCurve

/-! ### Solutions divisible by `ϖ` at a stage of the `Iₙ*` subprocedure -/

section Domain

variable {R : Type*} [CommRing R] {W : WeierstrassCurve R} {ϖ : R}

/-- One step of comparing powers of `ϖ`: at the odd stage `k`, a solution with `ϖʲ ∣ x` and
`ϖʲ ∣ y`, for `2 ≤ j ≤ k + 1`, has `ϖʲ⁺¹ ∣ x` and `ϖʲ⁺¹ ∣ y`. Modulo `ϖ²ʲ⁺¹` the equation reads
`y² ≡ 0`, and then modulo `ϖ²ʲ⁺²` it reads `a₂ x² ≡ 0` with `ϖ ∥ a₂`. -/
private theorem pow_succ_dvd_of_isTateOddStage [IsDomain R] (hϖ : Prime ϖ) {k : ℕ}
    (hk : IsTateOddStage ϖ k W) {x y : R} (h : W.toAffine.Equation x y) {j : ℕ} (hj : 2 ≤ j)
    (hjk : j ≤ k + 1)
    (hx : ϖ ^ j ∣ x) (hy : ϖ ^ j ∣ y) : ϖ ^ (j + 1) ∣ x ∧ ϖ ^ (j + 1) ∣ y := by
  obtain ⟨⟨A₁, hA₁⟩, ⟨A₂, hA₂⟩, hA₂', ⟨A₃, hA₃⟩, ⟨A₄, hA₄⟩, ⟨A₆, hA₆⟩⟩ :=
    isTateOddStage_iff.1 hk
  obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le' hj
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le (show i + 1 ≤ k by omega)
  obtain ⟨X, rfl⟩ := hx
  obtain ⟨Y, rfl⟩ := hy
  rw [Affine.equation_iff, hA₁, hA₂, hA₃, hA₄, hA₆] at h
  have hϖ0 := hϖ.ne_zero
  obtain ⟨Y, rfl⟩ : ϖ ∣ Y := hϖ.dvd_of_dvd_pow (n := 2)
    ⟨ϖ ^ (i + 1) * X ^ 3 + A₂ * X ^ 2 + ϖ ^ (d + 1) * A₄ * X + ϖ ^ (2 * d + 1) * A₆ -
        A₁ * X * Y - ϖ ^ d * A₃ * Y,
      mul_left_cancel₀ (pow_ne_zero (2 * i + 4) hϖ0) (by linear_combination h)⟩
  obtain ⟨X, rfl⟩ : ϖ ∣ X := by
    refine hϖ.dvd_of_dvd_pow (n := 2) ((hϖ.dvd_or_dvd ?_).resolve_left
      fun hd ↦ hA₂' (hA₂ ▸ by rw [pow_two]; exact mul_dvd_mul_left ϖ hd))
    exact ⟨Y ^ 2 + A₁ * X * Y + ϖ ^ d * A₃ * Y - ϖ ^ i * X ^ 3 - ϖ ^ d * A₄ * X -
        ϖ ^ (2 * d) * A₆,
      mul_left_cancel₀ (pow_ne_zero (2 * i + 5) hϖ0) (by linear_combination -h)⟩
  exact ⟨⟨X, by ring⟩, ⟨Y, by ring⟩⟩

/-- **At the odd stage `k`, a solution divisible by `ϖ` is near the simple root or deep.** Over a
domain with a prime `ϖ`, suppose that the equation is at the odd stage `k` of the `Iₙ*`
subprocedure of Tate's algorithm, so that its residue cubic is `T² (T + a₂ / ϖ)`. If `(x, y)` is a
solution with `ϖ ∣ x` and `ϖ ∣ y`, then either `x / ϖ` reduces to the simple root `-a₂ / ϖ`, that
is `ϖ² ∣ x + a₂`, and `ϖ² ∣ y`; or `ϖ^(k+2)` divides both `x` and `y`. -/
private theorem sq_dvd_or_pow_dvd_of_isTateOddStage [IsDomain R] (hϖ : Prime ϖ) {k : ℕ}
    (hk : IsTateOddStage ϖ k W) {x y : R} (h : W.toAffine.Equation x y) (hx : ϖ ∣ x)
    (hy : ϖ ∣ y) :
    (ϖ ^ 2 ∣ x + W.a₂ ∧ ϖ ^ 2 ∣ y) ∨ (ϖ ^ (k + 2) ∣ x ∧ ϖ ^ (k + 2) ∣ y) := by
  obtain ⟨⟨A₁, hA₁⟩, ⟨A₂, hA₂⟩, hA₂', ⟨A₃, hA₃⟩, ⟨A₄, hA₄⟩, ⟨A₆, hA₆⟩⟩ :=
    isTateOddStage_iff.1 hk
  have hϖ0 := hϖ.ne_zero
  have h' := h
  obtain ⟨X, rfl⟩ := hx
  obtain ⟨Y, rfl⟩ := hy
  rw [Affine.equation_iff, hA₁, hA₂, hA₃, hA₄, hA₆] at h
  -- modulo `ϖ³` the equation reads `ϖ² Y² ≡ 0`
  obtain ⟨Y, rfl⟩ : ϖ ∣ Y := hϖ.dvd_of_dvd_pow (n := 2)
    ⟨X ^ 3 + A₂ * X ^ 2 + ϖ ^ (k + 1) * A₄ * X + ϖ ^ (2 * k + 1) * A₆ - A₁ * X * Y -
        ϖ ^ k * A₃ * Y,
      mul_left_cancel₀ (pow_ne_zero 2 hϖ0) (by linear_combination h)⟩
  -- modulo `ϖ⁴` it reads `ϖ³ X² (X + A₂) ≡ 0`
  have hX : ϖ ∣ X ^ 2 * (X + A₂) :=
    ⟨Y ^ 2 + A₁ * X * Y + ϖ ^ k * A₃ * Y - ϖ ^ k * A₄ * X - ϖ ^ (2 * k) * A₆,
      mul_left_cancel₀ (pow_ne_zero 3 hϖ0) (by linear_combination -h)⟩
  rcases hϖ.dvd_or_dvd hX with hX | hX
  · -- `ϖ² ∣ x` and `ϖ² ∣ y`; compare powers of `ϖ` up to `ϖ^(k+2)`
    right
    obtain ⟨X, rfl⟩ := hϖ.dvd_of_dvd_pow hX
    have key : ∀ j, 2 ≤ j → j ≤ k + 2 → ϖ ^ j ∣ ϖ * (ϖ * X) ∧ ϖ ^ j ∣ ϖ * (ϖ * Y) := by
      intro j hj
      induction j, hj using Nat.le_induction with
      | base => exact fun _ ↦ ⟨⟨X, by ring⟩, ⟨Y, by ring⟩⟩
      | succ j hj ih =>
        intro hjk
        obtain ⟨h₁, h₂⟩ := ih (by omega)
        exact pow_succ_dvd_of_isTateOddStage hϖ hk h' hj (by omega) h₁ h₂
    exact key (k + 2) (by omega) le_rfl
  · left
    rw [hA₂, show ϖ * X + ϖ * A₂ = ϖ * (X + A₂) by ring, pow_two]
    exact ⟨mul_dvd_mul_left ϖ hX, ⟨Y, by ring⟩⟩

/-- At the odd stage `k`, a solution with `ϖ^(k+2)` dividing both coordinates gives the test of
`WeierstrassCurve.HasTateYRoot` at level `k + 2`: `ϖ^(2k+5) ∣ y² + a₃ y − a₆`. -/
private theorem pow_dvd_y_of_isTateOddStage {k : ℕ} (hk : IsTateOddStage ϖ k W) {x y : R}
    (h : W.toAffine.Equation x y) (hx : ϖ ^ (k + 2) ∣ x) (hy : ϖ ^ (k + 2) ∣ y) :
    ϖ ^ (2 * (k + 2) + 1) ∣ y ^ 2 + W.a₃ * y - W.a₆ := by
  obtain ⟨⟨A₁, hA₁⟩, ⟨A₂, hA₂⟩, -, -, ⟨A₄, hA₄⟩, -⟩ := isTateOddStage_iff.1 hk
  obtain ⟨X, rfl⟩ := hx
  obtain ⟨Y, rfl⟩ := hy
  rw [Affine.equation_iff] at h
  exact ⟨ϖ ^ (k + 1) * X ^ 3 + A₂ * X ^ 2 + A₄ * X - A₁ * X * Y, by
    rw [hA₁, hA₂, hA₄] at h
    linear_combination h⟩

/-- At the even stage `k`, a solution with `ϖ^(k+2)` dividing both coordinates has
`ϖ^(k+3) ∣ y`: modulo `ϖ^(2k+5)` the equation reads `y² ≡ 0`. -/
private theorem pow_dvd_of_isTateEvenStage [IsDomain R] (hϖ : Prime ϖ) {k : ℕ}
    (hk : IsTateEvenStage ϖ k W) {x y : R} (h : W.toAffine.Equation x y) (hx : ϖ ^ (k + 2) ∣ x)
    (hy : ϖ ^ (k + 2) ∣ y) :
    ϖ ^ (k + 3) ∣ y := by
  obtain ⟨⟨A₁, hA₁⟩, ⟨A₂, hA₂⟩, -, ⟨A₃, hA₃⟩, ⟨A₄, hA₄⟩, ⟨A₆, hA₆⟩⟩ := isTateEvenStage_iff.1 hk
  obtain ⟨X, rfl⟩ := hx
  obtain ⟨Y, rfl⟩ := hy
  rw [Affine.equation_iff, hA₁, hA₂, hA₃, hA₄, hA₆] at h
  obtain ⟨Y, rfl⟩ : ϖ ∣ Y := hϖ.dvd_of_dvd_pow (n := 2)
    ⟨ϖ ^ (k + 1) * X ^ 3 + A₂ * X ^ 2 + A₄ * X + A₆ - A₁ * X * Y - A₃ * Y,
      mul_left_cancel₀ (pow_ne_zero (2 * k + 4) hϖ.ne_zero) (by linear_combination h)⟩
  exact ⟨Y, by ring⟩

/-- At the even stage `k`, a solution with `ϖ^(k+2) ∣ x` and `ϖ^(k+3) ∣ y` gives the test of
`WeierstrassCurve.HasTateXRoot` at level `k + 2`: `ϖ^(2k+6) ∣ a₂ x² + a₄ x + a₆`. -/
private theorem pow_dvd_x_of_isTateEvenStage {k : ℕ} (hk : IsTateEvenStage ϖ k W) {x y : R}
    (h : W.toAffine.Equation x y) (hx : ϖ ^ (k + 2) ∣ x) (hy : ϖ ^ (k + 3) ∣ y) :
    ϖ ^ (2 * (k + 2) + 2) ∣ W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ := by
  obtain ⟨⟨A₁, hA₁⟩, -, -, ⟨A₃, hA₃⟩, -, -⟩ := isTateEvenStage_iff.1 hk
  obtain ⟨X, rfl⟩ := hx
  obtain ⟨Y, rfl⟩ := hy
  rw [Affine.equation_iff] at h
  exact ⟨Y ^ 2 + A₁ * X * Y + A₃ * Y - ϖ ^ k * X ^ 3, by
    rw [hA₁, hA₃] at h
    linear_combination -h⟩

/-- At the odd stage `k`, if `a₃ = ϖ^(k+2) A₃` and `a₆ = ϖ^(2k+4) A₆`, a solution `(x, ϖ^(k+2) Y)`
with `ϖ^(k+2) ∣ x` has `Y` a root modulo `ϖ` of the quadratic `Y² + A₃ Y − A₆`. -/
private theorem dvd_sq_add_mul_sub_of_isTateOddStage [IsDomain R] (hϖ : Prime ϖ) {k : ℕ}
    (hk : IsTateOddStage ϖ k W) {A₃ A₆ : R} (h₃ : W.a₃ = ϖ ^ (k + 2) * A₃)
    (h₆ : W.a₆ = ϖ ^ (2 * k + 4) * A₆) {x Y : R}
    (h : W.toAffine.Equation x (ϖ ^ (k + 2) * Y)) (hx : ϖ ^ (k + 2) ∣ x) :
    ϖ ∣ Y ^ 2 + A₃ * Y - A₆ := by
  have hd := pow_dvd_y_of_isTateOddStage hk h hx (dvd_mul_right _ _)
  rw [h₃, h₆, show (ϖ ^ (k + 2) * Y) ^ 2 + ϖ ^ (k + 2) * A₃ * (ϖ ^ (k + 2) * Y) -
    ϖ ^ (2 * k + 4) * A₆ = ϖ ^ (2 * (k + 2)) * (Y ^ 2 + A₃ * Y - A₆) by ring, pow_succ] at hd
  exact (mul_dvd_mul_iff_left (pow_ne_zero _ hϖ.ne_zero)).1 hd

/-- At the even stage `k`, if `a₂ = ϖ A₂`, `a₄ = ϖ^(k+3) A₄` and `a₆ = ϖ^(2k+5) A₆`, a solution
`(ϖ^(k+2) X, y)` with `ϖ^(k+3) ∣ y` has `X` a root modulo `ϖ` of the quadratic
`A₂ X² + A₄ X + A₆`. -/
private theorem dvd_mul_add_mul_add_of_isTateEvenStage [IsDomain R] (hϖ : Prime ϖ) {k : ℕ}
    (hk : IsTateEvenStage ϖ k W) {A₂ A₄ A₆ : R} (h₂ : W.a₂ = ϖ * A₂)
    (h₄ : W.a₄ = ϖ ^ (k + 3) * A₄) (h₆ : W.a₆ = ϖ ^ (2 * k + 5) * A₆) {X y : R}
    (h : W.toAffine.Equation (ϖ ^ (k + 2) * X) y) (hy : ϖ ^ (k + 3) ∣ y) :
    ϖ ∣ A₂ * (X * X) + A₄ * X + A₆ := by
  have hd := pow_dvd_x_of_isTateEvenStage hk h (dvd_mul_right _ _) hy
  rw [h₂, h₄, h₆, show ϖ * A₂ * (ϖ ^ (k + 2) * X) ^ 2 + ϖ ^ (k + 3) * A₄ * (ϖ ^ (k + 2) * X) +
    ϖ ^ (2 * k + 5) * A₆ = ϖ ^ (2 * (k + 2) + 1) * (A₂ * (X * X) + A₄ * X + A₆) by ring,
    pow_succ ϖ (2 * (k + 2) + 1)] at hd
  exact (mul_dvd_mul_iff_left (pow_ne_zero _ hϖ.ne_zero)).1 hd

/-- At the odd stage `k`, with `a₃ = ϖ^(k+2) A₃` and `a₆ = ϖ^(2k+4) A₆`, the stopping test
`ϖ^(2k+5) ∤ b₆` says that `ϖ` does not divide the discriminant `A₃² + 4 A₆` of the residue
quadratic `Y² + A₃ Y − A₆`. -/
private theorem not_dvd_sq_add_four_mul_of_not_pow_dvd_b₆ {k : ℕ} {A₃ A₆ : R}
    (h₃ : W.a₃ = ϖ ^ (k + 2) * A₃) (h₆ : W.a₆ = ϖ ^ (2 * k + 4) * A₆)
    (hb : ¬ ϖ ^ (2 * k + 5) ∣ W.b₆) : ¬ ϖ ∣ A₃ ^ 2 + 4 * A₆ := by
  rintro ⟨c, hc⟩
  exact hb ⟨c, by rw [b₆, h₃, h₆]; linear_combination ϖ ^ (2 * k + 4) * hc⟩

/-- At the even stage `k`, with `a₂ = ϖ A₂`, `a₄ = ϖ^(k+3) A₄` and `a₆ = ϖ^(2k+5) A₆`, the stopping
test `ϖ^(2k+7) ∤ a₄² − 4 a₂ a₆` says that `ϖ` does not divide the discriminant of the residue
quadratic `A₂ X² + A₄ X + A₆`. -/
private theorem not_dvd_discrim_of_not_pow_dvd_discrim {k : ℕ} {A₂ A₄ A₆ : R}
    (h₂ : W.a₂ = ϖ * A₂) (h₄ : W.a₄ = ϖ ^ (k + 3) * A₄) (h₆ : W.a₆ = ϖ ^ (2 * k + 5) * A₆)
    (hd : ¬ ϖ ^ (2 * k + 7) ∣ discrim W.a₂ W.a₄ W.a₆) : ¬ ϖ ∣ discrim A₂ A₄ A₆ := by
  rintro ⟨c, hc⟩
  rw [discrim] at hc
  exact hd ⟨c, by rw [discrim, h₂, h₄, h₆]; linear_combination ϖ ^ (2 * k + 6) * hc⟩

end Domain

namespace Affine

variable {F Γ₀ : Type*} [Field F] [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation F Γ₀)
  {W : Affine F} [IsIntegral v.valuationSubring W]

/-- At the odd stage `k`, the uniformiser is prime and `a₂`, `a₃`, `a₄` and `a₆` lie in the maximal
ideal; in particular the reduction is singular at the origin. -/
private theorem prime_and_mem_maximalIdeal_of_isTateOddStage {ϖ : v.valuationSubring}
    (hϖ : maximalIdeal v.valuationSubring = Ideal.span {ϖ}) {k : ℕ}
    (hk : IsTateOddStage ϖ k (integralModel v.valuationSubring W)) :
    Prime ϖ ∧ (integralModel v.valuationSubring W).a₂ ∈ maximalIdeal v.valuationSubring ∧
      (integralModel v.valuationSubring W).a₃ ∈ maximalIdeal v.valuationSubring ∧
      (integralModel v.valuationSubring W).a₄ ∈ maximalIdeal v.valuationSubring ∧
      (integralModel v.valuationSubring W).a₆ ∈ maximalIdeal v.valuationSubring := by
  obtain ⟨-, h₂, h₂', h₃, h₄, h₆⟩ := isTateOddStage_iff.1 hk
  -- `ϖ ≠ 0`, since otherwise `a₂ = 0` and then `ϖ² ∣ a₂`
  have hϖ0 : ϖ ≠ 0 := by
    rintro rfl
    exact h₂' (by simpa using h₂)
  refine ⟨(Ideal.span_singleton_prime hϖ0).1 (hϖ ▸ (maximalIdeal.isMaximal _).isPrime), ?_⟩
  simp only [hϖ, Ideal.mem_span_singleton]
  exact ⟨h₂, (dvd_pow_self ϖ (by omega)).trans h₃, (dvd_pow_self ϖ (by omega)).trans h₄,
    (dvd_pow_self ϖ (by omega)).trans h₆⟩

/-- The negative of a point `(x, y)` with integral coordinates is `(x, -y - a₁ x - a₃)`, computed in
the integral model. -/
private theorem exists_neg_some_eq {x y : v.valuationSubring} (h : W.Nonsingular x y) :
    ∃ h' : W.Nonsingular x ((integralModel v.valuationSubring W).toAffine.negY x y : F),
      -Point.some _ _ h = Point.some _ _ h' := by
  simp only [coe_negY_integralModel]
  exact ⟨(nonsingular_neg ..).2 h, Point.neg_some h⟩

variable [DecidableEq F]

/-- **The sum of two points with a chord slope in `𝔪` has singular reduction.** Here `a₂ ∈ 𝔪` and
the reduction is singular at the origin. If `(x₁, y₁)` and `(x₂, y₂)` have integral coordinates in
`𝔪`, with `x₁ ≠ x₂`, and the chord through them has slope `ℓ ∈ 𝔪`, then both coordinates of their
sum lie in `𝔪`. -/
private theorem add_notMem_of_slope_mem
    (h₂ : (integralModel v.valuationSubring W).a₂ ∈ maximalIdeal v.valuationSubring)
    (h₃ : (integralModel v.valuationSubring W).a₃ ∈ maximalIdeal v.valuationSubring)
    (h₄ : (integralModel v.valuationSubring W).a₄ ∈ maximalIdeal v.valuationSubring)
    (h₆ : (integralModel v.valuationSubring W).a₆ ∈ maximalIdeal v.valuationSubring)
    {x₁ y₁ x₂ y₂ ℓ : v.valuationSubring} {hP : W.Nonsingular x₁ y₁} {hQ : W.Nonsingular x₂ y₂}
    (hx₁ : x₁ ∈ maximalIdeal v.valuationSubring) (hy₁ : y₁ ∈ maximalIdeal v.valuationSubring)
    (hx₂ : x₂ ∈ maximalIdeal v.valuationSubring) (hℓ : ℓ ∈ maximalIdeal v.valuationSubring)
    (hne : x₁ ≠ x₂) (hslope : y₁ - y₂ = ℓ * (x₁ - x₂)) :
    Point.some _ _ hP + Point.some _ _ hQ ∉ W.nonsingularReduction v := by
  have hne' : (x₁ : F) ≠ x₂ := fun h ↦ hne (Subtype.ext h)
  have hslopeF : W.slope (x₁ : F) x₂ y₁ y₂ = ℓ := by
    rw [slope_of_X_ne hne', div_eq_iff (sub_ne_zero.2 hne')]
    exact_mod_cast hslope
  have hx₃ : (integralModel v.valuationSubring W).toAffine.addX x₁ x₂ ℓ ∈
      maximalIdeal v.valuationSubring :=
    sub_mem (sub_mem (sub_mem (add_mem (Ideal.pow_mem_of_mem _ hℓ 2 two_pos)
      (Ideal.mul_mem_left _ _ hℓ)) h₂) hx₁) hx₂
  have hy₃ : (integralModel v.valuationSubring W).toAffine.addY x₁ x₂ y₁ ℓ ∈
      maximalIdeal v.valuationSubring :=
    sub_mem (sub_mem (neg_mem (add_mem (Ideal.mul_mem_right _ _ hℓ) hy₁))
      (Ideal.mul_mem_left _ _ hx₃)) h₃
  rw [Point.add_some fun h ↦ hne' h.1, some_notMem_nonsingularReduction_iff v h₃ h₄ h₆, hslopeF,
    ← coe_addX_integralModel, ← coe_addY_integralModel]
  exact ⟨(Valuation.mem_maximalIdeal_iff (v := v)).1 hx₃,
    (Valuation.mem_maximalIdeal_iff (v := v)).1 hy₃⟩

/-- At the odd stage `k`, a point with singular reduction is an affine point `(x, y)` with integral
coordinates that is near the simple root of the residue cubic, `ϖ² ∣ x + a₂` and `ϖ² ∣ y`, or
deep, `ϖ^(k+2) ∣ x` and `ϖ^(k+2) ∣ y`. -/
private theorem exists_eq_some_of_notMem_of_isTateOddStage {ϖ : v.valuationSubring}
    (hϖ : maximalIdeal v.valuationSubring = Ideal.span {ϖ}) {k : ℕ}
    (hk : IsTateOddStage ϖ k (integralModel v.valuationSubring W)) {P : W.Point}
    (hP : P ∉ W.nonsingularReduction v) :
    ∃ (x y : v.valuationSubring) (h : W.Nonsingular x y), P = .some _ _ h ∧
      ((ϖ ^ 2 ∣ x + (integralModel v.valuationSubring W).a₂ ∧ ϖ ^ 2 ∣ y) ∨
        (ϖ ^ (k + 2) ∣ x ∧ ϖ ^ (k + 2) ∣ y)) := by
  obtain ⟨hp, -, m₃, m₄, m₆⟩ := prime_and_mem_maximalIdeal_of_isTateOddStage v hϖ hk
  obtain ⟨x, y, h, rfl, hx, hy⟩ := exists_eq_some_of_notMem_nonsingularReduction v m₃ m₄ m₆ hP
  have key (z : v.valuationSubring) : z ∈ maximalIdeal v.valuationSubring ↔ ϖ ∣ z := by
    rw [hϖ, Ideal.mem_span_singleton]
  exact ⟨x, y, h, rfl, sq_dvd_or_pow_dvd_of_isTateOddStage hp hk
    ((equation_integralModel_iff v).2 h.left) ((key _).1 hx) ((key _).1 hy)⟩

/-- **The chord through two points whose sum has singular reduction, at the odd stage `k`.** If
`ϖ ∣ x₁`, `ϖ ∣ x₂` and the sum of `(x₁, y₁)` and `(x₂, y₂)` has singular reduction, then the slope
of the chord is `ϖ L` with `L` integral, and with `x₃` the `x`-coordinate of the third point,

* `(ϖ L)² + a₁ (ϖ L) − a₂ = x₁ + x₂ + x₃`,
* `y₁ − y₂ = ϖ L (x₁ − x₂)`, and
* `a₄ − a₃ (ϖ L) − (2 ϖ L + a₁) (y₁ − ϖ L x₁) = x₁ x₂ + x₁ x₃ + x₂ x₃`. -/
private theorem exists_chord_of_isTateOddStage {ϖ : v.valuationSubring}
    (hϖ : maximalIdeal v.valuationSubring = Ideal.span {ϖ}) {k : ℕ}
    (hk : IsTateOddStage ϖ k (integralModel v.valuationSubring W))
    {x₁ y₁ x₂ y₂ : v.valuationSubring} {hP : W.Nonsingular x₁ y₁} {hQ : W.Nonsingular x₂ y₂}
    (hx₁ : ϖ ∣ x₁) (hx₂ : ϖ ∣ x₂)
    (hPQ : Point.some _ _ hP + Point.some _ _ hQ ∉ W.nonsingularReduction v) :
    ∃ x₃ L : v.valuationSubring,
      (ϖ * L) ^ 2 + (integralModel v.valuationSubring W).a₁ * (ϖ * L) -
        (integralModel v.valuationSubring W).a₂ = x₁ + x₂ + x₃ ∧
      y₁ - y₂ = ϖ * L * (x₁ - x₂) ∧
      (integralModel v.valuationSubring W).a₄ -
        (integralModel v.valuationSubring W).a₃ * (ϖ * L) -
          (2 * (ϖ * L) + (integralModel v.valuationSubring W).a₁) * (y₁ - ϖ * L * x₁) =
        x₁ * x₂ + x₁ * x₃ + x₂ * x₃ := by
  obtain ⟨hp, m₂, m₃, m₄, m₆⟩ := prime_and_mem_maximalIdeal_of_isTateOddStage v hϖ hk
  obtain ⟨h₁, -⟩ := isTateOddStage_iff.1 hk
  have key (z : v.valuationSubring) : z ∈ maximalIdeal v.valuationSubring ↔ ϖ ∣ z := by
    rw [hϖ, Ideal.mem_span_singleton]
  obtain ⟨x₃, -, ℓ, -, -, -, hx₃, -, hs, hL, hc⟩ :=
    exists_chord_of_add_notMem_nonsingularReduction v m₃ m₄ m₆ hPQ
  -- the slope lies in `𝔪`, since `ℓ² = x₁ + x₂ + x₃ + a₂ − a₁ ℓ`
  obtain ⟨L, rfl⟩ : ϖ ∣ ℓ := by
    refine hp.dvd_of_dvd_pow (n := 2) ?_
    rw [show ℓ ^ 2 = x₁ + x₂ + x₃ + (integralModel v.valuationSubring W).a₂ -
        (integralModel v.valuationSubring W).a₁ * ℓ by linear_combination hs]
    exact dvd_sub (dvd_add (dvd_add (dvd_add hx₁ hx₂) ((key _).1 hx₃)) ((key _).1 m₂))
      (h₁.mul_right ℓ)
  exact ⟨x₃, L, hs, hL, hc⟩

/-- **At the odd stage `k`, the sum of two points near the simple root has nonsingular
reduction.** Let `(x₁, y₁)` and `(x₂, y₂)` have `ϖ² ∣ xᵢ + a₂` and `ϖ² ∣ y₁`. If their sum had
singular reduction, the slope `ℓ` of the chord would lie in `𝔪`, and the coefficient
`a₄ − a₃ ℓ − (2 ℓ + a₁) (y₁ − ℓ x₁) = x₁ x₂ + x₁ x₃ + x₂ x₃` of the Weierstrass cubic restricted to
the chord, with `x₃ = ℓ² + a₁ ℓ − a₂ − x₁ − x₂`, would give `ϖ³ ∣ a₂²`, while `ϖ ∥ a₂`. -/
private theorem add_mem_of_sq_dvd_of_isTateOddStage {ϖ : v.valuationSubring}
    (hϖ : maximalIdeal v.valuationSubring = Ideal.span {ϖ}) {k : ℕ}
    (hk : IsTateOddStage ϖ k (integralModel v.valuationSubring W))
    {x₁ y₁ x₂ y₂ : v.valuationSubring} {hP : W.Nonsingular x₁ y₁} {hQ : W.Nonsingular x₂ y₂}
    (hx₁ : ϖ ^ 2 ∣ x₁ + (integralModel v.valuationSubring W).a₂) (hy₁ : ϖ ^ 2 ∣ y₁)
    (hx₂ : ϖ ^ 2 ∣ x₂ + (integralModel v.valuationSubring W).a₂) :
    Point.some _ _ hP + Point.some _ _ hQ ∈ W.nonsingularReduction v := by
  obtain ⟨hp, -⟩ := prime_and_mem_maximalIdeal_of_isTateOddStage v hϖ hk
  obtain ⟨⟨A₁, hA₁⟩, ⟨A₂, hA₂⟩, hA₂', ⟨A₃, hA₃⟩, ⟨A₄, hA₄⟩, -⟩ := isTateOddStage_iff.1 hk
  have hx (x : v.valuationSubring) (hx : ϖ ^ 2 ∣ x + (integralModel v.valuationSubring W).a₂) :
      ϖ ∣ x := by
    rw [show x = x + (integralModel v.valuationSubring W).a₂ - ϖ * A₂ by rw [hA₂]; ring]
    exact dvd_sub ((dvd_pow_self ϖ two_ne_zero).trans hx) (dvd_mul_right _ _)
  by_contra hPQ
  obtain ⟨x₃, L, hs, -, hc⟩ := exists_chord_of_isTateOddStage v hϖ hk (hx _ hx₁) (hx _ hx₂) hPQ
  obtain ⟨s₁, hs₁⟩ := hx₁
  obtain ⟨s₂, hs₂⟩ := hx₂
  obtain ⟨Y₁, rfl⟩ := hy₁
  rw [hA₂] at hs₁ hs₂
  obtain rfl : x₁ = ϖ ^ 2 * s₁ - ϖ * A₂ := by linear_combination hs₁
  obtain rfl : x₂ = ϖ ^ 2 * s₂ - ϖ * A₂ := by linear_combination hs₂
  rw [hA₁, hA₂] at hs
  obtain rfl : x₃ = (ϖ * L) ^ 2 + ϖ * A₁ * (ϖ * L) - ϖ * A₂ - (ϖ ^ 2 * s₁ - ϖ * A₂) -
      (ϖ ^ 2 * s₂ - ϖ * A₂) := by
    linear_combination -hs
  rw [hA₁, hA₃, hA₄] at hc
  -- `a₂² = ϖ² A₂²` is divisible by `ϖ³`
  refine hA₂' (by
    rw [hA₂, pow_two]
    refine mul_dvd_mul_left ϖ (hp.dvd_of_dvd_pow (n := 2) ⟨ϖ * s₁ * s₂ +
      ϖ * (L ^ 2 + A₁ * L) * (s₁ + s₂) - 2 * A₂ * (L ^ 2 + A₁ * L) - ϖ * (s₁ + s₂) ^ 2 +
      2 * A₂ * (s₁ + s₂) - ϖ ^ k * A₄ + ϖ ^ k * A₃ * L + (2 * L + A₁) * (Y₁ - L * (ϖ * s₁ - A₂)),
      mul_left_cancel₀ (pow_ne_zero 2 hp.ne_zero) ?_⟩)
    linear_combination hc)

/-- **At the odd stage `k`, a point near the simple root plus a deep point has singular
reduction.** If `ϖ² ∣ x₁ + a₂`, `ϖ² ∣ y₁`, `ϖ^(k+2) ∣ x₂` and `ϖ² ∣ y₂`, then `x₁ − x₂` is `ϖ` times
the unit `x₁ / ϖ − x₂ / ϖ ≡ −a₂ / ϖ`, while `ϖ² ∣ y₁ − y₂`, so the chord has slope in `𝔪`. -/
private theorem add_notMem_of_sq_dvd_of_pow_dvd {ϖ : v.valuationSubring}
    (hϖ : maximalIdeal v.valuationSubring = Ideal.span {ϖ}) {k : ℕ}
    (hk : IsTateOddStage ϖ k (integralModel v.valuationSubring W))
    {x₁ y₁ x₂ y₂ : v.valuationSubring} {hP : W.Nonsingular x₁ y₁} {hQ : W.Nonsingular x₂ y₂}
    (hx₁ : ϖ ^ 2 ∣ x₁ + (integralModel v.valuationSubring W).a₂) (hy₁ : ϖ ^ 2 ∣ y₁)
    (hx₂ : ϖ ^ (k + 2) ∣ x₂) (hy₂ : ϖ ^ 2 ∣ y₂) :
    Point.some _ _ hP + Point.some _ _ hQ ∉ W.nonsingularReduction v := by
  obtain ⟨hp, m₂, m₃, m₄, m₆⟩ := prime_and_mem_maximalIdeal_of_isTateOddStage v hϖ hk
  obtain ⟨-, ⟨A₂, hA₂⟩, hA₂', -⟩ := isTateOddStage_iff.1 hk
  have key (z : v.valuationSubring) : z ∈ maximalIdeal v.valuationSubring ↔ ϖ ∣ z := by
    rw [hϖ, Ideal.mem_span_singleton]
  obtain ⟨s₁, hs₁⟩ := hx₁
  rw [hA₂] at hs₁
  obtain ⟨X₂, rfl⟩ := hx₂
  obtain ⟨w, hw⟩ := dvd_sub hy₁ hy₂
  -- `x₁ − x₂ = ϖ u` with `u = ϖ s₁ − A₂ − ϖ^(k+1) X₂` a unit, since `ϖ ∤ A₂`
  have hu : IsUnit (ϖ * s₁ - A₂ - ϖ ^ (k + 1) * X₂) := by
    by_contra hn
    refine hA₂' ?_
    rw [hA₂, pow_two]
    refine mul_dvd_mul_left ϖ ?_
    rw [show A₂ = ϖ * (s₁ - ϖ ^ k * X₂) - (ϖ * s₁ - A₂ - ϖ ^ (k + 1) * X₂) by ring]
    exact dvd_sub (dvd_mul_right _ _) ((key _).1 ((mem_maximalIdeal _).2 hn))
  have hx : x₁ - ϖ ^ (k + 2) * X₂ = ϖ * (ϖ * s₁ - A₂ - ϖ ^ (k + 1) * X₂) := by
    linear_combination hs₁
  refine add_notMem_of_slope_mem v m₂ m₃ m₄ m₆ (ℓ := ϖ * (w * ↑hu.unit⁻¹))
    ((key _).2 ⟨ϖ * s₁ - A₂, by linear_combination hs₁⟩)
    ((key _).2 ((dvd_pow_self ϖ two_ne_zero).trans hy₁)) ((key _).2 ⟨ϖ ^ (k + 1) * X₂, by ring⟩)
    ((key _).2 (dvd_mul_right _ _)) (fun h ↦ mul_ne_zero hp.ne_zero hu.ne_zero ?_) ?_
  · rw [← hx, h, sub_self]
  · rw [hw, hx]
    linear_combination (-(ϖ ^ 2 * w)) * hu.val_inv_mul

/-- **At the odd stage `k`, two deep points whose classes are exchanged by negation add up to a
point of `E₀(F)`.** Here Tate's algorithm stops at the stage, `ϖ^(2k+5) ∤ b₆`, so the residue
quadratic `Y² + A₃ Y − A₆` has distinct roots. Let `(x₁, ϖ^(k+2) Y₁)` and `(x₂, ϖ^(k+2) Y₂)` have
`ϖ^(k+2) ∣ xᵢ` and `ϖ ∣ Y₁ + Y₂ + A₃`. If their sum had singular reduction, the chord would have
slope in `𝔪`, so `ϖ^(k+3) ∣ y₁ − y₂` and `ϖ ∣ Y₁ − Y₂`; then `ϖ` would divide the derivative
`2 Y₁ + A₃` at the root `Y₁`. -/
private theorem add_mem_of_isTateOddStage {ϖ : v.valuationSubring}
    (hϖ : maximalIdeal v.valuationSubring = Ideal.span {ϖ}) {k : ℕ}
    (hk : IsTateOddStage ϖ k (integralModel v.valuationSubring W))
    (hb : ¬ ϖ ^ (2 * k + 5) ∣ (integralModel v.valuationSubring W).b₆) {A₃ A₆ : v.valuationSubring}
    (h₃ : (integralModel v.valuationSubring W).a₃ = ϖ ^ (k + 2) * A₃)
    (h₆ : (integralModel v.valuationSubring W).a₆ = ϖ ^ (2 * k + 4) * A₆)
    {x₁ y₁ x₂ y₂ Y₁ Y₂ : v.valuationSubring} {hP : W.Nonsingular x₁ y₁}
    {hQ : W.Nonsingular x₂ y₂} (hx₁ : ϖ ^ (k + 2) ∣ x₁) (hy₁ : y₁ = ϖ ^ (k + 2) * Y₁)
    (hx₂ : ϖ ^ (k + 2) ∣ x₂) (hy₂ : y₂ = ϖ ^ (k + 2) * Y₂) (hY : ϖ ∣ Y₁ + Y₂ + A₃) :
    Point.some _ _ hP + Point.some _ _ hQ ∈ W.nonsingularReduction v := by
  obtain ⟨hp, -⟩ := prime_and_mem_maximalIdeal_of_isTateOddStage v hϖ hk
  -- `Y₁` is a simple root modulo `ϖ` of `Y² + A₃ Y − A₆`
  have hroot := dvd_sq_add_mul_sub_of_isTateOddStage hp hk h₃ h₆
    (hy₁ ▸ (equation_integralModel_iff v).2 hP.left) hx₁
  have hb' := not_dvd_sq_add_four_mul_of_not_pow_dvd_b₆ h₃ h₆ hb
  have h1 : ϖ ∣ x₁ := (dvd_pow_self ϖ (by omega)).trans hx₁
  have h2 : ϖ ∣ x₂ := (dvd_pow_self ϖ (by omega)).trans hx₂
  by_contra hPQ
  obtain ⟨-, L, -, hL, -⟩ := exists_chord_of_isTateOddStage v hϖ hk h1 h2 hPQ
  refine not_dvd_two_mul_add_of_not_dvd_sq_add_four_mul hb' hroot ?_
  obtain ⟨X₁, rfl⟩ := hx₁
  obtain ⟨X₂, rfl⟩ := hx₂
  rw [hy₁, hy₂] at hL
  rw [show 2 * Y₁ + A₃ = Y₁ + Y₂ + A₃ + ϖ * (L * (X₁ - X₂)) by
    linear_combination mul_left_cancel₀ (pow_ne_zero (k + 2) hp.ne_zero)
      (show ϖ ^ (k + 2) * (Y₁ - Y₂) = ϖ ^ (k + 2) * (ϖ * (L * (X₁ - X₂))) by
        linear_combination hL)]
  exact dvd_add hY (dvd_mul_right _ _)

/-- **At the even stage `k`, two deep points in the same class add up to a point of `E₀(F)`.**
Here Tate's algorithm stops at the stage, `ϖ^(2k+7) ∤ a₄² − 4 a₂ a₆`, so the residue quadratic
`A₂ X² + A₄ X + A₆` has distinct roots. Let `(ϖ^(k+2) X₁, y₁)` and `(ϖ^(k+2) X₂, y₂)` have
`ϖ^(k+3) ∣ y₁` and `ϖ ∣ X₁ − X₂`. If their sum had singular reduction, the coefficient of `x` in
the Weierstrass cubic restricted to the chord would give `ϖ ∣ A₄ + A₂ (X₁ + X₂)`, so `ϖ` would
divide the derivative `2 A₂ X₁ + A₄` at the root `X₁`. -/
private theorem add_mem_of_isTateEvenStage {ϖ : v.valuationSubring}
    (hϖ : maximalIdeal v.valuationSubring = Ideal.span {ϖ}) {k : ℕ}
    (hk : IsTateEvenStage ϖ k (integralModel v.valuationSubring W))
    (hd : ¬ ϖ ^ (2 * k + 7) ∣ discrim (integralModel v.valuationSubring W).a₂
      (integralModel v.valuationSubring W).a₄ (integralModel v.valuationSubring W).a₆)
    {x₁ y₁ x₂ y₂ X₁ X₂ : v.valuationSubring} {hP : W.Nonsingular x₁ y₁}
    {hQ : W.Nonsingular x₂ y₂} (hx₁ : x₁ = ϖ ^ (k + 2) * X₁) (hy₁ : ϖ ^ (k + 3) ∣ y₁)
    (hx₂ : x₂ = ϖ ^ (k + 2) * X₂) (hX : ϖ ∣ X₁ - X₂) :
    Point.some _ _ hP + Point.some _ _ hQ ∈ W.nonsingularReduction v := by
  have hodd := hk.isTateOddStage
  obtain ⟨⟨A₁, hA₁⟩, ⟨A₂, hA₂⟩, -, ⟨A₃, hA₃⟩, ⟨A₄, hA₄⟩, ⟨A₆, hA₆⟩⟩ := isTateEvenStage_iff.1 hk
  obtain ⟨hp, -⟩ := prime_and_mem_maximalIdeal_of_isTateOddStage v hϖ hodd
  -- `X₁` is a simple root modulo `ϖ` of `A₂ X² + A₄ X + A₆`
  have hroot := dvd_mul_add_mul_add_of_isTateEvenStage hp hk hA₂ hA₄ hA₆
    (hx₁ ▸ (equation_integralModel_iff v).2 hP.left) hy₁
  have hd' := not_dvd_discrim_of_not_pow_dvd_discrim hA₂ hA₄ hA₆ hd
  have h1 : ϖ ∣ x₁ := hx₁ ▸ (dvd_pow_self ϖ (by omega)).trans (dvd_mul_right _ _)
  have h2 : ϖ ∣ x₂ := hx₂ ▸ (dvd_pow_self ϖ (by omega)).trans (dvd_mul_right _ _)
  by_contra hPQ
  obtain ⟨x₃, L, hs, -, hc⟩ := exists_chord_of_isTateOddStage v hϖ hodd h1 h2 hPQ
  refine not_dvd_two_mul_mul_add_of_not_dvd_discrim hd' hroot ?_
  subst hx₁ hx₂
  obtain ⟨Y₁, rfl⟩ := hy₁
  rw [hA₁, hA₂] at hs
  obtain rfl : x₃ = (ϖ * L) ^ 2 + ϖ * A₁ * (ϖ * L) - ϖ * A₂ - ϖ ^ (k + 2) * X₁ -
      ϖ ^ (k + 2) * X₂ := by
    linear_combination -hs
  rw [hA₁, hA₃, hA₄] at hc
  -- `a₄ + a₂ (x₁ + x₂) = ϖ^(k+3) (A₄ + A₂ (X₁ + X₂))` is divisible by `ϖ^(k+4)`
  have hsum : ϖ ∣ A₄ + A₂ * (X₁ + X₂) :=
    ⟨A₃ * L + (2 * L + A₁) * (Y₁ - L * X₁) + ϖ ^ k * X₁ * X₂ +
      (L ^ 2 + A₁ * L - ϖ ^ k * (X₁ + X₂)) * (X₁ + X₂),
      mul_left_cancel₀ (pow_ne_zero (k + 3) hp.ne_zero) (by linear_combination hc)⟩
  rw [show 2 * A₂ * X₁ + A₄ = A₄ + A₂ * (X₁ + X₂) + A₂ * (X₁ - X₂) by ring]
  exact dvd_add hsum (hX.mul_left A₂)

/-! ### Points with singular reduction over a Henselian valuation ring -/

/-- **At the odd stage `k`, some point is near the simple root of the residue cubic**, when the
valuation ring is Henselian. The cubic `T³ + A₂ T² + ϖ^(k+1) A₄ T + ϖ^(2k+1) A₆`, the Weierstrass
equation at `(ϖ T, 0)` divided by `ϖ³`, reduces to `T² (T + A₂)`. Its simple root `−A₂` lifts to a
root `T`, and `(ϖ T, 0)` has singular reduction. -/
private theorem exists_sq_dvd_of_isTateOddStage [HenselianLocalRing v.valuationSubring]
    {ϖ : v.valuationSubring} (hϖ : maximalIdeal v.valuationSubring = Ideal.span {ϖ}) {k : ℕ}
    (hk : IsTateOddStage ϖ k (integralModel v.valuationSubring W)) :
    ∃ (x y : v.valuationSubring) (h : W.Nonsingular x y),
      ϖ ^ 2 ∣ x + (integralModel v.valuationSubring W).a₂ ∧ ϖ ^ 2 ∣ y ∧
        Point.some _ _ h ∉ W.nonsingularReduction v := by
  obtain ⟨hp, -, m₃, m₄, m₆⟩ := prime_and_mem_maximalIdeal_of_isTateOddStage v hϖ hk
  obtain ⟨-, ⟨A₂, hA₂⟩, hA₂', -, ⟨A₄, hA₄⟩, ⟨A₆, hA₆⟩⟩ := isTateOddStage_iff.1 hk
  have key (z : v.valuationSubring) : z ∈ maximalIdeal v.valuationSubring ↔ ϖ ∣ z := by
    rw [hϖ, Ideal.mem_span_singleton]
  have hA₂u : ¬ ϖ ∣ A₂ ^ 2 := fun hd ↦ hA₂' (by
    rw [hA₂, pow_two]
    exact mul_dvd_mul_left ϖ (hp.dvd_of_dvd_pow hd))
  set f : v.valuationSubring[X] := X ^ 3 + C A₂ * X ^ 2 + C (ϖ ^ (k + 1) * A₄) * X +
    C (ϖ ^ (2 * k + 1) * A₆) with hf
  have hmon : f.Monic := by
    rw [hf]
    monicity!
  have heval (z : v.valuationSubring) :
      f.eval z = z ^ 3 + A₂ * z ^ 2 + ϖ ^ (k + 1) * A₄ * z + ϖ ^ (2 * k + 1) * A₆ := by
    simp [hf, -map_mul, -map_pow]
  have hder (z : v.valuationSubring) :
      f.derivative.eval z = 3 * z ^ 2 + 2 * A₂ * z + ϖ ^ (k + 1) * A₄ := by
    simp [hf, -map_mul, -map_pow]
    ring
  -- the derivative is a unit at every lift of `−A₂`, where it is `A₂²` modulo `ϖ`
  have hunit (z : v.valuationSubring) (hz : ϖ ∣ z + A₂) :
      IsUnit (3 * z ^ 2 + 2 * A₂ * z + ϖ ^ (k + 1) * A₄) := by
    by_contra hn
    refine hA₂u ?_
    rw [show A₂ ^ 2 = 3 * z ^ 2 + 2 * A₂ * z + ϖ ^ (k + 1) * A₄ - (z + A₂) * (3 * z - A₂) -
      ϖ * (ϖ ^ k * A₄) by ring]
    exact dvd_sub (dvd_sub ((key _).1 ((mem_maximalIdeal _).2 hn)) (hz.mul_right _))
      (dvd_mul_right _ _)
  obtain ⟨T, hT, hTA⟩ := HenselianLocalRing.is_henselian f hmon (-A₂)
    ((key _).2 ⟨ϖ ^ k * A₄ * -A₂ + ϖ ^ (2 * k) * A₆, by rw [heval]; ring⟩)
    (by rw [hder]; exact hunit _ (by simp))
  have hT0 : T ^ 3 + A₂ * T ^ 2 + ϖ ^ (k + 1) * A₄ * T + ϖ ^ (2 * k + 1) * A₆ = 0 :=
    heval T ▸ hT.eq_zero
  have hTA' : ϖ ∣ T + A₂ := by
    rw [← sub_neg_eq_add]
    exact (key _).1 hTA
  have hns : (integralModel v.valuationSubring W).toAffine.Nonsingular (ϖ * T) 0 := by
    rw [nonsingular_iff']
    refine ⟨by
      rw [equation_iff, hA₂, hA₄, hA₆]
      linear_combination -ϖ ^ 3 * hT0, Or.inl ?_⟩
    rw [hA₂, hA₄, mul_zero, zero_sub, neg_ne_zero, show 3 * (ϖ * T) ^ 2 + 2 * (ϖ * A₂) * (ϖ * T) +
      ϖ ^ (k + 3) * A₄ = ϖ ^ 2 * (3 * T ^ 2 + 2 * A₂ * T + ϖ ^ (k + 1) * A₄) by ring]
    exact mul_ne_zero (pow_ne_zero 2 hp.ne_zero) (hunit T hTA').ne_zero
  have hF := (nonsingular_integralModel_iff v).1 hns
  refine ⟨ϖ * T, 0, hF, ?_, dvd_zero _, (some_notMem_nonsingularReduction_iff v m₃ m₄ m₆ hF).2
    ⟨(Valuation.mem_maximalIdeal_iff (v := v)).1 ((key _).2 (dvd_mul_right _ _)), by simp⟩⟩
  rw [hA₂, show ϖ * T + ϖ * A₂ = ϖ * (T + A₂) by ring, pow_two]
  exact mul_dvd_mul_left ϖ hTA'

/-- **At the odd stage `k`, some point is deep** when the valuation ring is Henselian and the
residue quadratic `Y² + A₃ Y − A₆` has a root, where `a₃ = ϖ^(k+2) A₃` and `a₆ = ϖ^(2k+4) A₆`.
Since `ϖ^(2k+5) ∤ b₆`, the root is simple; it lifts to a root `Y`, and the point is
`(0, ϖ^(k+2) Y)`. -/
private theorem exists_pow_dvd_of_hasTateYRoot [HenselianLocalRing v.valuationSubring]
    {ϖ : v.valuationSubring} (hϖ : maximalIdeal v.valuationSubring = Ideal.span {ϖ}) {k : ℕ}
    (hk : IsTateOddStage ϖ k (integralModel v.valuationSubring W))
    (hb : ¬ ϖ ^ (2 * k + 5) ∣ (integralModel v.valuationSubring W).b₆)
    (hr : (integralModel v.valuationSubring W).HasTateYRoot ϖ (k + 2)) :
    ∃ (x y : v.valuationSubring) (h : W.Nonsingular x y), ϖ ^ (k + 2) ∣ x ∧ ϖ ^ (k + 2) ∣ y ∧
      Point.some _ _ h ∉ W.nonsingularReduction v := by
  obtain ⟨hp, -, m₃, m₄, m₆⟩ := prime_and_mem_maximalIdeal_of_isTateOddStage v hϖ hk
  obtain ⟨-, -, -, ⟨A₃, hA₃⟩, -, ⟨A₆, hA₆⟩⟩ := isTateOddStage_iff.1 hk
  have key (z : v.valuationSubring) : z ∈ maximalIdeal v.valuationSubring ↔ ϖ ∣ z := by
    rw [hϖ, Ideal.mem_span_singleton]
  have hb' := not_dvd_sq_add_four_mul_of_not_pow_dvd_b₆ hA₃ hA₆ hb
  obtain ⟨t₀, ht₀⟩ := (hasTateYRoot_iff hp.ne_zero (b₆ := A₆) hA₃ (by rw [hA₆]; ring)).1 hr
  -- lift the root of the residue quadratic by Hensel's lemma
  set f : v.valuationSubring[X] := X ^ 2 + C A₃ * X - C A₆ with hf
  have hmon : f.Monic := by
    rw [hf]
    monicity!
  have heval (z : v.valuationSubring) : f.eval z = z ^ 2 + A₃ * z - A₆ := by
    simp [hf, -map_mul, -map_pow]
  have hder (z : v.valuationSubring) : f.derivative.eval z = 2 * z + A₃ := by
    simp [hf, one_add_one_eq_two]
  obtain ⟨Y, hY, -⟩ := HenselianLocalRing.is_henselian f hmon t₀ ((key _).2 (heval t₀ ▸ ht₀))
    (by
      rw [hder, ← residue_ne_zero_iff_isUnit, Ne, residue_eq_zero_iff, key]
      exact not_dvd_two_mul_add_of_not_dvd_sq_add_four_mul hb' ht₀)
  have hY : Y ^ 2 + A₃ * Y - A₆ = 0 := heval Y ▸ hY.eq_zero
  have hY' : ¬ ϖ ∣ 2 * Y + A₃ :=
    not_dvd_two_mul_add_of_not_dvd_sq_add_four_mul hb' (hY ▸ dvd_zero ϖ)
  have hns : (integralModel v.valuationSubring W).toAffine.Nonsingular 0 (ϖ ^ (k + 2) * Y) := by
    rw [nonsingular_iff']
    refine ⟨by
      rw [equation_iff, hA₃, hA₆]
      linear_combination ϖ ^ (2 * k + 4) * hY, Or.inr ?_⟩
    rw [hA₃, mul_zero, add_zero,
      show 2 * (ϖ ^ (k + 2) * Y) + ϖ ^ (k + 2) * A₃ = ϖ ^ (k + 2) * (2 * Y + A₃) by ring]
    exact mul_ne_zero (pow_ne_zero _ hp.ne_zero) fun h0 ↦ hY' (h0 ▸ dvd_zero ϖ)
  have hF := (nonsingular_integralModel_iff v).1 hns
  refine ⟨0, ϖ ^ (k + 2) * Y, hF, dvd_zero _, dvd_mul_right _ _,
    (some_notMem_nonsingularReduction_iff v m₃ m₄ m₆ hF).2 ⟨by simp, ?_⟩⟩
  exact (Valuation.mem_maximalIdeal_iff (v := v)).1 ((key _).2 (by
    rw [pow_succ]
    exact (dvd_mul_left ϖ _).mul_right Y))

/-- **Lifting a simple root of a residue quadratic to a perturbed cubic.** Over a Henselian local
ring whose maximal ideal is generated by `ϖ`, if `t₀` is a root modulo `ϖ` of `A₂ X² + A₄ X + A₆`
and `ϖ` does not divide the discriminant, then for every `c` divisible by `ϖ` the cubic
`c X³ + A₂ X² + A₄ X + A₆` has a root: its derivative at `t₀` is congruent to `2 A₂ t₀ + A₄`, a
unit. -/
private theorem exists_cubic_eq_zero_of_dvd {R : Type*} [CommRing R] [HenselianLocalRing R]
    {ϖ c A₂ A₄ A₆ t₀ : R} (hϖ : maximalIdeal R = Ideal.span {ϖ}) (hc : ϖ ∣ c)
    (hd : ¬ ϖ ∣ discrim A₂ A₄ A₆) (ht₀ : ϖ ∣ A₂ * (t₀ * t₀) + A₄ * t₀ + A₆) :
    ∃ X, c * X ^ 3 + A₂ * X ^ 2 + A₄ * X + A₆ = 0 := by
  have key (z : R) : z ∈ maximalIdeal R ↔ ϖ ∣ z := by
    rw [hϖ, Ideal.mem_span_singleton]
  set f : R[X] := C c * X ^ 3 + C A₂ * X ^ 2 + C A₄ * X + C A₆ with hf
  have hunit : IsUnit (f.derivative.eval t₀) := by
    by_contra hn
    refine not_dvd_two_mul_mul_add_of_not_dvd_discrim hd ht₀ ?_
    have hder : f.derivative.eval t₀ = 3 * c * t₀ ^ 2 + (2 * A₂ * t₀ + A₄) := by
      simp [hf]
      ring
    rw [show 2 * A₂ * t₀ + A₄ = f.derivative.eval t₀ - 3 * c * t₀ ^ 2 by rw [hder]; ring]
    exact dvd_sub ((key _).1 ((mem_maximalIdeal _).2 hn)) (by
      rw [mul_comm 3 c, mul_assoc]
      exact hc.mul_right _)
  obtain ⟨X, hX, -⟩ := Polynomial.exists_isRoot_sub_mem (J := maximalIdeal R) f (a₀ := t₀)
    ((key _).2 (by
      rw [show f.eval t₀ = c * t₀ ^ 3 + (A₂ * (t₀ * t₀) + A₄ * t₀ + A₆) by simp [hf]; ring]
      exact dvd_add (hc.mul_right _) ht₀)) (hunit.map _)
  exact ⟨X, by simpa [hf] using hX.eq_zero⟩

/-- **At the even stage `k`, some point is deep** when the valuation ring is Henselian and the
residue quadratic `A₂ X² + A₄ X + A₆` has a root, where `a₂ = ϖ A₂`, `a₄ = ϖ^(k+3) A₄` and
`a₆ = ϖ^(2k+5) A₆`. Since `ϖ^(2k+7) ∤ a₄² − 4 a₂ a₆`, the root is simple, and it lifts to a root
`X` of the Weierstrass equation at `(ϖ^(k+2) X, 0)` divided by `ϖ^(2k+5)`, the cubic
`ϖ^(k+1) X³ + A₂ X² + A₄ X + A₆`. -/
private theorem exists_eq_pow_mul_of_hasTateXRoot [HenselianLocalRing v.valuationSubring]
    {ϖ : v.valuationSubring} (hϖ : maximalIdeal v.valuationSubring = Ideal.span {ϖ}) {k : ℕ}
    (hk : IsTateEvenStage ϖ k (integralModel v.valuationSubring W))
    (hd : ¬ ϖ ^ (2 * k + 7) ∣ discrim (integralModel v.valuationSubring W).a₂
      (integralModel v.valuationSubring W).a₄ (integralModel v.valuationSubring W).a₆)
    (hr : (integralModel v.valuationSubring W).HasTateXRoot ϖ (k + 2)) :
    ∃ (x y X : v.valuationSubring) (h : W.Nonsingular x y), x = ϖ ^ (k + 2) * X ∧
      ϖ ^ (k + 3) ∣ y ∧ Point.some _ _ h ∉ W.nonsingularReduction v := by
  obtain ⟨hp, -, m₃, m₄, m₆⟩ :=
    prime_and_mem_maximalIdeal_of_isTateOddStage v hϖ hk.isTateOddStage
  obtain ⟨-, ⟨A₂, hA₂⟩, -, -, ⟨A₄, hA₄⟩, ⟨A₆, hA₆⟩⟩ := isTateEvenStage_iff.1 hk
  have key (z : v.valuationSubring) : z ∈ maximalIdeal v.valuationSubring ↔ ϖ ∣ z := by
    rw [hϖ, Ideal.mem_span_singleton]
  have hd' := not_dvd_discrim_of_not_pow_dvd_discrim hA₂ hA₄ hA₆ hd
  obtain ⟨t₀, ht₀⟩ :=
    (hasTateXRoot_iff hp.ne_zero (b₄ := A₄) (b₆ := A₆) hA₂ (by rw [hA₄])
      (by rw [hA₆]; ring)).1 hr
  obtain ⟨X, hX0⟩ := exists_cubic_eq_zero_of_dvd (c := ϖ ^ (k + 1)) (t₀ := t₀) hϖ
    (dvd_pow_self ϖ k.succ_ne_zero) hd' (by rw [← pow_two]; exact ht₀)
  have hXd : ¬ ϖ ∣ 2 * A₂ * X + A₄ :=
    not_dvd_two_mul_mul_add_of_not_dvd_discrim hd' ⟨-(ϖ ^ k * X ^ 3), by linear_combination hX0⟩
  have hns : (integralModel v.valuationSubring W).toAffine.Nonsingular (ϖ ^ (k + 2) * X) 0 := by
    rw [nonsingular_iff']
    refine ⟨by
      rw [equation_iff, hA₂, hA₄, hA₆]
      linear_combination -ϖ ^ (2 * k + 5) * hX0, Or.inl ?_⟩
    rw [hA₂, hA₄, mul_zero, zero_sub, neg_ne_zero, show 3 * (ϖ ^ (k + 2) * X) ^ 2 +
      2 * (ϖ * A₂) * (ϖ ^ (k + 2) * X) + ϖ ^ (k + 3) * A₄ =
        ϖ ^ (k + 3) * (ϖ * (3 * ϖ ^ k * X ^ 2) + (2 * A₂ * X + A₄)) by ring]
    refine mul_ne_zero (pow_ne_zero _ hp.ne_zero) fun h0 ↦ hXd ?_
    rw [show 2 * A₂ * X + A₄ = ϖ * (3 * ϖ ^ k * X ^ 2) + (2 * A₂ * X + A₄) -
      ϖ * (3 * ϖ ^ k * X ^ 2) by ring, h0]
    exact dvd_sub (dvd_zero _) (dvd_mul_right _ _)
  have hF := (nonsingular_integralModel_iff v).1 hns
  refine ⟨_, 0, X, hF, rfl, dvd_zero _,
    (some_notMem_nonsingularReduction_iff v m₃ m₄ m₆ hF).2 ⟨?_, by simp⟩⟩
  exact (Valuation.mem_maximalIdeal_iff (v := v)).1 ((key _).2 (by
    rw [pow_succ]
    exact (dvd_mul_left ϖ _).mul_right X))

/-! ### The index at `Iₙ*` -/

/-- **At the odd stage `k`, `[E(F) : E₀(F)] = 4` when the residue quadratic has a root.** Here the
valuation ring is Henselian and Tate's algorithm stops at the stage with the symbol `Iₙ*`,
`n = 2k + 1`. A point `P_S` near the simple root of the residue cubic and a deep point `P_d` exist,
and every point lies in `E₀(F)`, `P_S + E₀(F)`, `P_d + E₀(F)` or `-P_d + E₀(F)`. -/
private theorem index_eq_four_of_isTateOddStage [HenselianLocalRing v.valuationSubring]
    {ϖ : v.valuationSubring} (hϖ : maximalIdeal v.valuationSubring = Ideal.span {ϖ}) {k : ℕ}
    (hk : IsTateOddStage ϖ k (integralModel v.valuationSubring W))
    (hb : ¬ ϖ ^ (2 * k + 5) ∣ (integralModel v.valuationSubring W).b₆)
    (hr : (integralModel v.valuationSubring W).HasTateYRoot ϖ (k + 2)) :
    (W.nonsingularReduction v).index = 4 := by
  obtain ⟨hp, -⟩ := prime_and_mem_maximalIdeal_of_isTateOddStage v hϖ hk
  obtain ⟨⟨A₁, hA₁⟩, -, -, ⟨A₃, hA₃⟩, -, ⟨A₆, hA₆⟩⟩ := isTateOddStage_iff.1 hk
  obtain ⟨xs, ys, hS, hxs, hys, hSn⟩ := exists_sq_dvd_of_isTateOddStage v hϖ hk
  obtain ⟨xd, yd, hD, ⟨Xd, hXd⟩, ⟨Yd, rfl⟩, hDn⟩ := exists_pow_dvd_of_hasTateYRoot v hϖ hk hb hr
  obtain ⟨_, hnegS⟩ := exists_neg_some_eq v hS
  obtain ⟨_, hnegD⟩ := exists_neg_some_eq v hD
  -- `-P_d = (x_d, ϖ^(k+2) Y_d')` with `Y_d' ≡ -Y_d - A₃`
  have hnegY : (integralModel v.valuationSubring W).toAffine.negY xd (ϖ ^ (k + 2) * Yd) =
      ϖ ^ (k + 2) * (-Yd - ϖ * A₁ * Xd - A₃) := by
    rw [negY, hXd, hA₁, hA₃]
    ring
  have hroot := dvd_sq_add_mul_sub_of_isTateOddStage hp hk hA₃ hA₆
    ((equation_integralModel_iff v).2 hD.left) ⟨Xd, hXd⟩
  refine AddSubgroup.index_eq_four_of_two_nsmul_mem (s := .some _ _ hS) (d := .some _ _ hD)
    (g := -.some _ _ hD) (fun Q ↦ ?_) hSn ?_ hDn ?_
  · by_cases hQ : Q ∈ W.nonsingularReduction v
    · exact Or.inl hQ
    obtain ⟨x, y, h, rfl, ⟨hx, hy⟩ | ⟨hx, Y, rfl⟩⟩ :=
      exists_eq_some_of_notMem_of_isTateOddStage v hϖ hk hQ
    · -- `Q` is near the simple root, as is `-P_S`
      refine Or.inr (Or.inl ?_)
      rw [neg_add_eq_sub, sub_eq_add_neg, hnegS]
      exact add_mem_of_sq_dvd_of_isTateOddStage v hϖ hk hx hy hxs
    · -- `Y` is congruent to one of the two roots `Y_d` and `-Y_d - A₃` of the residue quadratic
      have hY := dvd_sq_add_mul_sub_of_isTateOddStage hp hk hA₃ hA₆
        ((equation_integralModel_iff v).2 h.left) hx
      rcases hp.dvd_or_dvd (show ϖ ∣ (Y - Yd) * (Y + Yd + A₃) by
        rw [show (Y - Yd) * (Y + Yd + A₃) = (Y ^ 2 + A₃ * Y - A₆) - (Yd ^ 2 + A₃ * Yd - A₆) by
          ring]
        exact dvd_sub hY hroot) with hd | hd
      · refine Or.inr (Or.inr (Or.inl ?_))
        rw [neg_add_eq_sub, sub_eq_add_neg, hnegD]
        refine add_mem_of_isTateOddStage v hϖ hk hb hA₃ hA₆ hx rfl ⟨Xd, hXd⟩ hnegY ?_
        rw [show Y + (-Yd - ϖ * A₁ * Xd - A₃) + A₃ = Y - Yd - ϖ * (A₁ * Xd) by ring]
        exact dvd_sub hd (dvd_mul_right _ _)
      · refine Or.inr (Or.inr (Or.inr ?_))
        rw [neg_neg, add_comm]
        exact add_mem_of_isTateOddStage v hϖ hk hb hA₃ hA₆ hx rfl ⟨Xd, hXd⟩ rfl hd
  · rw [two_nsmul]
    exact add_mem_of_sq_dvd_of_isTateOddStage v hϖ hk hxs hys hxs
  · rw [neg_add_eq_sub, ← neg_sub, neg_mem_iff, sub_eq_add_neg, hnegD]
    exact add_notMem_of_sq_dvd_of_pow_dvd v hϖ hk hxs hys ⟨Xd, hXd⟩
      ((pow_dvd_pow ϖ (by omega)).trans ⟨_, hnegY⟩)

/-- **At the odd stage `k`, `[E(F) : E₀(F)] = 2` when the residue quadratic has no root.** Here the
valuation ring is Henselian. No point is deep, since a deep point gives a root, so every point
outside `E₀(F)` is near the simple root of the residue cubic, and two such points add up into
`E₀(F)`. -/
private theorem index_eq_two_of_isTateOddStage [HenselianLocalRing v.valuationSubring]
    {ϖ : v.valuationSubring} (hϖ : maximalIdeal v.valuationSubring = Ideal.span {ϖ}) {k : ℕ}
    (hk : IsTateOddStage ϖ k (integralModel v.valuationSubring W))
    (hr : ¬ (integralModel v.valuationSubring W).HasTateYRoot ϖ (k + 2)) :
    (W.nonsingularReduction v).index = 2 := by
  obtain ⟨_, _, _, -, -, hSn⟩ := exists_sq_dvd_of_isTateOddStage v hϖ hk
  have hnear {P : W.Point} (hP : P ∉ W.nonsingularReduction v) :
      ∃ (x y : v.valuationSubring) (h : W.Nonsingular x y), P = .some _ _ h ∧
        ϖ ^ 2 ∣ x + (integralModel v.valuationSubring W).a₂ ∧ ϖ ^ 2 ∣ y := by
    obtain ⟨x, y, h, rfl, hxy | ⟨hx, hy⟩⟩ := exists_eq_some_of_notMem_of_isTateOddStage v hϖ hk hP
    · exact ⟨x, y, h, rfl, hxy⟩
    · exact absurd (hasTateYRoot_def.2 ⟨y, hy, pow_dvd_y_of_isTateOddStage hk
        ((equation_integralModel_iff v).2 h.left) hx hy⟩) hr
  refine AddSubgroup.index_eq_two_of_add_mem (fun P Q hP hQ ↦ ?_) hSn
  obtain ⟨x₁, y₁, h₁, rfl, hx₁, hy₁⟩ := hnear hP
  obtain ⟨x₂, y₂, h₂, rfl, hx₂, -⟩ := hnear hQ
  exact add_mem_of_sq_dvd_of_isTateOddStage v hϖ hk hx₁ hy₁ hx₂

/-- At the even stage `k`, let `P_S` be a point near the simple root of the residue cubic and
`P_d = (ϖ^(k+2) X_d, y_d)` a deep point. If every deep point whose class differs from that of `P_d`
lies in `g + E₀(F)`, then `[E(F) : E₀(F)] = 4`: every point lies in
`E₀(F)`, `P_S + E₀(F)`, `P_d + E₀(F)` or `g + E₀(F)`. -/
private theorem index_eq_four_of_isTateEvenStage_of_forall {ϖ : v.valuationSubring}
    (hϖ : maximalIdeal v.valuationSubring = Ideal.span {ϖ}) {k : ℕ}
    (hk : IsTateEvenStage ϖ k (integralModel v.valuationSubring W))
    (hd : ¬ ϖ ^ (2 * k + 7) ∣ discrim (integralModel v.valuationSubring W).a₂
      (integralModel v.valuationSubring W).a₄ (integralModel v.valuationSubring W).a₆)
    {xs ys : v.valuationSubring} {hS : W.Nonsingular xs ys}
    (hxs : ϖ ^ 2 ∣ xs + (integralModel v.valuationSubring W).a₂) (hys : ϖ ^ 2 ∣ ys)
    (hSn : Point.some _ _ hS ∉ W.nonsingularReduction v) {Xd yd : v.valuationSubring}
    {hD : W.Nonsingular ↑(ϖ ^ (k + 2) * Xd) yd} (hyd : ϖ ^ (k + 3) ∣ yd)
    (hDn : Point.some _ _ hD ∉ W.nonsingularReduction v) {g : W.Point}
    (hg : ∀ (y X : v.valuationSubring) (h : W.Nonsingular ↑(ϖ ^ (k + 2) * X) y),
      ϖ ^ (k + 3) ∣ y → ¬ ϖ ∣ X - Xd → -g + Point.some _ _ h ∈ W.nonsingularReduction v) :
    (W.nonsingularReduction v).index = 4 := by
  have hodd := hk.isTateOddStage
  obtain ⟨hp, -⟩ := prime_and_mem_maximalIdeal_of_isTateOddStage v hϖ hodd
  obtain ⟨⟨A₁, hA₁⟩, -, -, ⟨A₃, hA₃⟩, -⟩ := isTateEvenStage_iff.1 hk
  obtain ⟨_, hnegS⟩ := exists_neg_some_eq v hS
  obtain ⟨_, hnegD⟩ := exists_neg_some_eq v hD
  refine AddSubgroup.index_eq_four_of_two_nsmul_mem (s := .some _ _ hS) (d := .some _ _ hD)
    (g := g) (fun Q ↦ ?_) hSn ?_ hDn ?_
  · by_cases hQ : Q ∈ W.nonsingularReduction v
    · exact Or.inl hQ
    obtain ⟨x, y, h, rfl, ⟨hx, hy⟩ | ⟨hx, hy⟩⟩ :=
      exists_eq_some_of_notMem_of_isTateOddStage v hϖ hodd hQ
    · -- `Q` is near the simple root, as is `-P_S`
      refine Or.inr (Or.inl ?_)
      rw [neg_add_eq_sub, sub_eq_add_neg, hnegS]
      exact add_mem_of_sq_dvd_of_isTateOddStage v hϖ hodd hx hy hxs
    · -- `Q` is deep, in the class of `P_d` or not
      have hy' := pow_dvd_of_isTateEvenStage hp hk ((equation_integralModel_iff v).2 h.left) hx hy
      obtain ⟨X, rfl⟩ := hx
      by_cases hX : ϖ ∣ X - Xd
      · refine Or.inr (Or.inr (Or.inl ?_))
        rw [neg_add_eq_sub, sub_eq_add_neg, hnegD]
        exact add_mem_of_isTateEvenStage v hϖ hk hd rfl hy' rfl hX
      · exact Or.inr (Or.inr (Or.inr (hg y X h hy' hX)))
  · rw [two_nsmul]
    exact add_mem_of_sq_dvd_of_isTateOddStage v hϖ hodd hxs hys hxs
  · rw [neg_add_eq_sub, ← neg_sub, neg_mem_iff, sub_eq_add_neg, hnegD]
    refine add_notMem_of_sq_dvd_of_pow_dvd v hϖ hodd hxs hys (dvd_mul_right _ _) ?_
    -- `-P_d = (x_d, -y_d - a₁ x_d - a₃)` with `ϖ^(k+3)` dividing the second coordinate
    rw [negY, hA₁, hA₃]
    refine (pow_dvd_pow ϖ (by omega : 2 ≤ k + 3)).trans (dvd_sub (dvd_sub (dvd_neg.2 hyd) ?_)
      (dvd_mul_right _ _))
    exact ⟨A₁ * Xd, by ring⟩

/-- **At the even stage `k`, `[E(F) : E₀(F)] = 4` when the residue quadratic has a root.** Here
the valuation ring is Henselian and Tate's algorithm stops at the stage with the symbol `Iₙ*`,
`n = 2k + 2`. A point `P_S` near the simple root of the residue cubic and a deep point `P_d` exist.
Since the residue quadratic has at most two roots, the deep points outside the class of `P_d` all
lie in one coset. -/
private theorem index_eq_four_of_isTateEvenStage [HenselianLocalRing v.valuationSubring]
    {ϖ : v.valuationSubring} (hϖ : maximalIdeal v.valuationSubring = Ideal.span {ϖ}) {k : ℕ}
    (hk : IsTateEvenStage ϖ k (integralModel v.valuationSubring W))
    (hd : ¬ ϖ ^ (2 * k + 7) ∣ discrim (integralModel v.valuationSubring W).a₂
      (integralModel v.valuationSubring W).a₄ (integralModel v.valuationSubring W).a₆)
    (hr : (integralModel v.valuationSubring W).HasTateXRoot ϖ (k + 2)) :
    (W.nonsingularReduction v).index = 4 := by
  obtain ⟨hp, -⟩ := prime_and_mem_maximalIdeal_of_isTateOddStage v hϖ hk.isTateOddStage
  obtain ⟨-, ⟨A₂, hA₂⟩, hA₂', -, ⟨A₄, hA₄⟩, ⟨A₆, hA₆⟩⟩ := isTateEvenStage_iff.1 hk
  obtain ⟨xs, ys, hS, hxs, hys, hSn⟩ := exists_sq_dvd_of_isTateOddStage v hϖ hk.isTateOddStage
  obtain ⟨_, yd, Xd, hD, rfl, hyd, hDn⟩ := exists_eq_pow_mul_of_hasTateXRoot v hϖ hk hd hr
  have hroot (X y : v.valuationSubring) (h : W.Nonsingular ↑(ϖ ^ (k + 2) * X) y)
      (hy : ϖ ^ (k + 3) ∣ y) : ϖ ∣ A₂ * (X * X) + A₄ * X + A₆ :=
    dvd_mul_add_mul_add_of_isTateEvenStage hp hk hA₂ hA₄ hA₆
      ((equation_integralModel_iff v).2 h.left) hy
  by_cases hex : ∃ (y₀ X₀ : v.valuationSubring) (h₀ : W.Nonsingular ↑(ϖ ^ (k + 2) * X₀) y₀),
      ϖ ^ (k + 3) ∣ y₀ ∧ ¬ ϖ ∣ X₀ - Xd
  · obtain ⟨y₀, X₀, h₀, hy₀, hX₀⟩ := hex
    obtain ⟨_, hneg₀⟩ := exists_neg_some_eq v h₀
    refine index_eq_four_of_isTateEvenStage_of_forall v hϖ hk hd hxs hys hSn hyd hDn
      (g := .some _ _ h₀) fun y X h hy hX ↦ ?_
    rw [neg_add_eq_sub, sub_eq_add_neg, hneg₀]
    refine add_mem_of_isTateEvenStage v hϖ hk hd rfl hy rfl ?_
    -- the roots `X` and `X₀` of the residue quadratic both differ from the root `X_d`
    have hother {Z : v.valuationSubring} (hZ : ϖ ∣ A₂ * (Z * Z) + A₄ * Z + A₆)
        (hZd : ¬ ϖ ∣ Z - Xd) : ϖ ∣ A₂ * (Z + Xd) + A₄ := by
      refine (hp.dvd_or_dvd ?_).resolve_left hZd
      rw [show (Z - Xd) * (A₂ * (Z + Xd) + A₄) =
        (A₂ * (Z * Z) + A₄ * Z + A₆) - (A₂ * (Xd * Xd) + A₄ * Xd + A₆) by ring]
      exact dvd_sub hZ (hroot Xd yd hD hyd)
    refine (hp.dvd_or_dvd ?_).resolve_left fun hA ↦ hA₂' (by
      rw [hA₂, pow_two]
      exact mul_dvd_mul_left ϖ hA)
    rw [show A₂ * (X - X₀) = (A₂ * (X + Xd) + A₄) - (A₂ * (X₀ + Xd) + A₄) by ring]
    exact dvd_sub (hother (hroot X y h hy) hX) (hother (hroot X₀ y₀ h₀ hy₀) hX₀)
  · exact index_eq_four_of_isTateEvenStage_of_forall v hϖ hk hd hxs hys hSn hyd hDn (g := 0)
      fun y X h hy hX ↦ absurd ⟨y, X, h, hy, hX⟩ hex

/-- **At the even stage `k`, `[E(F) : E₀(F)] = 2` when the residue quadratic has no root.** Here
the valuation ring is Henselian. No point is deep, since a deep point gives a root, so every point
outside `E₀(F)` is near the simple root of the residue cubic, and two such points add up into
`E₀(F)`. -/
private theorem index_eq_two_of_isTateEvenStage [HenselianLocalRing v.valuationSubring]
    {ϖ : v.valuationSubring} (hϖ : maximalIdeal v.valuationSubring = Ideal.span {ϖ}) {k : ℕ}
    (hk : IsTateEvenStage ϖ k (integralModel v.valuationSubring W))
    (hr : ¬ (integralModel v.valuationSubring W).HasTateXRoot ϖ (k + 2)) :
    (W.nonsingularReduction v).index = 2 := by
  have hodd := hk.isTateOddStage
  obtain ⟨hp, -⟩ := prime_and_mem_maximalIdeal_of_isTateOddStage v hϖ hodd
  obtain ⟨_, _, _, -, -, hSn⟩ := exists_sq_dvd_of_isTateOddStage v hϖ hodd
  have hnear {P : W.Point} (hP : P ∉ W.nonsingularReduction v) :
      ∃ (x y : v.valuationSubring) (h : W.Nonsingular x y), P = .some _ _ h ∧
        ϖ ^ 2 ∣ x + (integralModel v.valuationSubring W).a₂ ∧ ϖ ^ 2 ∣ y := by
    obtain ⟨x, y, h, rfl, hxy | ⟨hx, hy⟩⟩ :=
      exists_eq_some_of_notMem_of_isTateOddStage v hϖ hodd hP
    · exact ⟨x, y, h, rfl, hxy⟩
    · have hE := (equation_integralModel_iff v).2 h.left
      exact absurd (hasTateXRoot_def.2 ⟨x, hx, pow_dvd_x_of_isTateEvenStage hk hE hx
        (pow_dvd_of_isTateEvenStage hp hk hE hx hy)⟩) hr
  refine AddSubgroup.index_eq_two_of_add_mem (fun P Q hP hQ ↦ ?_) hSn
  obtain ⟨x₁, y₁, h₁, rfl, hx₁, hy₁⟩ := hnear hP
  obtain ⟨x₂, y₂, h₂, rfl, hx₂, -⟩ := hnear hQ
  exact add_mem_of_sq_dvd_of_isTateOddStage v hϖ hodd hx₁ hy₁ hx₂

/-- **At the reduction symbol `Iₙ*` with `n ≥ 1`, Tate's local index is the point-group index.**
Suppose that `ϖ` generates the maximal ideal of the Henselian valuation ring, and that Tate's
algorithm, run on the integral model with uniformiser `ϖ`, stops with the symbol `Iₙ*` for some
`n ≥ 1`. Then `[W(F) : E₀(F)]` is the local index that the algorithm reports: `4` if the quadratic
at which the subprocedure of Step 7 stops has a root in the residue field, and `2` otherwise. -/
theorem index_nonsingularReduction_eq_tateLocalIndex_of_isTateTerminal_IStar_add_one
    [HenselianLocalRing v.valuationSubring] {ϖ : v.valuationSubring}
    (hϖ : maximalIdeal v.valuationSubring = Ideal.span {ϖ}) {n : ℕ}
    (h : (integralModel v.valuationSubring W).IsTateTerminal ϖ (.IStar (n + 1))) :
    (W.nonsingularReduction v).index =
      (integralModel v.valuationSubring W).tateLocalIndex ϖ (.IStar (n + 1)) := by
  classical
  rcases isTateTerminal_IStar_add_one.1 h with ⟨k, rfl, hk, hb⟩ | ⟨k, rfl, hk, hd⟩
  · rw [tateLocalIndex_IStar_odd]
    split_ifs with hr
    · exact index_eq_four_of_isTateOddStage v hϖ hk hb hr
    · exact index_eq_two_of_isTateOddStage v hϖ hk hr
  · rw [show 2 * k + 1 + 1 = 2 * k + 2 by ring, tateLocalIndex_IStar_even]
    split_ifs with hr
    · exact index_eq_four_of_isTateEvenStage v hϖ hk hd hr
    · exact index_eq_two_of_isTateEvenStage v hϖ hk hr

end Affine

end WeierstrassCurve

end

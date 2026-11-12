/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
public import Mathlib.Basic.Real.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Basic
-- Proof-only: the square root of `Ψ₂Sq(x)` gives the ordinate of a point.
import Mathlib.Analysis.Real.Sqrt
-- Proof-only: the cubic `Ψ₂Sq` tends to `±∞` at `±∞`.
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Topology.Algebra.Polynomial
-- Proof-only: `ψ₂(x, y)² = Ψ₂Sq(x)` characterises the points of the curve, and the points of order
-- two are the zeros of `ψ₂`.
import TauCeti.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Discriminant
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.TwoTorsion
-- Proof-only: the derivative of a cubic with three roots at one of them.
import TauCeti.Algebra.Polynomial.Derivative

/-!
# Real points of a Weierstrass curve

Over `ℝ`, completing the square writes the Weierstrass equation as
`(2y + a₁x + a₃)² = Ψ₂Sq(x)`, where `Ψ₂Sq(x) = 4x³ + b₂x² + 2b₄x + b₆` is Mathlib's
`WeierstrassCurve.Ψ₂Sq`. So the curve has a real point with abscissa `x` exactly when
`Ψ₂Sq(x) ≥ 0`. The two points `(x, y)` and `-(x, y)` over such an `x` coincide exactly when
`Ψ₂Sq(x) = 0`, that is, at the points of order two. These are the facts that let the real period
integral `∫_{Ψ₂Sq(x) > 0} dx / √Ψ₂Sq(x)` be read as an integral over the real points that are not
`2`-torsion.

The shape of the real locus is read off the real roots of the cubic `Ψ₂Sq`, whose leading
coefficient is `4`. It has a largest real root `e`, beyond which it is positive, and the
abscissas of the real points are bounded below. On an elliptic curve the roots are simple. So
either `Ψ₂Sq < 0` below `e`, and every real point other than `O` has abscissa at least `e`, or
`Ψ₂Sq` has three real roots `e₁ < e₂ < e`, and the abscissas of the real points fill
`[e₁, e₂] ∪ [e, ∞)`.

## Main results

* `WeierstrassCurve.Affine.exists_equation_iff_nonneg_eval_Ψ₂Sq`: there is a real point with
  abscissa `x` exactly when `Ψ₂Sq(x) ≥ 0`; `exists_nonsingular_of_nonneg_eval_Ψ₂Sq` is the
  same for a nonsingular point on an elliptic curve.
* `WeierstrassCurve.Affine.tendsto_eval_Ψ₂Sq_atTop` and `tendsto_eval_Ψ₂Sq_atBot`: `Ψ₂Sq` tends to
  `±∞` at `±∞`.
* `WeierstrassCurve.Affine.bddBelow_setOf_nonneg_eval_Ψ₂Sq`: the abscissas of the real points are
  bounded below.
* `WeierstrassCurve.Affine.exists_isRoot_Ψ₂Sq_and_forall_lt_pos_eval`: `Ψ₂Sq` has a real root `e`
  beyond which it is positive.
* `WeierstrassCurve.Affine.exists_Ψ₂Sq_eq_prod_three_roots`: on an elliptic curve with a real point
  of abscissa below that root `e`, `Ψ₂Sq = 4 (X - e₁)(X - e₂)(X - e)` with `e₁ < e₂ < e`.
* `WeierstrassCurve.pos_eval_Ψ₂Sq_iff_of_eq_prod_three_roots`: with three real roots
  `e₁ < e₂ < e₃`, `Ψ₂Sq` is positive exactly on `(e₁, e₂) ∪ (e₃, ∞)`.
* `WeierstrassCurve.Affine.Point.neg_ne_self_iff_ne_zero_and_pos_eval_Ψ₂Sq`: a point is not
  `2`-torsion exactly when it is affine and `Ψ₂Sq` is positive at its abscissa, over any ordered
  field; `Point.neg_some_ne_some_iff_pos_eval_Ψ₂Sq` is the affine case.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.1.
-/

public section

open Polynomial

namespace WeierstrassCurve.Affine

variable {W : WeierstrassCurve.Affine ℝ}

/-- **A real Weierstrass curve has a point with abscissa `x` exactly when `Ψ₂Sq(x) ≥ 0`.** One
such point has `2y + a₁x + a₃ = √Ψ₂Sq(x)`. -/
theorem exists_equation_iff_nonneg_eval_Ψ₂Sq {x : ℝ} :
    (∃ y, W.Equation x y) ↔ 0 ≤ W.Ψ₂Sq.eval x := by
  refine ⟨fun ⟨y, h⟩ ↦ W.evalEval_ψ₂_sq h ▸ sq_nonneg _, fun hx ↦
    ⟨(√(W.Ψ₂Sq.eval x) - W.a₁ * x - W.a₃) / 2, (W.evalEval_ψ₂_sq_eq_iff two_ne_zero).mp ?_⟩⟩
  rw [WeierstrassCurve.ψ₂, evalEval_polynomialY]
  convert Real.sq_sqrt hx using 2
  ring

/-- Over each `x` with `Ψ₂Sq(x) ≥ 0`, an elliptic curve over `ℝ` has a real point. -/
theorem exists_nonsingular_of_nonneg_eval_Ψ₂Sq [W.IsElliptic] {x : ℝ}
    (hx : 0 ≤ W.Ψ₂Sq.eval x) : ∃ y, W.Nonsingular x y :=
  (exists_equation_iff_nonneg_eval_Ψ₂Sq.mpr hx).imp fun _ ↦ equation_iff_nonsingular.mp

/-- **A point is not `2`-torsion exactly when it is affine and `Ψ₂Sq` is positive at its
abscissa**, over an ordered field such as `ℝ`. At an affine point `(x, y)`,
`Ψ₂Sq(x) = (2y + a₁x + a₃)²`, which vanishes exactly at the points of order two. -/
theorem Point.neg_ne_self_iff_ne_zero_and_pos_eval_Ψ₂Sq {F : Type*} [Field F] [LinearOrder F]
    [IsStrictOrderedRing F] {W : WeierstrassCurve.Affine F} {P : W.Point} :
    -P ≠ P ↔ P ≠ 0 ∧ 0 < W.Ψ₂Sq.eval P.xCoord := by
  classical
  rcases P with _ | ⟨x, y, h⟩
  · simp [← Point.zero_def]
  rw [ne_eq, neg_eq_iff_add_eq_zero, Point.some_add_self_eq_zero_iff h, Point.xCoord_some,
    ← W.evalEval_ψ₂_sq h.1, WeierstrassCurve.ψ₂, sq_pos_iff]
  exact ⟨fun h0 ↦ ⟨Point.some_ne_zero h, h0⟩, And.right⟩

/-- An affine point `(x, y)` is not `2`-torsion exactly when `Ψ₂Sq(x) > 0`, over an ordered field
such as `ℝ`. -/
theorem Point.neg_some_ne_some_iff_pos_eval_Ψ₂Sq {F : Type*} [Field F] [LinearOrder F]
    [IsStrictOrderedRing F] {W : WeierstrassCurve.Affine F} {x y : F} (h : W.Nonsingular x y) :
    -Point.some x y h ≠ .some x y h ↔ 0 < W.Ψ₂Sq.eval x := by
  rw [Point.neg_ne_self_iff_ne_zero_and_pos_eval_Ψ₂Sq, Point.xCoord_some]
  exact and_iff_right (Point.some_ne_zero h)

/-! ### The real roots of `Ψ₂Sq` -/

/-- `Ψ₂Sq(x) → ∞` as `x → ∞`: it is a cubic with leading coefficient `4`. -/
theorem tendsto_eval_Ψ₂Sq_atTop :
    Filter.Tendsto (fun x ↦ W.Ψ₂Sq.eval x) Filter.atTop Filter.atTop := by
  have h4 : (4 : ℝ) ≠ 0 := by norm_num
  refine W.Ψ₂Sq.tendsto_atTop_of_leadingCoeff_nonneg ?_ (by rw [W.leadingCoeff_Ψ₂Sq h4]; norm_num)
  rw [degree_eq_natDegree (fun h ↦ by simpa [h] using W.leadingCoeff_Ψ₂Sq h4),
    W.natDegree_Ψ₂Sq h4]
  norm_num

/-- `Ψ₂Sq(x) → -∞` as `x → -∞`: it is a cubic with leading coefficient `4`. -/
theorem tendsto_eval_Ψ₂Sq_atBot :
    Filter.Tendsto (fun x ↦ W.Ψ₂Sq.eval x) Filter.atBot Filter.atBot := by
  have h4 : (4 : ℝ) ≠ 0 := by norm_num
  -- `Ψ₂Sq(-x)` is a cubic with leading coefficient `-4`
  have hlc : (W.Ψ₂Sq.comp (-X)).leadingCoeff = -4 := by
    rw [leadingCoeff_comp (by simp), W.leadingCoeff_Ψ₂Sq h4, W.natDegree_Ψ₂Sq h4]
    norm_num
  have hdeg : (W.Ψ₂Sq.comp (-X)).natDegree = 3 := by
    rw [natDegree_comp, W.natDegree_Ψ₂Sq h4]
    simp
  have := (W.Ψ₂Sq.comp (-X)).tendsto_atBot_of_leadingCoeff_nonpos
    (by rw [degree_eq_natDegree (fun h ↦ by simp [h] at hlc), hdeg]; norm_num)
    (by rw [hlc]; norm_num)
  simpa [Function.comp_def] using this.comp Filter.tendsto_neg_atBot_atTop

/-- **The abscissas of the real points are bounded below**: `Ψ₂Sq` is a cubic with positive
leading coefficient, so it is negative far to the left. -/
theorem bddBelow_setOf_nonneg_eval_Ψ₂Sq : BddBelow {x | 0 ≤ W.Ψ₂Sq.eval x} := by
  obtain ⟨m, hm⟩ :=
    Filter.eventually_atBot.mp (tendsto_eval_Ψ₂Sq_atBot.eventually_lt_atBot 0)
  exact ⟨m, fun x hx ↦ le_of_not_gt fun h ↦ (hm x h.le).not_ge hx⟩

variable (W) in
/-- **`Ψ₂Sq` has a real root beyond which it is positive**: its largest real root. It exists since
`Ψ₂Sq` is a cubic with positive leading coefficient. -/
theorem exists_isRoot_Ψ₂Sq_and_forall_lt_pos_eval :
    ∃ e, W.Ψ₂Sq.IsRoot e ∧ ∀ ⦃x⦄, e < x → 0 < W.Ψ₂Sq.eval x := by
  -- `e` is the largest `x` with `Ψ₂Sq(x) ≤ 0`
  set S := {x | W.Ψ₂Sq.eval x ≤ 0}
  obtain ⟨m, hm⟩ :=
    Filter.eventually_atBot.mp (tendsto_eval_Ψ₂Sq_atBot (W := W).eventually_le_atBot 0)
  obtain ⟨M, hM⟩ :=
    Filter.eventually_atTop.mp (tendsto_eval_Ψ₂Sq_atTop (W := W).eventually_gt_atTop 0)
  have hS : S.Nonempty := ⟨m, hm m le_rfl⟩
  have hSb : BddAbove S := ⟨M, fun x hx ↦ le_of_not_gt fun h ↦ (hM x h.le).not_ge hx⟩
  have hSc : IsClosed S := isClosed_le W.Ψ₂Sq.continuous continuous_const
  have hpos : ∀ ⦃x⦄, sSup S < x → 0 < W.Ψ₂Sq.eval x := fun x hx ↦
    lt_of_not_ge fun h ↦ (le_csSup hSb h).not_gt hx
  refine ⟨sSup S, le_antisymm (hSc.csSup_mem hS hSb) ?_, hpos⟩
  exact ge_of_tendsto (W.Ψ₂Sq.continuous.continuousAt.tendsto.mono_left
    (nhdsWithin_le_nhds (s := Set.Ioi (sSup S))))
    (eventually_nhdsWithin_of_forall fun x hx ↦ (hpos (Set.mem_Ioi.mp hx)).le)

/-- **Three real roots.** Let `e` be a root of `Ψ₂Sq` beyond which it is positive, on an elliptic
curve over `ℝ`. If `Ψ₂Sq(x₀) ≥ 0` for some `x₀ < e`, that is, if some real point has abscissa below
`e`, then `Ψ₂Sq = 4 (X - e₁)(X - e₂)(X - e)` with `e₁ < e₂ < e`. -/
theorem exists_Ψ₂Sq_eq_prod_three_roots [W.IsElliptic] {e : ℝ} (he : W.Ψ₂Sq.IsRoot e)
    (hpos : ∀ ⦃x⦄, e < x → 0 < W.Ψ₂Sq.eval x) {x₀ : ℝ} (hx₀ : x₀ < e)
    (h₀ : 0 ≤ W.Ψ₂Sq.eval x₀) :
    ∃ e₁ e₂, e₁ < e₂ ∧ e₂ < e ∧ W.Ψ₂Sq = C 4 * (X - C e₁) * (X - C e₂) * (X - C e) := by
  -- dividing by `X - e` leaves the quadratic `4X² + βX + γ`, which is nonpositive at `x₀`
  set β := W.b₂ + 4 * e
  set γ := W.b₂ * e + 4 * e ^ 2 + 2 * W.b₄
  have hΨ (x : ℝ) : W.Ψ₂Sq.eval x = (x - e) * (4 * x ^ 2 + β * x + γ) := by
    have := he.eq_zero
    simp only [WeierstrassCurve.Ψ₂Sq, eval_add, eval_mul, eval_pow, eval_C, eval_X] at this ⊢
    linear_combination this
  have hq : 4 * x₀ ^ 2 + β * x₀ + γ ≤ 0 := by nlinarith [hΨ x₀]
  -- so its discriminant is nonnegative, and it splits
  have hd : 0 ≤ β ^ 2 - 16 * γ := by nlinarith [sq_nonneg (8 * x₀ + β)]
  set s := √(β ^ 2 - 16 * γ)
  have hs : s ^ 2 = β ^ 2 - 16 * γ := Real.sq_sqrt hd
  set e₁ := (-β - s) / 8
  set e₂ := (-β + s) / 8
  have hquad (x : ℝ) : 4 * x ^ 2 + β * x + γ = 4 * (x - e₁) * (x - e₂) := by
    simp only [e₁, e₂]
    linear_combination hs / 16
  have hfac (x : ℝ) : W.Ψ₂Sq.eval x = 4 * (x - e₁) * (x - e₂) * (x - e) := by
    rw [hΨ, hquad]
    ring
  have hpoly : W.Ψ₂Sq = C 4 * (X - C e₁) * (X - C e₂) * (X - C e) :=
    Polynomial.funext fun x ↦ by simp [hfac]
  have h₁₂ : e₁ ≤ e₂ := by simp only [e₁, e₂]; linarith [Real.sqrt_nonneg (β ^ 2 - 16 * γ)]
  have h₁ : e₁ ≤ x₀ := le_of_not_gt fun h ↦ by
    nlinarith [hquad x₀, mul_pos (sub_pos.2 h) (sub_pos.2 (h.trans_le h₁₂))]
  -- the roots are simple, and `Ψ₂Sq > 0` beyond `e` puts them below `e`
  have hd₁ := W.eval_derivative_Ψ₂Sq_ne_zero two_ne_zero (x := e₁) (by simp [IsRoot, hfac])
  have hd := W.eval_derivative_Ψ₂Sq_ne_zero two_ne_zero he
  rw [hpoly, eval_derivative_C_mul_X_sub_C_mul_X_sub_C_mul_X_sub_C] at hd₁
  rw [hpoly, show C 4 * (X - C e₁) * (X - C e₂) * (X - C e) =
    C 4 * (X - C e) * (X - C e₁) * (X - C e₂) by ring,
    eval_derivative_C_mul_X_sub_C_mul_X_sub_C_mul_X_sub_C] at hd
  refine ⟨e₁, e₂, lt_of_le_of_ne h₁₂ fun h ↦ hd₁ (by rw [h]; ring), ?_, hpoly⟩
  refine lt_of_le_of_ne (le_of_not_gt fun h ↦ ?_) fun h ↦ hd (by rw [h]; ring)
  have := hpos (x := (e + e₂) / 2) (by linarith)
  rw [hfac] at this
  nlinarith [mul_pos (mul_pos (by linarith : (0 : ℝ) < (e + e₂) / 2 - e₁)
    (by linarith : (0 : ℝ) < e₂ - (e + e₂) / 2)) (by linarith : (0 : ℝ) < (e + e₂) / 2 - e)]

end WeierstrassCurve.Affine

namespace WeierstrassCurve

open Set

variable (W : WeierstrassCurve ℝ)

/-- **Where `Ψ₂Sq` is positive, with three real roots**: if `Ψ₂Sq = 4 (X - e₁)(X - e₂)(X - e₃)`
with `e₁ < e₂ < e₃`, then `Ψ₂Sq(x) > 0` exactly on `(e₁, e₂) ∪ (e₃, ∞)`. -/
theorem pos_eval_Ψ₂Sq_iff_of_eq_prod_three_roots {e₁ e₂ e₃ : ℝ} (h₁₂ : e₁ < e₂) (h₂₃ : e₂ < e₃)
    (h : W.Ψ₂Sq = C 4 * (X - C e₁) * (X - C e₂) * (X - C e₃)) (x : ℝ) :
    0 < W.Ψ₂Sq.eval x ↔ x ∈ Ioo e₁ e₂ ∪ Ioi e₃ := by
  simp only [h, eval_mul, eval_sub, eval_C, eval_X, mem_union, mem_Ioo, mem_Ioi]
  constructor
  · intro hx
    by_contra hn
    simp only [not_or, not_and, not_lt] at hn
    rcases le_or_gt x e₁ with h₁ | h₁
    · nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.2 h₁) (by linarith : (0:ℝ) ≤ e₂ - x))
        (by linarith : (0:ℝ) ≤ e₃ - x)]
    · nlinarith [mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ x - e₁) (by linarith [hn.1 h₁] :
        (0:ℝ) ≤ x - e₂)) (by linarith : (0:ℝ) ≤ e₃ - x)]
  · rintro (⟨h₁, h₂⟩ | h₃)
    · nlinarith [mul_pos (mul_pos (sub_pos.2 h₁) (sub_pos.2 h₂)) (by linarith : (0:ℝ) < e₃ - x)]
    · nlinarith [mul_pos (mul_pos (by linarith : (0:ℝ) < x - e₁) (by linarith : (0:ℝ) < x - e₂))
        (sub_pos.2 h₃)]

end WeierstrassCurve

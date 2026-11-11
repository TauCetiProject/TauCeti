/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.TateCurve.Basic
public import TauCeti.NumberTheory.ArithmeticFunction.Sigma.Evaluation
import TauCeti.Analysis.Normed.Group.Ultra

/-!
# Specialization of the Tate equation

The coefficients of the Tate equation are formal power series with integer coefficients. In a
complete non-archimedean normed ring, their sums converge at every parameter of norm less than one.
This remains true in residue characteristics `2` and `3`: the sixth coefficient is summed from
its integral coefficients, with no division in the target ring.

For a unit parameter in the open unit ball of a complete non-archimedean normed commutative ring,
these sums give a nonsingular Tate equation, whose affine points are the solutions of
`y² + xy = x³ + a₄(q) x + a₆(q)`. The discriminant and the coefficient `a₆` have the
same norm as the parameter, even when the ring norm is only submultiplicative, and the coefficient
`a₄` has norm at most that of the parameter. The invariant `c₄` has norm one under `NormOneClass`
(`‖1‖ = 1`). Over a field, `|j| = 1 / |q| > 1`. Point uniformisation requires further arguments.

Over an ultrametric field, a solution of an equation `y² + xy = x³ + A₄x + A₆` with
`‖A₄‖, ‖A₆‖ ≤ 1` whose first coordinate has norm above one satisfies `‖x‖ < ‖x + y‖`
(`TauCeti.norm_lt_norm_add_of_equation`), and a line through the origin meets such a curve in at
most one point whose first coordinate has norm above one
(`TauCeti.eq_of_mul_eq_mul_of_one_lt_norm`).

## References

* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, V.3.
* J. Tate, *A review of non-Archimedean elliptic functions* (1995).
-/

public section

namespace TauCeti

section

variable {K : Type*} [NormedCommRing K] [CompleteSpace K]
  [IsUltrametricDist K]

/-- The analytic fourth Tate coefficient, obtained from the integral formal series. -/
noncomputable def tateCurveA₄ (q : K) (hq : ‖q‖ < 1) : K :=
  evalIntSeries q hq tateCurve.a₄

/-- The analytic sixth Tate coefficient, obtained from integral coefficients before reducing to
the residue characteristic of the ring. -/
noncomputable def tateCurveA₆ (q : K) (hq : ‖q‖ < 1) : K :=
  evalIntSeries q hq tateCurve.a₆

/-- The sixth Tate coefficient is the sum of its evaluated integral coefficients. -/
theorem tateCurveA₆_def (q : K) (hq : ‖q‖ < 1) :
    tateCurveA₆ q hq =
      ∑' n : ℕ, ((PowerSeries.coeff n tateCurve.a₆ : ℤ) : K) * q ^ n := by
  simp only [tateCurveA₆, evalIntSeries_apply]

/-- The fourth coefficient equals `-5 s₃(q)`. -/
@[simp] theorem tateCurveA₄_eq (q : K) (hq : ‖q‖ < 1) :
    tateCurveA₄ q hq = -5 * divisorSumAt 3 q := by
  simp only [tateCurveA₄, tateCurve_a₄, map_mul, map_neg, map_ofNat,
    evalIntSeries_divisorSumSeries]

/-- The integral identity `12 a₆(q) = -(5 s₃(q) + 7 s₅(q))` holds in every complete
non-archimedean normed commutative ring, even when `12 = 0` there. -/
@[simp] theorem twelve_mul_tateCurveA₆ {q : K} (hq : ‖q‖ < 1) :
    12 * tateCurveA₆ q hq = -(5 * divisorSumAt 3 q + 7 * divisorSumAt 5 q) := by
  simpa only [map_mul, map_ofNat, map_neg, map_add, evalIntSeries_divisorSumSeries, tateCurveA₆]
    using congrArg (evalIntSeries q hq) twelve_mul_tateCurve_a₆

/-- The Tate equation obtained by evaluating the integral formal curve at a unit parameter of
norm less than one. The unit parameter will also support its integer powers in uniformisation. -/
noncomputable def tateCurveAt (q : Kˣ) (hq : ‖(q : K)‖ < 1) : WeierstrassCurve K :=
  tateCurve.map (evalIntSeries (q : K) hq)

/-- The specialized Tate curve is obtained by applying integral-series evaluation to its
formal coefficients. -/
theorem tateCurveAt_def (q : Kˣ) (hq : ‖(q : K)‖ < 1) :
    tateCurveAt q hq = tateCurve.map (evalIntSeries (q : K) hq) := (rfl)

@[simp] theorem tateCurveAt_a₁ (q : Kˣ) (hq : ‖(q : K)‖ < 1) :
    (tateCurveAt q hq).a₁ = 1 := by
  simp [tateCurveAt, WeierstrassCurve.map, tateCurve_a₁]

@[simp] theorem tateCurveAt_a₂ (q : Kˣ) (hq : ‖(q : K)‖ < 1) :
    (tateCurveAt q hq).a₂ = 0 := by
  simp [tateCurveAt, WeierstrassCurve.map, tateCurve_a₂]

@[simp] theorem tateCurveAt_a₃ (q : Kˣ) (hq : ‖(q : K)‖ < 1) :
    (tateCurveAt q hq).a₃ = 0 := by
  simp [tateCurveAt, WeierstrassCurve.map, tateCurve_a₃]

/-- The analytic fourth coefficient is the evaluation of the formal fourth coefficient. -/
@[simp] theorem tateCurveAt_a₄ (q : Kˣ) (hq : ‖(q : K)‖ < 1) :
    (tateCurveAt q hq).a₄ = tateCurveA₄ (q : K) hq := by
  simp only [tateCurveAt, WeierstrassCurve.map, tateCurveA₄]

/-- The analytic sixth coefficient is the evaluation of the formal sixth coefficient. -/
@[simp] theorem tateCurveAt_a₆ (q : Kˣ) (hq : ‖(q : K)‖ < 1) :
    (tateCurveAt q hq).a₆ = tateCurveA₆ (q : K) hq := by
  simp only [tateCurveAt, WeierstrassCurve.map, tateCurveA₆]

/-- A point lies on `tateCurveAt q hq` exactly when it solves the Tate equation
`y² + xy = x³ + a₄(q) x + a₆(q)`. -/
theorem tateCurveAt_equation_iff (q : Kˣ) (hq : ‖(q : K)‖ < 1) {x y : K} :
    (tateCurveAt q hq).toAffine.Equation x y ↔
      y ^ 2 + x * y = x ^ 3 + tateCurveA₄ (q : K) hq * x + tateCurveA₆ (q : K) hq := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [tateCurveAt_a₁, tateCurveAt_a₂, tateCurveAt_a₃, tateCurveAt_a₄, tateCurveAt_a₆]
  constructor <;> intro h <;> linear_combination h

/-- The discriminant of the specialized Tate equation is the evaluation of the formal
discriminant of the Tate curve. -/
theorem tateCurveAt_Δ (q : Kˣ) (hq : ‖(q : K)‖ < 1) :
    (tateCurveAt q hq).Δ = evalIntSeries (q : K) hq tateCurve.Δ := by
  rw [tateCurveAt, WeierstrassCurve.map_Δ]

/-- The discriminant of the specialized Tate equation is a unit. -/
theorem isUnit_tateCurveAt_Δ (q : Kˣ) (hq : ‖(q : K)‖ < 1) :
    IsUnit (tateCurveAt q hq).Δ := by
  obtain ⟨u, -, hu, hΔ⟩ := exists_tateCurve_Δ_eq_X_mul
  rw [tateCurveAt, WeierstrassCurve.map_Δ, hΔ, map_mul, evalIntSeries_X]
  exact q.isUnit.mul (hu.map _)

/-- A unit parameter of norm below one gives an elliptic curve over the complete normed ring,
with no discreteness or characteristic assumption. -/
instance isElliptic_tateCurveAt (q : Kˣ) (hq : ‖(q : K)‖ < 1) :
    (tateCurveAt q hq).IsElliptic :=
  ⟨isUnit_tateCurveAt_Δ q hq⟩

/-- The specialized Tate discriminant has the same norm as the parameter, even for a
submultiplicative ring norm. -/
@[simp] theorem norm_tateCurveAt_Δ (q : Kˣ) (hq : ‖(q : K)‖ < 1) :
    ‖(tateCurveAt q hq).Δ‖ = ‖(q : K)‖ := by
  obtain ⟨u, -, hu, hΔ⟩ := exists_tateCurve_Δ_eq_X_mul
  rw [tateCurveAt, WeierstrassCurve.map_Δ, hΔ, map_mul, evalIntSeries_X]
  exact norm_mul_evalIntSeries_of_isUnit (q : K) (q : K) hq hu

/-- The fourth Tate coefficient has norm at most that of the parameter, since the formal series
`a₄` has no constant term. -/
theorem norm_tateCurveA₄_le (q : K) (hq : ‖q‖ < 1) : ‖tateCurveA₄ q hq‖ ≤ ‖q‖ :=
  norm_evalIntSeries_le_of_constantCoeff_eq_zero q hq constantCoeff_tateCurve_a₄

/-- **The sixth Tate coefficient has the same norm as the parameter**, since the formal series
`a₆` is `q` times a unit, even for a submultiplicative ring norm. -/
@[simp] theorem norm_tateCurveA₆ (q : K) (hq : ‖q‖ < 1) : ‖tateCurveA₆ q hq‖ = ‖q‖ := by
  obtain ⟨u, -, hu, ha₆⟩ := exists_tateCurve_a₆_eq_X_mul
  rw [tateCurveA₆, ha₆, map_mul, evalIntSeries_X]
  exact norm_mul_evalIntSeries_of_isUnit q q hq hu

variable [NormOneClass K]

/-- The invariant `c₄ = 1 + 240 s₃(q)` of the specialized Tate equation has norm one. -/
@[simp] theorem norm_tateCurveAt_c₄ (q : Kˣ) (hq : ‖(q : K)‖ < 1) :
    ‖(tateCurveAt q hq).c₄‖ = 1 := by
  rw [tateCurveAt, WeierstrassCurve.map_c₄]
  exact norm_evalIntSeries_eq_one_of_isUnit (q : K) hq
    (PowerSeries.isUnit_iff_constantCoeff.mpr (by simp))

end

section

variable {K : Type*} [NormedField K] [CompleteSpace K] [IsUltrametricDist K]

/-- **`|j(q)| = 1 / |q|`**: the `j`-invariant of the specialized Tate equation has norm the inverse
of that of the parameter. In particular `|j| > 1`, so `j` is not integral. -/
@[simp] theorem norm_tateCurveAt_j (q : Kˣ) (hq : ‖(q : K)‖ < 1) :
    ‖(tateCurveAt q hq).j‖ = ‖(q : K)‖⁻¹ := by
  rw [WeierstrassCurve.j, norm_mul, norm_pow, norm_tateCurveAt_c₄, Units.val_inv_eq_inv_val,
    WeierstrassCurve.coe_Δ', norm_inv, norm_tateCurveAt_Δ, one_pow, mul_one]

end

section

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

/-! ### Solutions of the Tate equation with a pole -/

/-- On a curve `y² + xy = x³ + A₄x + A₆` with `‖A₄‖, ‖A₆‖ ≤ 1`, a solution with `‖x‖ > 1` has
`‖x‖ < ‖x + y‖`. -/
theorem norm_lt_norm_add_of_equation {A₄ A₆ x y : K} (hA₄ : ‖A₄‖ ≤ 1) (hA₆ : ‖A₆‖ ≤ 1)
    (hx : 1 < ‖x‖) (h : y ^ 2 + x * y = x ^ 3 + A₄ * x + A₆) : ‖x‖ < ‖x + y‖ := by
  have hx₀ : 0 < ‖x‖ := one_pos.trans hx
  have hx₃ : ‖x‖ < ‖x‖ ^ 3 := lt_self_pow₀ hx (by norm_num)
  -- the right-hand side has the norm `‖x‖³` of its leading term
  have hsmall : ‖A₄ * x + A₆‖ < ‖x ^ 3‖ := by
    rw [norm_pow]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ?_)
    · rw [norm_mul]
      nlinarith
    · linarith
  have hr : ‖y * (x + y)‖ = ‖x‖ ^ 3 := by
    rw [← norm_pow, show y * (x + y) = x ^ 3 + (A₄ * x + A₆) by linear_combination h,
      IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hsmall.ne', max_eq_left hsmall.le]
  -- if `‖x + y‖ ≤ ‖x‖`, then also `‖y‖ ≤ ‖x‖`, and the left-hand side is too small
  by_contra! hle
  have hy : ‖y‖ ≤ ‖x‖ := by
    simpa using (IsUltrametricDist.norm_sub_le_max (x + y) x).trans (max_le hle le_rfl)
  have h₂ : ‖x‖ ^ 3 ≤ ‖x‖ * ‖x‖ := by
    rw [← hr, norm_mul]
    exact mul_le_mul hy hle (norm_nonneg _) hx₀.le
  nlinarith [mul_lt_mul_of_pos_left hx (mul_pos hx₀ hx₀)]

/-- **A line through the origin meets the curve in at most one point with a pole.** If `(x, y)`
and `(X, Y)` solve `y² + xy = x³ + A₄x + A₆` with `‖A₄‖, ‖A₆‖ ≤ 1`, both first coordinates have
norm above one and `x Y = y X`, then the two points are equal. -/
theorem eq_of_mul_eq_mul_of_one_lt_norm {A₄ A₆ x y X Y : K} (hA₄ : ‖A₄‖ ≤ 1)
    (hA₆ : ‖A₆‖ ≤ 1) (hx : 1 < ‖x‖) (hX : 1 < ‖X‖) (h₁ : y ^ 2 + x * y = x ^ 3 + A₄ * x + A₆)
    (h₂ : Y ^ 2 + X * Y = X ^ 3 + A₄ * X + A₆) (h : x * Y = y * X) : X = x ∧ Y = y := by
  have key : (x - X) * (x ^ 2 * X ^ 2 - (A₄ * x * X + A₆ * (x + X))) = 0 := by
    linear_combination x ^ 2 * h₂ - X ^ 2 * h₁ - (x * Y + y * X + x * X) * h
  have hx₀ : 0 < ‖x‖ := one_pos.trans hx
  have hX₀ : 0 < ‖X‖ := one_pos.trans hX
  have hxX : ‖x‖ * ‖X‖ < ‖x‖ ^ 2 * ‖X‖ ^ 2 :=
    (lt_self_pow₀ (one_lt_mul_of_lt_of_le hx hX.le) one_lt_two).trans_eq (by ring)
  -- the cofactor of `x - X` is dominated by `x² X²`, so it does not vanish
  have hlt : ‖A₄ * x * X + A₆ * (x + X)‖ < ‖x ^ 2 * X ^ 2‖ := by
    rw [norm_mul, norm_pow, norm_pow]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ?_)
    · rw [norm_mul, norm_mul, mul_assoc]
      exact (mul_le_of_le_one_left (mul_pos hx₀ hX₀).le hA₄).trans_lt hxX
    · have hsum : ‖x + X‖ ≤ ‖x‖ * ‖X‖ :=
        (IsUltrametricDist.norm_add_le_max _ _).trans
          (max_le (le_mul_of_one_le_right hx₀.le hX.le) (le_mul_of_one_le_left hX₀.le hx.le))
      rw [norm_mul]
      calc ‖A₆‖ * ‖x + X‖ ≤ ‖A₆‖ * (‖x‖ * ‖X‖) := by gcongr
        _ ≤ ‖x‖ * ‖X‖ := mul_le_of_le_one_left (mul_pos hx₀ hX₀).le hA₆
        _ < ‖x‖ ^ 2 * ‖X‖ ^ 2 := hxX
  have hne : x ^ 2 * X ^ 2 - (A₄ * x * X + A₆ * (x + X)) ≠ 0 := fun h₀ ↦ by
    rw [sub_eq_zero.mp h₀] at hlt
    exact lt_irrefl _ hlt
  have hXx : X = x := (sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_right hne)).symm
  refine ⟨hXx, ?_⟩
  rw [hXx, mul_comm y] at h
  exact mul_left_cancel₀ (norm_pos_iff.mp hx₀) h

end

end TauCeti

end

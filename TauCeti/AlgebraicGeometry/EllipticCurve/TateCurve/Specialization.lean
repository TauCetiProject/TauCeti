/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.TateCurve.Basic
public import TauCeti.NumberTheory.ArithmeticFunction.Sigma.Evaluation

/-!
# Specialization of the Tate equation

The coefficients of the Tate equation are formal power series with integer coefficients. In a
complete non-archimedean normed ring with `‖1‖ = 1`, their sums converge at every parameter of norm
less than one.
This remains true in residue characteristics `2` and `3`: the sixth coefficient is summed from
its integral coefficients, with no division in the target ring.

For a unit parameter in the open unit ball of a complete non-archimedean normed commutative ring
with `‖1‖ = 1`, these sums give a nonsingular Tate equation. Its discriminant has the same norm as
the parameter, even when the ring norm is only submultiplicative. Point uniformisation requires
further arguments.

## References

* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, V.3.
* J. Tate, *A review of non-Archimedean elliptic functions* (1995).
-/

public section

namespace TauCeti

section

variable {K : Type*} [NormedCommRing K] [NormOneClass K] [CompleteSpace K]
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
non-archimedean normed commutative ring with `‖1‖ = 1`, even when `12 = 0` there. -/
@[simp] theorem twelve_mul_tateCurveA₆ {q : K} (hq : ‖q‖ < 1) :
    12 * tateCurveA₆ q hq = -(5 * divisorSumAt 3 q + 7 * divisorSumAt 5 q) := by
  simpa only [map_mul, map_ofNat, map_neg, map_add, evalIntSeries_divisorSumSeries, tateCurveA₆]
    using congrArg (evalIntSeries q hq) twelve_mul_tateCurve_a₆

/-- The Tate equation obtained by evaluating the integral formal curve at a unit parameter of
norm less than one. The unit parameter will also support its integer powers in uniformisation. -/
noncomputable def tateCurveAt (q : Kˣ) (hq : ‖(q : K)‖ < 1) : WeierstrassCurve K :=
  tateCurve.map (evalIntSeries (q : K) hq)

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

end

end TauCeti

end

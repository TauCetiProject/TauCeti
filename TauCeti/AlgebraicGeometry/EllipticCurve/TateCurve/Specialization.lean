/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.TateCurve.Basic
public import TauCeti.Topology.Algebra.InfiniteSum.IntegralCoefficients
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Analysis.Normed.Ring.Lemmas

/-!
# Specialization of the Tate equation

The coefficients of the Tate equation are formal power series with integer coefficients. In a
complete non-archimedean field, their sums converge at every parameter of norm less than one.
This remains true in residue characteristics `2` and `3`: the sixth coefficient is summed from
its integral coefficients, with no division in the field.

These sums give a nonsingular Tate equation for every nonzero parameter in the open unit ball,
including fields with nondiscrete valuation. Its discriminant has the same norm as the parameter.
Point uniformisation requires further arguments.

## References

* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, V.3.
* J. Tate, *A review of non-Archimedean elliptic functions* (1995).
-/

public section

open PowerSeries ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace TauCeti

variable {K : Type*} [NormedField K] [CompleteSpace K] [IsUltrametricDist K]

/-- The divisor-sum series `s_k(q) = ∑ σ_k(n) q^n` converges for `‖q‖ < 1`. -/
theorem summable_divisorSumSeries (k : ℕ) {q : K} (hq : ‖q‖ < 1) :
    Summable (fun n : ℕ ↦ (((σ k n : ℕ) : ℤ) : K) * q ^ n) :=
  summable_intCast_mul_pow (fun n : ℕ ↦ ((σ k n : ℕ) : ℤ)) hq

/-- The fourth Tate coefficient, obtained by substituting `q` into its integral formal series,
is a convergent sum. -/
theorem summable_tateCurve_a₄ {q : K} (hq : ‖q‖ < 1) :
    Summable (fun n : ℕ ↦ ((PowerSeries.coeff n tateCurve.a₄ : ℤ) : K) * q ^ n) :=
  summable_intCast_mul_pow (fun n : ℕ ↦ PowerSeries.coeff n tateCurve.a₄) hq

/-- The sixth Tate coefficient converges as an integral series, even when `12` vanishes in the
field. -/
theorem summable_tateCurve_a₆ {q : K} (hq : ‖q‖ < 1) :
    Summable (fun n : ℕ ↦ ((PowerSeries.coeff n tateCurve.a₆ : ℤ) : K) * q ^ n) :=
  summable_intCast_mul_pow (fun n : ℕ ↦ PowerSeries.coeff n tateCurve.a₆) hq

/-- Evaluation of the integral divisor-sum series in a complete non-archimedean field. Its
convergence for `‖q‖ < 1` is `summable_divisorSumSeries`. -/
noncomputable def divisorSumAt (k : ℕ) (q : K) (_hq : ‖q‖ < 1) : K :=
  ∑' n : ℕ, (((σ k n : ℕ) : ℤ) : K) * q ^ n

/-- The analytic fourth Tate coefficient, obtained from the integral formal series. -/
noncomputable def tateCurveA4 (q : K) (_hq : ‖q‖ < 1) : K :=
  ∑' n : ℕ, ((PowerSeries.coeff n tateCurve.a₄ : ℤ) : K) * q ^ n

/-- The analytic sixth Tate coefficient, obtained from integral coefficients before reducing to
the residue characteristic of the field. -/
noncomputable def tateCurveA6 (q : K) (_hq : ‖q‖ < 1) : K :=
  ∑' n : ℕ, ((PowerSeries.coeff n tateCurve.a₆ : ℤ) : K) * q ^ n

omit [CompleteSpace K] [IsUltrametricDist K] in
/-- The fourth coefficient equals `-5 s₃(q)`. -/
theorem tateCurveA4_eq (q : K) (hq : ‖q‖ < 1) :
    tateCurveA4 q hq = -5 * divisorSumAt 3 q hq := by
  simp_rw [tateCurveA4, coeff_tateCurve_a₄, Int.cast_mul, Int.cast_neg, Int.cast_ofNat,
    neg_mul, mul_assoc]
  rw [tsum_neg, tsum_mul_left]
  rfl

/-- The integral identity `12 a₆(q) = -(5 s₃(q) + 7 s₅(q))` holds in every complete
non-archimedean field, even when `12 = 0` there. -/
theorem twelve_mul_tateCurveA6 {q : K} (hq : ‖q‖ < 1) :
    12 * tateCurveA6 q hq = -(5 * divisorSumAt 3 q hq + 7 * divisorSumAt 5 q hq) := by
  have hcoeff (n : ℕ) : (12 : K) * ((coeff n tateCurve.a₆ : ℤ) : K) =
      -(5 * (((σ 3 n : ℕ) : ℤ) : K) + 7 * (((σ 5 n : ℕ) : ℤ) : K)) := by
    have h := congrArg (fun z : ℤ ↦ (z : K)) (twelve_mul_coeff_tateCurve_a₆ n)
    simpa only [Int.cast_mul, Int.cast_neg, Int.cast_add, Int.cast_ofNat] using h
  rw [tateCurveA6, ← tsum_mul_left]
  simp_rw [← mul_assoc, hcoeff, neg_mul, add_mul]
  simp_rw [mul_assoc]
  rw [tsum_neg, (summable_divisorSumSeries 3 hq |>.mul_left 5).tsum_add
    (summable_divisorSumSeries 5 hq |>.mul_left 7)]
  simp only [← tsum_mul_left, divisorSumAt]

/-- The Tate equation obtained by evaluating the integral formal curve at a nonzero parameter of
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
    (tateCurveAt q hq).a₄ = tateCurveA4 (q : K) hq := by
  simp only [tateCurveAt, WeierstrassCurve.map, tateCurveA4, evalIntSeries_apply]

/-- The analytic sixth coefficient is the evaluation of the formal sixth coefficient. -/
@[simp] theorem tateCurveAt_a₆ (q : Kˣ) (hq : ‖(q : K)‖ < 1) :
    (tateCurveAt q hq).a₆ = tateCurveA6 (q : K) hq := by
  simp only [tateCurveAt, WeierstrassCurve.map, tateCurveA6, evalIntSeries_apply]

/-- The discriminant of the specialized Tate equation is nonzero. -/
theorem isUnit_tateCurveAt_Δ (q : Kˣ) (hq : ‖(q : K)‖ < 1) :
    IsUnit (tateCurveAt q hq).Δ := by
  obtain ⟨u, hu, hΔ⟩ := exists_tateCurve_Δ_eq_X_mul
  rw [tateCurveAt, WeierstrassCurve.map_Δ, hΔ, map_mul, evalIntSeries_X]
  exact q.isUnit.mul
    (((isUnit_iff_constantCoeff (φ := u)).mpr (by simp [hu])).map _)

/-- The specialized Tate discriminant has the same norm as the parameter. -/
theorem norm_tateCurveAt_Δ (q : Kˣ) (hq : ‖(q : K)‖ < 1) :
    ‖(tateCurveAt q hq).Δ‖ = ‖(q : K)‖ := by
  obtain ⟨u, hu, hΔ⟩ := exists_tateCurve_Δ_eq_X_mul
  rw [tateCurveAt, WeierstrassCurve.map_Δ, hΔ, map_mul, evalIntSeries_X, norm_mul,
    norm_evalIntSeries_of_isUnit (q : K) hq
      ((isUnit_iff_constantCoeff (φ := u)).mpr (by simp [hu])), mul_one]

/-- A unit parameter of norm below one gives an elliptic curve over the complete valued field,
with no discreteness or characteristic assumption. -/
theorem isElliptic_tateCurveAt (q : Kˣ) (hq : ‖(q : K)‖ < 1) :
    (tateCurveAt q hq).IsElliptic :=
  ⟨isUnit_tateCurveAt_Δ q hq⟩

end TauCeti

end

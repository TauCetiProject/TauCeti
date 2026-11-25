/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.LFunction
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.GoodPrimes
public import TauCeti.AlgebraicGeometry.EllipticCurve.PointCount
public import TauCeti.NumberTheory.Padics.RingHoms
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.VariableChange
import TauCeti.AlgebraicGeometry.EllipticCurve.HasseBound
import TauCeti.AlgebraicGeometry.EllipticCurve.LocalPolynomial
import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.Basic

/-!
# Frobenius angles of a rational Weierstrass curve

For a Weierstrass curve `E` over `ℚ` and a prime `p`, reduce the minimal equation of `E` over
`ℚ_p` modulo `p`. If that reduction is nonsingular, `E` has good reduction at `p`
(`WeierstrassCurve.HasGoodReductionAt`), and the trace
of Frobenius `a_p = p + 1 - #E_p(𝔽_p)` satisfies the Hasse bound `|a_p| ≤ 2√p`. The
**Frobenius angle** `θ_p ∈ [0, π]` is then defined by `a_p = 2√p cos θ_p`; equivalently, the
normalized roots of the Frobenius polynomial `X² - a_p X + p` are `exp (± i θ_p)`.

These are the objects of the Sato–Tate theorem: for a non-CM elliptic curve over `ℚ`, the angles
`θ_p`, taken over the good primes `p ≤ x` as `x → ∞`, are equidistributed for the measure
`(2/π) sin² θ dθ` on `[0, π]`. The finite sets of good primes over which the averages are taken
are `WeierstrassCurve.goodReductionPrimes`; this file defines the angles themselves and proves the
properties on which the statement and its proof through symmetric-power `L`-functions rest.

The angle is defined at every prime. The minimal equation is the one chosen by Mathlib
(`WeierstrassCurve.minimal`); for an elliptic curve the angle is independent of that choice
(`WeierstrassCurve.frobeniusAngle_smul`), while for a singular `E` it may depend on the chosen
minimal model. At a bad prime the angle is still the arccosine of
`(p + 1 - #E_p^{ns}(𝔽_p)) / (2√p)`, counting the nonsingular points of the minimal reduction, but
no Frobenius interpretation is asserted there.

## Main definitions

* `WeierstrassCurve.frobeniusAngle E p`: the angle `arccos ((p + 1 - #E_p(𝔽_p)) / (2√p))`.

## Main results

* `WeierstrassCurve.frobeniusAngle_def`: the defining formula of the angle, at every prime.
* `WeierstrassCurve.cos_frobeniusAngle`: at a good prime, `cos θ_p = a_p / (2√p)`.
* `WeierstrassCurve.map_localPolynomial_eq_mul`: at a good prime, the local polynomial
  `1 - a_p T + p T²` of `E` factors over `ℂ` as `(1 - α T)(1 - conj α T)` with
  `α = √p exp (i θ_p)`.
* `WeierstrassCurve.frobeniusAngle_smul`: isomorphic elliptic curves have the same angles.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], V.1.1 and VII.1.
* K. S. Kedlaya, *Notes on the Sato–Tate conjecture*, §24.
-/

public section

namespace WeierstrassCurve

open Polynomial

variable (E : WeierstrassCurve ℚ)

/-- The **Frobenius angle** `θ_p ∈ [0, π]` of `E` at the prime `p`: the arccosine of
`(p + 1 - #E_p(𝔽_p)) / (2√p)`, where `#E_p(𝔽_p)` counts the nonsingular points, including the
point at infinity, of the reduction modulo `p` of the minimal equation of `E` over `ℚ_p`.

At a prime of good reduction, `a_p = 2√p cos θ_p` (`cos_frobeniusAngle`) and the roots of the
Frobenius polynomial `X² - a_p X + p` are `√p exp (± i θ_p)` (`map_localPolynomial_eq_mul`). At a
bad prime the value is defined but carries no Frobenius interpretation. -/
noncomputable def frobeniusAngle (p : Nat.Primes) : ℝ :=
  Real.arccos (((p : ℝ) + 1 -
      Nat.card (((E.baseChange ℚ_[p]).minimal ℤ_[p]).reduction ℤ_[p]).toAffine.Point) /
    (2 * √(p : ℝ)))

/-- The defining formula of `frobeniusAngle`, valid at every prime, good or bad. -/
theorem frobeniusAngle_def (p : Nat.Primes) :
    E.frobeniusAngle p = Real.arccos (((p : ℝ) + 1 -
      Nat.card (((E.baseChange ℚ_[p]).minimal ℤ_[p]).reduction ℤ_[p]).toAffine.Point) /
        (2 * √(p : ℝ))) :=
  (rfl)

/-- The Frobenius angle is nonnegative. -/
theorem frobeniusAngle_nonneg (p : Nat.Primes) : 0 ≤ E.frobeniusAngle p :=
  Real.arccos_nonneg _

/-- The Frobenius angle is at most `π`. -/
theorem frobeniusAngle_le_pi (p : Nat.Primes) : E.frobeniusAngle p ≤ Real.pi :=
  Real.arccos_le_pi _

/-- **`a_p = 2√p cos θ_p`**: at a prime of good reduction, the cosine of the Frobenius angle is the
trace of Frobenius of the minimal reduction divided by `2√p`. The Hasse bound `a_p² ≤ 4p` puts this
ratio in `[-1, 1]`. -/
theorem cos_frobeniusAngle {p : Nat.Primes} (hp : E.HasGoodReductionAt p) :
    Real.cos (E.frobeniusAngle p) =
      (((E.baseChange ℚ_[p]).minimal ℤ_[p]).reduction ℤ_[p]).frobeniusTrace / (2 * √(p : ℝ)) := by
  set W := ((E.baseChange ℚ_[p]).minimal ℤ_[p]).reduction ℤ_[p]
  have : W.IsElliptic :=
    (hasGoodReduction_iff_isElliptic_reduction ℤ_[p]).1 (E.hasGoodReductionAt_iff.1 hp)
  have hcard := PadicInt.card_residueField (p := p)
  have ha : (W.frobeniusTrace : ℝ) = (p : ℝ) + 1 - Nat.card W.toAffine.Point := by
    rw [frobeniusTrace_eq_card_point, hcard]
    push_cast
    ring
  have hsq : (W.frobeniusTrace : ℝ) ^ 2 ≤ 4 * p := by
    exact_mod_cast hcard ▸ W.frobeniusTrace_sq_le_four_mul_card
  have hp0 : (0 : ℝ) < p := by exact_mod_cast p.prop.pos
  have hpos : 0 < 2 * √(p : ℝ) := by positivity
  -- the Hasse bound `a_p² ≤ 4p = (2√p)²`, read as `-2√p ≤ a_p ≤ 2√p`
  have habs := abs_le_of_sq_le_sq' (a := (W.frobeniusTrace : ℝ)) (b := 2 * √(p : ℝ))
    (by rw [mul_pow, Real.sq_sqrt hp0.le]; linarith) hpos.le
  rw [frobeniusAngle, ← ha]
  refine Real.cos_arccos ?_ ?_
  · rw [le_div_iff₀ hpos]
    linarith [habs.1]
  · rw [div_le_one hpos]
    exact habs.2

/-- **The local polynomial at a good prime factors through the Frobenius angle**: over `ℂ`, the
Euler factor `1 - a_p T + p T²` of `E` at `p` is `(1 - α T)(1 - conj α T)` with
`α = √p exp (i θ_p)`. So `exp (± i θ_p)` are the normalized Frobenius eigenvalues, and `α` is the
root of the Frobenius polynomial `X² - a_p X + p` with nonnegative imaginary part. -/
theorem map_localPolynomial_eq_mul {p : Nat.Primes} (hp : E.HasGoodReductionAt p) :
    ((E.baseChange ℚ_[p]).localPolynomial ℤ_[p]).map (Int.castRingHom ℂ) =
      (1 - C (√(p : ℝ) * Complex.exp (E.frobeniusAngle p * Complex.I)) * X) *
        (1 - C (√(p : ℝ) * Complex.exp (-(E.frobeniusAngle p * Complex.I))) * X) := by
  rw [localPolynomial_eq_of_hasGoodReduction _ _ (E.hasGoodReductionAt_iff.1 hp),
    PadicInt.card_residueField]
  set θ := E.frobeniusAngle p
  set a := (((E.baseChange ℚ_[p]).minimal ℤ_[p]).reduction ℤ_[p]).frobeniusTrace
  have hp0 : (0 : ℝ) < p := by exact_mod_cast p.prop.pos
  have hcos : Real.cos θ = a / (2 * √(p : ℝ)) := E.cos_frobeniusAngle hp
  have hsum : (√(p : ℝ) : ℂ) * Complex.exp (θ * Complex.I) +
      (√(p : ℝ) : ℂ) * Complex.exp (-(θ * Complex.I)) = a := by
    rw [← neg_mul, Complex.exp_mul_I, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg,
      ← Complex.ofReal_cos, hcos]
    have : (√(p : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 hp0).ne'
    push_cast
    field_simp
    ring
  have hprod : (√(p : ℝ) : ℂ) * Complex.exp (θ * Complex.I) *
      ((√(p : ℝ) : ℂ) * Complex.exp (-(θ * Complex.I))) = (p : ℂ) := by
    rw [mul_mul_mul_comm, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, mul_one,
      ← Complex.ofReal_mul, Real.mul_self_sqrt hp0.le, Complex.ofReal_natCast]
  have hmul (α β : ℂ) : (1 - C α * X) * (1 - C β * X) = 1 - C (α + β) * X + C (α * β) * X ^ 2 := by
    rw [C_add, C_mul]
    ring
  rw [hmul, hsum, hprod]
  simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_one, Polynomial.map_mul,
    Polynomial.map_pow, Polynomial.map_C, map_X]
  simp only [eq_intCast, Int.cast_natCast]

/-- **Isomorphic elliptic curves over `ℚ` have the same Frobenius angles**, at every prime: the
minimal reductions of two isomorphic curves are isomorphic over `𝔽_p`, so they have the same
number of nonsingular points. -/
@[simp]
theorem frobeniusAngle_smul [E.IsElliptic] (C : VariableChange ℚ) (p : Nat.Primes) :
    (C • E).frobeniusAngle p = E.frobeniusAngle p := by
  have hb : (C • E).baseChange ℚ_[p] = C.baseChange ℚ_[p] • E.baseChange ℚ_[p] :=
    (baseChange_smul_baseChange _ _ _).symm
  obtain ⟨D, hD⟩ := exists_smul_minimal_eq_minimal ℤ_[p] (C.baseChange ℚ_[p]) (E.baseChange ℚ_[p])
  obtain ⟨D', hD'⟩ := exists_smul_reduction_eq_of_isMinimal_smul ℤ_[p] D hD
  rw [frobeniusAngle_def, frobeniusAngle_def]
  simp only [hb]
  rw [← hD', Nat.card_congr (Affine.Point.equivVariableChange _ D')]

end WeierstrassCurve

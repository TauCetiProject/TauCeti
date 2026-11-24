/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.LFunction
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import TauCeti.AlgebraicGeometry.EllipticCurve.PointCount
public import TauCeti.Data.Nat.Prime.Basic
public import TauCeti.NumberTheory.Padics.RingHoms
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Tactic.NormNum.Prime
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.VariableChange
import TauCeti.AlgebraicGeometry.EllipticCurve.HasseBound
import TauCeti.AlgebraicGeometry.EllipticCurve.LocalPolynomial
import TauCeti.AlgebraicGeometry.EllipticCurve.IntegralModel
import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.Basic
import TauCeti.NumberTheory.Padics.PadicIntegers

/-!
# Good primes and Frobenius angles of a rational Weierstrass curve

For a Weierstrass curve `E` over `ℚ` and a prime `p`, reduce the minimal equation of `E` over
`ℚ_p` modulo `p`. If that reduction is nonsingular, `E` has good reduction at `p`, and the trace
of Frobenius `a_p = p + 1 - #E_p(𝔽_p)` satisfies the Hasse bound `|a_p| ≤ 2√p`. The
**Frobenius angle** `θ_p ∈ [0, π]` is then defined by `a_p = 2√p cos θ_p`; equivalently, the
normalized roots of the Frobenius polynomial `X² - a_p X + p` are `exp (± i θ_p)`.

These are the objects of the Sato–Tate theorem: for a non-CM elliptic curve over `ℚ`, the angles
`θ_p`, taken over the good primes `p ≤ x` as `x → ∞`, are equidistributed for the measure
`(2/π) sin² θ dθ` on `[0, π]`. This file sets up the finite sets of good primes over which the
averages are taken and the angles themselves, and proves the properties of both on which the
statement and its proof through symmetric-power `L`-functions rest.

Both definitions are total. The minimal equation is the one chosen by Mathlib
(`WeierstrassCurve.minimal`); every statement below is independent of that choice. At a bad
prime the angle is still the arccosine of `(p + 1 - #E_p^{ns}(𝔽_p)) / (2√p)`, counting the
nonsingular points of the minimal reduction, but no Frobenius interpretation is asserted there.

## Main definitions

* `WeierstrassCurve.HasGoodReductionAt E p`: the minimal equation of `E` over `ℚ_p` has good
  reduction.
* `WeierstrassCurve.goodReductionPrimes E x`: the finite set of primes `p ≤ x` of good reduction.
* `WeierstrassCurve.frobeniusAngle E p`: the angle `arccos ((p + 1 - #E_p(𝔽_p)) / (2√p))`.

## Main results

* `WeierstrassCurve.mem_goodReductionPrimes`: membership is `p ≤ x` together with good reduction.
* `WeierstrassCurve.goodReductionPrimes_mono`, `WeierstrassCurve.goodReductionPrimes_inter` and
  `WeierstrassCurve.iUnion_goodReductionPrimes`: the sets increase with the bound, meet at the
  minimum of the bounds, and exhaust the good primes.
* `WeierstrassCurve.hasGoodReductionAt_smul` and `WeierstrassCurve.goodReductionPrimes_smul`:
  good reduction depends only on the isomorphism class over `ℚ`.
* `WeierstrassCurve.hasGoodReductionAt_baseChange_iff`: for an integral equation that is minimal
  at `p`, good reduction at `p` means that `p` does not divide the discriminant.
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

/-! ### Primes of good reduction -/

/-- A Weierstrass curve `E` over `ℚ` **has good reduction at the prime `p`** when the minimal
equation of `E` over `ℚ_p` reduces to a nonsingular curve over `𝔽_p`. This tests the minimal
equation, not the given one: a nonminimal equation may have singular reduction at a prime of
good reduction. -/
def HasGoodReductionAt (p : Nat.Primes) : Prop :=
  ((E.baseChange ℚ_[p]).minimal ℤ_[p]).HasGoodReduction ℤ_[p]

/-- The defining property of `HasGoodReductionAt`. -/
theorem hasGoodReductionAt_iff {p : Nat.Primes} :
    E.HasGoodReductionAt p ↔ ((E.baseChange ℚ_[p]).minimal ℤ_[p]).HasGoodReduction ℤ_[p] :=
  Iff.rfl

/-- **Good reduction is a property of the curve**: isomorphic equations over `ℚ` have good
reduction at the same primes. No ellipticity is needed. -/
@[simp]
theorem hasGoodReductionAt_smul (C : VariableChange ℚ) {p : Nat.Primes} :
    (C • E).HasGoodReductionAt p ↔ E.HasGoodReductionAt p := by
  rw [hasGoodReductionAt_iff, hasGoodReductionAt_iff, baseChange, ← map_variableChange,
    ← VariableChange.baseChange, ← baseChange, hasGoodReduction_minimal_smul_iff]

/-- The finite set of **primes `p ≤ x` at which `E` has good reduction**, the range over which
the Frobenius angles of `E` are averaged in the Sato–Tate theorem. -/
noncomputable def goodReductionPrimes (x : ℕ) : Finset Nat.Primes := by
  classical
  exact ((Finset.range (x + 1)).subtype Nat.Prime).filter E.HasGoodReductionAt

/-- A prime lies in `goodReductionPrimes E x` exactly when it is at most `x` and `E` has good
reduction there. -/
@[simp]
theorem mem_goodReductionPrimes {x : ℕ} {p : Nat.Primes} :
    p ∈ E.goodReductionPrimes x ↔ (p : ℕ) ≤ x ∧ E.HasGoodReductionAt p := by
  classical
  exact Finset.mem_filter.trans
    (and_congr_left' (Finset.mem_subtype.trans (Finset.mem_range.trans Nat.lt_succ_iff)))

/-- The sets of good primes grow with the bound. -/
theorem goodReductionPrimes_mono : Monotone E.goodReductionPrimes := fun _ _ hxy _ hp ↦ by
  rw [mem_goodReductionPrimes] at hp ⊢
  exact ⟨hp.1.trans hxy, hp.2⟩

/-- The good primes up to `x` and up to `y` have in common the good primes up to `min x y`. -/
theorem goodReductionPrimes_inter (x y : ℕ) :
    E.goodReductionPrimes x ∩ E.goodReductionPrimes y = E.goodReductionPrimes (min x y) := by
  ext p
  simp only [Finset.mem_inter, mem_goodReductionPrimes, le_min_iff]
  tauto

/-- Below `2` there are no primes, so no good primes. -/
theorem goodReductionPrimes_eq_empty {x : ℕ} (hx : x < 2) : E.goodReductionPrimes x = ∅ := by
  ext p
  simp only [mem_goodReductionPrimes, Finset.notMem_empty, iff_false, not_and]
  exact fun hpx ↦ absurd (hpx.trans_lt hx) p.prop.two_le.not_gt

/-- **Removing the bound recovers the good primes**: the sets `goodReductionPrimes E x` exhaust
the primes of good reduction of `E`. -/
theorem iUnion_goodReductionPrimes :
    ⋃ x, (E.goodReductionPrimes x : Set Nat.Primes) = {p | E.HasGoodReductionAt p} := by
  ext p
  simp only [Set.mem_iUnion, Finset.mem_coe, mem_goodReductionPrimes, Set.mem_ofPred_eq]
  exact ⟨fun ⟨_, h⟩ ↦ h.2, fun h ↦ ⟨p, le_rfl, h⟩⟩

/-- **The sets of good primes depend only on the isomorphism class of `E` over `ℚ`.** -/
@[simp]
theorem goodReductionPrimes_smul (C : VariableChange ℚ) (x : ℕ) :
    (C • E).goodReductionPrimes x = E.goodReductionPrimes x := by
  ext p
  simp

/-! ### Good reduction of an integral equation -/

section Integral

variable (W : WeierstrassCurve ℤ) (p : Nat.Primes)

/-- Reading an integral equation over `ℚ` and then over `ℚ_p` is reading it over `ℤ_p` and then
over `ℚ_p`. -/
private theorem baseChange_baseChange_padic :
    (W.baseChange ℚ).baseChange ℚ_[p] = (W.baseChange ℤ_[p]).baseChange ℚ_[p] := by
  simp only [baseChange, map_map]
  congr 1

/-- **An integral equation has good reduction at every prime not dividing its discriminant.** -/
theorem hasGoodReductionAt_baseChange_of_not_dvd (h : ¬ (p : ℤ) ∣ W.Δ) :
    (W.baseChange ℚ).HasGoodReductionAt p := by
  rw [hasGoodReductionAt_iff, baseChange_baseChange_padic]
  have : IsIntegral ℤ_[p] ((W.baseChange ℤ_[p]).baseChange ℚ_[p]) := ⟨⟨_, rfl⟩⟩
  refine HasGoodReduction.hasGoodReduction_minimal ℤ_[p] ?_
  rwa [hasGoodReduction_iff_isUnit_integralModel_Δ, integralModel_baseChange_self, baseChange,
    map_Δ, algebraMap_int_eq, eq_intCast, PadicInt.isUnit_intCast_iff]

/-- **For an integral equation that is minimal at `p`, good reduction at `p` means that `p` does
not divide the discriminant.** The minimality hypothesis is that `p ^ 12` does not divide the
discriminant; without it, an equation such as `y² = x³ - p⁴ x + p⁶` can have good reduction at `p`
while `p` divides its discriminant. -/
theorem hasGoodReductionAt_baseChange_iff (h12 : ¬ (p : ℤ) ^ 12 ∣ W.Δ) :
    (W.baseChange ℚ).HasGoodReductionAt p ↔ ¬ (p : ℤ) ∣ W.Δ := by
  refine ⟨fun h ↦ ?_, W.hasGoodReductionAt_baseChange_of_not_dvd p⟩
  rw [hasGoodReductionAt_iff, baseChange_baseChange_padic] at h
  set V := (W.baseChange ℤ_[p]).baseChange ℚ_[p]
  have : IsIntegral ℤ_[p] V := ⟨⟨_, rfl⟩⟩
  have : IsMinimal ℤ_[p] V := isMinimal_baseChange_of_not_pow_twelve_dvd_Δ ℤ_[p] _
    PadicInt.irreducible_p (by
      rwa [baseChange, map_Δ, algebraMap_int_eq, eq_intCast, PadicInt.pow_p_dvd_int_iff])
  obtain ⟨C, hC⟩ := V.exists_smul_eq_minimal ℤ_[p]
  have hV : V.HasGoodReduction ℤ_[p] :=
    ⟨(valuation_Δ_eq_of_isMinimal_smul ℤ_[p] C hC).symm.trans h.goodReduction⟩
  rwa [hasGoodReduction_iff_isUnit_integralModel_Δ, integralModel_baseChange_self, baseChange,
    map_Δ, algebraMap_int_eq, eq_intCast, PadicInt.isUnit_intCast_iff] at hV

/-! The curve `y² = x³ - x + 1`, with discriminant `-368 = -2⁴ · 23`, has good reduction at `5`
but not at `23`, where its equation is minimal since `23¹²` does not divide `-368`. -/

example : ((⟨0, 0, 0, -1, 1⟩ : WeierstrassCurve ℤ).baseChange ℚ).HasGoodReductionAt
    ⟨5, by norm_num⟩ :=
  hasGoodReductionAt_baseChange_of_not_dvd _ _ (by norm_num [Δ, b₂, b₄, b₆, b₈])

example : ⟨5, by norm_num⟩ ∈
    ((⟨0, 0, 0, -1, 1⟩ : WeierstrassCurve ℤ).baseChange ℚ).goodReductionPrimes 5 :=
  mem_goodReductionPrimes _ |>.2
    ⟨le_rfl, hasGoodReductionAt_baseChange_of_not_dvd _ _ (by norm_num [Δ, b₂, b₄, b₆, b₈])⟩

example : ¬ ((⟨0, 0, 0, -1, 1⟩ : WeierstrassCurve ℤ).baseChange ℚ).HasGoodReductionAt
    ⟨23, by norm_num⟩ :=
  (hasGoodReductionAt_baseChange_iff _ _ (by norm_num [Δ, b₂, b₄, b₆, b₈])).not.2
    (by norm_num [Δ, b₂, b₄, b₆, b₈])

end Integral

/-! ### Frobenius angles -/

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
  have : W.IsElliptic := (hasGoodReduction_iff_isElliptic_reduction ℤ_[p]).1 hp
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
    (by rwa [mul_pow, Real.sq_sqrt hp0.le, show (2 : ℝ) ^ 2 = 4 by norm_num]) hpos.le
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
  rw [localPolynomial_eq_of_hasGoodReduction _ _ hp, PadicInt.card_residueField]
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
  have hb : (C • E).baseChange ℚ_[p] = C.baseChange ℚ_[p] • E.baseChange ℚ_[p] := by
    rw [baseChange, baseChange, VariableChange.baseChange, map_variableChange]
  obtain ⟨D, hD⟩ := exists_smul_minimal_eq_minimal ℤ_[p] (C.baseChange ℚ_[p]) (E.baseChange ℚ_[p])
  obtain ⟨D', hD'⟩ := exists_smul_reduction_eq_of_isMinimal_smul ℤ_[p] D hD
  rw [frobeniusAngle, frobeniusAngle]
  simp only [hb]
  rw [← hD', Nat.card_congr (Affine.Point.equivVariableChange _ D')]

end WeierstrassCurve

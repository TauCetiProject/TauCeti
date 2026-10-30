/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.HahnSeries.Valuation
public import Mathlib.RingTheory.LaurentSeries
public import TauCeti.NumberTheory.NewtonPolygon.Mul

/-!
# Newton polygons and initial polynomials over Laurent series

For a domain `R`, the order of vanishing `ord = HahnSeries.orderTop` on `R⸨X⸩`, with
`ord(0) = ⊤` and `ord(X) = 1`, becomes a real additive valuation
`TauCeti.LaurentSeries.realAddVal R` after the inclusion `ℤ → ℝ`. The general Newton-polygon
API, `Polynomial.newtonPolygon` together with its slope multisets and the Minkowski-sum formula
`Polynomial.newtonPolygon_mul`, therefore applies to polynomials `P = ∑ aₙ Yⁿ` over `R⸨X⸩`
with the coefficient heights `n ↦ ord(aₙ)`.

Fix a real slope `σ`. The tilted heights `ord(aₙ) - σ n` of a nonzero `P` attain their minimum,
the supporting value at `σ`, on a finite nonempty set of indices: the contact set of the
supporting line of slope `σ`. The *initial polynomial* `P.initialPolynomial σ ∈ R[Y]` collects
the leading coefficients `lc(aₙ)` of the coefficients at these indices,
```
P.initialPolynomial σ = ∑_{n on the supporting line} lc(aₙ) Yⁿ.
```
The Newton polygon of `P` has the same supporting values as its coefficient heights
(`Polynomial.supportingValue_newtonPolygon`), so the supporting line is that of the Newton polygon.

The main result is that taking initial polynomials is multiplicative,
`Polynomial.initialPolynomial_mul`: the initial polynomial of `P * Q` at `σ` is the product of
the initial polynomials of `P` and `Q`. This is the dominant-term identity behind the
Minkowski-sum formula, refined from valuations to leading coefficients. No completeness and no
characteristic hypothesis is used.

## Main definitions

* `TauCeti.LaurentSeries.realAddVal R`: the real additive valuation `ord` on `R⸨X⸩`.
* `Polynomial.initialPolynomial P σ`: the initial polynomial of `P` at slope `σ`.
* `Polynomial.initialPolynomialHom R σ`: the initial polynomial at slope `σ` as a monoid
  homomorphism `R⸨X⸩[Y] →* R[Y]`.

## Main results

* `TauCeti.LaurentSeries.realAddVal_apply`: `realAddVal R f` is `f.orderTop` cast to the reals,
  and `TauCeti.LaurentSeries.realAddVal_eq_top_iff`: only zero has infinite valuation.
* `Polynomial.coeff_initialPolynomial`: the coefficients of the initial polynomial.
* `Polynomial.initialPolynomial_eq_zero_iff`: only the zero polynomial has initial polynomial
  zero, at any slope.
* `Polynomial.initialPolynomial_monomial`: the initial polynomial of `a Yⁿ` is `lc(a) Yⁿ`.
* `Polynomial.initialPolynomial_mul`: initial polynomials are multiplicative.

## References

* S. Mannaa and T. Coquand, *Dynamic Newton–Puiseux Theorem*, J. Logic & Analysis 5 (2013),
  §1.
* M. Lazard, *Les zéros d'une fonction analytique d'une variable sur un corps valué complet*,
  Publications Mathématiques de l'IHÉS 14 (1962), §1, Proposition 1.
-/

public section

open HahnSeries TauCeti
open scoped LaurentSeries

namespace TauCeti.LaurentSeries

variable (R : Type*) [Ring R] [IsDomain R]

/-- The order of vanishing `ord = orderTop` on `R⸨X⸩` as a real additive valuation: a nonzero
Laurent series of order `n` has valuation `n`, and zero has valuation `⊤`. -/
noncomputable def realAddVal : AddValuation R⸨X⸩ (WithTop ℝ) :=
  (HahnSeries.addVal ℤ R).map
    { (Int.castAddHom ℝ).withTopMap with
      monotone' := WithTop.monotone_map_iff.mpr fun _ _ h => Int.cast_le.mpr h }
    rfl

variable {R}

/-- The real valuation of a Laurent series is its order, cast to the reals. -/
@[simp]
theorem realAddVal_apply (f : R⸨X⸩) :
    realAddVal R f = f.orderTop.map ((↑) : ℤ → ℝ) := by
  rw [← HahnSeries.addVal_apply (Γ := ℤ)]
  -- By construction, `realAddVal R` is `HahnSeries.addVal ℤ R` followed by `WithTop.map`.
  rfl

/-- The real valuation of a nonzero Laurent series is its order. -/
theorem realAddVal_of_ne_zero {f : R⸨X⸩} (hf : f ≠ 0) :
    realAddVal R f = ((f.order : ℝ) : WithTop ℝ) := by
  rw [realAddVal_apply, ← order_eq_orderTop_of_ne_zero hf, WithTop.map_coe]

/-- Only the zero Laurent series has infinite valuation. -/
theorem realAddVal_eq_top_iff {f : R⸨X⸩} : realAddVal R f = ⊤ ↔ f = 0 := by
  simp

/-- The monomial `r Xⁿ`, for `r ≠ 0`, has valuation `n`; in particular `X` has valuation one. -/
theorem realAddVal_single (n : ℤ) {r : R} (hr : r ≠ 0) :
    realAddVal R (single n r) = ((n : ℝ) : WithTop ℝ) := by
  rw [realAddVal_apply, orderTop_single hr, WithTop.map_coe]

/-- A Laurent series with a nonzero coefficient at `k` has valuation at most `k`. -/
theorem realAddVal_le_of_coeff_ne_zero {f : R⸨X⸩} {k : ℤ} (hk : f.coeff k ≠ 0) :
    realAddVal R f ≤ ((k : ℝ) : WithTop ℝ) := by
  rw [realAddVal_of_ne_zero (ne_zero_of_coeff_ne_zero hk), WithTop.coe_le_coe, Int.cast_le]
  exact order_le_of_coeff_ne_zero hk

/-! ### Coefficients at real exponents -/

section coeffReal

variable {R : Type*} [Ring R]

open Classical in
/-- The coefficient of a Laurent series at a real exponent: `f.coeff k` at the integer `k`, and
`0` at a non-integer exponent. -/
private noncomputable def coeffReal (f : R⸨X⸩) (r : ℝ) : R :=
  if h : ∃ k : ℤ, (k : ℝ) = r then f.coeff h.choose else 0

private theorem coeffReal_intCast (f : R⸨X⸩) (k : ℤ) : coeffReal f k = f.coeff k := by
  rw [coeffReal]
  split_ifs with h
  · rw [Int.cast_inj.mp h.choose_spec]
  · exact absurd ⟨k, rfl⟩ h

private theorem coeffReal_of_not_exists {r : ℝ} (hr : ¬∃ k : ℤ, (k : ℝ) = r) (f : R⸨X⸩) :
    coeffReal f r = 0 := by
  rw [coeffReal]
  split_ifs
  rfl

private theorem coeffReal_sum {ι : Type*} (s : Finset ι) (f : ι → R⸨X⸩) (r : ℝ) :
    coeffReal (∑ i ∈ s, f i) r = ∑ i ∈ s, coeffReal (f i) r := by
  by_cases hr : ∃ k : ℤ, (k : ℝ) = r
  · obtain ⟨k, rfl⟩ := hr
    simp only [coeffReal_intCast, coeff_sum]
  · simp only [coeffReal_of_not_exists hr, Finset.sum_const_zero]

/-- If `f` and `g` are supported at exponents at least `α` and `β`, the coefficient of `f * g`
at `α + β` is the product of the coefficients at `α` and `β`. -/
private theorem coeffReal_mul {f g : R⸨X⸩} {α β : ℝ}
    (hf : ∀ k : ℤ, f.coeff k ≠ 0 → α ≤ k) (hg : ∀ k : ℤ, g.coeff k ≠ 0 → β ≤ k) :
    coeffReal (f * g) (α + β) = coeffReal f α * coeffReal g β := by
  by_cases hab : (∃ a : ℤ, (a : ℝ) = α) ∧ ∃ b : ℤ, (b : ℝ) = β
  · obtain ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩ := hab
    rw [← Int.cast_add, coeffReal_intCast, coeffReal_intCast, coeffReal_intCast, coeff_mul]
    by_cases hmem : (a, b) ∈ Finset.antidiagonal f.isPWO_support g.isPWO_support (a + b)
    · refine Finset.sum_eq_single_of_mem _ hmem fun ij hij hne => ?_
      obtain ⟨hi, hj, hsum⟩ := Finset.mem_antidiagonal.mp hij
      have hai := Int.cast_le.mp (hf _ hi)
      have hbj := Int.cast_le.mp (hg _ hj)
      exact absurd (Prod.ext (by omega) (by omega)) hne
    · rw [Finset.sum_eq_zero fun ij hij => ?_]
      · rcases eq_or_ne (f.coeff a) 0 with ha | ha
        · rw [ha, zero_mul]
        rcases eq_or_ne (g.coeff b) 0 with hb | hb
        · rw [hb, mul_zero]
        exact absurd (Finset.mem_antidiagonal.mpr ⟨ha, hb, rfl⟩) hmem
      obtain ⟨hi, hj, hsum⟩ := Finset.mem_antidiagonal.mp hij
      have hai := Int.cast_le.mp (hf _ hi)
      have hbj := Int.cast_le.mp (hg _ hj)
      exact absurd (Prod.ext (by omega) (by omega) : ij = (a, b)) (by rintro rfl; exact hmem hij)
  · have hzero : coeffReal f α * coeffReal g β = 0 := by
      rcases not_and_or.mp hab with ha | hb
      · rw [coeffReal_of_not_exists ha, zero_mul]
      · rw [coeffReal_of_not_exists hb, mul_zero]
    rw [hzero]
    by_cases hk : ∃ k : ℤ, (k : ℝ) = α + β
    · obtain ⟨k, hk⟩ := hk
      rw [← hk, coeffReal_intCast, coeff_mul]
      refine Finset.sum_eq_zero fun ij hij => ?_
      obtain ⟨hi, hj, hsum⟩ := Finset.mem_antidiagonal.mp hij
      have hai := hf _ hi
      have hbj := hg _ hj
      have hsum' : (ij.1 : ℝ) + ij.2 = α + β := by rw [← hk, ← hsum, Int.cast_add]
      exact absurd ⟨⟨ij.1, by linarith⟩, ⟨ij.2, by linarith⟩⟩ hab
    · exact coeffReal_of_not_exists hk _

end coeffReal

end TauCeti.LaurentSeries

namespace Polynomial

open TauCeti.LaurentSeries

variable {R : Type*} [Ring R] [IsDomain R]

/-- The initial polynomial of a polynomial `P = ∑ aₙ Yⁿ` over `R⸨X⸩` at the real slope `σ`.
It is the sum of the monomials `lc(aₙ) Yⁿ` over the indices `n` at which the tilted height
`ord(aₙ) - σ n` equals the supporting value, the minimum of all tilted heights; these are the
indices at which the coefficient heights touch the supporting line of slope `σ`. The initial
polynomial of `0` is `0`. -/
noncomputable def initialPolynomial (P : R⸨X⸩[X]) (σ : ℝ) : R[X] :=
  ∑ n ∈ P.support with (realAddVal R (P.coeff n)).toEReal - ((σ * n : ℝ) : EReal) =
      supportingValue (fun m => realAddVal R (P.coeff m)) σ,
    monomial n (P.coeff n).leadingCoeff

/-- The `n`-th coefficient of the initial polynomial at slope `σ` is the leading coefficient of
`aₙ` when the tilted height `ord(aₙ) - σ n` is the supporting value at `σ`, and zero
otherwise. -/
theorem coeff_initialPolynomial (P : R⸨X⸩[X]) (σ : ℝ) (n : ℕ) :
    (P.initialPolynomial σ).coeff n =
      if (realAddVal R (P.coeff n)).toEReal - ((σ * n : ℝ) : EReal) =
          supportingValue (fun m => realAddVal R (P.coeff m)) σ then
        (P.coeff n).leadingCoeff
      else 0 := by
  rw [initialPolynomial, Finset.sum_filter, finsetSum_coeff, Finset.sum_eq_single n]
  · split_ifs <;> simp
  · intro m _ hmn
    split_ifs <;> simp [coeff_monomial, hmn]
  · intro hn
    rw [notMem_support_iff.mp hn]
    split_ifs <;> simp

/-- The initial polynomial of the zero polynomial is zero. -/
@[simp]
theorem initialPolynomial_zero (σ : ℝ) : (0 : R⸨X⸩[X]).initialPolynomial σ = 0 := by
  simp [initialPolynomial]

variable {P Q : R⸨X⸩[X]} {σ : ℝ}

/-- The coefficient heights of a nonzero polynomial over Laurent series have a finite
supporting value at every slope. -/
private theorem supportingValue_ne_top_ne_bot (hP : P ≠ 0) :
    supportingValue (fun n => realAddVal R (P.coeff n)) σ ≠ ⊤ ∧
      supportingValue (fun n => realAddVal R (P.coeff n)) σ ≠ ⊥ := by
  refine ⟨fun h => hP ?_, supportingValue_ne_bot_of_finite
    (finite_setOf_addValuation_coeff_ne_top P _) σ⟩
  refine Polynomial.ext fun n => ?_
  simpa using congrFun (supportingValue_eq_top_iff.mp h) n

/-- The real supporting value of the coefficient heights of `P` at slope `σ`. -/
private noncomputable def intercept (P : R⸨X⸩[X]) (σ : ℝ) : ℝ :=
  (supportingValue (fun n => realAddVal R (P.coeff n)) σ).toReal

private theorem coe_intercept (hP : P ≠ 0) :
    (intercept P σ : EReal) = supportingValue (fun n => realAddVal R (P.coeff n)) σ :=
  EReal.coe_toReal (supportingValue_ne_top_ne_bot hP).1 (supportingValue_ne_top_ne_bot hP).2

private theorem isSupportingLine_intercept (hP : P ≠ 0) :
    IsSupportingLine (fun n => realAddVal R (P.coeff n)) σ (intercept P σ) :=
  isSupportingLine_iff.mpr (coe_intercept hP).le

/-- For `P ≠ 0`, a tilted height equals the supporting value exactly when the height lies on
the supporting line. -/
private theorem sub_eq_supportingValue_iff (hP : P ≠ 0) (n : ℕ) :
    (realAddVal R (P.coeff n)).toEReal - ((σ * n : ℝ) : EReal) =
        supportingValue (fun m => realAddVal R (P.coeff m)) σ ↔
      realAddVal R (P.coeff n) = ((intercept P σ + σ * n : ℝ) : WithTop ℝ) := by
  rw [← coe_intercept hP]
  cases h : realAddVal R (P.coeff n) with
  | top =>
    rw [WithTop.toEReal_top, EReal.top_sub_coe]
    exact iff_of_false (EReal.top_ne_coe _) WithTop.top_ne_coe
  | coe x =>
    rw [WithTop.toEReal_coe, ← EReal.coe_sub, EReal.coe_eq_coe_iff, WithTop.coe_eq_coe]
    constructor <;> intro h <;> linarith

/-- On a supporting line of `P ≠ 0`, every exponent of a coefficient of `P` lies above the
line. -/
private theorem le_of_coeff_ne_zero (hP : P ≠ 0) (i : ℕ) :
    ∀ k : ℤ, (P.coeff i).coeff k ≠ 0 → intercept P σ + σ * i ≤ k := fun _ hk =>
  WithTop.coe_le_coe.mp ((isSupportingLine_iff_forall.mp (isSupportingLine_intercept hP) i).trans
    (realAddVal_le_of_coeff_ne_zero hk))

/-- For `P ≠ 0`, the `n`-th coefficient of the initial polynomial is the coefficient of `aₙ` at
the real exponent where the supporting line meets the vertical line through `n`. -/
private theorem coeff_initialPolynomial_eq_coeffReal (hP : P ≠ 0) (n : ℕ) :
    (P.initialPolynomial σ).coeff n = coeffReal (P.coeff n) (intercept P σ + σ * n) := by
  rw [coeff_initialPolynomial]
  split_ifs with h
  · rw [sub_eq_supportingValue_iff hP] at h
    have hne : P.coeff n ≠ 0 := by
      intro h0
      rw [h0, AddValuation.map_zero] at h
      exact WithTop.top_ne_coe h
    rw [realAddVal_of_ne_zero hne, WithTop.coe_eq_coe] at h
    rw [← h, coeffReal_intCast, leadingCoeff_eq]
  · rw [sub_eq_supportingValue_iff hP] at h
    by_cases hk : ∃ k : ℤ, (k : ℝ) = intercept P σ + σ * n
    · obtain ⟨k, hk⟩ := hk
      rw [← hk, coeffReal_intCast]
      by_contra hc
      refine h (le_antisymm ?_
        (isSupportingLine_iff_forall.mp (isSupportingLine_intercept hP) n))
      rw [← hk]
      exact realAddVal_le_of_coeff_ne_zero (Ne.symm hc)
    · rw [coeffReal_of_not_exists hk]

variable (σ) in
/-- A nonzero polynomial has a nonzero initial polynomial at every slope: the coefficient
heights touch each supporting line. -/
theorem initialPolynomial_ne_zero (hP : P ≠ 0) : P.initialPolynomial σ ≠ 0 := by
  have hne : {n | realAddVal R (P.coeff n) ≠ ⊤}.Nonempty := by
    obtain ⟨n, hn⟩ := not_forall.mp (mt Polynomial.ext hP)
    exact ⟨n, by simpa using hn⟩
  obtain ⟨c, i, hc, hi⟩ := exists_isSupportingLine_isLeast_supportingFace
    (finite_setOf_addValuation_coeff_ne_top P _) hne σ
  have hci : intercept P σ = c := EReal.coe_eq_coe_iff.mp
    ((coe_intercept hP).trans (supportingValue_eq_coe_of_mem_supportingFace hc hi.1))
  have hPi : P.coeff i ≠ 0 := by
    intro h0
    have := mem_supportingFace.mp hi.1
    rw [h0, AddValuation.map_zero] at this
    exact WithTop.top_ne_coe this
  intro h0
  have hcoeff := congrArg (fun F : R[X] => F.coeff i) h0
  simp only [coeff_initialPolynomial, coeff_zero] at hcoeff
  rw [ite_eq_left ((sub_eq_supportingValue_iff hP i).mpr (hci ▸ mem_supportingFace.mp hi.1))]
    at hcoeff
  exact hPi (HahnSeries.leadingCoeff_eq_zero.mp hcoeff)

/-- The initial polynomial of a monomial `a Yⁿ` is `lc(a) Yⁿ`, at every slope. -/
@[simp]
theorem initialPolynomial_monomial (n : ℕ) (a : R⸨X⸩) (σ : ℝ) :
    (monomial n a).initialPolynomial σ = monomial n a.leadingCoeff := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  have hface : n ∈ supportingFace (fun m => realAddVal R ((monomial n a).coeff m)) σ
      (a.order - σ * n) := by
    rw [mem_supportingFace, coeff_monomial, ite_eq_left rfl, realAddVal_of_ne_zero ha,
      sub_add_cancel]
  have hline : IsSupportingLine (fun m => realAddVal R ((monomial n a).coeff m)) σ
      (a.order - σ * n) := isSupportingLine_iff_forall.mpr fun m => by
    rcases eq_or_ne n m with rfl | hnm
    · exact (mem_supportingFace.mp hface).ge
    · simp [coeff_monomial, hnm]
  have hsv := supportingValue_eq_coe_of_mem_supportingFace hline hface
  refine Polynomial.ext fun m => ?_
  rw [coeff_initialPolynomial, hsv]
  rcases eq_or_ne n m with rfl | hnm
  · simp only [coeff_monomial, realAddVal_of_ne_zero ha, WithTop.toEReal_coe, ← EReal.coe_sub,
      ite_true]
  · simp [coeff_monomial, hnm]

/-- The initial polynomial vanishes exactly for the zero polynomial. -/
@[simp]
theorem initialPolynomial_eq_zero_iff : P.initialPolynomial σ = 0 ↔ P = 0 :=
  ⟨fun h => by_contra fun hP => initialPolynomial_ne_zero σ hP h,
    fun h => h ▸ initialPolynomial_zero σ⟩

/-- The initial polynomial of a constant `a` is the constant `lc(a)`. -/
@[simp]
theorem initialPolynomial_C (a : R⸨X⸩) (σ : ℝ) :
    (C a).initialPolynomial σ = C a.leadingCoeff := by
  simp only [← monomial_zero_left, initialPolynomial_monomial]

/-- The initial polynomial of `1` is `1`. -/
@[simp]
theorem initialPolynomial_one (σ : ℝ) : (1 : R⸨X⸩[X]).initialPolynomial σ = 1 := by
  rw [← C_1, initialPolynomial_C, HahnSeries.leadingCoeff_one, C_1]

/-- The initial polynomial of `Y` is `Y`. -/
@[simp]
theorem initialPolynomial_X (σ : ℝ) : (X : R⸨X⸩[X]).initialPolynomial σ = X := by
  rw [← monomial_one_one_eq_X, initialPolynomial_monomial, HahnSeries.leadingCoeff_one,
    monomial_one_one_eq_X]

/-- Taking initial polynomials is multiplicative: at every slope `σ`, the initial polynomial of
`P * Q` is the product of the initial polynomials of `P` and `Q`. -/
@[simp]
theorem initialPolynomial_mul (P Q : R⸨X⸩[X]) (σ : ℝ) :
    (P * Q).initialPolynomial σ = P.initialPolynomial σ * Q.initialPolynomial σ := by
  rcases eq_or_ne P 0 with rfl | hP
  · simp
  rcases eq_or_ne Q 0 with rfl | hQ
  · simp
  have hPQ : P * Q ≠ 0 := mul_ne_zero hP hQ
  -- The supporting values of the coefficient heights add under multiplication.
  have hc : intercept (P * Q) σ = intercept P σ + intercept Q σ := by
    have := supportingValue_addValuation_coeff_mul P Q (realAddVal R) σ
    rw [← coe_intercept hPQ, ← coe_intercept hP, ← coe_intercept hQ, ← EReal.coe_add] at this
    exact EReal.coe_eq_coe_iff.mp this
  refine Polynomial.ext fun n => ?_
  rw [coeff_initialPolynomial_eq_coeffReal hPQ, Polynomial.coeff_mul, Polynomial.coeff_mul,
    coeffReal_sum, hc]
  refine Finset.sum_congr rfl fun ij hij => ?_
  rw [coeff_initialPolynomial_eq_coeffReal hP, coeff_initialPolynomial_eq_coeffReal hQ,
    ← coeffReal_mul (le_of_coeff_ne_zero hP _) (le_of_coeff_ne_zero hQ _)]
  congr 1
  rw [← Finset.HasAntidiagonal.mem_antidiagonal.mp hij, Nat.cast_add]
  ring

variable (R) in
/-- Taking initial polynomials at the slope `σ`, as a monoid homomorphism. -/
noncomputable def initialPolynomialHom (σ : ℝ) : R⸨X⸩[X] →* R[X] where
  toFun P := P.initialPolynomial σ
  map_one' := initialPolynomial_one σ
  map_mul' P Q := initialPolynomial_mul P Q σ

/-- The monoid homomorphism `initialPolynomialHom R σ` sends `P` to its initial polynomial. -/
@[simp]
theorem initialPolynomialHom_apply (P : R⸨X⸩[X]) (σ : ℝ) :
    initialPolynomialHom R σ P = P.initialPolynomial σ :=
  (rfl)

/-- The initial polynomial of a power is the power of the initial polynomial. -/
@[simp]
theorem initialPolynomial_pow (P : R⸨X⸩[X]) (k : ℕ) (σ : ℝ) :
    (P ^ k).initialPolynomial σ = P.initialPolynomial σ ^ k :=
  map_pow (initialPolynomialHom R σ) P k

end Polynomial

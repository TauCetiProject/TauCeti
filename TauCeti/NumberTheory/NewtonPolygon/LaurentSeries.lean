/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NewtonPolygon.Mul
public import TauCeti.RingTheory.HahnSeries.Multiplication
public import TauCeti.RingTheory.LaurentSeries.Valuation.Basic
import TauCeti.Analysis.Convex.Sequence.Vertex

/-!
# Newton polygons and initial polynomials over Laurent series

For a domain `R`, the order of vanishing `ord = HahnSeries.orderTop` on `R⸨X⸩`, with
`ord(0) = ⊤` and `ord(X) = 1`, is the real additive valuation
`LaurentSeries.realAddVal R`. The general Newton-polygon API, `Polynomial.newtonPolygon`
together with its slope multisets and the Minkowski-sum formula
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
characteristic hypothesis is used. The proof reads coefficients at the real exponents where
supporting lines cross, through the embedding `HahnSeries.embDomainRingHom` of `R⸨X⸩` into the
Hahn series with real exponents.

The initial polynomial at `σ` also records the face of slope `σ` of the Newton polygon. If that
face runs from `l` to `u`, the initial polynomial has order of vanishing `l` at `Y = 0` and
degree `u`, with extreme coefficients `lc(a_l)` and `lc(a_u)`. So the multiplicity of `σ` as a
slope, which for a split polynomial counts its roots of order `-σ`, is the degree minus the
order of vanishing of the initial polynomial at `σ`.

## Main definitions

* `Polynomial.initialPolynomial P σ`: the initial polynomial of `P` at slope `σ`.
* `Polynomial.initialPolynomialHom R σ`: the initial polynomial at slope `σ` as a monoid
  homomorphism `R⸨X⸩[Y] →* R[Y]`.

## Main results

* `Polynomial.coeff_initialPolynomial`: the coefficients of the initial polynomial.
* `Polynomial.initialPolynomial_eq_zero_iff`: only the zero polynomial has initial polynomial
  zero, at any slope.
* `Polynomial.initialPolynomial_monomial`: the initial polynomial of `a Yⁿ` is `lc(a) Yⁿ`.
* `Polynomial.initialPolynomial_mul`: initial polynomials are multiplicative.
* `Polynomial.natTrailingDegree_initialPolynomial_of_isFiniteFace` and
  `Polynomial.natDegree_initialPolynomial_of_isFiniteFace`: the order of vanishing at `Y = 0` and
  the degree of the initial polynomial at `σ` are the endpoints of the face of slope `σ`.
* `Polynomial.trailingCoeff_initialPolynomial_of_isFiniteFace` and
  `Polynomial.leadingCoeff_initialPolynomial_of_isFiniteFace`: its extreme coefficients are the
  leading coefficients of the coefficients of `P` at these endpoints.
* `Polynomial.natTrailingDegree_initialPolynomial` and `Polynomial.natDegree_initialPolynomial`:
  the same endpoints counted by slopes, as the order of vanishing of `P` at `Y = 0` plus the
  number of slopes below `σ`, respectively at most `σ`.
* `Polynomial.count_newtonSlopes_eq_natDegree_sub_natTrailingDegree_initialPolynomial`: the
  multiplicity of a slope `σ` is the degree minus the order of vanishing at `Y = 0` of the
  initial polynomial at `σ`.

## References

* S. Mannaa and T. Coquand, *Dynamic Newton–Puiseux Theorem*, J. Logic & Analysis 5 (2013),
  §1.
* M. Lazard, *Les zéros d'une fonction analytique d'une variable sur un corps valué complet*,
  Publications Mathématiques de l'IHÉS 14 (1962), §1, Proposition 1.
-/

public section

open HahnSeries LaurentSeries TauCeti
open scoped LaurentSeries

namespace Polynomial

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

/-- On a supporting line of `P ≠ 0`, every exponent of a coefficient of `P`, read in the Hahn
series with real exponents, lies above the line. -/
private theorem le_of_mem_support_embDomainRingHom (hP : P ≠ 0) (i : ℕ) :
    ∀ r ∈ (embDomainRingHom (Int.castAddHom ℝ) Int.cast_injective (fun _ _ => Int.cast_le)
      (P.coeff i)).support, intercept P σ + σ * i ≤ r := fun _ hr => by
  obtain ⟨k, hk, rfl⟩ := support_embDomain_subset hr
  exact WithTop.coe_le_coe.mp ((isSupportingLine_iff_forall.mp (isSupportingLine_intercept hP)
    i).trans (realAddVal_le_of_coeff_ne_zero hk))

/-- For `P ≠ 0`, the `n`-th coefficient of the initial polynomial is the coefficient of `aₙ` at
the real exponent where the supporting line meets the vertical line through `n`. -/
private theorem coeff_initialPolynomial_eq_coeff_embDomainRingHom (hP : P ≠ 0) (n : ℕ) :
    (P.initialPolynomial σ).coeff n =
      (embDomainRingHom (Int.castAddHom ℝ) Int.cast_injective (fun _ _ => Int.cast_le)
        (P.coeff n)).coeff (intercept P σ + σ * n) := by
  rw [coeff_initialPolynomial]
  split_ifs with h
  · rw [sub_eq_supportingValue_iff hP] at h
    have hne : P.coeff n ≠ 0 := by
      intro h0
      rw [h0, AddValuation.map_zero] at h
      exact WithTop.top_ne_coe h
    rw [realAddVal_of_ne_zero hne, WithTop.coe_eq_coe] at h
    rw [← h, leadingCoeff_eq]
    exact embDomain_coeff.symm
  · rw [sub_eq_supportingValue_iff hP] at h
    by_cases hk : ∃ k : ℤ, (k : ℝ) = intercept P σ + σ * n
    · obtain ⟨k, hk⟩ := hk
      rw [← hk]
      refine (embDomain_coeff.trans ?_).symm
      by_contra hc
      refine h (le_antisymm ?_
        (isSupportingLine_iff_forall.mp (isSupportingLine_intercept hP) n))
      rw [← hk]
      exact realAddVal_le_of_coeff_ne_zero hc
    · exact (embDomain_of_notMem_range hk).symm

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
  rw [coeff_initialPolynomial_eq_coeff_embDomainRingHom hPQ, Polynomial.coeff_mul,
    Polynomial.coeff_mul, map_sum, HahnSeries.coeff_sum, hc]
  refine Finset.sum_congr rfl fun ij hij => ?_
  rw [coeff_initialPolynomial_eq_coeff_embDomainRingHom hP,
    coeff_initialPolynomial_eq_coeff_embDomainRingHom hQ,
    ← coeff_mul_add_of_forall_le (le_of_mem_support_embDomainRingHom hP _)
      (le_of_mem_support_embDomainRingHom hQ _), ← map_mul]
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

/-! ### Initial polynomials and faces of the Newton polygon -/

section Face

variable {l u : ℕ}

/-- For `P ≠ 0`, the `n`-th coefficient of the initial polynomial at `σ` is nonzero exactly when
the height of `aₙ` lies on the supporting line of slope `σ`. -/
private theorem coeff_initialPolynomial_ne_zero_iff (hP : P ≠ 0) (n : ℕ) :
    (P.initialPolynomial σ).coeff n ≠ 0 ↔
      n ∈ supportingFace (fun m => realAddVal R (P.coeff m)) σ (intercept P σ) := by
  rw [mem_supportingFace, ← sub_eq_supportingValue_iff hP, coeff_initialPolynomial]
  split_ifs with h
  · refine iff_of_true (fun h0 => ?_) h
    rw [sub_eq_supportingValue_iff hP, HahnSeries.leadingCoeff_eq_zero.mp h0,
      AddValuation.map_zero] at h
    exact WithTop.top_ne_coe h
  · exact iff_of_false (fun h0 => h0 rfl) h

/-- A polynomial whose Newton polygon has a finite face is nonzero. -/
private theorem ne_zero_of_isFiniteFace
    (hface : IsFiniteFace (P.newtonPolygon (realAddVal R)) σ l u) : P ≠ 0 := by
  rintro rfl
  exact hface.left_ne_top (by simp)

/-- If the Newton polygon of `P` has the finite face `[l, u]` of slope `σ`, the coefficient
heights of `P` touch their supporting line of slope `σ` only inside `[l, u]`, and at both
endpoints. -/
private theorem supportingFace_intercept_of_isFiniteFace
    (hface : IsFiniteFace (P.newtonPolygon (realAddVal R)) σ l u) :
    supportingFace (fun n => realAddVal R (P.coeff n)) σ (intercept P σ) ⊆ Set.Icc l u ∧
      l ∈ supportingFace (fun n => realAddVal R (P.coeff n)) σ (intercept P σ) ∧
      u ∈ supportingFace (fun n => realAddVal R (P.coeff n)) σ (intercept P σ) := by
  have hP := ne_zero_of_isFiniteFace hface
  have hh := isLowerConvexEnvelope_newtonPolygon P (realAddVal R)
  obtain ⟨c, hc, hfc⟩ := hface.exists_intercept
  have hl : l ∈ Set.Icc l u := ⟨le_rfl, hface.left_le_right⟩
  have hu : u ∈ Set.Icc l u := ⟨hface.left_le_right, le_rfl⟩
  -- The supporting line of the coefficient heights is the line of the face.
  obtain rfl : intercept P σ = c := EReal.coe_injective <| by
    rw [coe_intercept hP, ← supportingValue_newtonPolygon P (realAddVal R),
      supportingValue_eq_coe_of_mem_supportingFace hc (hfc.symm.subset hl)]
  refine ⟨(hh.supportingFace_subset (isSupportingLine_intercept hP)).trans hfc.subset, ?_, ?_⟩
  · rw [mem_supportingFace, ← hh.eq_left_of_isFiniteFace hface]
    exact mem_supportingFace.mp (hfc.symm.subset hl)
  · rw [mem_supportingFace, ← hh.eq_right_of_isFiniteFace hface]
    exact mem_supportingFace.mp (hfc.symm.subset hu)

/-- If the Newton polygon of `P` has the finite face `[l, u]` of slope `σ`, the initial
polynomial of `P` at `σ` is supported in `[l, u]`. -/
theorem support_initialPolynomial_subset_Icc
    (hface : IsFiniteFace (P.newtonPolygon (realAddVal R)) σ l u) :
    (P.initialPolynomial σ).support ⊆ Finset.Icc l u := fun n hn =>
  Finset.mem_Icc.mpr <| (supportingFace_intercept_of_isFiniteFace hface).1 <|
    (coeff_initialPolynomial_ne_zero_iff (ne_zero_of_isFiniteFace hface) n).mp
      (mem_support_iff.mp hn)

/-- If the Newton polygon of `P` has the finite face `[l, u]` of slope `σ`, the initial
polynomial of `P` at `σ` vanishes at `Y = 0` to order exactly `l`. -/
theorem natTrailingDegree_initialPolynomial_of_isFiniteFace
    (hface : IsFiniteFace (P.newtonPolygon (realAddVal R)) σ l u) :
    (P.initialPolynomial σ).natTrailingDegree = l := by
  have hP := ne_zero_of_isFiniteFace hface
  refine le_antisymm (natTrailingDegree_le_of_ne_zero <|
    (coeff_initialPolynomial_ne_zero_iff hP l).mpr
      (supportingFace_intercept_of_isFiniteFace hface).2.1) ?_
  exact (Finset.mem_Icc.mp <| support_initialPolynomial_subset_Icc hface <|
    natTrailingDegree_mem_support_of_nonzero (initialPolynomial_ne_zero σ hP)).1

/-- If the Newton polygon of `P` has the finite face `[l, u]` of slope `σ`, the initial
polynomial of `P` at `σ` has degree exactly `u`. -/
theorem natDegree_initialPolynomial_of_isFiniteFace
    (hface : IsFiniteFace (P.newtonPolygon (realAddVal R)) σ l u) :
    (P.initialPolynomial σ).natDegree = u := by
  have hP := ne_zero_of_isFiniteFace hface
  refine le_antisymm ?_ (le_natDegree_of_ne_zero <|
    (coeff_initialPolynomial_ne_zero_iff hP u).mpr
      (supportingFace_intercept_of_isFiniteFace hface).2.2)
  exact (Finset.mem_Icc.mp <| support_initialPolynomial_subset_Icc hface <|
    natDegree_mem_support_of_nonzero (initialPolynomial_ne_zero σ hP)).2

/-- If the Newton polygon of `P` has the finite face `[l, u]` of slope `σ`, the trailing
coefficient of the initial polynomial of `P` at `σ` is the leading coefficient of `a_l`. -/
theorem trailingCoeff_initialPolynomial_of_isFiniteFace
    (hface : IsFiniteFace (P.newtonPolygon (realAddVal R)) σ l u) :
    (P.initialPolynomial σ).trailingCoeff = (P.coeff l).leadingCoeff := by
  rw [trailingCoeff, natTrailingDegree_initialPolynomial_of_isFiniteFace hface,
    coeff_initialPolynomial, ite_eq_left <| (sub_eq_supportingValue_iff
      (ne_zero_of_isFiniteFace hface) l).mpr <|
        mem_supportingFace.mp (supportingFace_intercept_of_isFiniteFace hface).2.1]

/-- If the Newton polygon of `P` has the finite face `[l, u]` of slope `σ`, the leading
coefficient of the initial polynomial of `P` at `σ` is the leading coefficient of `a_u`. -/
theorem leadingCoeff_initialPolynomial_of_isFiniteFace
    (hface : IsFiniteFace (P.newtonPolygon (realAddVal R)) σ l u) :
    (P.initialPolynomial σ).leadingCoeff = (P.coeff u).leadingCoeff := by
  rw [Polynomial.leadingCoeff, natDegree_initialPolynomial_of_isFiniteFace hface,
    coeff_initialPolynomial, ite_eq_left <| (sub_eq_supportingValue_iff
      (ne_zero_of_isFiniteFace hface) u).mpr <|
        mem_supportingFace.mp (supportingFace_intercept_of_isFiniteFace hface).2.2]

variable (σ) in
/-- The Newton polygon of a nonzero polynomial over `R⸨X⸩` has a finite face of every slope. -/
private theorem exists_isFiniteFace_newtonPolygon_realAddVal (hP : P ≠ 0) :
    ∃ l u : ℕ, IsFiniteFace (P.newtonPolygon (realAddVal R)) σ l u :=
  exists_isFiniteFace_newtonPolygon
    (newtonPolygon_ne_top_of_ne_zero (fun _ => realAddVal_eq_top_iff.mp) hP) σ

variable (P σ)

/-- The order of vanishing at `Y = 0` of the initial polynomial of `P` at slope `σ` is that of
`P` plus the number of slopes of the Newton polygon of `P` below `σ`. -/
theorem natTrailingDegree_initialPolynomial :
    (P.initialPolynomial σ).natTrailingDegree =
      P.natTrailingDegree + ((P.newtonSlopes (realAddVal R)).filter (· < σ)).card := by
  rcases eq_or_ne P 0 with rfl | hP
  · simp
  obtain ⟨l, u, hface⟩ := exists_isFiniteFace_newtonPolygon_realAddVal σ hP
  rw [natTrailingDegree_initialPolynomial_of_isFiniteFace hface]
  exact left_eq_natTrailingDegree_add_card_filter_newtonSlopes_lt
    (fun _ => realAddVal_eq_top_iff.mp) hface

/-- The degree of the initial polynomial of `P` at slope `σ` is the order of vanishing of `P`
at `Y = 0` plus the number of slopes of the Newton polygon of `P` at most `σ`. -/
theorem natDegree_initialPolynomial :
    (P.initialPolynomial σ).natDegree =
      P.natTrailingDegree + ((P.newtonSlopes (realAddVal R)).filter (· ≤ σ)).card := by
  rcases eq_or_ne P 0 with rfl | hP
  · simp
  obtain ⟨l, u, hface⟩ := exists_isFiniteFace_newtonPolygon_realAddVal σ hP
  rw [natDegree_initialPolynomial_of_isFiniteFace hface]
  exact right_eq_natTrailingDegree_add_card_filter_newtonSlopes_le
    (fun _ => realAddVal_eq_top_iff.mp) hface

/-- The multiplicity of `σ` as a slope of the Newton polygon of `P` is the difference between
the degree of the initial polynomial of `P` at `σ` and its order of vanishing at `Y = 0`. When
`P` splits, this is the number of roots of `P` of order `-σ`, counted with multiplicity, by
`Polynomial.newtonSlopes_eq_map_roots`. -/
theorem count_newtonSlopes_eq_natDegree_sub_natTrailingDegree_initialPolynomial :
    (P.newtonSlopes (realAddVal R)).count σ =
      (P.initialPolynomial σ).natDegree - (P.initialPolynomial σ).natTrailingDegree := by
  rcases eq_or_ne P 0 with rfl | hP
  · simp
  obtain ⟨l, u, hface⟩ := exists_isFiniteFace_newtonPolygon_realAddVal σ hP
  rw [count_newtonSlopes_of_isFiniteFace hface,
    natDegree_initialPolynomial_of_isFiniteFace hface,
    natTrailingDegree_initialPolynomial_of_isFiniteFace hface]

end Face

end Polynomial

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Archimedean.Defs
public import Mathlib.Algebra.Order.SuccPred
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Data.Finsupp.Lex
public import TauCeti.Algebra.Order.Ring.Synonym
public import TauCeti.Algebra.Polynomial.Coeff.Basic

/-!
# The colexicographic order on polynomials

For a semiring `R` with a partial order, two polynomials in `R[X]` are compared at the largest
degree at which their coefficients differ. This is the colexicographic order of their coefficient
sequences, put on the type synonym `Colex R[X]`; it is linear when the order on `R` is. For
`R = ℤ` it is the order on `ℤ[t]` with `t` infinitely large: `ℤ[t]` is the direct sum of the cyclic
groups `ℤ tⁿ`, ordered by its right lexicographic order, so a polynomial is positive exactly when
its leading coefficient is.

This makes `Colex ℤ[X]` a discretely ordered abelian group with least positive element `1`, in
which `t` exceeds every integer; it is not Archimedean. It is moreover an ordered ring.

## Main declarations

* `Polynomial.Colex.partialOrder`, `Polynomial.Colex.linearOrder`: the colexicographic order on
  `Colex R[X]`.
* `Polynomial.Colex.lt_iff`, `Polynomial.Colex.le_iff`: `x < y` exactly when `x` and `y` agree
  above some degree `i` and the coefficient of `x` at `i` is smaller.
* `Polynomial.Colex.pos_iff`, `Polynomial.Colex.nonneg_iff`, `Polynomial.Colex.lt_zero_iff`,
  `Polynomial.Colex.nonpos_iff`: a polynomial has the sign of its leading coefficient.
* `Polynomial.Colex.lt_iff_of_degree_lt`, `Polynomial.Colex.lt_iff_of_degree_gt`: between
  polynomials of different degrees, the sign of the leading coefficient of the one of larger degree
  decides the comparison.
* `Polynomial.Colex.isOrderedCancelAddMonoid`: the order is compatible with addition.
* `Polynomial.Colex.succAddOrder`, `Polynomial.Colex.predSubOrder`: if `succ a = a + 1` (resp.
  `pred a = a - 1`) in `R`, then `succ p = p + 1` (resp. `pred p = p - 1`) in `Colex R[X]`; in
  particular `1` is the least positive element of `Colex ℤ[X]`.
* `Polynomial.Colex.toColex_C_lt_toColex_X`: the variable is larger than every constant.
* `Polynomial.Colex.not_archimedean`: the order is not Archimedean.
* `Polynomial.Colex.isOrderedRing`, `Polynomial.Colex.isStrictOrderedRing`: the order is
  compatible with multiplication.

## Implementation notes

The order is pulled back from Mathlib's colexicographic order on `ℕ →₀ R` along the coefficient
map. Mathlib's lexicographic order on Hahn series `Lex R⟦Γ⟧` with `Γ = ℕᵒᵈ` describes an
isomorphic ordered ring on a different carrier; using `R[X]` itself keeps one type for `ℤ[t]` as
a ring of exponents and as an ordered group.

## References

* A. Myasnikov, V. Remeslennikov, D. Serbin, *Regular free length functions on Lyndon's free
  `ℤ[t]`-group `F^{ℤ[t]}`*, Contemp. Math. 378 (2005), 37–77, §2.3.
-/

public section

namespace Polynomial

namespace Colex

variable {R : Type*}

section Semiring

variable [Semiring R]

section PartialOrder

variable [PartialOrder R]

/-- The colexicographic order on `R[X]`: two polynomials are compared at the largest degree at
which their coefficients differ. It is pulled back from the colexicographic order on the
coefficient sequences `ℕ →₀ R`. -/
instance partialOrder : PartialOrder (Colex R[X]) :=
  PartialOrder.lift (fun p ↦ toColex (ofColex p).coeff)
    (toColex.injective.comp (AddMonoidAlgebra.coeff_injective.comp ofColex.injective))

/-- Two polynomials compare as their coefficients at the largest degree where they differ. -/
theorem lt_iff {x y : Colex R[X]} :
    x < y ↔ ∃ i, (∀ j, i < j → (ofColex x).coeff j = (ofColex y).coeff j) ∧
      (ofColex x).coeff i < (ofColex y).coeff i :=
  -- The order is defined as the colexicographic order of the coefficient sequences.
  Finsupp.Colex.lt_iff

/-- `x ≤ y` exactly when `x = y` or they compare as their coefficients at the largest degree where
they differ. -/
theorem le_iff {x y : Colex R[X]} :
    x ≤ y ↔ x = y ∨ ∃ i, (∀ j, i < j → (ofColex x).coeff j = (ofColex y).coeff j) ∧
      (ofColex x).coeff i < (ofColex y).coeff i := by
  rw [le_iff_eq_or_lt, lt_iff]

/-- Two polynomials compare as their coefficients at the largest degree where they differ. -/
theorem toColex_lt_toColex {p q : R[X]} :
    toColex p < toColex q ↔ ∃ i, (∀ j, i < j → p.coeff j = q.coeff j) ∧ p.coeff i < q.coeff i := by
  simp only [lt_iff, ofColex_toColex]

/-- `toColex p ≤ toColex q` exactly when `p = q` or they compare as their coefficients at the
largest degree where they differ. -/
theorem toColex_le_toColex {p q : R[X]} :
    toColex p ≤ toColex q ↔
      p = q ∨ ∃ i, (∀ j, i < j → p.coeff j = q.coeff j) ∧ p.coeff i < q.coeff i := by
  simp only [le_iff, ofColex_toColex, toColex_inj]

/-- If `x` has smaller degree than `y`, then `x < y` exactly when the leading coefficient of `y`
is positive. -/
theorem lt_iff_of_degree_lt {x y : Colex R[X]} (h : (ofColex x).degree < (ofColex y).degree) :
    x < y ↔ 0 < (ofColex y).leadingCoeff :=
  lt_iff.trans (exists_coeff_iff_of_degree_lt (fun a ↦ lt_irrefl a) h)

/-- If `x` has larger degree than `y`, then `x < y` exactly when the leading coefficient of `x`
is negative. -/
theorem lt_iff_of_degree_gt {x y : Colex R[X]} (h : (ofColex y).degree < (ofColex x).degree) :
    x < y ↔ (ofColex x).leadingCoeff < 0 :=
  lt_iff.trans <| (exists_congr fun _ ↦ and_congr_left' (forall₂_congr fun _ _ ↦ eq_comm)).trans
    (exists_coeff_iff_of_degree_lt (r := fun a b ↦ b < a) (fun a ↦ lt_irrefl a) h)

/-- A polynomial is positive exactly when its leading coefficient is. -/
@[simp, grind =]
theorem pos_iff {x : Colex R[X]} : 0 < x ↔ 0 < (ofColex x).leadingCoeff := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · exact lt_iff_of_degree_lt (by simpa [bot_lt_iff_ne_bot] using hx)

/-- A polynomial is negative exactly when its leading coefficient is. -/
@[simp, grind =]
theorem lt_zero_iff {x : Colex R[X]} : x < 0 ↔ (ofColex x).leadingCoeff < 0 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · exact lt_iff_of_degree_gt (by simpa [bot_lt_iff_ne_bot] using hx)

/-- A polynomial is nonnegative exactly when its leading coefficient is. -/
@[simp, grind =]
theorem nonneg_iff {x : Colex R[X]} : 0 ≤ x ↔ 0 ≤ (ofColex x).leadingCoeff := by
  simp [le_iff_lt_or_eq, eq_comm (a := (0 : R)), eq_comm (a := (0 : Colex R[X]))]

/-- A polynomial is nonpositive exactly when its leading coefficient is. -/
@[simp, grind =]
theorem nonpos_iff {x : Colex R[X]} : x ≤ 0 ↔ (ofColex x).leadingCoeff ≤ 0 := by
  simp [le_iff_lt_or_eq]

/-- The constant polynomials are ordered as `R`. -/
@[simp, grind =]
theorem toColex_C_lt_toColex_C {a b : R} : toColex (C a) < toColex (C b) ↔ a < b := by
  rw [toColex_lt_toColex]
  refine ⟨?_, fun h ↦ ⟨0, fun j hj ↦ by simp [coeff_C, hj.ne'], by simpa using h⟩⟩
  rintro ⟨_ | i, -, h⟩ <;> simp_all

/-- The constant polynomials are ordered as `R`. -/
@[simp, grind =]
theorem toColex_C_le_toColex_C {a b : R} : toColex (C a) ≤ toColex (C b) ↔ a ≤ b := by
  simp [le_iff_eq_or_lt]

/-- When `0 < 1` in `R`, the variable is larger than every constant polynomial. -/
@[simp, grind .]
theorem toColex_C_lt_toColex_X [ZeroLEOneClass R] [Nontrivial R] (a : R) :
    toColex (C a) < toColex (X : R[X]) :=
  (lt_iff_of_degree_lt <| by
    simpa using (degree_C_le (a := a)).trans_lt (zero_lt_one' (WithBot ℕ))).2 (by simp)

/-- When `0 < 1` in `R`, the variable is larger than `1`. -/
@[simp, grind .]
theorem one_lt_toColex_X [ZeroLEOneClass R] [Nontrivial R] : (1 : Colex R[X]) < toColex X := by
  simpa using toColex_C_lt_toColex_X (1 : R)

/-- When `0 < 1` in `R`, the variable is larger than every natural number. -/
@[simp, grind .]
theorem natCast_lt_toColex_X [ZeroLEOneClass R] [Nontrivial R] (n : ℕ) :
    (n : Colex R[X]) < toColex X := by
  simpa using toColex_C_lt_toColex_X (n : R)

/-- When `0 < 1` in `R`, the variable is larger than every numeral. -/
@[simp, grind .]
theorem ofNat_lt_toColex_X [ZeroLEOneClass R] [Nontrivial R] (n : ℕ) [n.AtLeastTwo] :
    (ofNat(n) : Colex R[X]) < toColex X := by
  simpa using natCast_lt_toColex_X (R := R) ofNat(n)

/-- When `0 ≤ 1` in `R`, also `0 ≤ 1` in `Colex R[X]`. -/
instance zeroLEOneClass [ZeroLEOneClass R] : ZeroLEOneClass (Colex R[X]) where
  zero_le_one := nonneg_iff.2 (by simp)

/-- The colexicographic order on `R[X]` is compatible with addition. -/
instance isOrderedCancelAddMonoid [IsOrderedCancelAddMonoid R] :
    IsOrderedCancelAddMonoid (Colex R[X]) :=
  -- The order on `Colex R[X]` is defined by pulling back along the coefficient map.
  Function.Injective.isOrderedCancelAddMonoid (fun p ↦ toColex (ofColex p).coeff)
    (fun _ _ ↦ by simp) .rfl

/-- Polynomials that agree in every positive degree compare as their constant terms. -/
theorem le_of_coeff_zero_le {x y : Colex R[X]}
    (h : ∀ j, 0 < j → (ofColex x).coeff j = (ofColex y).coeff j)
    (h0 : (ofColex x).coeff 0 ≤ (ofColex y).coeff 0) : x ≤ y := by
  rcases h0.lt_or_eq with h0 | h0
  · exact (lt_iff.2 ⟨0, h, h0⟩).le
  · exact (ofColex.injective (by ext j; rcases j with _ | j <;> grind)).le

/-- Let `x < y`, and let `x'` and `y'` agree with `x` and `y` in every positive degree. Then
`x' ≤ y'` provided the constant terms of `x'` and `y'` compare whenever those of `x` and `y`
decide `x < y`. -/
theorem le_of_lt_of_coeff_pos_eq {x y x' y' : Colex R[X]} (h : x < y)
    (hx : ∀ j, 0 < j → (ofColex x').coeff j = (ofColex x).coeff j)
    (hy : ∀ j, 0 < j → (ofColex y').coeff j = (ofColex y).coeff j)
    (h0 : (ofColex x).coeff 0 < (ofColex y).coeff 0 →
      (ofColex x').coeff 0 ≤ (ofColex y').coeff 0) : x' ≤ y' := by
  obtain ⟨i, hi, hlt⟩ := lt_iff.1 h
  rcases i.eq_zero_or_pos with rfl | hi0
  · exact le_of_coeff_zero_le (fun j hj ↦ by rw [hx j hj, hy j hj, hi j hj]) (h0 hlt)
  · refine (lt_iff.2 ⟨i, fun j hj ↦ ?_, ?_⟩).le
    · rw [hx j (hi0.trans hj), hy j (hi0.trans hj), hi j hj]
    · rwa [hx i hi0, hy i hi0]

/-- If `succ a = a + 1` in `R` and addition in `R` is left-cancellative, then `succ p = p + 1` in
`Colex R[X]`: the polynomial `p + 1` is the least polynomial larger than `p`. Cancellation cannot
be dropped: over `ℕ∞`, `C ⊤ + 1 = C ⊤` although `C ⊤ < X`. -/
noncomputable instance succAddOrder [SuccAddOrder R] [IsLeftCancelAdd R] :
    SuccAddOrder (Colex R[X]) :=
  -- Adding `1` changes only the constant coefficient.
  have hcoeff (x : Colex R[X]) (j : ℕ) (hj : 0 < j) :
      (ofColex (x + 1)).coeff j = (ofColex x).coeff j := by
    simp [coeff_one, hj.ne']
  have hle (x : Colex R[X]) : x ≤ x + 1 :=
    le_of_coeff_zero_le (fun j hj ↦ (hcoeff x j hj).symm)
      (by simpa [Order.succ_eq_add_one] using Order.le_succ ((ofColex x).coeff 0))
  { succ x := x + 1
    le_succ := hle
    max_of_succ_le {x} h := by
      have h1 : (1 : R) = 0 := by
        simpa using congrArg (·.coeff 0) (congrArg ofColex (h.antisymm (hle x)))
      have : Subsingleton R := subsingleton_of_zero_eq_one h1.symm
      have : Subsingleton (Colex R[X]) := ofColex.subsingleton
      exact fun y _ ↦ (Subsingleton.elim y x).le
    succ_le_of_lt h := le_of_lt_of_coeff_pos_eq h (hcoeff _) (fun _ _ ↦ rfl)
      fun h0 ↦ by simpa using Order.add_one_le_of_lt h0
    succ_eq_add_one _ := rfl }

/-- When `0 < 1` in `R`, the colexicographic order on `R[X]` is not Archimedean: no multiple of
`1` reaches `X`. -/
theorem not_archimedean [ZeroLEOneClass R] [Nontrivial R] : ¬ Archimedean (Colex R[X]) := by
  intro h
  obtain ⟨n, hn⟩ := Archimedean.arch (toColex (X : R[X])) (zero_lt_one' (Colex R[X]))
  exact (natCast_lt_toColex_X n).not_ge (by simpa using hn)

end PartialOrder

/-- The colexicographic order on `R[X]` is linear when the order on `R` is. -/
noncomputable instance linearOrder [LinearOrder R] : LinearOrder (Colex R[X]) where
  -- The order on `Colex R[X]` is defined by pulling back along the coefficient map.
  le_total x y := le_total (toColex (ofColex x).coeff) (toColex (ofColex y).coeff)
  toDecidableLE := Classical.decRel _

end Semiring

section Ring

variable [Ring R] [PartialOrder R]

/-- When `0 < 1` in `R`, the variable is larger than every integer. -/
@[simp, grind .]
theorem intCast_lt_toColex_X [ZeroLEOneClass R] [Nontrivial R] (n : ℤ) :
    (n : Colex R[X]) < toColex X := by
  simpa using toColex_C_lt_toColex_X (n : R)

/-- If `pred a = a - 1` in `R`, then `pred p = p - 1` in `Colex R[X]`: the polynomial `p - 1` is the
greatest polynomial smaller than `p`. -/
noncomputable instance predSubOrder [PredSubOrder R] : PredSubOrder (Colex R[X]) :=
  -- Subtracting `1` changes only the constant coefficient.
  have hcoeff (x : Colex R[X]) (j : ℕ) (hj : 0 < j) :
      (ofColex (x - 1)).coeff j = (ofColex x).coeff j := by
    simp [coeff_one, hj.ne']
  have hle (x : Colex R[X]) : x - 1 ≤ x :=
    le_of_coeff_zero_le (hcoeff x)
      (by simpa [Order.pred_eq_sub_one] using Order.pred_le ((ofColex x).coeff 0))
  { pred x := x - 1
    pred_le := hle
    min_of_le_pred {x} h := by
      have h1 : (1 : R) = 0 := by
        simpa using congrArg (·.coeff 0) (congrArg ofColex ((hle x).antisymm h))
      have : Subsingleton R := subsingleton_of_zero_eq_one h1.symm
      have : Subsingleton (Colex R[X]) := ofColex.subsingleton
      exact fun y _ ↦ (Subsingleton.elim x y).le
    le_pred_of_lt h := le_of_lt_of_coeff_pos_eq h (fun _ _ ↦ rfl) (hcoeff _)
      fun h0 ↦ by simpa using Order.le_sub_one_of_lt h0
    pred_eq_sub_one _ := rfl }

/-- When multiplication by nonnegative elements is monotone in `R` and `R` has no zero divisors,
the colexicographic order makes `R[X]` an ordered ring. -/
instance isOrderedRing [IsOrderedRing R] [NoZeroDivisors R] : IsOrderedRing (Colex R[X]) :=
  .of_mul_nonneg fun x y hx hy ↦ by
    rw [nonneg_iff] at hx hy ⊢
    rw [ofColex_mul, leadingCoeff_mul]
    exact mul_nonneg hx hy

/-- When `R` is a strictly ordered ring, so is `Colex R[X]`. -/
instance isStrictOrderedRing [IsStrictOrderedRing R] : IsStrictOrderedRing (Colex R[X]) :=
  .of_mul_pos fun x y hx hy ↦ by
    rw [pos_iff] at hx hy ⊢
    rw [ofColex_mul, leadingCoeff_mul' (mul_pos hx hy).ne']
    exact mul_pos hx hy

end Ring

end Colex

end Polynomial

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
* `Polynomial.Colex.pos_iff`, `Polynomial.Colex.nonneg_iff`, `Polynomial.Colex.neg_iff`,
  `Polynomial.Colex.nonpos_iff`: a polynomial has the sign of its leading coefficient.
* `Polynomial.Colex.lt_iff_of_degree_lt`, `Polynomial.Colex.lt_iff_of_degree_gt`,
  `Polynomial.Colex.le_iff_of_degree_lt`, `Polynomial.Colex.le_iff_of_degree_gt`: between
  polynomials of different degrees, the sign of the leading coefficient of the one of larger degree
  decides the comparison.
* `Polynomial.Colex.isOrderedCancelAddMonoid`: when `R` is an ordered cancellative additive
  monoid, the order is compatible with addition.
* `Polynomial.Colex.succAddOrder`, `Polynomial.Colex.predSubOrder`: if addition in `R` is
  left-cancellative and `succ a = a + 1` in `R`, then `succ p = p + 1` in `Colex R[X]`; if `R` is a
  ring and `pred a = a - 1` in `R`, then `pred p = p - 1` in `Colex R[X]`. In particular `1` is the
  least positive element of `Colex ℤ[X]`.
* `Polynomial.Colex.toColex_C_lt_toColex_X`: the variable is larger than every constant.
* `Polynomial.Colex.not_archimedean`: the order is not Archimedean.
* `Polynomial.Colex.posMulStrictMono`, `Polynomial.Colex.mulPosStrictMono`: multiplication by a
  positive polynomial is strictly monotone when multiplication by a positive element of `R` is.
* `Polynomial.Colex.isOrderedRing`, `Polynomial.Colex.isStrictOrderedRing`: the order is
  compatible with multiplication.
* `Polynomial.leadingCoeff_add_pos`, `Polynomial.leadingCoeff_sum_pos`: positive leading
  coefficients do not cancel in sums, since they are the positive elements of `Colex R[X]`.

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

/-- If `x` has smaller degree than `y`, then `x ≤ y` exactly when the leading coefficient of `y`
is positive. -/
theorem le_iff_of_degree_lt {x y : Colex R[X]} (h : (ofColex x).degree < (ofColex y).degree) :
    x ≤ y ↔ 0 < (ofColex y).leadingCoeff := by
  rw [le_iff_eq_or_lt, lt_iff_of_degree_lt h, or_iff_right (by rintro rfl; exact h.false)]

/-- If `x` has larger degree than `y`, then `x ≤ y` exactly when the leading coefficient of `x`
is negative. -/
theorem le_iff_of_degree_gt {x y : Colex R[X]} (h : (ofColex y).degree < (ofColex x).degree) :
    x ≤ y ↔ (ofColex x).leadingCoeff < 0 := by
  rw [le_iff_eq_or_lt, lt_iff_of_degree_gt h, or_iff_right (by rintro rfl; exact h.false)]

/-- A polynomial is positive exactly when its leading coefficient is. -/
@[simp, grind =]
theorem pos_iff {x : Colex R[X]} : 0 < x ↔ 0 < (ofColex x).leadingCoeff := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · exact lt_iff_of_degree_lt (by simpa [bot_lt_iff_ne_bot] using hx)

/-- A polynomial is negative exactly when its leading coefficient is. -/
@[simp, grind =]
theorem neg_iff {x : Colex R[X]} : x < 0 ↔ (ofColex x).leadingCoeff < 0 := by
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
@[simp]
theorem toColex_C_lt_toColex_X [ZeroLEOneClass R] [Nontrivial R] (a : R) :
    toColex (C a) < toColex (X : R[X]) :=
  (lt_iff_of_degree_lt <| by
    simpa using (degree_C_le (a := a)).trans_lt (zero_lt_one' (WithBot ℕ))).2 (by simp)

grind_pattern toColex_C_lt_toColex_X => toColex (C a), toColex (X : R[X])

/-- When `0 < 1` in `R`, the variable is larger than `1`. -/
@[simp]
theorem one_lt_toColex_X [ZeroLEOneClass R] [Nontrivial R] : (1 : Colex R[X]) < toColex X := by
  simpa using toColex_C_lt_toColex_X (1 : R)

grind_pattern one_lt_toColex_X => toColex (X : R[X])

/-- When `0 < 1` in `R`, the variable is larger than every natural number. -/
@[simp]
theorem natCast_lt_toColex_X [ZeroLEOneClass R] [Nontrivial R] (n : ℕ) :
    (n : Colex R[X]) < toColex X := by
  simpa using toColex_C_lt_toColex_X (n : R)

grind_pattern natCast_lt_toColex_X => (n : Colex R[X]), toColex (X : R[X])

/-- When `0 < 1` in `R`, the variable is larger than every numeral. -/
@[simp]
theorem ofNat_lt_toColex_X [ZeroLEOneClass R] [Nontrivial R] (n : ℕ) [n.AtLeastTwo] :
    (ofNat(n) : Colex R[X]) < toColex X := by
  simpa using natCast_lt_toColex_X (R := R) ofNat(n)

-- `grind` does not accept a bare numeral as a trigger, so the comparisons themselves are used.
grind_pattern ofNat_lt_toColex_X => (OfNat.ofNat n : Colex R[X]) < toColex (X : R[X])
grind_pattern ofNat_lt_toColex_X => (OfNat.ofNat n : Colex R[X]) ≤ toColex (X : R[X])

/-- When `0 ≤ 1` in `R`, also `0 ≤ 1` in `Colex R[X]`. -/
instance zeroLEOneClass [ZeroLEOneClass R] : ZeroLEOneClass (Colex R[X]) where
  zero_le_one := nonneg_iff.2 (by simp)

/-- When `R` is an ordered cancellative additive monoid, the colexicographic order on `R[X]` is
compatible with addition. -/
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

/-- Let the coefficients of `x` and `y` be the sums of `F` and `G` over the antidiagonals. If `F`
and `G` agree at every pair other than `m` whose sum is at least that of `m`, and `F m < G m`,
then `x < y`. -/
private theorem lt_of_coeff_eq_sum [IsOrderedCancelAddMonoid R] {x y : Colex R[X]}
    {F G : ℕ × ℕ → R} {m : ℕ × ℕ}
    (hx : ∀ j, (ofColex x).coeff j = ∑ k ∈ Finset.antidiagonal j, F k)
    (hy : ∀ j, (ofColex y).coeff j = ∑ k ∈ Finset.antidiagonal j, G k)
    (hFG : ∀ k, k ≠ m → m.1 + m.2 ≤ k.1 + k.2 → F k = G k) (hm : F m < G m) : x < y := by
  refine lt_iff.2 ⟨m.1 + m.2, fun j hj ↦ ?_, ?_⟩ <;> rw [hx, hy]
  · refine Finset.sum_congr rfl fun k hk ↦ hFG k ?_ ?_ <;>
      grind [Finset.mem_antidiagonal]
  · refine Finset.sum_lt_sum (fun k hk ↦ ?_) ⟨m, by simp, hm⟩
    obtain rfl | hk' := eq_or_ne k m
    · exact hm.le
    · exact (hFG k hk' (by grind [Finset.mem_antidiagonal])).le

/-- When multiplication on the left by a positive element of `R` is strictly monotone, so is
multiplication on the left by a positive polynomial in `Colex R[X]`. -/
instance posMulStrictMono [IsOrderedCancelAddMonoid R] [PosMulStrictMono R] :
    PosMulStrictMono (Colex R[X]) where
  mul_lt_mul_of_pos_left a ha b c h := by
    -- The largest degree where the coefficients of `a * b` and `a * c` differ is
    -- `natDegree a + i`, where `i` is the largest degree where those of `b` and `c` differ.
    obtain ⟨i, hi, hlt⟩ := lt_iff.1 h
    refine lt_of_coeff_eq_sum (m := ((ofColex a).natDegree, i))
      (F := fun k ↦ (ofColex a).coeff k.1 * (ofColex b).coeff k.2)
      (G := fun k ↦ (ofColex a).coeff k.1 * (ofColex c).coeff k.2)
      (fun _ ↦ coeff_mul ..) (fun _ ↦ coeff_mul ..) (fun k hk hle ↦ ?_) ?_
    · obtain hk | hk : (ofColex a).natDegree < k.1 ∨ i < k.2 := by grind
      · simp [coeff_eq_zero_of_natDegree_lt hk]
      · rw [hi _ hk]
    · exact mul_lt_mul_of_pos_left hlt (by simpa using pos_iff.1 ha)

/-- When multiplication on the right by a positive element of `R` is strictly monotone, so is
multiplication on the right by a positive polynomial in `Colex R[X]`. -/
instance mulPosStrictMono [IsOrderedCancelAddMonoid R] [MulPosStrictMono R] :
    MulPosStrictMono (Colex R[X]) where
  mul_lt_mul_of_pos_right a ha b c h := by
    obtain ⟨i, hi, hlt⟩ := lt_iff.1 h
    refine lt_of_coeff_eq_sum (m := (i, (ofColex a).natDegree))
      (F := fun k ↦ (ofColex b).coeff k.1 * (ofColex a).coeff k.2)
      (G := fun k ↦ (ofColex c).coeff k.1 * (ofColex a).coeff k.2)
      (fun _ ↦ coeff_mul ..) (fun _ ↦ coeff_mul ..) (fun k hk hle ↦ ?_) ?_
    · obtain hk | hk : i < k.1 ∨ (ofColex a).natDegree < k.2 := by grind
      · rw [hi _ hk]
      · simp [coeff_eq_zero_of_natDegree_lt hk]
    · exact mul_lt_mul_of_pos_right hlt (by simpa using pos_iff.1 ha)

/-- When `R` is a strictly ordered semiring, so is `Colex R[X]`. -/
instance isStrictOrderedRing [IsStrictOrderedRing R] : IsStrictOrderedRing (Colex R[X]) where

/-- When `R` is an ordered semiring whose addition, and multiplication by nonzero elements, are
cancellative, `Colex R[X]` is an ordered semiring. For a ring `R` the multiplicative condition says
that `R` has no zero divisors, and it cannot be dropped: over `ℤ × ℤ`, `0 ≤ C (1, 0)` and
`C (5, 0) < C (0, 1) * X`, but `C (1, 0) * C (5, 0) = C (5, 0)` is larger than
`C (1, 0) * (C (0, 1) * X) = 0`. -/
instance isOrderedRing [IsOrderedRing R] [IsOrderedCancelAddMonoid R] [IsCancelMulZero R] :
    IsOrderedRing (Colex R[X]) :=
  haveI := PosMulMono.toPosMulStrictMono (α := R)
  haveI := MulPosMono.toMulPosStrictMono (α := R)
  {}

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
@[simp]
theorem intCast_lt_toColex_X [ZeroLEOneClass R] [Nontrivial R] (n : ℤ) :
    (n : Colex R[X]) < toColex X := by
  simpa using toColex_C_lt_toColex_X (n : R)

grind_pattern intCast_lt_toColex_X => (n : Colex R[X]), toColex (X : R[X])

/-- Over a ring `R` with `pred a = a - 1`, also `pred p = p - 1` in `Colex R[X]`: the polynomial
`p - 1` is the greatest polynomial smaller than `p`. -/
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

end Ring

end Colex

section LeadingCoeff

variable {R : Type*} [Semiring R] [PartialOrder R] [IsOrderedCancelAddMonoid R]

/-- Positive leading coefficients cannot cancel: the sum of two polynomials with positive leading
coefficients has positive leading coefficient. -/
theorem leadingCoeff_add_pos {p q : R[X]} (hp : 0 < p.leadingCoeff) (hq : 0 < q.leadingCoeff) :
    0 < (p + q).leadingCoeff := by
  simpa using Colex.pos_iff.1 (add_pos (Colex.pos_iff.2 hp) (Colex.pos_iff.2 hq) :
    0 < toColex p + toColex q)

/-- A nonempty finite sum of polynomials with positive leading coefficients has positive leading
coefficient. -/
theorem leadingCoeff_sum_pos {ι : Type*} {s : Finset ι} {f : ι → R[X]} (hs : s.Nonempty)
    (hf : ∀ i ∈ s, 0 < (f i).leadingCoeff) : 0 < (∑ i ∈ s, f i).leadingCoeff := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton i => simpa using hf i (by simp)
  | cons i s hi _ ih =>
    rw [Finset.sum_cons]
    exact leadingCoeff_add_pos (hf i (by simp)) (ih fun j hj ↦ hf j (by simp [hj]))

end LeadingCoeff

end Polynomial

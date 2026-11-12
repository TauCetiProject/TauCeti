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

/-!
# The colexicographic order on polynomials

For a semiring `R` with a linear order, two polynomials in `R[X]` are compared at the largest
degree at which their coefficients differ. This is the colexicographic order of their coefficient
sequences, put on the type synonym `Colex R[X]`. For `R = ℤ` it is the order on `ℤ[t]` with `t`
infinitely large: `ℤ[t]` is the direct sum of the cyclic groups `ℤ tⁿ`, ordered by its right
lexicographic order, so a polynomial is positive exactly when its leading coefficient is.

This makes `Colex ℤ[X]` a discretely ordered abelian group with least positive element `1`, in
which `t` exceeds every integer; it is not Archimedean.

## Main declarations

* `Polynomial.Colex.linearOrder`: the colexicographic linear order on `Colex R[X]`.
* `Polynomial.Colex.toColex_lt_toColex`: `p < q` exactly when `p` and `q` agree above some degree
  `i` and the coefficient of `p` at `i` is smaller.
* `Polynomial.Colex.toColex_pos`, `Polynomial.Colex.toColex_nonneg`,
  `Polynomial.Colex.toColex_lt_zero`, `Polynomial.Colex.toColex_nonpos`: a polynomial has the sign
  of its leading coefficient.
* `Polynomial.Colex.toColex_lt_toColex_iff_of_degree_lt`: a polynomial of larger degree is larger
  iff its leading coefficient is positive.
* `Polynomial.Colex.isOrderedCancelAddMonoid`: the order is compatible with addition.
* `Polynomial.Colex.succAddOrder`: if `succ a = a + 1` in `R` and addition in `R` is
  left-cancellative, then `succ p = p + 1` in `Colex R[X]`; in particular `1` is the least positive
  element of `Colex ℤ[X]`.
* `Polynomial.Colex.toColex_C_lt_toColex_X`: the variable is larger than every constant.
* `Polynomial.Colex.not_archimedean`: the order is not Archimedean.

## Implementation notes

The order is pulled back from Mathlib's colexicographic order on `ℕ →₀ R` along the coefficient
map. Mathlib's lexicographic order on Hahn series `Lex R⟦Γ⟧` with `Γ = ℕᵒᵈ` describes an
isomorphic ordered group on a different carrier; using `R[X]` itself keeps one type for `ℤ[t]` as
a ring of exponents and as an ordered group.

## References

* A. Myasnikov, V. Remeslennikov, D. Serbin, *Regular free length functions on Lyndon's free
  `ℤ[t]`-group `F^{ℤ[t]}`*, Contemp. Math. 378 (2005), 37–77, §2.3.
-/

public section

namespace Polynomial

namespace Colex

variable {R : Type*} [Semiring R] [LinearOrder R]

/-- The colexicographic order on `R[X]`: two polynomials are compared at the largest degree at
which their coefficients differ. It is pulled back from the colexicographic order on the
coefficient sequences `ℕ →₀ R`. -/
instance linearOrder : LinearOrder (Colex R[X]) :=
  LinearOrder.lift' (fun p ↦ toColex (ofColex p).coeff)
    (toColex.injective.comp (coeff_injective.comp ofColex.injective))

/-- Two polynomials compare as their coefficients at the largest degree where they differ. -/
theorem toColex_lt_toColex {p q : R[X]} :
    toColex p < toColex q ↔ ∃ i, (∀ j, i < j → p.coeff j = q.coeff j) ∧ p.coeff i < q.coeff i :=
  Finsupp.Colex.lt_iff

/-- A polynomial of larger degree is larger exactly when its leading coefficient is positive. -/
theorem toColex_lt_toColex_iff_of_degree_lt {p q : R[X]} (h : p.degree < q.degree) :
    toColex p < toColex q ↔ 0 < q.leadingCoeff := by
  have hp : p.coeff q.natDegree = 0 := coeff_natDegree_eq_zero_of_degree_lt h
  have hpq (j) (hj : q.natDegree < j) : p.coeff j = q.coeff j := by
    rw [coeff_eq_zero_of_natDegree_lt hj, coeff_eq_zero_of_degree_lt
      (h.trans_le (degree_le_natDegree.trans (by exact_mod_cast hj.le)))]
  refine ⟨fun hlt ↦ ?_, fun hq ↦ toColex_lt_toColex.2 ⟨_, hpq, by rwa [hp]⟩⟩
  refine (lt_or_gt_of_ne (leadingCoeff_ne_zero.2 (ne_zero_of_degree_gt h))).resolve_left
    fun hq ↦ hlt.not_gt (toColex_lt_toColex.2 ⟨_, fun j hj ↦ (hpq j hj).symm, ?_⟩)
  rwa [hp, coeff_natDegree]

/-- A polynomial is positive exactly when its leading coefficient is. -/
@[simp]
theorem toColex_pos {p : R[X]} : 0 < toColex p ↔ 0 < p.leadingCoeff := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  · simpa using toColex_lt_toColex_iff_of_degree_lt (p := 0) (by simpa [bot_lt_iff_ne_bot] using hp)

/-- A polynomial is nonnegative exactly when its leading coefficient is. -/
@[simp]
theorem toColex_nonneg {p : R[X]} : 0 ≤ toColex p ↔ 0 ≤ p.leadingCoeff := by
  simp [le_iff_lt_or_eq, eq_comm (a := (0 : R)), eq_comm (a := (0 : Colex R[X]))]

/-- A polynomial is negative exactly when its leading coefficient is. -/
@[simp]
theorem toColex_lt_zero {p : R[X]} : toColex p < 0 ↔ p.leadingCoeff < 0 := by
  rw [← not_le, toColex_nonneg, not_le]

/-- A polynomial is nonpositive exactly when its leading coefficient is. -/
@[simp]
theorem toColex_nonpos {p : R[X]} : toColex p ≤ 0 ↔ p.leadingCoeff ≤ 0 := by
  rw [← not_lt, toColex_pos, not_lt]

/-- The constant polynomials are ordered as `R`. -/
@[simp]
theorem toColex_C_lt_toColex_C {a b : R} : toColex (C a) < toColex (C b) ↔ a < b := by
  rw [toColex_lt_toColex]
  refine ⟨?_, fun h ↦ ⟨0, fun j hj ↦ by simp [coeff_C, hj.ne'], by simpa using h⟩⟩
  rintro ⟨_ | i, -, h⟩ <;> simp_all

/-- The constant polynomials are ordered as `R`. -/
@[simp]
theorem toColex_C_le_toColex_C {a b : R} : toColex (C a) ≤ toColex (C b) ↔ a ≤ b := by
  simp [le_iff_eq_or_lt]

/-- When `0 < 1` in `R`, the variable is larger than every constant polynomial. -/
theorem toColex_C_lt_toColex_X [ZeroLEOneClass R] [NeZero (1 : R)] (a : R) :
    toColex (C a) < toColex (X : R[X]) :=
  have : Nontrivial R := ⟨0, 1, NeZero.ne' 1⟩
  (toColex_lt_toColex_iff_of_degree_lt (degree_C_le.trans_lt (by simp))).2 (by simp)

/-- The colexicographic order on `R[X]` is compatible with addition. -/
instance isOrderedCancelAddMonoid [IsOrderedCancelAddMonoid R] :
    IsOrderedCancelAddMonoid (Colex R[X]) :=
  Function.Injective.isOrderedCancelAddMonoid (fun p ↦ toColex (ofColex p).coeff)
    (fun _ _ ↦ (congrArg toColex (Finsupp.ext (coeff_add _ _))).trans (toColex_add _ _)) .rfl

/-- Polynomials that agree in every positive degree compare as their constant terms. -/
theorem toColex_le_toColex_of_coeff_zero_le {p q : R[X]} (h : ∀ j, 0 < j → p.coeff j = q.coeff j)
    (h0 : p.coeff 0 ≤ q.coeff 0) : toColex p ≤ toColex q := by
  rcases h0.lt_or_eq with h0 | h0
  · exact (toColex_lt_toColex.2 ⟨0, h, h0⟩).le
  · exact (congrArg toColex (ext fun j ↦ by rcases j with _ | j <;> grind)).le

/-- If `succ a = a + 1` in `R` and addition in `R` is left-cancellative, then `succ p = p + 1` in
`Colex R[X]`: the polynomial `p + 1` is the least polynomial larger than `p`. Cancellation cannot
be dropped: over `ℕ∞`, `C ⊤ + 1 = C ⊤` although `C ⊤ < X`. -/
noncomputable instance succAddOrder [SuccAddOrder R] [IsLeftCancelAdd R] :
    SuccAddOrder (Colex R[X]) :=
  -- Adding `1` changes only the constant coefficient.
  have hcoeff (p : R[X]) {j : ℕ} (hj : 0 < j) : (p + 1).coeff j = p.coeff j :=
    coeff_add_eq_left_of_lt (by simpa using hj)
  have hle (p : R[X]) : toColex p ≤ toColex (p + 1) :=
    toColex_le_toColex_of_coeff_zero_le (fun _ hj ↦ (hcoeff p hj).symm)
      (by simpa [Order.succ_eq_add_one] using Order.le_succ (p.coeff 0))
  have hmax (p : R[X]) (h : toColex (p + 1) ≤ toColex p) : IsMax (toColex p) := by
    have hp : p + 1 = p := toColex.injective (h.antisymm (hle p))
    have h1 : (1 : R) = 0 := by simpa using congrArg (coeff · 0) hp
    have : Subsingleton R := subsingleton_of_zero_eq_one h1.symm
    have : Subsingleton (Colex R[X]) := ofColex.subsingleton
    exact fun q _ ↦ (Subsingleton.elim q _).le
  have hsucc {p q : R[X]} (h : toColex p < toColex q) : toColex (p + 1) ≤ toColex q := by
    obtain ⟨i, hi, hlt⟩ := toColex_lt_toColex.1 h
    rcases i.eq_zero_or_pos with rfl | hi0
    · refine toColex_le_toColex_of_coeff_zero_le (fun j hj ↦ ?_) ?_
      · rw [hcoeff _ hj, hi j hj]
      · simpa using Order.add_one_le_of_lt hlt
    · refine (toColex_lt_toColex.2 ⟨i, fun j hj ↦ ?_, ?_⟩).le
      · rw [hcoeff _ (hi0.trans hj), hi j hj]
      · rwa [hcoeff _ hi0]
  -- `toColex` and `ofColex` are the identity, so each field is the polynomial statement above.
  { succ p := p + 1
    le_succ p := hle (ofColex p)
    max_of_succ_le {p} := hmax (ofColex p)
    succ_le_of_lt {p q} := hsucc (p := ofColex p) (q := ofColex q)
    succ_eq_add_one _ := rfl }

/-- When `0 < 1` in `R`, the colexicographic order on `R[X]` is not Archimedean: no multiple of
`1` reaches `X`. -/
theorem not_archimedean [ZeroLEOneClass R] [NeZero (1 : R)] : ¬ Archimedean (Colex R[X]) := by
  intro h
  have h1 : (0 : Colex R[X]) < 1 := by
    simpa using toColex_C_lt_toColex_C.2 (zero_lt_one' R)
  obtain ⟨n, hn⟩ := Archimedean.arch (toColex (X : R[X])) h1
  refine (toColex_C_lt_toColex_X (n • 1 : R)).not_ge (hn.trans_eq ?_)
  rw [map_nsmul, C_1, toColex_smul, toColex_one]

end Colex

end Polynomial

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
public import Mathlib.Data.Nat.Dist
public import TauCeti.AlgebraicGeometry.EllipticCurve.TateCurve.Basic
public import TauCeti.RingTheory.PowerSeries.Swap
import Mathlib.Algebra.BigOperators.Field
import TauCeti.Algebra.Polynomial.Laurent.Symmetric
import TauCeti.NumberTheory.Divisors
import TauCeti.RingTheory.LaurentSeries.LaurentPolynomial
import TauCeti.RingTheory.Polynomial.Chebyshev.Taylor

/-!
# The formal point of the Tate curve

The Tate curve `E_q : y² + x y = x³ + a₄(q) x + a₆(q)` over `ℤ⟦q⟧` (`TauCeti.tateCurve`) is
uniformised by

`X(u) = ∑_{n ∈ ℤ} qⁿu / (1 - qⁿu)² - 2 s₁(q)`,  `Y(u) = ∑_{n ∈ ℤ} (qⁿu)² / (1 - qⁿu)³ + s₁(q)`.

Expanded on the annulus `|q| < |u| < 1`, every monomial is `uᵃ (q / u)ᵇ` with `a, b ≥ 0`, so `X`
and `Y` are power series in `u` and `v = q / u` with integer coefficients. This file defines them
as `tateFormalX R` and `tateFormalY R` in `R⟦u⟧⟦v⟧`, for any commutative ring `R`, and proves that
the point `(X, Y)` lies on the Tate curve after the substitution `q = u v`.

This is the algebraic identity behind Tate's uniformisation. Over a complete non-archimedean field
the series converge at `u` and `v = q / u` whenever `|q| < |u| < 1`. Once their values there are
identified with the analytic coordinates `TauCeti.tateUniformizationX` and
`TauCeti.tateUniformizationY`, which this file does not do, the identity shows that those
coordinates satisfy the equation of the specialised Tate curve.

## Main definitions

* `TauCeti.tateFormalX`, `TauCeti.tateFormalY`: the formal Tate coordinates in `R⟦u⟧⟦v⟧`.
* `TauCeti.tateParamHom`: the substitution `q = u v`, a ring map `ℤ⟦q⟧ → R⟦u⟧⟦v⟧`.

## Main results

* `TauCeti.coeff_coeff_tateFormalX`, `TauCeti.coeff_coeff_tateFormalY`: their coefficients.
* `TauCeti.swap_tateFormalX`, `TauCeti.swap_tateFormalY`: exchanging `u` and `v` sends the formal
  point `(X, Y)` to its negative `(X, -Y - X)`.
* `TauCeti.equation_tateFormalX_tateFormalY`: the formal point `(X, Y)` lies on the Tate curve.

## References

* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, GTM 151, §V.1 and §V.3.
* J. Tate, *A review of non-Archimedean elliptic functions*, in *Elliptic curves, modular forms,
  & Fermat's last theorem* (Hong Kong, 1993), International Press (1995), 162–184.
-/

public section

open PowerSeries ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace TauCeti

variable (R : Type*) [CommRing R]

/-- The `x`-coordinate of the formal Tate point, as a power series in `u` and `v`, the coefficient
of `uᵃ vᵇ` being `coeff a (coeff b _)`. That coefficient is `-2 σ₁(a)` when `a = b`, and otherwise
`d = |a - b|` when `d` divides `min a b` (equivalently `a`, or `b`) and `0` when it does not. With
`q = u v` this is the expansion of `∑_{n ∈ ℤ} qⁿu / (1 - qⁿu)² - 2 s₁(q)` on `|q| < |u| < 1`. -/
noncomputable def tateFormalX : R⟦X⟧⟦X⟧ :=
  mk fun b ↦ mk fun a ↦
    if a = b then -2 * (σ 1 a : R) else if a.dist b ∣ min a b then (a.dist b : R) else 0

/-- The `y`-coordinate of the formal Tate point, as a power series in `u` and `v`, the coefficient
of `uᵃ vᵇ` being `coeff a (coeff b _)`. That coefficient is `σ₁(a)` when `a = b`. Otherwise, with
`d = |a - b|`, it is `0` unless `d` divides `min a b`, in which case it is `d (d - 1) / 2` when
`b < a` and `-d (d + 1) / 2` when `a < b`. With `q = u v` this is the expansion of
`∑_{n ∈ ℤ} (qⁿu)² / (1 - qⁿu)³ + s₁(q)` on `|q| < |u| < 1`. -/
noncomputable def tateFormalY : R⟦X⟧⟦X⟧ :=
  mk fun b ↦ mk fun a ↦
    if a = b then (σ 1 a : R) else if a.dist b ∣ min a b then
      (if b < a then ((a.dist b).choose 2 : R) else -((a.dist b + 1).choose 2 : R)) else 0

/-- The ring map `ℤ⟦q⟧ → R⟦u⟧⟦v⟧` substituting `q = u v`. -/
noncomputable def tateParamHom : ℤ⟦X⟧ →+* R⟦X⟧⟦X⟧ :=
  (rescale (X : R⟦X⟧)).comp (map ((C (R := R)).comp (Int.castRingHom R)))

variable {R}

/-- The coefficient of `uᵃ vᵇ` in the formal Tate coordinate `x`. -/
@[simp]
theorem coeff_coeff_tateFormalX (a b : ℕ) :
    coeff a (coeff b (tateFormalX R)) =
      if a = b then -2 * (σ 1 a : R) else if a.dist b ∣ min a b then (a.dist b : R) else 0 := by
  simp [tateFormalX]

/-- The coefficient of `uᵃ vᵇ` in the formal Tate coordinate `y`. -/
@[simp]
theorem coeff_coeff_tateFormalY (a b : ℕ) :
    coeff a (coeff b (tateFormalY R)) =
      if a = b then (σ 1 a : R) else if a.dist b ∣ min a b then
        (if b < a then ((a.dist b).choose 2 : R) else -((a.dist b + 1).choose 2 : R)) else 0 := by
  simp [tateFormalY]

/-- The coefficient of `uᵃ vᵇ` in `f(u v)` is the coefficient of `qᵃ` in `f` when `a = b`, and `0`
otherwise. -/
@[simp]
theorem coeff_coeff_tateParamHom (f : ℤ⟦X⟧) (a b : ℕ) :
    coeff a (coeff b (tateParamHom R f)) = if a = b then ((coeff b f : ℤ) : R) else 0 := by
  simp [tateParamHom]

/-- The substitution `q = u v` sends `q` to the product of the inner variable `u` and the outer
variable `v`. -/
@[simp]
theorem tateParamHom_X : tateParamHom R X = C X * X := by
  rw [tateParamHom, RingHom.comp_apply, map_X, rescale_X]

/-- Exchanging `u` and `v` fixes the substitution `q = u v`. -/
@[simp]
theorem swap_tateParamHom (g : ℤ⟦X⟧) :
    PowerSeries.swap (tateParamHom R g) = tateParamHom R g := by
  refine PowerSeries.ext fun b ↦ PowerSeries.ext fun a ↦ ?_
  rw [PowerSeries.coeff_coeff_swap, coeff_coeff_tateParamHom, coeff_coeff_tateParamHom]
  by_cases h : a = b
  · subst h
    rfl
  · rw [ite_eq_right h, ite_eq_right (Ne.symm h)]

/-- Exchanging `u` and `v` fixes the formal Tate coordinate `x`. -/
@[simp]
theorem swap_tateFormalX : PowerSeries.swap (tateFormalX R) = tateFormalX R := by
  refine PowerSeries.ext fun b ↦ PowerSeries.ext fun a ↦ ?_
  rw [PowerSeries.coeff_coeff_swap, coeff_coeff_tateFormalX, coeff_coeff_tateFormalX,
    Nat.dist_comm, min_comm]
  by_cases h : a = b
  · subst h
    rfl
  · rw [ite_eq_right h, ite_eq_right (Ne.symm h)]

/-- Exchanging `u` and `v` sends the formal Tate coordinate `y` to `-y - x`: it maps the formal
Tate point to its negative on the curve `y² + x y = x³ + a₄ x + a₆`. -/
@[simp]
theorem swap_tateFormalY :
    PowerSeries.swap (tateFormalY R) = -tateFormalY R - tateFormalX R := by
  refine PowerSeries.ext fun b ↦ PowerSeries.ext fun a ↦ ?_
  rw [PowerSeries.coeff_coeff_swap, map_sub, map_sub, map_neg, map_neg, coeff_coeff_tateFormalY,
    coeff_coeff_tateFormalY, coeff_coeff_tateFormalX, Nat.dist_comm, min_comm]
  rcases lt_trichotomy a b with h | rfl | h
  · simp only [h.ne', h, h.ne, not_lt_of_gt h, ite_false, ite_true]
    split_ifs <;> simp [Nat.choose_succ_succ, Nat.choose_one_right, sub_eq_add_neg]
  · simp
    ring
  · simp only [h.ne, h, h.ne', not_lt_of_gt h, ite_false, ite_true]
    split_ifs <;> simp [Nat.choose_succ_succ, Nat.choose_one_right, sub_eq_add_neg]

/-! ### Laurent polynomials and Laurent series in `u` -/

/-- Substitution of `u + u⁻¹` into a polynomial. -/
private noncomputable abbrev symmHom : Polynomial ℚ →+* LaurentPolynomial ℚ :=
  Polynomial.eval₂RingHom LaurentPolynomial.C (LaurentPolynomial.T 1 + LaurentPolynomial.T (-1))

/-- Substitution of `u + u⁻¹` into a polynomial, as a Laurent series in `u`. -/
private noncomputable abbrev psi : Polynomial ℚ →+* LaurentSeries ℚ :=
  LaurentPolynomial.toLaurentSeries.comp symmHom

private theorem psi_chebyshevC (d : ℕ) :
    psi (Polynomial.Chebyshev.C ℚ d) =
      HahnSeries.single (d : ℤ) 1 + HahnSeries.single (-d : ℤ) 1 := by
  rw [RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.Chebyshev.eval₂_C_add_T_neg,
    map_add, LaurentPolynomial.toLaurentSeries_T, LaurentPolynomial.toLaurentSeries_T]

private theorem psi_X : psi Polynomial.X = HahnSeries.single 1 1 + HahnSeries.single (-1) 1 := by
  rw [RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, map_add,
    LaurentPolynomial.toLaurentSeries_T, LaurentPolynomial.toLaurentSeries_T]

/-- `u - u⁻¹`. -/
private noncomputable abbrev sL : LaurentSeries ℚ :=
  HahnSeries.single 1 1 - HahnSeries.single (-1) 1

private theorem sL_mul_psi_chebyshevS (n : ℕ) :
    sL * psi (Polynomial.Chebyshev.S ℚ n) =
      HahnSeries.single ((n : ℤ) + 1) 1 - HahnSeries.single (-((n : ℤ) + 1)) 1 := by
  have h := congrArg LaurentPolynomial.toLaurentSeries
    (Polynomial.Chebyshev.T_sub_T_neg_mul_eval₂_S_add_T_neg (R := ℚ) n)
  rw [map_mul, map_sub, map_sub, LaurentPolynomial.toLaurentSeries_T,
    LaurentPolynomial.toLaurentSeries_T, LaurentPolynomial.toLaurentSeries_T,
    LaurentPolynomial.toLaurentSeries_T] at h
  exact h

private theorem psi_C (r : ℚ) : psi (Polynomial.C r) = HahnSeries.C r := by
  rw [RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C,
    LaurentPolynomial.toLaurentSeries_C]

private theorem psi_C_two : psi (Polynomial.C 2) = 2 := by
  rw [map_ofNat Polynomial.C 2, map_ofNat psi 2]

private theorem single_neg_one_mul_single_one :
    (HahnSeries.single (-1 : ℤ) (1 : ℚ)) * HahnSeries.single 1 1 = 1 := by
  rw [HahnSeries.single_mul_single, neg_add_cancel, mul_one, ← HahnSeries.C_apply, map_one]

/-- `w = u - 2 + u⁻¹`, the image of `X - 2`, is `u⁻¹ (1 - u)²`. -/
private theorem psi_X_sub_two :
    psi (Polynomial.X - Polynomial.C 2) =
      HahnSeries.single (-1) 1 * HahnSeries.ofPowerSeries ℤ ℚ ((1 - X) ^ 2) := by
  rw [map_sub, psi_X, psi_C_two, map_pow, map_sub, RingHom.map_one, HahnSeries.ofPowerSeries_X]
  linear_combination (2 - HahnSeries.single (1 : ℤ) (1 : ℚ)) * single_neg_one_mul_single_one

private theorem sL_sq : sL ^ 2 =
    psi (Polynomial.X - Polynomial.C 2) ^ 2 + 4 * psi (Polynomial.X - Polynomial.C 2) := by
  rw [map_sub, psi_X, psi_C_two]
  linear_combination (-4 : LaurentSeries ℚ) * single_neg_one_mul_single_one

/-- The map `ℚ⟦u⟧⟦v⟧ → ℚ⸨u⸩⟦q⟧` substituting `v = q / u`. -/
private noncomputable abbrev toLaurent : ℚ⟦X⟧⟦X⟧ →+* (LaurentSeries ℚ)⟦X⟧ :=
  (rescale (HahnSeries.single (-1 : ℤ) (1 : ℚ))).comp (map (HahnSeries.ofPowerSeries ℤ ℚ))

private theorem coeff_toLaurent (G : ℚ⟦X⟧⟦X⟧) (N : ℕ) :
    coeff N (toLaurent G) =
      HahnSeries.single (-(N : ℤ)) 1 * HahnSeries.ofPowerSeries ℤ ℚ (coeff N G) := by
  rw [RingHom.comp_apply, coeff_rescale, coeff_map, HahnSeries.single_pow]
  simp

/-! ### The coordinates in the variable `X = u + u⁻¹` -/

/-- `w = X - 2`, which becomes `u - 2 + u⁻¹ = u⁻¹ (1 - u)²`. -/
private noncomputable abbrev wP : Polynomial ℚ := Polynomial.X - Polynomial.C 2

/-- The regular part of the `x`-coordinate: its `qᴺ` coefficient is `∑_{d ∣ N} d (C_d - 2)`, which
becomes `∑_{d ∣ N} d (uᵈ + u⁻ᵈ - 2)`. -/
private noncomputable def tP : (Polynomial ℚ)⟦X⟧ :=
  mk fun N ↦ ∑ d ∈ N.divisors, (d : Polynomial ℚ) * (Polynomial.Chebyshev.C ℚ d - Polynomial.C 2)

/-- The regular part of `(2y + x) / (u - u⁻¹)`: its `qᴺ` coefficient is `∑_{d ∣ N} d² S_{d-1}`. -/
private noncomputable def tQ : (Polynomial ℚ)⟦X⟧ :=
  mk fun N ↦ ∑ d ∈ N.divisors, (d : Polynomial ℚ) ^ 2 * Polynomial.Chebyshev.S ℚ ((d : ℤ) - 1)

/-- `s₃(q)`, with constant polynomial coefficients. -/
private noncomputable def sig₃ : (Polynomial ℚ)⟦X⟧ := mk fun N ↦ Polynomial.C (σ 3 N : ℚ)

/-- `(s₅(q) - s₃(q)) / 12`, with constant polynomial coefficients. -/
private noncomputable def sig₅ : (Polynomial ℚ)⟦X⟧ :=
  mk fun N ↦ Polynomial.C (((σ 5 N : ℚ) - σ 3 N) / 12)

/-- The expansion of the regular part of `x` at `w = 0`:
`P = s₃ w + (s₅ - s₃) / 12 · w² + O(w³)`. -/
private theorem exists_tP_eq : ∃ P₃ : (Polynomial ℚ)⟦X⟧,
    tP = C wP * sig₃ + C wP ^ 2 * sig₅ + C wP ^ 3 * P₃ := by
  choose r hr using fun d : ℕ ↦ Polynomial.Chebyshev.exists_C_sub_two_eq (R := ℚ) d
  simp only [Int.cast_natCast] at hr
  refine ⟨mk fun N ↦ ∑ d ∈ N.divisors, (d : Polynomial ℚ) * r d, PowerSeries.ext fun N ↦ ?_⟩
  rw [tP, sig₃, sig₅, map_add, map_add, ← map_pow, ← map_pow, coeff_C_mul, coeff_C_mul,
    coeff_C_mul, coeff_mk, coeff_mk, coeff_mk, coeff_mk]
  simp only [sigma_apply, Nat.cast_sum, Nat.cast_pow, ← Finset.sum_sub_distrib, Finset.sum_div,
    map_sum, Finset.mul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun d _ ↦ ?_
  rw [hr d, ← map_natCast Polynomial.C]
  have e₁ : Polynomial.C (d : ℚ) * Polynomial.C ((d : ℚ) ^ 2) = Polynomial.C ((d : ℚ) ^ 3) := by
    rw [← map_mul]
    ring_nf
  have e₂ : Polynomial.C (d : ℚ) * Polynomial.C ((d : ℚ) ^ 2 * ((d : ℚ) ^ 2 - 1) / 12) =
      Polynomial.C (((d : ℚ) ^ 5 - (d : ℚ) ^ 3) / 12) := by
    rw [← map_mul]
    ring_nf
  linear_combination wP * e₁ + wP ^ 2 * e₂

/-- The expansion of `Q` at `w = 0`: `Q = s₃ + 2 (s₅ - s₃)/12 · w + O(w²)`. -/
private theorem exists_tQ_eq : ∃ Q₂ : (Polynomial ℚ)⟦X⟧,
    tQ = sig₃ + 2 * C wP * sig₅ + C wP ^ 2 * Q₂ := by
  choose r hr using fun d : ℕ ↦ Polynomial.Chebyshev.exists_S_eq (R := ℚ) ((d : ℤ) - 1)
  simp only [Int.cast_sub, Int.cast_natCast, Int.cast_one, sub_add_cancel] at hr
  refine ⟨mk fun N ↦ ∑ d ∈ N.divisors, (d : Polynomial ℚ) ^ 2 * r d, PowerSeries.ext fun N ↦ ?_⟩
  rw [tQ, sig₃, sig₅, map_add, map_add, ← map_pow, mul_assoc, ← map_ofNat C 2, coeff_C_mul,
    coeff_C_mul, coeff_C_mul, coeff_mk, coeff_mk, coeff_mk, coeff_mk]
  simp only [sigma_apply, Nat.cast_sum, Nat.cast_pow, ← Finset.sum_sub_distrib, Finset.sum_div,
    map_sum, Finset.mul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun d _ ↦ ?_
  rw [hr d, ← map_natCast Polynomial.C]
  have e₁ : Polynomial.C (d : ℚ) ^ 2 * Polynomial.C (d : ℚ) = Polynomial.C ((d : ℚ) ^ 3) := by
    rw [← map_pow, ← map_mul]
    ring_nf
  have e₂ : Polynomial.C (d : ℚ) ^ 2 * Polynomial.C (((d : ℚ) - 1 + 2) * d * ((d : ℚ) - 1) / 6) =
      2 * Polynomial.C (((d : ℚ) ^ 5 - (d : ℚ) ^ 3) / 12) := by
    rw [← map_pow, ← map_mul, ← map_ofNat Polynomial.C 2, ← map_mul]
    ring_nf
  linear_combination e₁ + wP * e₂

/-! ### The coordinates as power series in `u` -/

private theorem mk_id_mul_one_sub_X_sq : (mk fun a : ℕ ↦ (a : ℚ)) * (1 - X) ^ 2 = X := by
  have h : ((1 : ℚ⟦X⟧) - X) ^ 2 = 1 - C 2 * X ^ 1 + X ^ 2 := by rw [map_ofNat]; ring
  rw [h]
  refine PowerSeries.ext fun n ↦ ?_
  simp only [mul_add, mul_sub, mul_one, map_add, map_sub, mul_left_comm _ (C _), coeff_C_mul,
    coeff_mul_X_pow', coeff_mk, coeff_X]
  rcases n with _ | _ | n <;> simp
  ring

private theorem mk_sq_mul_one_sub_X_pow_four :
    (mk fun a : ℕ ↦ (a : ℚ) ^ 2) * (1 - X) ^ 4 = X - X ^ 3 := by
  have h : ((1 : ℚ⟦X⟧) - X) ^ 4 = 1 - C 4 * X ^ 1 + C 6 * X ^ 2 - C 4 * X ^ 3 + X ^ 4 := by
    rw [map_ofNat, map_ofNat]; ring
  rw [h]
  refine PowerSeries.ext fun n ↦ ?_
  simp only [mul_add, mul_sub, mul_one, map_add, map_sub, mul_left_comm _ (C _), coeff_C_mul,
    coeff_mul_X_pow', coeff_mk, coeff_X, coeff_X_pow]
  rcases n with _ | _ | _ | _ | n <;> simp <;> ring

/-- The coefficients of `2y + x`: the coefficient of `uᵃ vᵇ` is `0` when `a = b`, and otherwise
`± d²` for `d = |a - b|` when `d ∣ a`, with the sign of `a - b`. -/
private theorem coeff_coeff_two_mul_tateFormalY_add (a b : ℕ) :
    coeff a (coeff b (2 * tateFormalY ℚ + tateFormalX ℚ)) =
      if a = b then 0 else if a.dist b ∣ min a b then
        (if b < a then (a.dist b : ℚ) ^ 2 else -(a.dist b : ℚ) ^ 2) else 0 := by
  rw [two_mul, map_add, map_add, map_add, map_add, coeff_coeff_tateFormalX,
    coeff_coeff_tateFormalY]
  split_ifs <;> simp [Nat.cast_choose_two] <;> ring

/-- The coefficient of `vᴺ` in `x` for `N ≠ 0`, as the power series
`∑_{d ∣ N} d (uᴺ⁺ᵈ + uᴺ⁻ᵈ - 2uᴺ)` in `u`. -/
private theorem coeff_tateFormalX_of_ne_zero {N : ℕ} (hN : N ≠ 0) :
    coeff N (tateFormalX ℚ) =
      ∑ d ∈ N.divisors, (d : ℚ⟦X⟧) * (X ^ (N + d) + X ^ (N - d) - 2 * X ^ N) := by
  refine PowerSeries.ext fun a ↦ ?_
  simp only [coeff_coeff_tateFormalX, map_sum, ← map_natCast (C (R := ℚ)), coeff_C_mul,
    map_add, map_sub, ← map_ofNat (C (R := ℚ)) 2, coeff_X_pow, mul_add, mul_sub, mul_ite,
    mul_one, mul_zero, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [Nat.sum_divisors_ite_eq_add hN, Nat.sum_divisors_ite_eq_sub hN]
  rcases lt_trichotomy a N with h | rfl | h
  · rw [Nat.dist_eq_sub_of_le h.le, min_eq_left h.le]
    simp only [h.ne, h, not_lt_of_gt h, false_and, true_and, ite_false,
      Finset.sum_const_zero, zero_add, sub_zero]
  · simp [sigma_one_apply, Finset.sum_mul, mul_comm]
  · rw [Nat.dist_eq_sub_of_le_right h.le, min_eq_right h.le]
    simp only [h.ne', h, not_lt_of_gt h, false_and, true_and, ite_false,
      Finset.sum_const_zero, add_zero, sub_zero]

/-- The coefficient of `vᴺ` in `2y + x` for `N ≠ 0`, as the power series
`∑_{d ∣ N} d² (uᴺ⁺ᵈ - uᴺ⁻ᵈ)` in `u`. -/
private theorem coeff_two_mul_tateFormalY_add_of_ne_zero {N : ℕ} (hN : N ≠ 0) :
    coeff N (2 * tateFormalY ℚ + tateFormalX ℚ) =
      ∑ d ∈ N.divisors, (d : ℚ⟦X⟧) ^ 2 * (X ^ (N + d) - X ^ (N - d)) := by
  refine PowerSeries.ext fun a ↦ ?_
  simp only [coeff_coeff_two_mul_tateFormalY_add, map_sum, ← map_natCast (C (R := ℚ)),
    ← map_pow, coeff_C_mul, map_sub, coeff_X_pow, mul_sub, mul_ite, mul_one, mul_zero,
    Finset.sum_sub_distrib]
  rw [Nat.sum_divisors_ite_eq_add hN, Nat.sum_divisors_ite_eq_sub hN]
  rcases lt_trichotomy a N with h | rfl | h
  · rw [Nat.dist_eq_sub_of_le h.le, min_eq_left h.le]
    simp only [h.ne, h, not_lt_of_gt h, false_and, true_and, ite_false, zero_sub]
    split_ifs <;> simp
  · simp
  · rw [Nat.dist_eq_sub_of_le_right h.le, min_eq_right h.le]
    simp only [h.ne', h, not_lt_of_gt h, false_and, true_and, ite_false, sub_zero, ite_true]

private theorem coeff_zero_tateFormalX : coeff 0 (tateFormalX ℚ) = mk fun a ↦ (a : ℚ) := by
  refine PowerSeries.ext fun a ↦ ?_
  rw [coeff_coeff_tateFormalX, coeff_mk]
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  · simp [ha, Nat.dist_zero_right]

private theorem coeff_zero_two_mul_tateFormalY_add :
    coeff 0 (2 * tateFormalY ℚ + tateFormalX ℚ) = mk fun a ↦ (a : ℚ) ^ 2 := by
  refine PowerSeries.ext fun a ↦ ?_
  rw [coeff_coeff_two_mul_tateFormalY_add, coeff_mk]
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  · simp [ha, Nat.pos_of_ne_zero ha, Nat.dist_zero_right]

private theorem single_neg_mul_single (N d : ℕ) (h : d ≤ N) :
    HahnSeries.single (-(N : ℤ)) (1 : ℚ) * HahnSeries.single ((N - d : ℕ) : ℤ) 1 =
      HahnSeries.single (-(d : ℤ)) 1 := by
  rw [HahnSeries.single_mul_single, mul_one, Nat.cast_sub h]
  ring_nf

private theorem single_neg_mul_single_add (N d : ℕ) :
    HahnSeries.single (-(N : ℤ)) (1 : ℚ) * HahnSeries.single ((N + d : ℕ) : ℤ) 1 =
      HahnSeries.single (d : ℤ) 1 := by
  rw [HahnSeries.single_mul_single, mul_one, Nat.cast_add]
  ring_nf

private theorem single_neg_mul_single_self (N : ℕ) :
    HahnSeries.single (-(N : ℤ)) (1 : ℚ) * HahnSeries.single (N : ℤ) 1 = 1 := by
  rw [HahnSeries.single_mul_single, mul_one, neg_add_cancel, ← HahnSeries.C_apply, map_one]

/-- `[qᴺ] x = ∑_{d ∣ N} d (uᵈ + u⁻ᵈ - 2)` for `N ≠ 0`. -/
private theorem single_mul_coeff_tateFormalX {N : ℕ} (hN : N ≠ 0) :
    HahnSeries.single (-(N : ℤ)) 1 * HahnSeries.ofPowerSeries ℤ ℚ (coeff N (tateFormalX ℚ)) =
      psi (coeff N tP) := by
  rw [coeff_tateFormalX_of_ne_zero hN, tP, coeff_mk, map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd ↦ ?_
  have hdN := Nat.divisor_le hd
  simp only [map_mul, map_natCast, map_sub, map_add, map_ofNat, HahnSeries.ofPowerSeries_X_pow,
    psi_chebyshevC]
  linear_combination (d : LaurentSeries ℚ) * (single_neg_mul_single_add N d +
    single_neg_mul_single N d hdN - 2 * single_neg_mul_single_self N)

/-- `[qᴺ] (2y + x) = ∑_{d ∣ N} d² (uᵈ - u⁻ᵈ)` for `N ≠ 0`. -/
private theorem single_mul_coeff_two_mul_tateFormalY_add {N : ℕ} (hN : N ≠ 0) :
    HahnSeries.single (-(N : ℤ)) 1 *
        HahnSeries.ofPowerSeries ℤ ℚ (coeff N (2 * tateFormalY ℚ + tateFormalX ℚ)) =
      sL * psi (coeff N tQ) := by
  rw [coeff_two_mul_tateFormalY_add_of_ne_zero hN, tQ, coeff_mk, map_sum, map_sum,
    Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd ↦ ?_
  have hdN := Nat.divisor_le hd
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (Nat.pos_of_mem_divisors hd).ne'
  have hS := sL_mul_psi_chebyshevS n
  have h₁ := single_neg_mul_single_add N (n + 1)
  have h₂ := single_neg_mul_single N (n + 1) hdN
  rw [Nat.cast_add_one (R := ℤ), add_sub_cancel_right, map_mul, map_sub,
    HahnSeries.ofPowerSeries_X_pow, HahnSeries.ofPowerSeries_X_pow]
  simp only [map_mul, map_pow, map_natCast]
  push_cast at h₁ h₂ ⊢
  linear_combination ((n : LaurentSeries ℚ) + 1) ^ 2 * (h₁ - h₂) -
    ((n : LaurentSeries ℚ) + 1) ^ 2 * hS

private theorem ofPowerSeries_mk_id_mul_psi :
    HahnSeries.ofPowerSeries ℤ ℚ (mk fun a ↦ (a : ℚ)) * psi wP = 1 := by
  rw [psi_X_sub_two, mul_left_comm, ← map_mul, mk_id_mul_one_sub_X_sq,
    HahnSeries.ofPowerSeries_X, single_neg_one_mul_single_one]

private theorem ofPowerSeries_mk_sq_mul_psi_sq :
    HahnSeries.ofPowerSeries ℤ ℚ (mk fun a ↦ (a : ℚ) ^ 2) * psi wP ^ 2 = -sL := by
  rw [psi_X_sub_two, mul_pow, ← map_pow (HahnSeries.ofPowerSeries ℤ ℚ), ← pow_mul,
    mul_left_comm, ← map_mul (HahnSeries.ofPowerSeries ℤ ℚ), mk_sq_mul_one_sub_X_pow_four,
    map_sub (HahnSeries.ofPowerSeries ℤ ℚ), map_pow (HahnSeries.ofPowerSeries ℤ ℚ),
    HahnSeries.ofPowerSeries_X]
  linear_combination (HahnSeries.single (-1 : ℤ) (1 : ℚ) - HahnSeries.single (1 : ℤ) (1 : ℚ) *
    (HahnSeries.single (-1 : ℤ) (1 : ℚ) * HahnSeries.single (1 : ℤ) (1 : ℚ) + 1)) *
      single_neg_one_mul_single_one

private theorem psi_wP_ne_zero : psi wP ≠ 0 := fun h ↦ by
  simpa [h] using ofPowerSeries_mk_id_mul_psi

/-- Multiplied by `w`, the `x`-coordinate becomes `1 + w P`. -/
private theorem toLaurent_tateFormalX_mul :
    toLaurent (tateFormalX ℚ) * C (psi wP) = map psi (1 + C wP * tP) := by
  refine PowerSeries.ext fun N ↦ ?_
  rw [coeff_mul_C, coeff_toLaurent, coeff_map, map_add, coeff_one, coeff_C_mul]
  rcases eq_or_ne N 0 with rfl | hN
  · rw [coeff_zero_tateFormalX, tP, coeff_mk, Nat.divisors_zero, Finset.sum_empty, mul_zero,
      add_zero, ite_eq_left rfl, psi.map_one, Nat.cast_zero, neg_zero, HahnSeries.single_zero_one,
      one_mul, ofPowerSeries_mk_id_mul_psi]
  · rw [single_mul_coeff_tateFormalX hN, ite_eq_right hN, zero_add, map_mul, mul_comm]

/-- Multiplied by `w²`, the `y`-coordinate `2y + x` becomes `(u - u⁻¹) (-1 + w² Q)`. -/
private theorem toLaurent_two_mul_tateFormalY_add_mul :
    toLaurent (2 * tateFormalY ℚ + tateFormalX ℚ) * C (psi wP ^ 2) =
      C sL * map psi (-1 + C wP ^ 2 * tQ) := by
  refine PowerSeries.ext fun N ↦ ?_
  have hc : coeff N (-1 + C wP ^ 2 * tQ) = -coeff N 1 + wP ^ 2 * coeff N tQ := by
    rw [map_add, map_neg, ← map_pow, coeff_C_mul]
  rw [coeff_mul_C, coeff_toLaurent, coeff_C_mul, coeff_map, hc, coeff_one]
  rcases eq_or_ne N 0 with rfl | hN
  · rw [coeff_zero_two_mul_tateFormalY_add, tQ, coeff_mk, Nat.divisors_zero, Finset.sum_empty,
      mul_zero, add_zero, ite_eq_left rfl, psi.map_neg, psi.map_one, mul_neg_one, Nat.cast_zero,
      neg_zero, HahnSeries.single_zero_one, one_mul, ofPowerSeries_mk_sq_mul_psi_sq]
  · rw [single_mul_coeff_two_mul_tateFormalY_add hN, ite_eq_right hN, neg_zero, zero_add, map_mul,
      map_pow]
    ring

/-! ### The identity at `u = 1` -/

/-- The polar part of the Weierstrass equation, as an identity in any commutative ring: if
`x w = P`, `y w² = S Q` and `S² = w² + 4w`, and `P` and `Q` have the expansions that make the
displayed combination divisible by `w⁴`, then `w⁴ (y² - x² - 4x³ + 20 p x + 4 (p + 7 r))` is
divisible by `w⁵`. -/
private theorem pow_four_mul_eq {A : Type*} [CommRing A] {W x y S P Q p r h : A}
    (hx : x * W = P) (hy : y * W ^ 2 = S * Q) (hS : S ^ 2 = W ^ 2 + 4 * W)
    (hH : (W + 4) * Q ^ 2 - W * P ^ 2 - 4 * P ^ 3 + 20 * p * W ^ 2 * P +
      4 * (p + 7 * r) * W ^ 3 = W ^ 4 * h) :
    W ^ 4 * (y ^ 2 - x ^ 2 - 4 * x ^ 3 + 20 * p * x + 4 * (p + 7 * r)) = W ^ 4 * (W * h) := by
  linear_combination (y * W ^ 2 + S * Q) * hy - W ^ 2 * (x * W + P) * hx -
    4 * W * ((x * W) ^ 2 + x * W * P + P ^ 2) * hx + 20 * p * W ^ 3 * hx + Q ^ 2 * hS + W * hH

/-- The expansions of `P` and `Q` at `w = 0` make the polar combination divisible by `w⁴`. -/
private theorem exists_polar_eq : ∃ h : (Polynomial ℚ)⟦X⟧,
    (C wP + 4) * (-1 + C wP ^ 2 * tQ) ^ 2 - C wP * (1 + C wP * tP) ^ 2 -
        4 * (1 + C wP * tP) ^ 3 + 20 * sig₃ * C wP ^ 2 * (1 + C wP * tP) +
          4 * (sig₃ + 7 * sig₅) * C wP ^ 3 = C wP ^ 4 * h := by
  obtain ⟨A, hP⟩ := exists_tP_eq
  obtain ⟨B, hQ⟩ := exists_tQ_eq
  rw [hP, hQ]
  set W := C wP
  set p := sig₃
  set r := sig₅
  exact ⟨-8 * B - 12 * A - 6 * r + 12 * p ^ 2 - 2 * W * B - 2 * W * A + 12 * W * p * r +
    4 * W ^ 2 * r ^ 2 + 8 * W ^ 2 * p * B - 4 * W ^ 2 * p * A + 2 * W ^ 2 * p * r -
    4 * W ^ 2 * p ^ 3 + 16 * W ^ 3 * r * B - 24 * W ^ 3 * r * A + 3 * W ^ 3 * r ^ 2 +
    2 * W ^ 3 * p * B - 2 * W ^ 3 * p * A - 12 * W ^ 3 * p ^ 2 * r + 4 * W ^ 4 * B ^ 2 -
    12 * W ^ 4 * A ^ 2 + 4 * W ^ 4 * r * B - 2 * W ^ 4 * r * A - 12 * W ^ 4 * p * r ^ 2 -
    12 * W ^ 4 * p ^ 2 * A + W ^ 5 * B ^ 2 - W ^ 5 * A ^ 2 - 4 * W ^ 5 * r ^ 3 -
    24 * W ^ 5 * p * r * A - 12 * W ^ 6 * r ^ 2 * A - 12 * W ^ 6 * p * A ^ 2 -
    12 * W ^ 7 * r * A ^ 2 - 4 * W ^ 8 * A ^ 3, by ring⟩

/-! ### A formal Liouville theorem -/

/-- **A formal Liouville theorem.** Let `G ∈ ℚ⟦u⟧⟦v⟧` be symmetric in `u` and `v`. Suppose that
after substituting `v = q / u` each coefficient of `qᴺ` is `F(u + u⁻¹)` for a polynomial `F`
vanishing at `2`. Then `G = 0`.

A symmetric Laurent polynomial `L_N` in `u` that is the `qᴺ` coefficient has no exponent of
absolute value larger than `N`, and the symmetry in `u` and `v` moves the coefficient of `uᵐ` in
`L_N` to that of `uᵐ` in `L_{N-m}`. By induction only the constant terms survive, and these
vanish because `F(2) = 0`.

This is a formal counterpart of the non-archimedean Liouville theorem in Tate, *A review of
non-Archimedean elliptic functions*: an analytic function on `Kˣ` invariant under `u ↦ q u` is
constant. -/
private theorem eq_zero_of_swap_eq_self {G : ℚ⟦X⟧⟦X⟧} (hT : PowerSeries.swap G = G)
    {f : (Polynomial ℚ)⟦X⟧} (hj : toLaurent G = map psi (C wP * f)) : G = 0 := by
  set L : ℕ → LaurentPolynomial ℚ := fun N ↦ symmHom (coeff N (C wP * f)) with hLdef
  have hcoe (N : ℕ) (k : ℤ) :
      (L N).coeff k = if k + N < 0 then 0 else coeff (k + N).natAbs (coeff N G) := by
    rw [← LaurentPolynomial.coeff_toLaurentSeries]
    have h := congrArg (coeff N) hj
    rw [coeff_toLaurent, coeff_map] at h
    rw [hLdef, ← RingHom.comp_apply, ← h, HahnSeries.coeff_single_mul, one_mul, sub_neg_eq_add,
      PowerSeries.coeff_coe]
  have hsymm (N : ℕ) (k : ℤ) : (L N).coeff (-k) = (L N).coeff k := by
    have h : LaurentPolynomial.invert (L N) = L N :=
      (LaurentPolynomial.invert_eq_self_iff_exists_eval₂ _).mpr ⟨_, rfl⟩
    rw [← LaurentPolynomial.invert_apply, h]
  have hswap (a b : ℕ) : coeff a (coeff b G) = coeff b (coeff a G) := by
    rw [← PowerSeries.coeff_coeff_swap, hT]
  have key (N : ℕ) : ∀ m : ℕ, 0 < m → (L N).coeff m = 0 := by
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      intro m hm
      rw [← hsymm, hcoe]
      split_ifs with h
      · rfl
      · have hmN : m ≤ N := by omega
        have h' := ih (N - m) (by omega) m hm
        rw [hcoe, ite_eq_right (by omega)] at h'
        have e₁ : (-(m : ℤ) + N).natAbs = N - m := by omega
        have e₂ : ((m : ℤ) + (N - m : ℕ)).natAbs = N := by omega
        rw [e₁, hswap]
        rwa [e₂] at h'
  have hconst (N : ℕ) : L N = LaurentPolynomial.C ((L N).coeff 0) := by
    refine LaurentPolynomial.ext fun k ↦ ?_
    rw [LaurentPolynomial.C_apply]
    rcases lt_trichotomy k 0 with hk | rfl | hk
    · obtain ⟨m, rfl⟩ : ∃ m : ℕ, k = -m := ⟨k.natAbs, by omega⟩
      rw [hsymm, key N m (by omega), ite_eq_right (by omega)]
    · simp
    · obtain ⟨m, rfl⟩ : ∃ m : ℕ, k = m := ⟨k.natAbs, by omega⟩
      rw [key N m (by omega), ite_eq_right (by omega)]
  have hzero (N : ℕ) : L N = 0 := by
    set ev := LaurentPolynomial.eval₂ (RingHom.id ℚ) (1 : ℚˣ)
    have hw : ev (symmHom wP) = 0 := by
      simp [ev, symmHom, wP]
      norm_num
    have h : ev (L N) = 0 := by
      simp only [hLdef, coeff_C_mul, map_mul, hw, zero_mul]
    rw [hconst N, LaurentPolynomial.eval₂_C, RingHom.id_apply] at h
    rw [hconst N, h, _root_.map_zero]
  refine PowerSeries.ext fun b ↦ PowerSeries.ext fun a ↦ ?_
  have h := hcoe b ((a : ℤ) - b)
  have e : ((a : ℤ) - b + b).natAbs = a := by omega
  rw [hzero, ite_eq_right (by omega), e] at h
  rw [_root_.map_zero, _root_.map_zero]
  exact h.symm.trans (by simp)

/-! ### The Weierstrass equation -/

private theorem coeff_toLaurent_tateParamHom (g : ℤ⟦X⟧) (N : ℕ) :
    coeff N (toLaurent (tateParamHom ℚ g)) = HahnSeries.C ((coeff N g : ℤ) : ℚ) := by
  rw [coeff_toLaurent, tateParamHom, RingHom.comp_apply, coeff_rescale, coeff_map,
    RingHom.comp_apply, map_mul, map_pow, HahnSeries.ofPowerSeries_X, HahnSeries.single_pow,
    HahnSeries.ofPowerSeries_C, ← mul_assoc, HahnSeries.single_mul_single]
  simp

private theorem toLaurent_tateParamHom_a₄ :
    toLaurent (tateParamHom ℚ tateCurve.a₄) = -5 * map psi sig₃ := by
  refine PowerSeries.ext fun N ↦ ?_
  rw [coeff_toLaurent_tateParamHom, coeff_tateCurve_a₄, ← map_ofNat C 5, ← map_neg, coeff_C_mul,
    coeff_map, sig₃, coeff_mk, psi_C]
  push_cast
  rw [map_mul, map_neg, map_ofNat]

private theorem toLaurent_tateParamHom_a₆ :
    toLaurent (tateParamHom ℚ tateCurve.a₆) = -(map psi sig₃ + 7 * map psi sig₅) := by
  refine PowerSeries.ext fun N ↦ ?_
  have h : (12 : ℚ) * ((coeff N tateCurve.a₆ : ℤ) : ℚ) = -(5 * σ 3 N + 7 * σ 5 N) := by
    exact_mod_cast twelve_mul_coeff_tateCurve_a₆ N
  rw [coeff_toLaurent_tateParamHom, ← map_ofNat C 7, map_neg, map_add, coeff_C_mul, coeff_map,
    coeff_map, sig₃, sig₅, coeff_mk, coeff_mk, psi_C, psi_C, ← map_ofNat HahnSeries.C 7,
    ← map_mul, ← map_add, ← map_neg]
  congr 1
  linear_combination h / 12

/-- **The formal Tate point is on the Tate curve, over `ℚ`**, in the form `(2y + x)² = x² + 4x³ +
4a₄x + 4a₆`. -/
private theorem two_mul_tateFormalY_add_sq_sub_eq_zero :
    (2 * tateFormalY ℚ + tateFormalX ℚ) ^ 2 - tateFormalX ℚ ^ 2 - 4 * tateFormalX ℚ ^ 3 -
      4 * tateParamHom ℚ tateCurve.a₄ * tateFormalX ℚ - 4 * tateParamHom ℚ tateCurve.a₆ = 0 := by
  obtain ⟨h, hH⟩ := exists_polar_eq
  refine eq_zero_of_swap_eq_self (f := h) ?_ ?_
  · simp only [map_sub, map_mul, map_pow, map_add, map_ofNat, swap_tateFormalX, swap_tateFormalY,
      swap_tateParamHom]
    ring
  have hx := toLaurent_tateFormalX_mul
  have hy := toLaurent_two_mul_tateFormalY_add_mul
  have hS : (C sL : (LaurentSeries ℚ)⟦X⟧) ^ 2 = C (psi wP) ^ 2 + 4 * C (psi wP) := by
    rw [← map_pow, sL_sq, map_add, map_pow, map_mul, map_ofNat (C (R := LaurentSeries ℚ)) 4]
  rw [map_pow, ← map_C] at hy
  rw [← map_C] at hx hS
  rw [map_mul]
  generalize 1 + C wP * tP = Pt at hH hx
  generalize -1 + C wP ^ 2 * tQ = Qt at hH hy
  have hW : map psi (C wP) ^ 4 ≠ 0 := by
    rw [map_C]
    exact pow_ne_zero _ ((map_ne_zero_iff _ (C_injective (R := LaurentSeries ℚ))).mpr
      psi_wP_ne_zero)
  generalize C wP = W at hH hx hy hS hW ⊢
  have hH' := congrArg (map psi) hH
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat] at hH'
  refine mul_left_cancel₀ hW (Eq.trans ?_ (pow_four_mul_eq hx hy hS hH'))
  simp only [map_sub, map_mul, map_pow, map_ofNat, toLaurent_tateParamHom_a₄,
    toLaurent_tateParamHom_a₆]
  ring

private theorem equation_rat :
    (tateCurve.map (tateParamHom ℚ)).toAffine.Equation (tateFormalX ℚ) (tateFormalY ℚ) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆, tateCurve_a₁, tateCurve_a₂, tateCurve_a₃,
    map_one, _root_.map_zero]
  have h₄ : (4 : ℚ⟦X⟧⟦X⟧) ≠ 0 := fun h ↦ by
    have h' := congrArg (fun F ↦ constantCoeff (constantCoeff F)) h
    simp only [map_ofNat, _root_.map_zero] at h'
    norm_num at h'
  refine mul_left_cancel₀ h₄ ?_
  linear_combination two_mul_tateFormalY_add_sq_sub_eq_zero

variable {S : Type*} [CommRing S]

/-- The formal Tate coordinate `x` is compatible with change of coefficients. -/
@[simp]
theorem map_map_tateFormalX (f : R →+* S) : map (map f) (tateFormalX R) = tateFormalX S := by
  refine PowerSeries.ext fun b ↦ PowerSeries.ext fun a ↦ ?_
  simp only [coeff_map, coeff_coeff_tateFormalX]
  split_ifs <;> simp [map_ofNat]

/-- The formal Tate coordinate `y` is compatible with change of coefficients. -/
@[simp]
theorem map_map_tateFormalY (f : R →+* S) : map (map f) (tateFormalY R) = tateFormalY S := by
  refine PowerSeries.ext fun b ↦ PowerSeries.ext fun a ↦ ?_
  simp only [coeff_map, coeff_coeff_tateFormalY]
  split_ifs <;> simp

/-- The substitution `q = u v` is compatible with change of coefficients. -/
@[simp]
theorem map_map_comp_tateParamHom (f : R →+* S) :
    (map (map f)).comp (tateParamHom R) = tateParamHom S := by
  refine RingHom.ext fun g ↦ PowerSeries.ext fun b ↦ PowerSeries.ext fun a ↦ ?_
  simp only [RingHom.comp_apply, coeff_map, coeff_coeff_tateParamHom]
  split_ifs <;> simp

variable (R) in
/-- **The formal Tate point lies on the Tate curve**: over `R⟦u⟧⟦v⟧` with `q = u v`, the formal
Tate coordinates satisfy `y² + x y = x³ + a₄(q) x + a₆(q)` (Silverman, *Advanced Topics*, §V.1). -/
theorem equation_tateFormalX_tateFormalY :
    (tateCurve.map (tateParamHom R)).toAffine.Equation (tateFormalX R) (tateFormalY R) := by
  -- The identity holds over `ℚ`; it descends to `ℤ` by injectivity of `ℤ → ℚ`, then maps to `R`.
  have hinj : Function.Injective (map (map (Int.castRingHom ℚ))) :=
    map_injective _ (map_injective _ Int.cast_injective)
  have hℤ :
      (tateCurve.map (tateParamHom ℤ)).toAffine.Equation (tateFormalX ℤ) (tateFormalY ℤ) := by
    rw [← WeierstrassCurve.Affine.map_equation _ hinj]
    -- `Affine.map` abbreviates `WeierstrassCurve.map`; unfold it to compose the two base changes.
    dsimp only [WeierstrassCurve.Affine.map]
    rw [WeierstrassCurve.map_map, map_map_comp_tateParamHom, map_map_tateFormalX,
      map_map_tateFormalY]
    exact equation_rat
  have h := hℤ.map (map (map (Int.castRingHom R)))
  -- As above, unfold `Affine.map` to compose the two base changes.
  dsimp only [WeierstrassCurve.Affine.map] at h
  rwa [WeierstrassCurve.map_map, map_map_comp_tateParamHom, map_map_tateFormalX,
    map_map_tateFormalY] at h

end TauCeti

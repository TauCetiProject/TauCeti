/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.NumberTheory.Divisors
public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.PiTopology
public import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors
public import TauCeti.RingTheory.Polynomial.Monic.Irreducible
public import TauCeti.RingTheory.Polynomial.Monic.OfCoeff.Basic
public import TauCeti.RingTheory.PowerSeries.Derivative
import TauCeti.RingTheory.Polynomial.Monic.Factorization
import TauCeti.RingTheory.PowerSeries.Basic

/-!
# The `L`-series of a multiplicative function on monic polynomials

Let `F` be a finite field and `λ : F[X] → R` a function that is multiplicative on monic
polynomials: `λ 1 = 1` and `λ (g * h) = λ g * λ h` for monic `g` and `h`
(`TauCeti.Polynomial.IsMonicMultiplicative`; the values off the monic polynomials do not matter).
Its `L`-series is the power series

`L(λ, T) = ∑_{d ≥ 0} (∑_{g monic, deg g = d} λ(g)) T ^ d` (`TauCeti.Polynomial.lSeries`),

whose degree-`d` coefficient sums over the `q ^ d` monic polynomials `X ^ d + ∑_{i < d} c_i X ^ i`
(`TauCeti.Polynomial.monicOfCoeff`). The character sums of Weil's theorem are coefficients of such
series. This file proves the three facts that make the series useful.

* **The Euler product.** Unique factorization in `F[X]` gives
  `L(λ, T) = ∏_P (1 - λ(P) T ^ deg P)⁻¹` over the monic irreducible `P`, as an infinite product
  in Mathlib's coefficientwise topology `PowerSeries.WithPiTopology`. Only the finitely many `P`
  of degree at most `n` affect the coefficient of `T ^ n`, so the finite products converge
  coefficientwise. The Euler factor `(1 - λ(P) T ^ deg P)⁻¹` is
  `TauCeti.Polynomial.lSeriesFactor λ P = ∑_k λ(P) ^ k T ^ (k deg P)`, which makes sense over any
  commutative semiring `R`; over a field it is the inverse.
* **The logarithmic derivative.** `T L'(λ, T) = (∑_{n ≥ 1} S_n(λ) T ^ n) L(λ, T)`, where
  `S_n(λ) = ∑_P deg P · λ(P) ^ (n / deg P)` over the monic irreducible `P` of degree dividing `n`
  (`TauCeti.Polynomial.lSeriesPowerSum`). Each Euler factor `E` satisfies `T E' = D E` with
  `D = deg P · λ(P) T ^ deg P · E`, and the identity for `L` is the limit of the finite products.
* **The polynomial criterion.** If the coefficient sums vanish from degree `d₀` on, then
  `L(λ, T)` is a polynomial of degree less than `d₀`.

Multiplicativity on monic polynomials and the identities for a single Euler factor hold over every
semiring `F`, with values in a monoid or a semiring `R`; the derivative identities need `R`
commutative. The series `L(λ, T)` and the polynomial criterion hold for every finite commutative
semiring `F`, and the power sums `S_n(λ)` for every finite semiring `F`. The degree-`d` coefficient
sums over the polynomials `monicOfCoeff c`, `c : Fin d → F`
(`TauCeti.Polynomial.coeff_lSeries_eq_sum_monicOfCoeff`), which are the monic polynomials of
degree `d` when `F` is nontrivial (`TauCeti.Polynomial.coeff_lSeries`). All of these depend only
on the values of `λ` on monic polynomials. The Euler product and the logarithmic derivative of
`L(λ, T)` use unique factorization in `F[X]`, so they need a field.

## Main definitions

* `TauCeti.Polynomial.IsMonicMultiplicative λ`: `λ` is multiplicative on monic polynomials.
* `TauCeti.Polynomial.lSeries λ`: the `L`-series `L(λ, T)`.
* `TauCeti.Polynomial.lSeriesFactor λ P`: the Euler factor, `∑_k λ(P) ^ k T ^ (k deg P)` for
  `deg P > 0` and `1` for `deg P = 0`.
* `TauCeti.Polynomial.lSeriesPowerSum λ n`: the power sum `S_n(λ)`.

## Main results

* `TauCeti.Polynomial.isMonicMultiplicative_congr`, `TauCeti.Polynomial.lSeries_congr`,
  `TauCeti.Polynomial.lSeriesPowerSum_congr`: functions that agree on monic polynomials have the
  same multiplicativity, `L`-series and power sums.
* `TauCeti.Polynomial.coeff_lSeriesFactor`, `TauCeti.Polynomial.constantCoeff_lSeriesFactor`,
  `TauCeti.Polynomial.lSeriesFactor_eq_one_add`, `TauCeti.Polynomial.lSeriesFactor_eq_inv`: the
  coefficients of an Euler factor, its constant coefficient `1`, the equation that it satisfies,
  and its value `(1 - λ(P) T ^ deg P)⁻¹` over a field.
* `TauCeti.Polynomial.coeff_lSeries_eq_sum_monicOfCoeff`, `TauCeti.Polynomial.coeff_lSeries`,
  `TauCeti.Polynomial.constantCoeff_lSeries`: the coefficients of `L(λ, T)`, and its constant
  coefficient `λ 1`, which is `1` for multiplicative `λ`.
* `TauCeti.Polynomial.lSeriesPowerSum_eq_sum_divisors`: `S_n(λ)` as a sum over the divisors `e` of
  `n` and the monic irreducibles of degree `e`.
* `TauCeti.Polynomial.coeff_prod_lSeriesFactor`: for a finite set `S` of monic irreducibles, the
  coefficient of `T ^ n` in `∏_{P ∈ S} lSeriesFactor λ P` is the sum of `λ` over the monic
  polynomials of degree `n` whose irreducible factors lie in `S`.
* `TauCeti.Polynomial.hasProd_lSeriesFactor`, `TauCeti.Polynomial.lSeries_eq_tprod_lSeriesFactor`,
  `TauCeti.Polynomial.hasProd_inv_one_sub_lSeries`, `TauCeti.Polynomial.lSeries_eq_tprod`: the
  Euler product.
* `TauCeti.Polynomial.X_mul_derivative_lSeries`,
  `TauCeti.Polynomial.X_mul_derivative_lSeries_mul_inv`: the logarithmic derivative.
* `TauCeti.Polynomial.exists_degree_lt_coe_eq_lSeries`: the polynomial criterion, from
  `PowerSeries.exists_degree_lt_coe_eq`.

## References

* K. Ireland and M. Rosen, *A Classical Introduction to Modern Number Theory*, 2nd ed., Graduate
  Texts in Mathematics 84, Springer, 1990, Chapter 11, §4.
-/

public section

open Finset Polynomial UniqueFactorizationMonoid

namespace TauCeti.Polynomial

/-! ### Multiplicative functions on monic polynomials -/

section Monoid

variable {F R : Type*} [Semiring F] [Monoid R]

/-- A function on `F[X]` is *multiplicative on monic polynomials* if it sends `1` to `1` and
`g * h` to `λ g * λ h` for all monic `g` and `h`. -/
def IsMonicMultiplicative (lam : F[X] → R) : Prop :=
  lam 1 = 1 ∧ ∀ g h : F[X], g.Monic → h.Monic → lam (g * h) = lam g * lam h

theorem isMonicMultiplicative_iff {lam : F[X] → R} :
    IsMonicMultiplicative lam ↔
      lam 1 = 1 ∧ ∀ g h : F[X], g.Monic → h.Monic → lam (g * h) = lam g * lam h :=
  Iff.rfl

theorem IsMonicMultiplicative.map_one {lam : F[X] → R} (hlam : IsMonicMultiplicative lam) :
    lam 1 = 1 :=
  hlam.1

theorem IsMonicMultiplicative.map_mul {lam : F[X] → R} (hlam : IsMonicMultiplicative lam)
    {g h : F[X]} (hg : g.Monic) (hh : h.Monic) : lam (g * h) = lam g * lam h :=
  hlam.2 g h hg hh

theorem IsMonicMultiplicative.map_pow {lam : F[X] → R} (hlam : IsMonicMultiplicative lam)
    {P : F[X]} (hP : P.Monic) (k : ℕ) : lam (P ^ k) = lam P ^ k := by
  induction k with
  | zero => simpa using hlam.map_one
  | succ k ih => rw [pow_succ, hlam.map_mul (hP.pow k) hP, ih, pow_succ]

/-- Multiplicativity on monic polynomials depends only on the values on monic polynomials. -/
theorem isMonicMultiplicative_congr {lam mu : F[X] → R} (h : ∀ g : F[X], g.Monic → lam g = mu g) :
    IsMonicMultiplicative lam ↔ IsMonicMultiplicative mu := by
  refine ⟨fun hlam ↦ ⟨(h 1 monic_one).symm.trans hlam.map_one, fun g k hg hk ↦ ?_⟩,
    fun hmu ↦ ⟨(h 1 monic_one).trans hmu.map_one, fun g k hg hk ↦ ?_⟩⟩
  · rw [← h _ (hg.mul hk), ← h g hg, ← h k hk, hlam.map_mul hg hk]
  · rw [h _ (hg.mul hk), h g hg, h k hk, hmu.map_mul hg hk]

end Monoid

theorem IsMonicMultiplicative.map_prod_pow {F R : Type*} [CommSemiring F] [CommMonoid R]
    {lam : F[X] → R} (hlam : IsMonicMultiplicative lam) {ι : Type*} (s : Finset ι) (P : ι → F[X])
    (e : ι → ℕ) (hP : ∀ i ∈ s, (P i).Monic) :
    lam (∏ i ∈ s, P i ^ e i) = ∏ i ∈ s, lam (P i) ^ e i := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hlam.map_one
  | insert i s hi ih =>
    rw [prod_insert hi, prod_insert hi,
      hlam.map_mul ((hP i (mem_insert_self i s)).pow _)
        (monic_prod_of_monic _ _ fun j hj ↦ (hP j (mem_insert_of_mem hj)).pow _),
      hlam.map_pow (hP i (mem_insert_self i s)), ih fun j hj ↦ hP j (mem_insert_of_mem hj)]

/-! ### Euler factors -/

section Semiring

variable {F R : Type*} [Semiring F] [Semiring R]

/-- The Euler factor of `L(λ, T)` at `P`: the coefficient of `T ^ m` is `λ(P) ^ (m / deg P)` if
`deg P ∣ m` and `0` otherwise. For `deg P > 0` it is the geometric series
`∑_k λ(P) ^ k T ^ (k deg P)`, the inverse of `1 - λ(P) T ^ deg P`
(`TauCeti.Polynomial.one_sub_mul_lSeriesFactor`). For `deg P = 0` it is `1`
(`TauCeti.Polynomial.lSeriesFactor_of_natDegree_eq_zero`). -/
noncomputable def lSeriesFactor (lam : F[X] → R) (P : F[X]) : PowerSeries R :=
  PowerSeries.mk fun m ↦ if P.natDegree ∣ m then lam P ^ (m / P.natDegree) else 0

@[simp]
theorem coeff_lSeriesFactor (lam : F[X] → R) (P : F[X]) (m : ℕ) :
    PowerSeries.coeff m (lSeriesFactor lam P) =
      if P.natDegree ∣ m then lam P ^ (m / P.natDegree) else 0 :=
  PowerSeries.coeff_mk _ _

/-- The constant coefficient of an Euler factor is `1`, also for `deg P = 0`. -/
@[simp]
theorem constantCoeff_lSeriesFactor (lam : F[X] → R) (P : F[X]) :
    PowerSeries.constantCoeff (lSeriesFactor lam P) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_lSeriesFactor]
  simp

theorem lSeriesFactor_of_natDegree_eq_zero (lam : F[X] → R) {P : F[X]} (hP : P.natDegree = 0) :
    lSeriesFactor lam P = 1 := by
  ext m
  simp [hP, PowerSeries.coeff_one]

/-- For `deg P > 0`, the coefficient of `T ^ i` in `λ(P) T ^ deg P · lSeriesFactor λ P` is
`λ(P) ^ (i / deg P)` if `deg P ∣ i` and `i ≠ 0`, and `0` otherwise. -/
theorem coeff_C_mul_X_pow_mul_lSeriesFactor_of_natDegree_pos (lam : F[X] → R) {P : F[X]}
    (hP : 0 < P.natDegree) (i : ℕ) :
    PowerSeries.coeff i
        (PowerSeries.C (lam P) * PowerSeries.X ^ P.natDegree * lSeriesFactor lam P) =
      if P.natDegree ∣ i ∧ i ≠ 0 then lam P ^ (i / P.natDegree) else 0 := by
  rw [mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul', coeff_lSeriesFactor]
  set d := P.natDegree
  by_cases hdi : d ∣ i
  · obtain ⟨k, rfl⟩ := hdi
    rcases k with _ | j
    · simp [hP.ne']
    · have h : d * (j + 1) - d = d * j := by rw [mul_add_one, Nat.add_sub_cancel]
      simp [h, Nat.mul_div_cancel_left _ hP, hP.ne', Nat.le_mul_of_pos_right _ j.succ_pos,
        pow_succ']
  · have h : ¬(d ≤ i ∧ d ∣ i - d) := fun h ↦
      hdi (by simpa [Nat.sub_add_cancel h.1] using Nat.dvd_add h.2 (dvd_refl d))
    split_ifs <;> simp_all

/-- For `deg P > 0`, the Euler factor `E` satisfies `E = 1 + λ(P) T ^ deg P · E`. -/
theorem lSeriesFactor_eq_one_add (lam : F[X] → R) {P : F[X]} (hP : 0 < P.natDegree) :
    lSeriesFactor lam P =
      1 + PowerSeries.C (lam P) * PowerSeries.X ^ P.natDegree * lSeriesFactor lam P := by
  ext m
  rw [map_add, coeff_C_mul_X_pow_mul_lSeriesFactor_of_natDegree_pos lam hP, coeff_lSeriesFactor,
    PowerSeries.coeff_one]
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  · simp [hm]

/-- The Euler factor is the inverse of `1 - λ(P) T ^ deg P`. -/
theorem one_sub_mul_lSeriesFactor {R : Type*} [Ring R] (lam : F[X] → R) {P : F[X]}
    (hP : 0 < P.natDegree) :
    (1 - PowerSeries.C (lam P) * PowerSeries.X ^ P.natDegree) * lSeriesFactor lam P = 1 := by
  rw [sub_mul, one_mul, sub_eq_iff_eq_add]
  exact lSeriesFactor_eq_one_add lam hP

/-- Over a field, the Euler factor is `(1 - λ(P) T ^ deg P)⁻¹`. -/
theorem lSeriesFactor_eq_inv {K : Type*} [Field K] (lam : F[X] → K) {P : F[X]}
    (hP : 0 < P.natDegree) :
    lSeriesFactor lam P = (1 - PowerSeries.C (lam P) * PowerSeries.X ^ P.natDegree)⁻¹ := by
  rw [PowerSeries.eq_inv_iff_mul_eq_one, mul_comm, one_sub_mul_lSeriesFactor lam hP]
  simp [hP.ne']

/-- The coefficients of `D_P = λ(P) deg P · X ^ deg P · lSeriesFactor λ P`. -/
theorem coeff_C_mul_X_pow_mul_lSeriesFactor (lam : F[X] → R) (P : F[X]) (i : ℕ) :
    PowerSeries.coeff i (PowerSeries.C (lam P * P.natDegree) * PowerSeries.X ^ P.natDegree *
        lSeriesFactor lam P) =
      if P.natDegree ∣ i ∧ i ≠ 0 then P.natDegree * lam P ^ (i / P.natDegree) else 0 := by
  rcases Nat.eq_zero_or_pos P.natDegree with hP | hP
  · simp [hP]
  have h : PowerSeries.C (lam P * P.natDegree) * PowerSeries.X ^ P.natDegree *
      lSeriesFactor lam P = PowerSeries.C (P.natDegree : R) *
        (PowerSeries.C (lam P) * PowerSeries.X ^ P.natDegree * lSeriesFactor lam P) := by
    rw [← Nat.cast_comm P.natDegree (lam P), map_mul]
    simp only [mul_assoc]
  rw [h, PowerSeries.coeff_C_mul, coeff_C_mul_X_pow_mul_lSeriesFactor_of_natDegree_pos lam hP]
  split_ifs <;> simp

end Semiring

/-! ### The logarithmic derivative of the Euler factors -/

section CommSemiring

variable {F R : Type*} [Semiring F] [CommSemiring R]

/-- The logarithmic derivative of an Euler factor: `X E' = D E` with
`D = λ(P) deg P · X ^ deg P · E`, where `E = lSeriesFactor λ P`. -/
theorem X_mul_derivative_lSeriesFactor (lam : F[X] → R) (P : F[X]) :
    PowerSeries.X * PowerSeries.derivative (R := R) (lSeriesFactor lam P) =
      PowerSeries.C (lam P * P.natDegree) * PowerSeries.X ^ P.natDegree * lSeriesFactor lam P *
        lSeriesFactor lam P := by
  rcases Nat.eq_zero_or_pos P.natDegree with hP | hP
  · simp [lSeriesFactor_of_natDegree_eq_zero lam hP, hP]
  set E := lSeriesFactor lam P
  set d := P.natDegree
  have hE : E = 1 + PowerSeries.C (lam P) * PowerSeries.X ^ d * E :=
    lSeriesFactor_eq_one_add lam hP
  have hX : PowerSeries.X * PowerSeries.derivative (R := R)
      (PowerSeries.C (lam P) * PowerSeries.X ^ d) =
        PowerSeries.C (lam P * d) * PowerSeries.X ^ d := by
    rw [PowerSeries.derivative_C_mul_X_pow, mul_left_comm, ← pow_succ', Nat.sub_add_cancel hP]
  have hd := congrArg (fun f ↦ PowerSeries.X * PowerSeries.derivative (R := R) f) hE
  simp only [map_add, Derivation.map_one_eq_zero, zero_add, PowerSeries.X_mul_derivative_mul,
    hX] at hd
  -- Both sides solve `D = C (λ(P) deg P) X ^ deg P E + λ(P) X ^ deg P D`.
  refine TauCeti.eq_of_eq_add_C_mul_X_pow_mul
    (B := PowerSeries.C (lam P * d) * PowerSeries.X ^ d * E) (a := lam P) hP hd ?_
  calc PowerSeries.C (lam P * d) * PowerSeries.X ^ d * E * E
      = PowerSeries.C (lam P * d) * PowerSeries.X ^ d * E *
          (1 + PowerSeries.C (lam P) * PowerSeries.X ^ d * E) := by rw [← hE]
    _ = _ := by ring

/-- The logarithmic derivative of a finite Euler product:
`X (∏_{P ∈ S} E_P)' = (∑_{P ∈ S} D_P) ∏_{P ∈ S} E_P`. -/
theorem X_mul_derivative_prod_lSeriesFactor (lam : F[X] → R) (S : Finset F[X]) :
    PowerSeries.X * PowerSeries.derivative (R := R) (∏ P ∈ S, lSeriesFactor lam P) =
      (∑ P ∈ S, PowerSeries.C (lam P * P.natDegree) * PowerSeries.X ^ P.natDegree *
        lSeriesFactor lam P) * ∏ P ∈ S, lSeriesFactor lam P := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert Q S hQ ih =>
    rw [prod_insert hQ, sum_insert hQ, PowerSeries.X_mul_derivative_mul, ih,
      X_mul_derivative_lSeriesFactor]
    ring

end CommSemiring

/-! ### The `L`-series -/

section LSeries

variable {F R : Type*} [CommSemiring F]

/-- The `L`-series of a function `λ` on `F[X]`: the coefficient of `T ^ d` sums `λ` over the
polynomials `monicOfCoeff c`, `c : Fin d → F`
(`TauCeti.Polynomial.coeff_lSeries_eq_sum_monicOfCoeff`). For a nontrivial `F` (for instance a
field) these are the monic polynomials of degree `d`, so
`L(λ, T) = ∑_d (∑_{g monic, deg g = d} λ(g)) T ^ d` (`TauCeti.Polynomial.coeff_lSeries`). -/
noncomputable def lSeries [Finite F] [AddCommMonoid R] (lam : F[X] → R) : PowerSeries R :=
  letI := Fintype.ofFinite F
  PowerSeries.mk fun d ↦ ∑ c : Fin d → F, lam (monicOfCoeff c)

/-- The `L`-series depends only on the values of `λ` on monic polynomials. -/
theorem lSeries_congr [Finite F] [AddCommMonoid R] {lam mu : F[X] → R}
    (h : ∀ g : F[X], g.Monic → lam g = mu g) : lSeries lam = lSeries mu := by
  rw [lSeries, lSeries]
  exact congrArg PowerSeries.mk (funext fun d ↦ sum_congr rfl fun c _ ↦ h _ (monic_monicOfCoeff c))

variable [Semiring R]

/-- The degree-`d` coefficient of `L(λ, T)` is the sum of `λ` over the polynomials
`monicOfCoeff c`, `c : Fin d → F`. -/
theorem coeff_lSeries_eq_sum_monicOfCoeff [Fintype F] (lam : F[X] → R) (d : ℕ) :
    PowerSeries.coeff d (lSeries lam) = ∑ c : Fin d → F, lam (monicOfCoeff c) := by
  rw [lSeries, PowerSeries.coeff_mk]
  convert rfl

variable [Finite F]

/-- For a nontrivial `F`, the degree-`d` coefficient of `L(λ, T)` is the sum of `λ` over the monic
polynomials of degree `d`. -/
@[simp]
theorem coeff_lSeries [Nontrivial F] (lam : F[X] → R) (d : ℕ) :
    PowerSeries.coeff d (lSeries lam) = ∑ g ∈ monicsOfDegree F d, lam g := by
  have := Fintype.ofFinite F
  rw [coeff_lSeries_eq_sum_monicOfCoeff, sum_monicsOfDegree]

/-- The constant coefficient of `L(λ, T)` is `λ 1`. -/
@[simp]
theorem constantCoeff_lSeries (lam : F[X] → R) :
    PowerSeries.constantCoeff (lSeries lam) = lam 1 := by
  have := Fintype.ofFinite F
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_lSeries_eq_sum_monicOfCoeff]
  simp

/-- The `L`-series of a function multiplicative on monic polynomials has constant
coefficient `1`. -/
theorem constantCoeff_lSeries_of_isMonicMultiplicative {lam : F[X] → R}
    (hlam : IsMonicMultiplicative lam) : PowerSeries.constantCoeff (lSeries lam) = 1 := by
  rw [constantCoeff_lSeries, hlam.map_one]

/-! ### The polynomial criterion -/

/-- **The polynomial criterion.** If the coefficient sums of `L(λ, T)` vanish in every degree
`d ≥ d₀`, then `L(λ, T)` is a polynomial of degree less than `d₀` (the zero polynomial if
`d₀ = 0`). -/
theorem exists_degree_lt_coe_eq_lSeries (lam : F[X] → R) {d₀ : ℕ}
    (h : ∀ d ≥ d₀, PowerSeries.coeff d (lSeries lam) = 0) :
    ∃ p : R[X], p.degree < d₀ ∧ (p : PowerSeries R) = lSeries lam :=
  (lSeries lam).exists_degree_lt_coe_eq h

end LSeries

/-! ### The power sums -/

section PowerSum

variable {F R : Type*} [Semiring F] [Finite F] [Semiring R]

open Classical in
/-- The power sum `S_n(λ) = ∑_P deg P · λ(P) ^ (n / deg P)` over the monic irreducible `P` whose
degree divides `n`; it is `0` for `n = 0` (`TauCeti.Polynomial.lSeriesPowerSum_zero`). -/
noncomputable def lSeriesPowerSum (lam : F[X] → R) (n : ℕ) : R :=
  ∑ P ∈ n.divisors.biUnion fun e ↦ (finite_monicIrreduciblesOfDegree F e).toFinset,
    (P.natDegree : R) * lam P ^ (n / P.natDegree)

@[simp]
theorem lSeriesPowerSum_zero (lam : F[X] → R) : lSeriesPowerSum lam 0 = 0 := by
  simp [lSeriesPowerSum]

/-- `S_n(λ)` summed degree by degree: over the divisors `e` of `n`, and over the monic irreducible
`P` of degree `e`. -/
theorem lSeriesPowerSum_eq_sum_divisors (lam : F[X] → R) (n : ℕ) :
    lSeriesPowerSum lam n = ∑ e ∈ n.divisors,
      ∑ P ∈ (finite_monicIrreduciblesOfDegree F e).toFinset, (e : R) * lam P ^ (n / e) := by
  classical
  rw [lSeriesPowerSum, sum_biUnion]
  · refine sum_congr rfl fun e _ ↦ sum_congr rfl fun P hP ↦ ?_
    rw [(mem_monicIrreduciblesOfDegree_iff.1 ((Set.Finite.mem_toFinset _).1 hP)).2.2]
  · intro e₁ _ e₂ _ he
    refine disjoint_left.2 fun P hP₁ hP₂ ↦ he ?_
    rw [Set.Finite.mem_toFinset, mem_monicIrreduciblesOfDegree_iff] at hP₁ hP₂
    exact hP₁.2.2.symm.trans hP₂.2.2

/-- The power sums depend only on the values of `λ` on monic polynomials. -/
theorem lSeriesPowerSum_congr {lam mu : F[X] → R} (h : ∀ g : F[X], g.Monic → lam g = mu g)
    (n : ℕ) : lSeriesPowerSum lam n = lSeriesPowerSum mu n := by
  rw [lSeriesPowerSum_eq_sum_divisors, lSeriesPowerSum_eq_sum_divisors]
  refine sum_congr rfl fun e _ ↦ sum_congr rfl fun P hP ↦ ?_
  rw [h P (mem_monicIrreduciblesOfDegree_iff.1 ((Set.Finite.mem_toFinset _).1 hP)).1]

/-- `S_n(λ)` is the sum over any finset `S` whose elements are exactly the monic irreducible `P`
with `deg P ∣ n`, for `n ≠ 0`; for `n = 0` such an `S` is empty. -/
theorem lSeriesPowerSum_eq_sum (lam : F[X] → R) {n : ℕ} {S : Finset F[X]}
    (hS : ∀ P, P ∈ S ↔ P.Monic ∧ Irreducible P ∧ P.natDegree ∣ n ∧ n ≠ 0) :
    lSeriesPowerSum lam n = ∑ P ∈ S, (P.natDegree : R) * lam P ^ (n / P.natDegree) := by
  classical
  rw [lSeriesPowerSum]
  refine sum_congr (ext fun P ↦ ?_) fun _ _ ↦ rfl
  simp only [mem_biUnion, Nat.mem_divisors, Set.Finite.mem_toFinset,
    mem_monicIrreduciblesOfDegree_iff, hS]
  constructor
  · rintro ⟨e, he, hPm, hPirr, rfl⟩
    exact ⟨hPm, hPirr, he⟩
  · rintro ⟨hPm, hPirr, he⟩
    exact ⟨_, he, hPm, hPirr, rfl⟩

/-- Once `S` contains every monic irreducible of degree at most `i`, the coefficient of `T ^ i`
in `∑_{P ∈ S} D_P` is `S_i(λ)`. -/
theorem sum_ite_eq_lSeriesPowerSum (lam : F[X] → R) {S : Finset F[X]}
    (hS : ∀ P ∈ S, P.Monic ∧ Irreducible P) {i : ℕ}
    (hi : ∀ P : F[X], P.Monic → Irreducible P → P.natDegree ≤ i → P ∈ S) :
    ∑ P ∈ S, (if P.natDegree ∣ i ∧ i ≠ 0 then (P.natDegree : R) * lam P ^ (i / P.natDegree)
      else 0) = lSeriesPowerSum lam i := by
  rw [← sum_filter]
  refine (lSeriesPowerSum_eq_sum lam fun P ↦ ?_).symm
  rw [mem_filter]
  exact ⟨fun ⟨hP, h⟩ ↦ ⟨(hS P hP).1, (hS P hP).2, h⟩, fun ⟨hPm, hPirr, hdi, hi0⟩ ↦
    ⟨hi P hPm hPirr (Nat.le_of_dvd (Nat.pos_of_ne_zero hi0) hdi), hdi, hi0⟩⟩

end PowerSum

section Field

variable {F R : Type*} [Field F] [Finite F] [CommSemiring R]

/-! ### The finite Euler product -/

/-- **The finite Euler product.** For a finite set `S` of monic irreducible polynomials, the
coefficient of `T ^ n` in `∏_{P ∈ S} lSeriesFactor λ P` is the sum of `λ` over the monic
polynomials of degree `n` whose irreducible factors lie in `S`. -/
theorem coeff_prod_lSeriesFactor [DecidableEq F] {lam : F[X] → R}
    (hlam : IsMonicMultiplicative lam) {S : Finset F[X]} (hS : ∀ P ∈ S, P.Monic ∧ Irreducible P)
    (n : ℕ) :
    PowerSeries.coeff n (∏ P ∈ S, lSeriesFactor lam P) =
      ∑ g ∈ (monicsOfDegree F n).filter (fun g ↦ (normalizedFactors g).toFinset ⊆ S), lam g := by
  rw [PowerSeries.coeff_prod]
  simp only [coeff_lSeriesFactor, prod_ite_zero, ← sum_filter]
  rw [← sum_finsuppAntidiag_eq_sum_monicsOfDegree hS n lam]
  exact sum_congr rfl fun l _ ↦ (hlam.map_prod_pow _ _ _ fun P hP ↦ (hS P hP).1).symm

/-- Once `S` contains every monic irreducible of degree at most `n`, the coefficient of `T ^ n`
in the finite Euler product over `S` is that of `L(λ, T)`. -/
theorem coeff_prod_lSeriesFactor_eq_coeff_lSeries {lam : F[X] → R}
    (hlam : IsMonicMultiplicative lam) {S : Finset F[X]} (hS : ∀ P ∈ S, P.Monic ∧ Irreducible P)
    {n : ℕ} (hn : ∀ P : F[X], P.Monic → Irreducible P → P.natDegree ≤ n → P ∈ S) :
    PowerSeries.coeff n (∏ P ∈ S, lSeriesFactor lam P) = PowerSeries.coeff n (lSeries lam) := by
  classical
  rw [coeff_prod_lSeriesFactor hlam hS, coeff_lSeries, filter_true_of_mem]
  intro g hg P hP
  have hgm := mem_monicsOfDegree.1 hg
  have hPg : P ∈ normalizedFactors g := Multiset.mem_toFinset.1 hP
  refine hn P (hgm.1.monic_of_mem_normalizedFactors hPg) (irreducible_of_normalized_factor P hPg) ?_
  rw [← hgm.2]
  exact natDegree_le_of_dvd (dvd_of_mem_normalizedFactors hPg) hgm.1.ne_zero

/-! ### The Euler product -/

section EulerProduct

open PowerSeries.WithPiTopology

variable [TopologicalSpace R]

/-- **The Euler product**, with the factors `lSeriesFactor λ P` over the monic irreducible `P`,
in the coefficientwise topology. -/
theorem hasProd_lSeriesFactor {lam : F[X] → R} (hlam : IsMonicMultiplicative lam) :
    HasProd (fun P : {P : F[X] // P.Monic ∧ Irreducible P} ↦ lSeriesFactor lam P)
      (lSeries lam) := by
  classical
  simp only [HasProd, SummationFilter.unconditional_filter]
  rw [PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto]
  intro n
  obtain ⟨S, -, hSn⟩ := exists_finset_monic_irreducible_mem_of_natDegree_le F n
  refine tendsto_atTop_of_eventually_const (i₀ := S.subtype _) fun s hs ↦ ?_
  have hS : ∀ P ∈ s.map (Function.Embedding.subtype _), P.Monic ∧ Irreducible P := by
    intro P hP
    obtain ⟨Q, -, rfl⟩ := mem_map.1 hP
    exact Q.property
  have hprod : ∏ P ∈ s, lSeriesFactor lam (P : F[X]) =
      ∏ P ∈ s.map (Function.Embedding.subtype _), lSeriesFactor lam P := by
    simp only [prod_map, Function.Embedding.coe_subtype]
  rw [hprod]
  exact coeff_prod_lSeriesFactor_eq_coeff_lSeries hlam hS fun P hPm hPirr hPn ↦
    mem_map.2 ⟨⟨P, hPm, hPirr⟩, hs (mem_subtype.2 (hSn P hPm hPirr hPn)), rfl⟩

/-- **The Euler product** as an infinite product of the factors `lSeriesFactor λ P`, for values
in a Hausdorff space. -/
theorem lSeries_eq_tprod_lSeriesFactor [T2Space R] {lam : F[X] → R}
    (hlam : IsMonicMultiplicative lam) :
    lSeries lam = ∏' P : {P : F[X] // P.Monic ∧ Irreducible P}, lSeriesFactor lam P :=
  (hasProd_lSeriesFactor hlam).tprod_eq.symm

/-- **The Euler product** `L(λ, T) = ∏_P (1 - λ(P) T ^ deg P)⁻¹` over the monic irreducible `P`,
for values in a field. -/
theorem hasProd_inv_one_sub_lSeries {K : Type*} [Field K] [TopologicalSpace K] {lam : F[X] → K}
    (hlam : IsMonicMultiplicative lam) :
    HasProd (fun P : {P : F[X] // P.Monic ∧ Irreducible P} ↦
      (1 - PowerSeries.C (lam P) * PowerSeries.X ^ (P : F[X]).natDegree)⁻¹) (lSeries lam) := by
  convert hasProd_lSeriesFactor hlam using 2 with P
  exact (lSeriesFactor_eq_inv lam P.property.2.natDegree_pos).symm

/-- **The Euler product** as an infinite product, for values in a Hausdorff topological field. -/
theorem lSeries_eq_tprod {K : Type*} [Field K] [TopologicalSpace K] [T2Space K]
    {lam : F[X] → K} (hlam : IsMonicMultiplicative lam) :
    lSeries lam = ∏' P : {P : F[X] // P.Monic ∧ Irreducible P},
      (1 - PowerSeries.C (lam P) * PowerSeries.X ^ (P : F[X]).natDegree)⁻¹ := by
  rw [lSeries_eq_tprod_lSeriesFactor hlam]
  exact tprod_congr fun P ↦ lSeriesFactor_eq_inv lam P.property.2.natDegree_pos

end EulerProduct

/-! ### The logarithmic derivative of the `L`-series -/

/-- **The logarithmic derivative** of the `L`-series: `X L' = (∑_n S_n(λ) X ^ n) L`. -/
theorem X_mul_derivative_lSeries {lam : F[X] → R} (hlam : IsMonicMultiplicative lam) :
    PowerSeries.X * PowerSeries.derivative (R := R) (lSeries lam) =
      PowerSeries.mk (lSeriesPowerSum lam) * lSeries lam := by
  classical
  ext n
  obtain ⟨S, hS, hSn⟩ := exists_finset_monic_irreducible_mem_of_natDegree_le F n
  have hA : ∀ j ≤ n, PowerSeries.coeff j (∏ P ∈ S, lSeriesFactor lam P) =
      PowerSeries.coeff j (lSeries lam) := fun j hj ↦
    coeff_prod_lSeriesFactor_eq_coeff_lSeries hlam hS fun P hPm hPirr hPd ↦
      hSn P hPm hPirr (hPd.trans hj)
  have hB : ∀ i ≤ n, PowerSeries.coeff i (∑ P ∈ S, PowerSeries.C (lam P * P.natDegree) *
      PowerSeries.X ^ P.natDegree * lSeriesFactor lam P) = lSeriesPowerSum lam i := by
    intro i hi
    rw [map_sum, sum_congr rfl fun P _ ↦ coeff_C_mul_X_pow_mul_lSeriesFactor lam P i]
    exact sum_ite_eq_lSeriesPowerSum lam hS fun P hPm hPirr hPd ↦ hSn P hPm hPirr (hPd.trans hi)
  rw [PowerSeries.coeff_X_mul_derivative, ← hA n le_rfl, ← PowerSeries.coeff_X_mul_derivative,
    X_mul_derivative_prod_lSeriesFactor lam S, PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  refine sum_congr rfl fun ij hij ↦ ?_
  have := mem_antidiagonal.1 hij
  rw [hA ij.2 (by omega), hB ij.1 (by omega), PowerSeries.coeff_mk]

/-- **The logarithmic derivative** of the `L`-series over a field:
`X L' / L = ∑_n S_n(λ) X ^ n`. -/
theorem X_mul_derivative_lSeries_mul_inv {K : Type*} [Field K] {lam : F[X] → K}
    (hlam : IsMonicMultiplicative lam) :
    PowerSeries.X * PowerSeries.derivative (R := K) (lSeries lam) * (lSeries lam)⁻¹ =
      PowerSeries.mk (lSeriesPowerSum lam) := by
  rw [X_mul_derivative_lSeries hlam, mul_assoc, PowerSeries.mul_inv_cancel, mul_one]
  rw [constantCoeff_lSeries_of_isMonicMultiplicative hlam]
  exact one_ne_zero

end Field

end TauCeti.Polynomial

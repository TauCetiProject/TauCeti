/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.RingTheory.PowerSeries.WellKnown
public import TauCeti.RingTheory.PowerSeries.Expand
public import TauCeti.RingTheory.PowerSeries.PiTopology
import TauCeti.RingTheory.PowerSeries.Derivative
import TauCeti.RingTheory.PowerSeries.Geometric
import TauCeti.RingTheory.PowerSeries.Trunc

/-!
# Integral Euler products `∏ (1 - X ^ r) ^ (-e r)`

Every power series `f ∈ ℤ⟦X⟧` with constant coefficient `1` factors uniquely as an infinite
product

`f = ∏_{r ≥ 1} (1 - X ^ r) ^ (-e r)`

with integer exponents `e r`, converging coefficientwise (`PowerSeries.WithPiTopology`). In
combinatorics `f` is the Euler transform of the sequence `e`. The factor `(1 - X ^ r) ^ (-e r)`
is written `expand r _ ↑(invOneSubPow ℤ 1 ^ e r)`: the expansion `X ↦ X ^ r` of the integer
power `e r` of the unit `(1 - X)⁻¹` of `ℤ⟦X⟧`. The exponents are constructed recursively, without
division: once `e 1, …, e (r - 1)` are fixed, `e r` is the integer that removes the coefficient of
`X ^ r` from the remaining quotient, because `(1 - X ^ r) ^ (-k) = 1 + k X ^ r` modulo
`X ^ (r + 1)`.

Taking `X` times the logarithmic derivative (`PowerSeries.xLogDeriv`) turns the product into the
sum `X f' / f = ∑_{m ≥ 1} (∑_{d ∣ m} d e_d) X ^ m`. For `f = 1 - x X` the left side is
`-∑_{m ≥ 1} x ^ m X ^ m`, so Möbius inversion gives `m e_m = -∑_{d ∣ m} μ(d) x ^ (m / d)`. Since the
recursion produces integers, this proves the necklace congruence: `m` divides
`∑_{d ∣ m} μ(d) x ^ (m / d)` for every integer `x`. The resulting factorization of `1 - x X` is
the cyclotomic identity of Metropolis and Rota.

## Main results

* `PowerSeries.expand_invOneSubPow_zpow_neg_natCast`,
  `PowerSeries.expand_invOneSubPow_zpow_natCast_mul_one_sub_X_pow_pow`: the factor
  `expand r _ ↑(invOneSubPow R 1 ^ e)` is `(1 - X ^ r) ^ (-e)`.
* `PowerSeries.X_pow_dvd_expand_invOneSubPow_zpow_sub`: `(1 - X ^ r) ^ (-k) = 1 + k X ^ r` modulo
  `X ^ (r + 1)`.
* `PowerSeries.hasProd_expand_invOneSubPow_zpow_iff`: an integral Euler product converges to `f`
  exactly when `f` agrees with its first `n` factors modulo `X ^ (n + 1)`, for every `n`.
* `PowerSeries.exists_hasProd_expand_invOneSubPow_zpow`: every `f ∈ ℤ⟦X⟧` with constant
  coefficient `1` is an integral Euler product.
* `PowerSeries.eq_of_hasProd_expand_invOneSubPow_zpow_of_X_pow_dvd_sub` and
  `PowerSeries.eq_of_hasProd_expand_invOneSubPow_zpow`: the exponents `e 1, …, e s` are determined
  by `f` modulo `X ^ (s + 1)`; in particular they are unique.
* `PowerSeries.X_mul_derivative_eq_mul_of_hasProd`:
  `X f' = f ∑_{m ≥ 1} (∑_{d ∣ m} d e_d) X ^ m`.
* `PowerSeries.natCast_mul_eq_neg_sum_moebius_mul_pow_of_hasProd`: the Möbius formula for the
  exponents of `1 - x X`.
* `PowerSeries.hasProd_expand_invOneSubPow_zpow_one_sub_C_mul_X`: the cyclotomic identity
  `1 - x X = ∏_{r ≥ 1} (1 - X ^ r) ^ (M(x, r))`, `M(x, r) = (1 / r) ∑_{d ∣ r} μ(d) x ^ (r / d)`.
* `Int.natCast_dvd_sum_divisors_moebius_mul_pow`: the necklace congruence
  `m ∣ ∑_{d ∣ m} μ(d) x ^ (m / d)`.

## References

* N. Metropolis, G.-C. Rota, *Witt vectors and the algebra of necklaces*, Adv. Math. 50 (1983),
  95–125.
* M. Bernstein, N. J. A. Sloane, *Some canonical sequences of integers*, Linear Algebra Appl.
  226–228 (1995), 57–72, for the Euler transform.
-/

public section

open Finset
open scoped ArithmeticFunction.Moebius PowerSeries.WithPiTopology

namespace PowerSeries

section CommRing

variable {R : Type*} [CommRing R]

/-- The inverse of the unit `(1 - X)⁻¹ ^ d`, as a power series, is `(1 - X) ^ d`. -/
@[simp]
theorem val_inv_invOneSubPow (d : ℕ) : (↑(invOneSubPow R d)⁻¹ : R⟦X⟧) = (1 - X) ^ d := by
  rw [← Units.inv_eq_val_inv, invOneSubPow_inv_eq_one_sub_pow]

/-- The integer powers of `(1 - X)⁻¹` have constant coefficient `1`. -/
@[simp]
theorem constantCoeff_invOneSubPow_zpow (k : ℤ) :
    constantCoeff (↑(invOneSubPow R 1 ^ k) : R⟦X⟧) = 1 := by
  have h1 : Units.map ((constantCoeff : R⟦X⟧ →+* R) : R⟦X⟧ →* R) (invOneSubPow R 1) = 1 :=
    Units.ext (by simp [invOneSubPow_val_succ_eq_mk_add_choose])
  rw [constantCoeff_val_zpow, h1, one_zpow, Units.val_one]

/-- The coefficient of `X` in `(1 - X) ^ (-k)` is `k`. -/
@[simp]
theorem coeff_one_invOneSubPow_zpow (k : ℤ) :
    coeff 1 (↑(invOneSubPow R 1 ^ k) : R⟦X⟧) = k := by
  induction k using Int.induction_on with
  | zero => simp
  | succ k ih =>
    rw [zpow_add_one, Units.val_mul, coeff_one_mul, ih, constantCoeff_invOneSubPow_zpow]
    simp [invOneSubPow_val_succ_eq_mk_add_choose]
  | pred k ih =>
    rw [zpow_sub_one, Units.val_mul, coeff_one_mul, ih, val_inv_invOneSubPow, pow_one,
      constantCoeff_invOneSubPow_zpow]
    simp [sub_eq_add_neg]

/-- The integral Euler factor `(1 - X ^ r) ^ (-e)` at `e = -1` is `1 - X ^ r`. -/
theorem expand_val_inv_invOneSubPow (r : ℕ) (hr : r ≠ 0) :
    expand r hr (↑(invOneSubPow R 1)⁻¹ : R⟦X⟧) = 1 - X ^ r := by
  rw [val_inv_invOneSubPow, pow_one, map_sub, map_one, expand_X]

/-- The integral Euler factor `(1 - X ^ r) ^ (-e)` at a nonpositive exponent `e = -k` is the
polynomial `(1 - X ^ r) ^ k`. -/
theorem expand_invOneSubPow_zpow_neg_natCast (r : ℕ) (hr : r ≠ 0) (k : ℕ) :
    expand r hr (↑(invOneSubPow R 1 ^ (-(k : ℤ))) : R⟦X⟧) = (1 - X ^ r) ^ k := by
  rw [zpow_neg, zpow_natCast, ← inv_pow, Units.val_pow_eq_pow_val, map_pow,
    expand_val_inv_invOneSubPow]

/-- The integral Euler factor `(1 - X ^ r) ^ (-k)` at a natural number `k` inverts
`(1 - X ^ r) ^ k`. -/
theorem expand_invOneSubPow_zpow_natCast_mul_one_sub_X_pow_pow (r : ℕ) (hr : r ≠ 0) (k : ℕ) :
    expand r hr (↑(invOneSubPow R 1 ^ (k : ℤ)) : R⟦X⟧) * (1 - X ^ r) ^ k = 1 := by
  rw [← expand_invOneSubPow_zpow_neg_natCast r hr k, ← map_mul, ← Units.val_mul, ← zpow_add,
    add_neg_cancel, zpow_zero, Units.val_one, map_one]

/-- `(1 - X ^ r) ^ (-k)` is `1` modulo `X ^ r`. -/
theorem X_pow_dvd_expand_invOneSubPow_zpow_sub_one (r : ℕ) (hr : r ≠ 0) (k : ℤ) :
    X ^ r ∣ expand r hr (↑(invOneSubPow R 1 ^ k) : R⟦X⟧) - 1 := by
  simpa using X_pow_dvd_expand_sub_C_constantCoeff r hr (↑(invOneSubPow R 1 ^ k) : R⟦X⟧)

/-- `(1 - X ^ r) ^ (-k)` is `1 + k X ^ r` modulo `X ^ (r + 1)`. -/
theorem X_pow_dvd_expand_invOneSubPow_zpow_sub (r : ℕ) (hr : r ≠ 0) (k : ℤ) :
    X ^ (r + 1) ∣ expand r hr (↑(invOneSubPow R 1 ^ k) : R⟦X⟧) - 1 - C (k : R) * X ^ r := by
  rw [X_pow_dvd_iff]
  intro m hm
  obtain ⟨q, hq⟩ := X_pow_dvd_expand_invOneSubPow_zpow_sub_one (R := R) r hr k
  rcases Nat.lt_succ_iff_lt_or_eq.1 hm with hm | rfl
  · have h0 : coeff m (expand r hr (↑(invOneSubPow R 1 ^ k) : R⟦X⟧) - 1) = 0 := by
      rw [hq, coeff_X_pow_mul', ite_eq_right (by omega)]
    rw [map_sub, h0, coeff_C_mul_X_pow, ite_eq_right hm.ne, sub_zero]
  · have := coeff_expand_mul m hr (↑(invOneSubPow R 1 ^ k) : R⟦X⟧) 1
    rw [mul_one, coeff_one_invOneSubPow_zpow] at this
    simp [this, coeff_one, hr]

end CommRing

/-- The unit `(1 - X ^ r)⁻¹ = ∑ X ^ (r * j)` of `ℤ⟦X⟧`. -/
private noncomputable def invOneSubXPow (r : ℕ+) : ℤ⟦X⟧ˣ :=
  Units.map (expand (R := ℤ) r r.ne_zero : ℤ⟦X⟧ →* ℤ⟦X⟧) (invOneSubPow ℤ 1)

private theorem expand_invOneSubPow_zpow (r : ℕ+) (k : ℤ) :
    expand r r.ne_zero ↑(invOneSubPow ℤ 1 ^ k) = (↑(invOneSubXPow r ^ k) : ℤ⟦X⟧) := by
  rw [invOneSubXPow, ← map_zpow, Units.coe_map, MonoidHom.coe_ofClass]

private theorem val_invOneSubXPow (r : ℕ+) :
    (↑(invOneSubXPow r) : ℤ⟦X⟧) = expand r r.ne_zero (mk 1) := by
  rw [← zpow_one (invOneSubXPow r), ← expand_invOneSubPow_zpow, zpow_one,
    invOneSubPow_val_succ_eq_mk_add_choose]
  congr 2
  funext n
  simp

/-- Modulo `X ^ (k + 2)`, the factor of index `k + 1` with exponent `j` is `1 + j X ^ (k + 1)`. -/
private theorem X_pow_dvd_val_invOneSubXPow_zpow_sub (k : ℕ) (j : ℤ) :
    X ^ (k + 1 + 1) ∣ (↑(invOneSubXPow k.succPNat ^ j) : ℤ⟦X⟧) - 1 - C j * X ^ (k + 1) := by
  have := X_pow_dvd_expand_invOneSubPow_zpow_sub (R := ℤ) _ k.succPNat.ne_zero j
  rwa [expand_invOneSubPow_zpow, Nat.succPNat_coe, Nat.succ_eq_add_one, Int.cast_id] at this

/-- `X` times the logarithmic derivative of `(1 - X ^ r)⁻¹` is `r X ^ r (1 - X ^ r)⁻¹`. -/
private theorem toAdd_xLogDeriv_invOneSubXPow (r : ℕ+) :
    (xLogDeriv (invOneSubXPow r)).toAdd =
      C (r : ℤ) * X ^ (r : ℕ) * (↑(invOneSubXPow r) : ℤ⟦X⟧) := by
  set w : ℤ⟦X⟧ := ↑(invOneSubXPow r)
  have hinv : (↑(invOneSubXPow r)⁻¹ : ℤ⟦X⟧) = 1 - X ^ (r : ℕ) := by
    rw [← zpow_neg_one, ← expand_invOneSubPow_zpow, zpow_neg_one, expand_val_inv_invOneSubPow]
  have hw : w * (1 - X ^ (r : ℕ)) = 1 := by
    rw [← hinv]
    exact (invOneSubXPow r).mul_inv
  have hd := congrArg d⁄dX hw
  rw [Derivation.leibniz, map_sub, Derivation.map_one_eq_zero, derivative_X_pow, smul_eq_mul,
    smul_eq_mul] at hd
  have hX : X * X ^ ((r : ℕ) - 1) = (X : ℤ⟦X⟧) ^ (r : ℕ) := by
    rw [← pow_succ', Nat.sub_add_cancel r.pos]
  rw [toAdd_xLogDeriv, hinv]
  linear_combination X * hd + C (r : ℤ) * w * hX

/-- The coefficients of `X ^ r (1 - X ^ r)⁻¹ = ∑_{j ≥ 1} X ^ (r * j)`. -/
private theorem coeff_X_pow_mul_invOneSubXPow (r : ℕ+) (m : ℕ) :
    coeff m (X ^ (r : ℕ) * (↑(invOneSubXPow r) : ℤ⟦X⟧)) =
      if (r : ℕ) ∣ m ∧ m ≠ 0 then 1 else 0 := by
  rw [val_invOneSubXPow, coeff_X_pow_mul', coeff_expand]
  by_cases hrm : (r : ℕ) ≤ m
  · have : (r : ℕ) ∣ m - r ↔ (r : ℕ) ∣ m := Nat.dvd_sub_iff_left hrm dvd_rfl
    simp [hrm, this, show m ≠ 0 by have := r.pos; omega]
  · have : ¬ ((r : ℕ) ∣ m ∧ m ≠ 0) := fun h ↦ hrm (Nat.le_of_dvd (Nat.pos_of_ne_zero h.2) h.1)
    simp [hrm, this]

/-- The finite Euler product `∏_{r = 1}^{n} (1 - X ^ r) ^ (-e r)`, as a unit. -/
private noncomputable def eulerUnit (e : ℕ → ℤ) (n : ℕ) : ℤ⟦X⟧ˣ :=
  ∏ i ∈ range n, invOneSubXPow i.succPNat ^ e (i + 1)

private theorem val_eulerUnit (e : ℕ → ℤ) (n : ℕ) :
    (↑(eulerUnit e n) : ℤ⟦X⟧) =
      ∏ i ∈ range n, expand (i + 1) i.succ_ne_zero ↑(invOneSubPow ℤ 1 ^ e (i + 1)) := by
  rw [eulerUnit, Units.coe_prod]
  exact prod_congr rfl fun i _ ↦ (expand_invOneSubPow_zpow i.succPNat (e (i + 1))).symm

/-- Factors of index above `m` do not change the coefficients of degree at most `m`. -/
private theorem coeff_val_eulerUnit_of_le (e : ℕ → ℤ) {m n : ℕ} (hmn : m ≤ n) :
    coeff m (↑(eulerUnit e n) : ℤ⟦X⟧) = coeff m (↑(eulerUnit e m) : ℤ⟦X⟧) := by
  simp only [eulerUnit, Units.coe_prod]
  refine coeff_prod_eq_coeff_prod_of_X_pow_dvd_sub_one (range_subset_range.2 hmn) fun i hi ↦ ?_
  have him : m < i + 1 := by simp at hi; omega
  rw [← expand_invOneSubPow_zpow]
  exact (pow_dvd_pow X him).trans
    (X_pow_dvd_expand_invOneSubPow_zpow_sub_one _ i.succPNat.ne_zero _)

private theorem constantCoeff_val_eulerUnit (e : ℕ → ℤ) (n : ℕ) :
    constantCoeff (↑(eulerUnit e n) : ℤ⟦X⟧) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_val_eulerUnit_of_le e (Nat.zero_le n)]
  simp [eulerUnit]

/-- `X` times the logarithmic derivative of a finite Euler product. -/
private theorem toAdd_xLogDeriv_eulerUnit (e : ℕ → ℤ) (n : ℕ) :
    (xLogDeriv (eulerUnit e n)).toAdd = ∑ i ∈ range n,
      e (i + 1) • (C ((i + 1 : ℕ) : ℤ) * X ^ (i + 1) * (↑(invOneSubXPow i.succPNat) : ℤ⟦X⟧)) := by
  simp only [eulerUnit, map_prod, map_zpow, toAdd_prod, toAdd_zpow]
  exact sum_congr rfl fun i _ ↦ by
    rw [toAdd_xLogDeriv_invOneSubXPow, Nat.succPNat_coe, Nat.succ_eq_add_one]

/-- In degrees at most `n`, `X` times the logarithmic derivative of the finite Euler product
up to `n` has the coefficients `∑_{d ∣ m} d * e d`. -/
private theorem coeff_toAdd_xLogDeriv_eulerUnit (e : ℕ → ℤ) {m n : ℕ} (hmn : m ≤ n) :
    coeff m (xLogDeriv (eulerUnit e n)).toAdd = ∑ d ∈ m.divisors, (d : ℤ) * e d := by
  have hterm (i : ℕ) : coeff m (e (i + 1) • (C ((i + 1 : ℕ) : ℤ) * X ^ (i + 1) *
      (↑(invOneSubXPow i.succPNat) : ℤ⟦X⟧))) =
      if (i + 1) ∣ m ∧ m ≠ 0 then ((i + 1 : ℕ) : ℤ) * e (i + 1) else 0 := by
    rw [map_zsmul, mul_assoc, coeff_C_mul, smul_eq_mul]
    have := coeff_X_pow_mul_invOneSubXPow i.succPNat m
    rw [Nat.succPNat_coe, Nat.succ_eq_add_one] at this
    rw [this]
    split_ifs <;> simp [mul_comm]
  rw [toAdd_xLogDeriv_eulerUnit, map_sum]
  simp only [hterm]
  rw [← sum_filter]
  refine sum_nbij' (· + 1) (· - 1) ?_ ?_ ?_ ?_ ?_ <;> intro i hi
  all_goals simp only [mem_filter, mem_range, Nat.mem_divisors] at hi ⊢
  · exact hi.2
  · have := Nat.le_of_dvd (Nat.pos_of_ne_zero hi.2) hi.1
    have := Nat.pos_of_dvd_of_pos hi.1 (Nat.pos_of_ne_zero hi.2)
    exact ⟨by omega, by rw [Nat.sub_add_cancel this]; exact hi⟩
  · omega
  · have := Nat.pos_of_dvd_of_pos hi.1 (Nat.pos_of_ne_zero hi.2)
    omega

/-- **Integral Euler products.** The product of the factors `(1 - X ^ r) ^ (-e r)` over the
positive integers `r` converges to `f` in the coefficientwise topology exactly when `f` agrees
with the finite product of the first `n` factors modulo `X ^ (n + 1)`, for every `n`. -/
theorem hasProd_expand_invOneSubPow_zpow_iff {e : ℕ → ℤ} {f : ℤ⟦X⟧} :
    HasProd (fun r : ℕ+ ↦ expand r r.ne_zero ↑(invOneSubPow ℤ 1 ^ e r)) f ↔
      ∀ n : ℕ, X ^ (n + 1) ∣
        f - ∏ i ∈ range n, expand (i + 1) i.succ_ne_zero ↑(invOneSubPow ℤ 1 ^ e (i + 1)) := by
  set g : ℕ+ → ℤ⟦X⟧ := fun r ↦ expand r r.ne_zero ↑(invOneSubPow ℤ 1 ^ e r)
  have hF (n : ℕ) (r : ℕ+) (hr : r ∉ (range n).map ⟨Nat.succPNat, Nat.succPNat_injective⟩) :
      X ^ (n + 1) ∣ g r - 1 := by
    have hnr : n + 1 ≤ (r : ℕ) := by
      have := r.pos
      by_contra hrn
      refine hr (mem_map.2 ⟨(r : ℕ) - 1, mem_range.2 (by omega), PNat.eq ?_⟩)
      simp [Nat.sub_add_cancel r.pos]
    exact (pow_dvd_pow X hnr).trans (X_pow_dvd_expand_invOneSubPow_zpow_sub_one _ r.ne_zero _)
  have hprod (n : ℕ) :
      ∏ r ∈ (range n).map ⟨Nat.succPNat, Nat.succPNat_injective⟩, g r = ↑(eulerUnit e n) := by
    simp only [prod_map, val_eulerUnit, Function.Embedding.coeFn_mk, Nat.succPNat_coe,
      Nat.succ_eq_add_one, g]
  have hL : HasProd g (mk fun n ↦ coeff n (↑(eulerUnit e n) : ℤ⟦X⟧)) := by
    simpa only [hprod] using WithPiTopology.hasProd_of_X_pow_dvd_sub_one _ hF
  have hmk (n : ℕ) :
      X ^ (n + 1) ∣ mk (fun n ↦ coeff n (↑(eulerUnit e n) : ℤ⟦X⟧)) - (↑(eulerUnit e n) : ℤ⟦X⟧) := by
    rw [X_pow_dvd_iff]
    intro m hm
    rw [map_sub, coeff_mk, coeff_val_eulerUnit_of_le e (Nat.lt_succ_iff.1 hm), sub_self]
  simp only [← val_eulerUnit]
  constructor
  · intro h n
    rw [h.unique hL]
    exact hmk n
  · intro h
    convert hL
    exact eq_of_forall_X_pow_dvd_sub fun n ↦ by simpa using dvd_sub (h n) (hmk n)

/-- The remainders of the recursive construction of integral Euler exponents: the `n`-th
remainder is `f ∏_{r = 1}^{n} (1 - X ^ r) ^ (e r)`, where each `e r` removes the coefficient of
`X ^ r` of the previous remainder. -/
private noncomputable def eulerRemainder (f : ℤ⟦X⟧) : ℕ → ℤ⟦X⟧
  | 0 => f
  | n + 1 => eulerRemainder f n *
      ↑(invOneSubXPow n.succPNat ^ (-coeff (n + 1) (eulerRemainder f n)))

/-- The remainders agree with `1` to increasing order. -/
private theorem X_pow_dvd_eulerRemainder_sub_one {f : ℤ⟦X⟧} (hf : constantCoeff f = 1) (n : ℕ) :
    X ^ (n + 1) ∣ eulerRemainder f n - 1 := by
  induction n with
  | zero => simp [eulerRemainder, X_dvd_iff, hf]
  | succ n ih =>
    set g := eulerRemainder f n
    set a := coeff (n + 1) g
    -- Modulo `X ^ (n + 2)`, `g = 1 + a X ^ (n + 1)` and the new factor is `1 - a X ^ (n + 1)`.
    have hg : X ^ (n + 1 + 1) ∣ g - (1 + C a * X ^ (n + 1)) := by
      rw [X_pow_dvd_iff]
      intro m hm
      rcases Nat.lt_succ_iff_lt_or_eq.1 hm with hm | rfl
      · rw [← sub_sub, map_sub, X_pow_dvd_iff.1 ih m hm, coeff_C_mul_X_pow, ite_eq_right hm.ne,
          sub_zero]
      · simp [a, coeff_one]
    have hw : X ^ (n + 1 + 1) ∣
        (↑(invOneSubXPow n.succPNat ^ (-a)) : ℤ⟦X⟧) - (1 - C a * X ^ (n + 1)) := by
      convert X_pow_dvd_val_invOneSubXPow_zpow_sub n (-a) using 1
      rw [map_neg]
      ring
    have hsq : X ^ (n + 1 + 1) ∣ (1 + C a * X ^ (n + 1)) * (1 - C a * X ^ (n + 1)) - 1 := by
      rw [show (1 + C a * X ^ (n + 1)) * (1 - C a * X ^ (n + 1)) - 1 =
        -(C a ^ 2 * X ^ (2 * (n + 1))) by ring, dvd_neg]
      exact dvd_mul_of_dvd_right (pow_dvd_pow X (by omega)) _
    rw [eulerRemainder]
    convert dvd_add (dvd_mul_sub_mul hg hw) hsq using 1
    ring

/-- The integral Euler exponents constructed recursively from the remainders. -/
private noncomputable def recExponents (f : ℤ⟦X⟧) (r : ℕ) : ℤ :=
  coeff r (eulerRemainder f (r - 1))

private theorem val_eulerUnit_succ (e : ℕ → ℤ) (n : ℕ) :
    (↑(eulerUnit e (n + 1)) : ℤ⟦X⟧) =
      ↑(eulerUnit e n) * ↑(invOneSubXPow n.succPNat ^ e (n + 1)) := by
  rw [eulerUnit, prod_range_succ, Units.val_mul, ← eulerUnit]

/-- The `n`-th remainder times the finite Euler product of the constructed exponents is `f`. -/
private theorem eulerRemainder_mul_val_eulerUnit (f : ℤ⟦X⟧) (n : ℕ) :
    eulerRemainder f n * ↑(eulerUnit (recExponents f) n) = f := by
  induction n with
  | zero => simp [eulerRemainder, eulerUnit]
  | succ n ih =>
    set w := invOneSubXPow n.succPNat
    set a := coeff (n + 1) (eulerRemainder f n)
    have hw : (↑(w ^ (-a)) : ℤ⟦X⟧) * ↑(w ^ a) = 1 := by
      rw [← Units.val_mul, ← zpow_add, neg_add_cancel, zpow_zero, Units.val_one]
    rw [val_eulerUnit_succ, eulerRemainder, recExponents, Nat.add_sub_cancel]
    linear_combination (eulerRemainder f n * ↑(eulerUnit
      (recExponents f) n)) * hw + ih

/-- **Existence of integral Euler exponents.** Every power series over `ℤ` with constant
coefficient `1` is an infinite product `∏_{r ≥ 1} (1 - X ^ r) ^ (-e r)` with integer exponents,
converging coefficientwise. The exponents are constructed recursively: once `e 1, …, e (r - 1)`
are fixed, `e r` is the integer removing the coefficient of `X ^ r` of the remaining quotient. -/
theorem exists_hasProd_expand_invOneSubPow_zpow {f : ℤ⟦X⟧} (hf : constantCoeff f = 1) :
    ∃ e : ℕ → ℤ, HasProd (fun r : ℕ+ ↦ expand r r.ne_zero ↑(invOneSubPow ℤ 1 ^ e r)) f := by
  refine ⟨recExponents f, hasProd_expand_invOneSubPow_zpow_iff.2 fun n ↦ ?_⟩
  rw [← val_eulerUnit]
  obtain ⟨h, hh⟩ := X_pow_dvd_eulerRemainder_sub_one hf n
  refine ⟨h * ↑(eulerUnit (recExponents f) n), ?_⟩
  linear_combination (-1 : ℤ⟦X⟧) * eulerRemainder_mul_val_eulerUnit f n +
    (↑(eulerUnit (recExponents f) n) : ℤ⟦X⟧) * hh

/-- **Uniqueness of integral Euler exponents, truncated.** If two integral Euler products agree
modulo `X ^ (s + 1)`, their exponents agree at every positive index `r ≤ s`. In particular the
exponents `e 1, …, e s` of a power series depend only on its coefficients up to degree `s`. -/
theorem eq_of_hasProd_expand_invOneSubPow_zpow_of_X_pow_dvd_sub {e e' : ℕ → ℤ} {f f' : ℤ⟦X⟧}
    (h : HasProd (fun r : ℕ+ ↦ expand r r.ne_zero ↑(invOneSubPow ℤ 1 ^ e r)) f)
    (h' : HasProd (fun r : ℕ+ ↦ expand r r.ne_zero ↑(invOneSubPow ℤ 1 ^ e' r)) f')
    {s : ℕ} (hs : X ^ (s + 1) ∣ f - f') {r : ℕ} (hr : r ≠ 0) (hrs : r ≤ s) : e r = e' r := by
  rw [hasProd_expand_invOneSubPow_zpow_iff] at h h'
  simp only [← val_eulerUnit] at h h'
  induction r using Nat.strong_induction_on with
  | _ r ih =>
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr
  have hU : eulerUnit e k = eulerUnit e' k := prod_congr rfl fun i hi ↦ by
    rw [mem_range] at hi
    rw [ih (i + 1) (by omega) (by omega) (by omega)]
  have hdiv := dvd_sub (dvd_add ((pow_dvd_pow X (by omega : k + 1 + 1 ≤ s + 1)).trans hs)
    (h' (k + 1))) (h (k + 1))
  rw [val_eulerUnit_succ, val_eulerUnit_succ, hU] at hdiv
  set Q : ℤ⟦X⟧ := ↑(eulerUnit e' k)
  have hQ : X ∣ Q - 1 := by
    rw [X_dvd_iff, map_sub, constantCoeff_val_eulerUnit, map_one, sub_self]
  -- So `Q (1 + e X ^ (k + 1)) = Q (1 + e' X ^ (k + 1))` mod `X ^ (k + 2)`, and `Q = 1` mod `X`.
  have hdvd : X ^ (k + 1 + 1) ∣ C (e (k + 1)) * X ^ (k + 1) - C (e' (k + 1)) * X ^ (k + 1) := by
    have hQW := (dvd_sub (X_pow_dvd_val_invOneSubXPow_zpow_sub k (e (k + 1)))
      (X_pow_dvd_val_invOneSubXPow_zpow_sub k (e' (k + 1)))).mul_left Q
    have hQ1 : X ^ (k + 1 + 1) ∣
        (Q - 1) * (C (e (k + 1)) * X ^ (k + 1) - C (e' (k + 1)) * X ^ (k + 1)) := by
      rw [pow_succ']
      exact mul_dvd_mul hQ (dvd_sub (dvd_mul_left _ _) (dvd_mul_left _ _))
    convert dvd_sub (dvd_sub hdiv hQW) hQ1 using 1
    ring
  have := X_pow_dvd_iff.1 hdvd (k + 1) (Nat.lt_succ_self _)
  rwa [map_sub, coeff_C_mul_X_pow, coeff_C_mul_X_pow, ite_eq_left rfl, ite_eq_left rfl,
    sub_eq_zero] at this

/-- **Uniqueness of integral Euler exponents.** Two integral Euler products with the same value
have the same exponents at every positive index. -/
theorem eq_of_hasProd_expand_invOneSubPow_zpow {e e' : ℕ → ℤ} {f : ℤ⟦X⟧}
    (h : HasProd (fun r : ℕ+ ↦ expand r r.ne_zero ↑(invOneSubPow ℤ 1 ^ e r)) f)
    (h' : HasProd (fun r : ℕ+ ↦ expand r r.ne_zero ↑(invOneSubPow ℤ 1 ^ e' r)) f)
    {r : ℕ} (hr : r ≠ 0) : e r = e' r :=
  eq_of_hasProd_expand_invOneSubPow_zpow_of_X_pow_dvd_sub h h' (s := r) (by simp) hr le_rfl

/-- **Logarithmic derivative of an integral Euler product.** If
`f = ∏_{r ≥ 1} (1 - X ^ r) ^ (-e r)`, then `X f' = f ∑_{m ≥ 1} (∑_{d ∣ m} d e_d) X ^ m`. -/
theorem X_mul_derivative_eq_mul_of_hasProd {e : ℕ → ℤ} {f : ℤ⟦X⟧}
    (h : HasProd (fun r : ℕ+ ↦ expand r r.ne_zero ↑(invOneSubPow ℤ 1 ^ e r)) f) :
    X * d⁄dX f = f * mk fun m ↦ ∑ d ∈ m.divisors, (d : ℤ) * e d := by
  rw [hasProd_expand_invOneSubPow_zpow_iff] at h
  simp only [← val_eulerUnit] at h
  set G : ℤ⟦X⟧ := mk fun m ↦ ∑ d ∈ m.divisors, (d : ℤ) * e d
  refine eq_of_forall_X_pow_dvd_sub fun n ↦ ?_
  set U := eulerUnit e n
  set S := (xLogDeriv U).toAdd
  have hS : X * d⁄dX (U : ℤ⟦X⟧) = S * (U : ℤ⟦X⟧) := by
    simp only [S, toAdd_xLogDeriv]
    rw [mul_assoc (X * d⁄dX (U : ℤ⟦X⟧)), Units.inv_mul, mul_one]
  have hSG : X ^ (n + 1) ∣ S - G := by
    rw [X_pow_dvd_iff]
    intro m hm
    rw [map_sub, coeff_toAdd_xLogDeriv_eulerUnit e (Nat.lt_succ_iff.1 hm), coeff_mk, sub_self]
  have hd := X_pow_dvd_X_mul_derivative_sub (h n)
  rw [hS] at hd
  convert dvd_add (dvd_sub hd (dvd_mul_of_dvd_right (h n) S)) (dvd_mul_of_dvd_right hSG f)
    using 1
  ring

/-- If `1 - x X = ∏_{r ≥ 1} (1 - X ^ r) ^ (-e r)`, then `∑_{d ∣ m} d e_d = -x ^ m` for every
positive `m`. -/
theorem sum_divisors_mul_eq_neg_pow_of_hasProd {e : ℕ → ℤ} {x : ℤ}
    (h : HasProd (fun r : ℕ+ ↦ expand r r.ne_zero ↑(invOneSubPow ℤ 1 ^ e r)) (1 - C x * X))
    {m : ℕ} (hm : m ≠ 0) : ∑ d ∈ m.divisors, (d : ℤ) * e d = -x ^ m := by
  set M : ℤ⟦X⟧ := mk fun n ↦ x ^ n
  set G : ℤ⟦X⟧ := mk fun m ↦ ∑ d ∈ m.divisors, (d : ℤ) * e d
  have hinv : (1 - C x * X) * M = 1 := by
    rw [mul_comm]
    exact TauCeti.powerSeries_mk_pow_mul_one_sub_C_mul_X_eq_one x
  have hd := X_mul_derivative_eq_mul_of_hasProd h
  rw [map_sub, Derivation.map_one_eq_zero, derivative_C_mul_X, zero_sub] at hd
  have hG : G = -C x * X * M := by linear_combination (-G) * hinv - M * hd
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
  have := congrArg (coeff (k + 1)) hG
  rw [coeff_mk] at this
  rw [this, mul_comm (-C x), mul_assoc, coeff_succ_X_mul, neg_mul, map_neg, coeff_C_mul, coeff_mk,
    pow_succ']

/-- **Möbius formula for integral Euler exponents.** If `1 - x X = ∏_{r ≥ 1} (1 - X ^ r) ^ (-e r)`,
then `m e_m = -∑_{d ∣ m} μ(d) x ^ (m / d)`. -/
theorem natCast_mul_eq_neg_sum_moebius_mul_pow_of_hasProd {e : ℕ → ℤ} {x : ℤ}
    (h : HasProd (fun r : ℕ+ ↦ expand r r.ne_zero ↑(invOneSubPow ℤ 1 ^ e r)) (1 - C x * X))
    (m : ℕ) : (m : ℤ) * e m = -∑ d ∈ m.divisors, μ d * x ^ (m / d) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  have := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq.1 fun n hn ↦
    sum_divisors_mul_eq_neg_pow_of_hasProd h hn.ne') m hm
  simp only [Int.cast_id] at this
  rw [← this, Nat.sum_divisorsAntidiagonal (fun a b ↦ μ a * -x ^ b)]
  simp [mul_neg, sum_neg_distrib]

/-- **The cyclotomic identity** of Metropolis and Rota, over `ℤ`:
`1 - x X = ∏_{r ≥ 1} (1 - X ^ r) ^ (M(x, r))`, where `M(x, r) = (1 / r) ∑_{d ∣ r} μ(d) x ^ (r / d)`
is an integer. The product converges coefficientwise. -/
theorem hasProd_expand_invOneSubPow_zpow_one_sub_C_mul_X (x : ℤ) :
    HasProd (fun r : ℕ+ ↦ expand r r.ne_zero ↑(invOneSubPow ℤ 1 ^
      ((-∑ d ∈ (r : ℕ).divisors, μ d * x ^ ((r : ℕ) / d)) / ((r : ℕ) : ℤ))))
      (1 - C x * X) := by
  obtain ⟨e, he⟩ := exists_hasProd_expand_invOneSubPow_zpow (f := 1 - C x * X) (by simp)
  convert he using 4 with r
  rw [← natCast_mul_eq_neg_sum_moebius_mul_pow_of_hasProd he,
    Int.mul_ediv_cancel_left _ (by exact_mod_cast r.ne_zero)]

end PowerSeries

/-- **Necklace congruence.** For every integer `x` and natural number `m`, the integer
`∑_{d ∣ m} μ(d) x ^ (m / d)` is divisible by `m`. For `x ≥ 0` the quotient counts the primitive
necklaces of length `m` in `x` colours. -/
theorem Int.natCast_dvd_sum_divisors_moebius_mul_pow (x : ℤ) (m : ℕ) :
    (m : ℤ) ∣ ∑ d ∈ m.divisors, μ d * x ^ (m / d) := by
  obtain ⟨e, he⟩ := PowerSeries.exists_hasProd_expand_invOneSubPow_zpow
    (f := 1 - PowerSeries.C x * PowerSeries.X) (by simp)
  exact ⟨-e m, by
    linear_combination PowerSeries.natCast_mul_eq_neg_sum_moebius_mul_pow_of_hasProd he m⟩

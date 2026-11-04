/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Binomial
public import TauCeti.RingTheory.Binomial
public import TauCeti.RingTheory.Nilpotent.Log
import Mathlib.RingTheory.PowerSeries.Trunc

/-!
# Binomial powers of unipotent elements

Let `R` be a commutative binomial ring, for instance `ℤ`, a `ℚ`-algebra, or a polynomial ring over
one, and let `A` be an associative `R`-algebra. For an element `u : A` with `u - 1` nilpotent
and `t : R`, the **binomial power**

```text
u ^ t = ∑ j < N, (t choose j) • (u - 1) ^ j,       (u - 1) ^ N = 0,
```

is the finite binomial expansion of `(1 + (u - 1)) ^ t`. It does not depend on the bound `N`.
Taking `R` to be a polynomial ring `k[t]` and evaluating at the indeterminate gives the
polynomial curve `t ↦ u ^ t` through a unipotent matrix `u`: a one-parameter group of unipotent
units whose value at `1` is `u` and whose first-order term at `0` is the finite logarithm of `u`.
Unlike `TauCeti.expSMulHom`, the construction needs no rational structure, so it applies over `ℤ`
and over the `p`-adic integers as well.

The main results are:

* `TauCeti.binomialPow_natCast`: at a natural number `m` the binomial power is `u ^ m`;
* `TauCeti.binomialPow_add`: `u ^ (t + s) = u ^ t * u ^ s`, so `t ↦ u ^ t` is a one-parameter
  group of units `TauCeti.binomialPowHom : Multiplicative R →* Aˣ`;
* `TauCeti.binomialPow_intCast`: at integers it is the integer power of the unit `u`;
* `TauCeti.pow_binomialPow_sub_one_eq_zero`: every binomial power is unipotent, with the same
  nilpotency bound as `u`;
* `TauCeti.map_binomialPow`: binomial powers commute with algebra homomorphisms;
* `TauCeti.binomialPow_eq_one_add_smul_log`: at a square-zero parameter `ε`, over a rational
  algebra, `u ^ ε = 1 + ε • log u`. Thus the tangent vector of the curve `t ↦ u ^ t` at `t = 0`
  is the finite logarithm `IsNilpotent.log u`.

The group law is Chu--Vandermonde, in the form of Mathlib's `PowerSeries.binomialSeries_add`,
transported to `A` by evaluating truncated series at the nilpotent element `u - 1`. This is the
nilpotent counterpart of Mathlib's binomial powers `HahnSeries.binomial_power` of Hahn series
close to one, which sum the same series `HahnSeries.SummableFamily.binomialFamily`.

## References

* J. E. Humphreys, *Linear Algebraic Groups*, (1975), Chapter VI.
-/

public section

namespace TauCeti

open Finset Polynomial

variable {R A : Type*} [CommRing R] [BinomialRing R] [Ring A] [Algebra R A]

/-- The binomial power `u ^ t = ∑ j, (t choose j) • (u - 1) ^ j` of an element `u` with
`u - 1` nilpotent, the sum running below the nilpotency class of `u - 1`. When `u - 1` is not
nilpotent the sum is empty and the value `0` is a junk value. -/
noncomputable def binomialPow (u : A) (t : R) : A :=
  ∑ j ∈ range (nilpotencyClass (u - 1)), Ring.choose t j • (u - 1) ^ j

/-- The binomial power is the binomial sum below the nilpotency class of `u - 1`. -/
theorem binomialPow_def (u : A) (t : R) :
    binomialPow u t = ∑ j ∈ range (nilpotencyClass (u - 1)), Ring.choose t j • (u - 1) ^ j :=
  (rfl)

/-- Any vanishing power of `u - 1` gives a finite binomial expansion of `u ^ t`. -/
theorem binomialPow_eq_sum {u : A} {n : ℕ} (hn : (u - 1) ^ n = 0) (t : R) :
    binomialPow u t = ∑ j ∈ range n, Ring.choose t j • (u - 1) ^ j := by
  rw [binomialPow_def]
  apply sum_subset (range_mono (nilpotencyClass_le_of_pow_eq_zero hn))
  intro j _ hj
  rw [mem_range, not_lt] at hj
  rw [pow_eq_zero_of_le hj (pow_nilpotencyClass ⟨n, hn⟩), smul_zero]

/-- The binomial power evaluates the truncated binomial series `(1 + X) ^ t` at `u - 1`. -/
private theorem binomialPow_eq_aeval {u : A} {n : ℕ} (hn : (u - 1) ^ n = 0) (t : R) :
    binomialPow u t = aeval (u - 1) (PowerSeries.trunc n (PowerSeries.binomialSeries R t)) := by
  rw [binomialPow_eq_sum hn, aeval_def, PowerSeries.eval₂_trunc_eq_sum_range]
  simp [Algebra.smul_def]

omit [BinomialRing R] in
/-- Evaluation at an element `x` with `x ^ n = 0` sees a power series only through its
coefficients below `n`. -/
private theorem aeval_trunc_eq_aeval {x : A} {n : ℕ} (hx : x ^ n = 0) {f : PowerSeries R}
    {p : R[X]} (h : ∀ d < n, PowerSeries.coeff d f = p.coeff d) :
    aeval x (PowerSeries.trunc n f) = aeval x p := by
  obtain ⟨q, hq⟩ : (X : R[X]) ^ n ∣ PowerSeries.trunc n f - p :=
    X_pow_dvd_iff.2 fun d hd => by simp [PowerSeries.coeff_trunc, hd, h d hd]
  rw [← sub_eq_zero, ← map_sub, hq, map_mul, map_pow, aeval_X, hx, zero_mul]

variable {u : A}

/-- Every binomial power of one is one. -/
@[simp]
theorem binomialPow_one_left (t : R) : binomialPow (1 : A) t = 1 := by
  rw [binomialPow_eq_sum (n := 1) (by simp)]
  simp

/-- At a natural number the binomial power is the ordinary power. -/
@[simp]
theorem binomialPow_natCast (hu : IsNilpotent (u - 1)) (m : ℕ) :
    binomialPow u (m : R) = u ^ m := by
  obtain ⟨n, hn⟩ := hu
  rw [binomialPow_eq_aeval hn, aeval_trunc_eq_aeval hn (p := (1 + X) ^ m)]
  · simp
  · intro d _
    rw [PowerSeries.binomialSeries_nat, ← Polynomial.coeff_coe]
    simp

/-- The binomial power with exponent zero is one. -/
@[simp]
theorem binomialPow_zero (hu : IsNilpotent (u - 1)) : binomialPow u (0 : R) = 1 := by
  simpa using binomialPow_natCast (R := R) hu 0

/-- The binomial power with exponent one is the element itself. -/
@[simp]
theorem binomialPow_one (hu : IsNilpotent (u - 1)) : binomialPow u (1 : R) = u := by
  simpa using binomialPow_natCast (R := R) hu 1

/-- **The group law of binomial powers**: `u ^ (t + s) = u ^ t * u ^ s`. -/
theorem binomialPow_add (hu : IsNilpotent (u - 1)) (t s : R) :
    binomialPow u (t + s) = binomialPow u t * binomialPow u s := by
  obtain ⟨n, hn⟩ := hu
  simp only [binomialPow_eq_aeval hn, ← map_mul]
  refine aeval_trunc_eq_aeval hn fun d hd => ?_
  rw [PowerSeries.binomialSeries_add, PowerSeries.coeff_mul_eq_coeff_trunc_mul_trunc _ _ hd,
    ← Polynomial.coe_mul, Polynomial.coeff_coe]

/-- Binomial powers of the same element commute. -/
theorem commute_binomialPow (hu : IsNilpotent (u - 1)) (t s : R) :
    Commute (binomialPow u t) (binomialPow u s) := by
  rw [Commute, SemiconjBy, ← binomialPow_add hu, ← binomialPow_add hu, add_comm]

/-- The binomial power with opposite exponent is a two-sided inverse. -/
theorem binomialPow_neg_mul (hu : IsNilpotent (u - 1)) (t : R) :
    binomialPow u (-t) * binomialPow u t = 1 := by
  rw [← binomialPow_add hu, neg_add_cancel, binomialPow_zero hu]

/-- The binomial power with opposite exponent is a two-sided inverse. -/
theorem binomialPow_mul_neg (hu : IsNilpotent (u - 1)) (t : R) :
    binomialPow u t * binomialPow u (-t) = 1 := by
  rw [← binomialPow_add hu, add_neg_cancel, binomialPow_zero hu]

/-- Every binomial power of a unipotent element is a unit. -/
theorem isUnit_binomialPow (hu : IsNilpotent (u - 1)) (t : R) : IsUnit (binomialPow u t) :=
  isUnit_iff_exists.2 ⟨_, binomialPow_mul_neg hu t, binomialPow_neg_mul hu t⟩

variable (R) in
/-- The one-parameter group of units `t ↦ u ^ t`, parametrised by the additive group of `R`, through
an element `u` with `u - 1` nilpotent. Its value at `1` is `u` (`TauCeti.binomialPow_one`). -/
noncomputable def binomialPowHom (hu : IsNilpotent (u - 1)) : Multiplicative R →* Aˣ where
  toFun t := ⟨binomialPow u t.toAdd, binomialPow u (-t.toAdd), binomialPow_mul_neg hu _,
    binomialPow_neg_mul hu _⟩
  map_one' := Units.ext (binomialPow_zero hu)
  map_mul' _ _ := Units.ext (binomialPow_add hu _ _)

/-- The one-parameter group of a unipotent element takes its binomial powers as values. -/
@[simp]
theorem coe_binomialPowHom (hu : IsNilpotent (u - 1)) (t : Multiplicative R) :
    (binomialPowHom R hu t : A) = binomialPow u t.toAdd :=
  (rfl)

/-- The inverse of a value of the one-parameter group is the binomial power with opposite
exponent. -/
@[simp]
theorem coe_inv_binomialPowHom (hu : IsNilpotent (u - 1)) (t : Multiplicative R) :
    (((binomialPowHom R hu t)⁻¹ : Aˣ) : A) = binomialPow u (-t.toAdd) :=
  (rfl)

/-- At an integer the binomial power is the integer power of the unit. -/
@[simp]
theorem binomialPow_intCast {g : Aˣ} (hg : IsNilpotent ((g : A) - 1)) (z : ℤ) :
    binomialPow (g : A) (z : R) = ((g ^ z : Aˣ) : A) := by
  cases z with
  | ofNat m => simpa using binomialPow_natCast hg m
  | negSucc m =>
    rw [zpow_negSucc]
    apply Units.eq_inv_of_mul_eq_one_left
    rw [Int.cast_negSucc, Units.val_pow_eq_pow_val, ← binomialPow_natCast (R := R) hg,
      binomialPow_mul_neg hg]

/-- **Binomial powers are unipotent, with the same bound**: if `(u - 1) ^ n = 0`, then
`(u ^ t - 1) ^ n = 0`. -/
theorem pow_binomialPow_sub_one_eq_zero {n : ℕ} (hn : (u - 1) ^ n = 0) (t : R) :
    (binomialPow u t - 1) ^ n = 0 := by
  rw [binomialPow_eq_sum (pow_eq_zero_of_le n.le_succ hn), sum_range_succ', Ring.choose_zero_right,
    pow_zero, one_smul, add_sub_cancel_right]
  exact pow_sum_smul_pow_succ_eq_zero hn (range n) fun j => Ring.choose t (j + 1)

/-- Binomial powers of a unipotent element are unipotent. -/
theorem isNilpotent_binomialPow_sub_one (hu : IsNilpotent (u - 1)) (t : R) :
    IsNilpotent (binomialPow u t - 1) :=
  let ⟨n, hn⟩ := hu
  ⟨n, pow_binomialPow_sub_one_eq_zero hn t⟩

/-- Binomial powers commute with algebra homomorphisms. -/
theorem map_binomialPow {B F : Type*} [Ring B] [Algebra R B] [FunLike F A B]
    [AlgHomClass F R A B] (hu : IsNilpotent (u - 1)) (f : F) (t : R) :
    f (binomialPow u t) = binomialPow (f u) t := by
  obtain ⟨n, hn⟩ := hu
  have hn' : (f u - 1) ^ n = 0 := by simpa using congrArg f hn
  simp [binomialPow_eq_sum hn, binomialPow_eq_sum hn']

/-- Over a rational module, a binomial coefficient of a square-zero element acts through its
first-order Taylor coefficient: `(ε choose (j + 1)) • y = ε • ((-1) ^ j / (j + 1)) • y`. -/
private theorem choose_succ_smul_of_sq_eq_zero [Module ℚ A] {ε : R} (hε : ε ^ 2 = 0) (j : ℕ)
    (y : A) : Ring.choose ε (j + 1) • y = ε • (((-1) ^ j / (j + 1 : ℕ) : ℚ) • y) := by
  have hj : ((j + 1 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 j.succ_ne_zero
  -- Both sides are determined by their `(j + 1)`-fold multiples, since `A` is a `ℚ`-module.
  apply smul_right_injective A hj
  dsimp only
  rw [Nat.cast_smul_eq_nsmul ℚ (j + 1) (Ring.choose ε (j + 1) • y), ← smul_assoc,
    TauCeti.Ring.succ_nsmul_choose_succ_of_sq_eq_zero hε, smul_comm ((j + 1 : ℕ) : ℚ) ε,
    smul_smul, mul_div_cancel₀ _ hj, mul_smul, smul_comm ε]
  -- The sign `(-1) ^ j` acts through `ℤ`, whether it is read in `R` or in `ℚ`.
  rw [show ((-1) ^ j : R) = (((-1) ^ j : ℤ) : R) by push_cast; rfl,
    show ((-1) ^ j : ℚ) = (((-1) ^ j : ℤ) : ℚ) by push_cast; rfl, Int.cast_smul_eq_zsmul,
    Int.cast_smul_eq_zsmul]

/-- **The tangent vector of a binomial power curve is the logarithm.** Over a rational algebra,
a square-zero exponent `ε` gives `u ^ ε = 1 + ε • log u`. Taking `R` to be the dual numbers over
the exponent ring, this says that the curve `t ↦ u ^ t` has derivative `log u` at `t = 0`. -/
theorem binomialPow_eq_one_add_smul_log [Module ℚ A] (hu : IsNilpotent (u - 1)) {ε : R}
    (hε : ε ^ 2 = 0) : binomialPow u ε = 1 + ε • IsNilpotent.log u := by
  obtain ⟨n, hn⟩ := hu
  have hn' : (u - 1) ^ (n + 1) = 0 := pow_eq_zero_of_le n.le_succ hn
  rw [binomialPow_eq_sum hn', IsNilpotent.log_eq_sum hn', sum_range_succ', sum_range_succ',
    Ring.choose_zero_right, pow_zero, one_smul, add_comm, Nat.cast_zero, div_zero, zero_smul,
    add_zero, smul_sum]
  congr 1
  refine sum_congr rfl fun j _ => ?_
  rw [choose_succ_smul_of_sq_eq_zero hε, show (-1 : ℚ) ^ (j + 1 + 1) = (-1) ^ j by ring]

end TauCeti

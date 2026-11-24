/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.Derivative
public import TauCeti.RingTheory.LambdaRing.Binomial
public import TauCeti.RingTheory.LambdaRing.MonoidAlgebra
import TauCeti.RingTheory.PowerSeries.Binomial
import TauCeti.RingTheory.PowerSeries.Rescale

/-!
# Adams operations of a pre-λ structure

The Adams operations `ψⁿ`, `n ≥ 1`, of a pre-λ structure are the coefficients of `-t` times the
logarithmic derivative of the total operation at `-t`:

```text
∑_{n ≥ 1} ψⁿ x tⁿ = -t λ_{-t}'(x) / λ_{-t}(x).
```

Since `λ_t` turns sums into products, its logarithmic derivative turns them into sums, so every
`ψⁿ` is additive, although `λⁿ` for `n ≥ 2` in general is not. Comparing coefficients gives Newton's
recurrence

```text
ψⁿ x = ∑_{i = 1}^{n - 1} (-1)^(i - 1) λⁱ x ψⁿ⁻ⁱ x + (-1)^(n - 1) n λⁿ x,
```

so `ψⁿ` is an integral polynomial in `λ¹, …, λⁿ` and no denominator is inverted: `ψ¹ x = x`,
`ψ² x = x² - 2 λ² x` and `ψ³ x = x³ - 3 x λ² x + 3 λ³ x`. Morphisms of pre-λ structures commute
with Adams operations, a line element `l` has `ψⁿ l = lⁿ`, and the Adams operations of the binomial
structure are all the identity. In particular Adams operations are not power maps: in binomial `ℤ`,
`ψ² (-1) = -1`, while in the line-monomial structure of a monoid algebra `ψ² [m] = [m]²`.

The series has no constant term, so `ψ⁰` is the zero map here. An Adams operation `ψ⁰` in the
sense of an augmented λ-ring, the augmentation followed by a section, needs that extra data and is
not this zero map.

Multiplicativity, `ψⁿ ∘ ψᵐ = ψⁿᵐ` and the congruence `ψᵖ x ≡ xᵖ` modulo a prime `p` hold for
special λ-rings, and are not proved here.

## Main definitions

* `TauCeti.PreLambdaStructure.adamsSeries`: the generating series `ψ_t x = ∑ₙ ψⁿ x tⁿ`.
* `TauCeti.PreLambdaStructure.adams`: the `n`th Adams operation `ψⁿ`, as an additive map.

## Main results

* `TauCeti.PreLambdaStructure.rescale_totalSeries_mul_adamsSeries`: the generating-series identity
  `λ_{-t}(x) ψ_t(x) = -t λ_{-t}'(x)`, which characterizes `ψ_t`
  (`TauCeti.PreLambdaStructure.eq_adamsSeries_iff`).
* `TauCeti.PreLambdaStructure.adamsSeries_add`: the Adams series is additive.
* `TauCeti.PreLambdaStructure.sum_antidiagonal_lambda_mul_adams`: Newton's identity
  `∑_{i + j = n} (-1)ⁱ λⁱ x ψʲ x = (-1)^(n + 1) n λⁿ x`.
* `TauCeti.PreLambdaStructure.adams_eq_sum`: Newton's recurrence for `ψⁿ`.
* `TauCeti.PreLambdaStructure.adams_one`, `TauCeti.PreLambdaStructure.adams_two`,
  `TauCeti.PreLambdaStructure.adams_three`: the first three Adams operations.
* `TauCeti.PreLambdaHom.map_adams`: morphisms of pre-λ structures commute with Adams operations.
* `TauCeti.PreLambdaStructure.IsLine.adams_eq_pow`: `ψⁿ l = lⁿ` for a line element `l` and `n ≥ 1`.
* `TauCeti.PreLambdaStructure.binomial_adamsSeries`,
  `TauCeti.PreLambdaStructure.binomial_adams_apply`: the binomial Adams series is `∑_{n ≥ 1} x tⁿ`,
  so the binomial Adams operations are the identity.

## References

* C. A. Weibel, *The K-book*, §II.4, pp. 93–94, and Exercises II.4.6–4.7.
-/

public noncomputable section

open PowerSeries Finset

namespace TauCeti

namespace PreLambdaStructure

variable {R : Type*} [CommRing R]
variable (Λ : PreLambdaStructure R)

/-! ### The Adams series -/

/-- The coefficients of the total operation at `-t` are `(-1)ⁿ λⁿ x`. -/
theorem coeff_rescale_totalSeries (n : ℕ) (x : R) :
    coeff n (rescale (-1) (Λ.totalSeries x)) = (-1) ^ n * Λ.lambda n x := by
  rw [coeff_rescale, coeff_totalSeries]

/-- The total operation at `-t` is a unit of `R⟦X⟧`. -/
theorem isUnit_rescale_totalSeries (x : R) : IsUnit (rescale (-1) (Λ.totalSeries x)) :=
  (Λ.isUnit_totalSeries x).map _

/-- The coefficients of `-t λ_{-t}'(x)`: the coefficient of `tⁿ` is `(-1)^(n + 1) n λⁿ x`. -/
theorem coeff_neg_X_mul_derivative_rescale_totalSeries (n : ℕ) (x : R) :
    coeff n (-(X * d⁄dX (rescale (-1) (Λ.totalSeries x)))) = (-1) ^ (n + 1) * n * Λ.lambda n x := by
  rw [map_neg, coeff_X_mul_derivative, coeff_rescale_totalSeries]
  ring

/-- The **Adams series** `ψ_t x = -t λ_{-t}'(x) / λ_{-t}(x)`, the generating series of the Adams
operations: minus `PowerSeries.xLogDeriv` of the unit `λ_{-t}(x)`. -/
def adamsSeries (x : R) : R⟦X⟧ :=
  -(xLogDeriv (Λ.isUnit_rescale_totalSeries x).unit).toAdd

/-- The **generating-series identity** of the Adams operations:
`λ_{-t}(x) ψ_t(x) = -t λ_{-t}'(x)`. -/
theorem rescale_totalSeries_mul_adamsSeries (x : R) :
    rescale (-1) (Λ.totalSeries x) * Λ.adamsSeries x =
      -(X * d⁄dX (rescale (-1) (Λ.totalSeries x))) := by
  rw [adamsSeries, toAdd_xLogDeriv, IsUnit.unit_spec, mul_neg, mul_comm, mul_assoc,
    IsUnit.val_inv_mul, mul_one]

/-- The generating-series identity characterizes the Adams series, since `λ_{-t}(x)` is a unit. -/
theorem eq_adamsSeries_iff {x : R} {φ : R⟦X⟧} :
    φ = Λ.adamsSeries x ↔
      rescale (-1) (Λ.totalSeries x) * φ = -(X * d⁄dX (rescale (-1) (Λ.totalSeries x))) := by
  refine ⟨fun h => h ▸ Λ.rescale_totalSeries_mul_adamsSeries x, fun h => ?_⟩
  exact (Λ.isUnit_rescale_totalSeries x).mul_left_cancel
    (h.trans (Λ.rescale_totalSeries_mul_adamsSeries x).symm)

/-- The Adams series is additive. -/
theorem adamsSeries_add (x y : R) :
    Λ.adamsSeries (x + y) = Λ.adamsSeries x + Λ.adamsSeries y := by
  have h : (Λ.isUnit_rescale_totalSeries (x + y)).unit =
      (Λ.isUnit_rescale_totalSeries x).unit * (Λ.isUnit_rescale_totalSeries y).unit :=
    Units.ext (by simp only [IsUnit.unit_spec, Units.val_mul, totalSeries_add, map_mul])
  rw [adamsSeries, adamsSeries, adamsSeries, h, map_mul, toAdd_mul, neg_add]

@[simp]
theorem adamsSeries_zero : Λ.adamsSeries 0 = 0 := by
  simpa using Λ.adamsSeries_add 0 0

/-- The Adams series has no constant term. -/
@[simp]
theorem constantCoeff_adamsSeries (x : R) : constantCoeff (Λ.adamsSeries x) = 0 := by
  simp [adamsSeries]

/-! ### Adams operations -/

/-- The `n`th **Adams operation** `ψⁿ`, the `n`th coefficient of the Adams series. It is additive.
For `n = 0` it is the zero map, since the Adams series has no constant term. -/
def adams (n : ℕ) : R →+ R where
  toFun x := coeff n (Λ.adamsSeries x)
  map_zero' := by simp
  map_add' x y := by simp [adamsSeries_add]

theorem adams_apply (n : ℕ) (x : R) : Λ.adams n x = coeff n (Λ.adamsSeries x) :=
  (rfl)

@[simp]
theorem coeff_adamsSeries (n : ℕ) (x : R) : coeff n (Λ.adamsSeries x) = Λ.adams n x :=
  (rfl)

theorem adamsSeries_eq_mk (x : R) : Λ.adamsSeries x = PowerSeries.mk fun n => Λ.adams n x := by
  ext n
  simp

@[simp]
theorem adams_zero : Λ.adams 0 = 0 := by
  ext x
  rw [adams_apply, coeff_zero_eq_constantCoeff_apply, constantCoeff_adamsSeries,
    AddMonoidHom.zero_apply]

/-- **Newton's identity** for the Adams operations:
`∑_{i + j = n} (-1)ⁱ λⁱ x ψʲ x = (-1)^(n + 1) n λⁿ x`. It is the coefficient of `tⁿ` in the
generating-series identity. -/
theorem sum_antidiagonal_lambda_mul_adams (n : ℕ) (x : R) :
    ∑ p ∈ antidiagonal n, (-1) ^ p.1 * Λ.lambda p.1 x * Λ.adams p.2 x =
      (-1) ^ (n + 1) * n * Λ.lambda n x := by
  have h := congrArg (coeff n) (Λ.rescale_totalSeries_mul_adamsSeries x)
  simpa only [coeff_mul, coeff_neg_X_mul_derivative_rescale_totalSeries, coeff_rescale_totalSeries,
    coeff_adamsSeries] using h

/-- **Newton's recurrence** for the Adams operations:
`ψⁿ x = ∑_{0 < i < n} (-1)^(i + 1) λⁱ x ψⁿ⁻ⁱ x + (-1)^(n + 1) n λⁿ x`. In particular `ψⁿ` is an
integral polynomial in `λ¹ x, …, λⁿ x`. -/
theorem adams_eq_sum (n : ℕ) (x : R) :
    Λ.adams n x = ∑ i ∈ Ico 1 n, (-1) ^ (i + 1) * Λ.lambda i x * Λ.adams (n - i) x +
      (-1) ^ (n + 1) * n * Λ.lambda n x := by
  rcases n with _ | n
  · simp
  have h := Λ.sum_antidiagonal_lambda_mul_adams (n + 1) x
  rw [Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => (-1) ^ i * Λ.lambda i x * Λ.adams j x), sum_range_succ, sum_range_succ'] at h
  rw [sum_Ico_eq_sum_range, ← h]
  simp [add_comm 1, pow_succ]

@[simp]
theorem adams_one : Λ.adams 1 = AddMonoidHom.id R := by
  ext x
  rw [adams_eq_sum]
  simp

/-- `ψ² x = x² - 2 λ² x`. -/
theorem adams_two (x : R) : Λ.adams 2 x = x ^ 2 - 2 * Λ.lambda 2 x := by
  rw [adams_eq_sum, Nat.Ico_succ_singleton]
  simp only [sum_singleton, lambda_one, Nat.reduceSub, adams_one, AddMonoidHom.id_apply]
  ring

/-- `ψ³ x = x³ - 3 x λ² x + 3 λ³ x`. -/
theorem adams_three (x : R) :
    Λ.adams 3 x = x ^ 3 - 3 * x * Λ.lambda 2 x + 3 * Λ.lambda 3 x := by
  rw [adams_eq_sum, show Ico 1 3 = {1, 2} by decide, sum_pair (by decide)]
  simp only [lambda_one, Nat.reduceSub, adams_one, AddMonoidHom.id_apply, adams_two]
  ring

/-! ### Line elements -/

/-- A line element `l` has Adams operations `ψⁿ l = lⁿ` for `n ≥ 1`. -/
theorem IsLine.adams_eq_pow {Λ : PreLambdaStructure R} {l : R} (h : Λ.IsLine l) {n : ℕ}
    (hn : n ≠ 0) :
    Λ.adams n l = l ^ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | n
    · exact absurd rfl hn
    · simp
    rw [adams_eq_sum, h.lambda_eq_zero (by omega), mul_zero, add_zero,
      sum_eq_single_of_mem 1 (by simp)]
    · rw [Nat.add_sub_cancel, ih (n + 1) (by omega) (by omega), lambda_one]
      ring
    · intro i hi hi1
      rw [h.lambda_eq_zero (by simp at hi; omega), mul_zero, zero_mul]

end PreLambdaStructure

/-! ### Naturality -/

namespace PreLambdaHom

variable {R S : Type*} [CommRing R] [CommRing S]
variable {Λ : PreLambdaStructure R} {Λ' : PreLambdaStructure S}

/-- A morphism of pre-λ structures carries the Adams series of `x` to that of its image. -/
theorem map_adamsSeries (f : PreLambdaHom Λ Λ') (x : R) :
    PowerSeries.map (f : R →+* S) (Λ.adamsSeries x) = Λ'.adamsSeries (f x) := by
  have hrescale : PowerSeries.map (f : R →+* S) (rescale (-1) (Λ.totalSeries x)) =
      rescale (-1) (Λ'.totalSeries (f x)) := by
    rw [← map_totalSeries, ← rescale_map, map_neg, map_one]
  rw [Λ'.eq_adamsSeries_iff, ← hrescale, ← map_mul, Λ.rescale_totalSeries_mul_adamsSeries,
    map_neg, map_mul, map_X, ← derivative_map]

/-- **Morphisms of pre-λ structures commute with Adams operations.** -/
@[simp]
theorem map_adams (f : PreLambdaHom Λ Λ') (n : ℕ) (x : R) :
    f (Λ.adams n x) = Λ'.adams n (f x) := by
  simpa using congrArg (coeff n) (f.map_adamsSeries x)

end PreLambdaHom

/-! ### The binomial and line-monomial structures -/

namespace PreLambdaStructure

section Binomial

variable {R : Type*} [CommRing R] [BinomialRing R]

/-- The binomial Adams series is `∑_{n ≥ 1} x tⁿ`. -/
theorem binomial_adamsSeries (x : R) :
    (binomial R).adamsSeries x = PowerSeries.mk fun k => if k = 0 then 0 else x := by
  -- Rescale the differential equation `(1 + X) (1 + X)^x' = x (1 + X)^x` of `λ_t(x)` to `-t`,
  -- and cancel the unit `1 - X`.
  have h := congrArg (fun φ => rescale (-1 : R) (X * φ))
    (one_add_X_mul_derivative_binomialSeries (A := R) x)
  rw [mul_left_comm, map_mul, rescale_X_mul_derivative] at h
  simp only [map_add, map_one, rescale_X, smul_eq_C_mul, map_mul, rescale_C, map_neg,
    neg_one_mul] at h
  have hφ : (1 - X) * (PowerSeries.mk fun k => if k = 0 then (0 : R) else x) = C x * X := by
    ext k
    rcases k with _ | _ | k <;> simp [sub_mul, coeff_succ_X_mul, coeff_X]
  rw [eq_comm, eq_adamsSeries_iff, totalSeries_binomial]
  refine (isUnit_iff_constantCoeff.mpr (by simp) : IsUnit (1 - X : R⟦X⟧)).mul_left_cancel ?_
  rw [mul_left_comm, hφ]
  linear_combination h

/-- **The binomial Adams operations are the identity**: `ψⁿ x = x` for `n ≥ 1`. -/
@[simp]
theorem binomial_adams_apply {n : ℕ} (hn : n ≠ 0) (x : R) : (binomial R).adams n x = x := by
  rw [adams_apply, binomial_adamsSeries, coeff_mk]
  simp [hn]

end Binomial

/-- In the line-monomial structure on a monoid algebra, `ψⁿ [m] = [mⁿ]` for `n ≥ 1`. -/
theorem lineMonomial_adams_of {M : Type*} [CommMonoid M] {n : ℕ} (hn : n ≠ 0) (m : M) :
    (lineMonomial M).adams n (MonoidAlgebra.of ℤ M m) = MonoidAlgebra.of ℤ M (m ^ n) := by
  rw [(isLine_lineMonomial_of m).adams_eq_pow hn, map_pow]

end PreLambdaStructure

end TauCeti

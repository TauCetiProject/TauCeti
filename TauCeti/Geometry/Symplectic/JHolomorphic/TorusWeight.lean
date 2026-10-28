/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.WellKnown
public import TauCeti.RingTheory.PowerSeries.Expand

/-!
# Four-twist multiplicity weights of square-zero pseudoholomorphic tori

In Taubes's count of embedded pseudoholomorphic curves in a symplectic four-manifold, an
embedded square-zero torus `C` may appear in a curve configuration with any positive
multiplicity `m`. The contribution of `C` with multiplicity `m` is the integer
`[t ^ m] f_(σ, i)`, the `m`-th coefficient of one of eight integral power series. The label
`(σ, i)` is read off from the four normal operators of `C` twisted by the real sign characters
`π₁(C) → {±1}`: `σ` is the determinant sign of the untwisted operator and `i ∈ {0, 1, 2, 3}`
counts the negative signs among the three nontrivially twisted operators. The series are

* `f_(+,0) = 1 / (1 - t)`, `f_(+,1) = 1 + t`, `f_(+,2) = (1 + t) / (1 + t ^ 2)`,
  `f_(+,3) = (1 + t) (1 - t ^ 2) / (1 + t ^ 2)`,
* `f_(-,i) = 1 / f_(+,i)`.

Each has constant term `1`, so the divisions take place in the unit group of `ℤ⟦X⟧`, using the
inverse `PowerSeries.invOfUnit`. For a finite family of pairwise disjoint tori the total weight
of the configurations with total multiplicity `n` is the `n`-th coefficient of the product of
their local series, which `TauCeti.coeff_prod_torusWeightSeries` expands as a sum of products of
local weights.

On the homology ray of a primitive square-zero class `A₀`, a torus of class `m • A₀` enters
with its local series evaluated at `t ^ m`. The ray series `∏_C f_label(C)(t ^ m_C)` of a family
of such tori, with finitely many tori in each class, is an infinite product in the
coefficientwise topology (`PowerSeries.WithPiTopology`); each of its coefficients is computed by
a finite cutoff and expands as a sum over the configurations of these tori of the given total
class. A configuration of total class `n • A₀` from a finite family `s` of tori, the torus `c`
having class `m c • A₀`, is a multiplicity assignment `l` in the weighted antidiagonal
`s.weightedFinsuppAntidiag m n`, that is, supported in `s` with `∑ c ∈ s, m c * l c = n`. The
expansion, cutoff and infinite product hold for any family of power series in place of the local
series (`PowerSeries.coeff_prod_expand`, `PowerSeries.coeff_prod_expand_of_subset`,
`PowerSeries.coeff_tprod_expand`), and are specialised here to the tori.

This file constructs only this series data and its coefficients; it assumes no geometric
regularity and gives no curve-count interpretation.

## Main declarations

* `TauCeti.torusWeightSeries σ i`: the local series `f_(σ, i)`, where `σ = true` stands for a
  positive determinant sign and `σ = false` for a negative one.
* `TauCeti.torusWeight σ i m`: the local weight `w_(σ, i)(m) = [t ^ m] f_(σ, i)`. The simp
  lemma `TauCeti.torusWeight_def` reduces it to the coefficient, so the closed forms below apply
  to it directly.
* `TauCeti.coeff_prod_torusWeightSeries`: the weight of a finite configuration of tori with total
  multiplicity `n` is the sum, over all distributions of `n` among the tori, of the products of
  the local weights.
* `TauCeti.torusWeightSeries_not_mul`, `TauCeti.isUnit_torusWeightSeries`: the series of
  opposite sign and equal index are mutually inverse units.
* `TauCeti.torusWeightSeries_true_zero`, `TauCeti.torusWeightSeries_true_one`,
  `TauCeti.torusWeightSeries_true_two_mul`, `TauCeti.torusWeightSeries_true_three_mul`,
  `TauCeti.torusWeightSeries_false_zero`, `TauCeti.torusWeightSeries_false_one_mul`,
  `TauCeti.torusWeightSeries_false_two_mul`, `TauCeti.torusWeightSeries_false_three_mul`:
  the rational-function identities characterizing the eight series.
* `TauCeti.coeff_torusWeightSeries_true_two`, `TauCeti.coeff_torusWeightSeries_true_three`,
  `TauCeti.coeff_torusWeightSeries_false_one`, `TauCeti.coeff_torusWeightSeries_false_two`,
  `TauCeti.coeff_torusWeightSeries_false_three`: closed forms for the multiplicity weights
  of the five series that are neither polynomials nor `PowerSeries.mk 1`.
* `TauCeti.rayTorusWeightSeries s m σ i`: the ray series `∏ c ∈ s, f_(σ c, i c)(t ^ m c)` of a
  finite family of tori; `TauCeti.constantCoeff_rayTorusWeightSeries` gives its constant term.
* `TauCeti.coeff_rayTorusWeightSeries`: the independent-component expansion of the coefficients
  of the ray series as sums over configurations of products of local weights.
* `TauCeti.coeff_rayTorusWeightSeries_of_subset`: tori of class larger than `n • A₀` do not
  affect the `n`-th coefficient.
* `TauCeti.multipliable_expand_torusWeightSeries`,
  `TauCeti.coeff_tprod_expand_torusWeightSeries`: the infinite ray product over a family with
  finitely many tori in each class exists, and its coefficients are those of finite cutoffs.

## References

* C. H. Taubes, *Counting pseudo-holomorphic submanifolds in dimension 4*,
  J. Differential Geom. 44 (1996), 818--893.
-/

public section

open PowerSeries

namespace TauCeti

/-- The positive-sign local series `f_(+, i)`, written with the actual inverse of the unit
`1 + X ^ 2`. -/
private noncomputable def positiveSeries : Fin 4 → ℤ⟦X⟧
  | 0 => mk 1
  | 1 => 1 + X
  | 2 => (1 + X) * invOfUnit (1 + X ^ 2) 1
  | 3 => (1 + X) * (1 - X ^ 2) * invOfUnit (1 + X ^ 2) 1

/-- The local multiplicity series `f_(σ, i) ∈ ℤ⟦X⟧` attached to an embedded square-zero
pseudoholomorphic torus with determinant sign `σ` (`true` for `+`, `false` for `-`) and with
`i` negative signs among its three nontrivially twisted normal operators. The positive series
are `1 / (1 - X)`, `1 + X`, `(1 + X) / (1 + X ^ 2)` and `(1 + X) (1 - X ^ 2) / (1 + X ^ 2)`,
and each negative series is the inverse of the positive series with the same index. The weight
of the torus with multiplicity `m` is the coefficient `coeff m (torusWeightSeries σ i)`. -/
noncomputable def torusWeightSeries (σ : Bool) (i : Fin 4) : ℤ⟦X⟧ :=
  if σ then positiveSeries i else invOfUnit (positiveSeries i) 1

/-- The local weight `w_(σ, i)(m) ∈ ℤ` of an embedded square-zero pseudoholomorphic torus with
label `(σ, i)` appearing with multiplicity `m`: the `m`-th coefficient of `torusWeightSeries σ i`.
-/
noncomputable def torusWeight (σ : Bool) (i : Fin 4) (m : ℕ) : ℤ :=
  coeff m (torusWeightSeries σ i)

/-- The local weight `w_(σ, i)(m)` is the `m`-th coefficient of the local series `f_(σ, i)`. -/
@[simp]
theorem torusWeight_def (σ : Bool) (i : Fin 4) (m : ℕ) :
    torusWeight σ i m = coeff m (torusWeightSeries σ i) := by
  rw [torusWeight]

/-- For a finite family `s` of tori, the torus `c` carrying the label `(σ c, i c)`, the `n`-th
coefficient of the product of the local series is the sum, over all ways `l` of distributing the
total multiplicity `n` among the tori, of the products of the local weights `w_(σ c, i c)(l c)`.
-/
theorem coeff_prod_torusWeightSeries {ι : Type*} [DecidableEq ι] (s : Finset ι) (σ : ι → Bool)
    (i : ι → Fin 4) (n : ℕ) :
    coeff n (∏ c ∈ s, torusWeightSeries (σ c) (i c)) =
      ∑ l ∈ s.finsuppAntidiag n, ∏ c ∈ s, torusWeight (σ c) (i c) (l c) :=
  coeff_prod _ n s

/-- Every local series has constant term `1`, so the multiplicity-zero weight is `1`. -/
@[simp]
theorem constantCoeff_torusWeightSeries (σ : Bool) (i : Fin 4) :
    constantCoeff (torusWeightSeries σ i) = 1 := by
  cases σ <;> fin_cases i <;> simp [torusWeightSeries, positiveSeries, constantCoeff_invOfUnit]

/-- The multiplicity-zero weight of every torus is `1`. -/
theorem torusWeight_zero (σ : Bool) (i : Fin 4) : torusWeight σ i 0 = 1 := by
  simp [torusWeight_def]

/-- The negative series is a right inverse of the positive series with the same index. -/
theorem torusWeightSeries_true_mul_false (i : Fin 4) :
    torusWeightSeries true i * torusWeightSeries false i = 1 := by
  simpa [torusWeightSeries] using
    mul_invOfUnit _ 1 (constantCoeff_torusWeightSeries true i)

/-- The negative series is a left inverse of the positive series with the same index. -/
theorem torusWeightSeries_false_mul_true (i : Fin 4) :
    torusWeightSeries false i * torusWeightSeries true i = 1 := by
  simpa [torusWeightSeries] using
    invOfUnit_mul _ 1 (constantCoeff_torusWeightSeries true i)

/-- Reversing the determinant sign inverts the local series. -/
theorem torusWeightSeries_not_mul (σ : Bool) (i : Fin 4) :
    torusWeightSeries (!σ) i * torusWeightSeries σ i = 1 := by
  cases σ
  · exact torusWeightSeries_true_mul_false i
  · exact torusWeightSeries_false_mul_true i

/-- Reversing the determinant sign inverts the local series. -/
theorem torusWeightSeries_mul_not (σ : Bool) (i : Fin 4) :
    torusWeightSeries σ i * torusWeightSeries (!σ) i = 1 := by
  rw [mul_comm, torusWeightSeries_not_mul]

/-- Every local series is a unit of `ℤ⟦X⟧`. -/
theorem isUnit_torusWeightSeries (σ : Bool) (i : Fin 4) : IsUnit (torusWeightSeries σ i) :=
  IsUnit.of_mul_eq_one _ (torusWeightSeries_mul_not σ i)

/-- A series equals the negative series `f_(-, i)` exactly when it inverts `f_(+, i)`. -/
theorem torusWeightSeries_false_eq_iff (i : Fin 4) (φ : ℤ⟦X⟧) :
    torusWeightSeries false i = φ ↔ torusWeightSeries true i * φ = 1 := by
  refine ⟨fun h ↦ h ▸ torusWeightSeries_true_mul_false i, fun h ↦ ?_⟩
  rw [← mul_one (torusWeightSeries false i), ← h, ← mul_assoc,
    torusWeightSeries_false_mul_true, one_mul]

/-! ### The rational-function identities -/

/-- `f_(+,0)` is the geometric series `1 + X + X ^ 2 + ⋯`. -/
@[simp]
theorem torusWeightSeries_true_zero : torusWeightSeries true 0 = mk 1 := by
  simp [torusWeightSeries, positiveSeries]

/-- `f_(+,1)` is the polynomial `1 + X`. -/
@[simp]
theorem torusWeightSeries_true_one : torusWeightSeries true 1 = 1 + X := by
  simp [torusWeightSeries, positiveSeries]

/-- `f_(+,0) = 1 / (1 - X)`. -/
theorem torusWeightSeries_true_zero_mul : torusWeightSeries true 0 * (1 - X) = 1 := by
  simpa using mk_one_mul_one_sub_eq_one ℤ

/-- `f_(+,2) = (1 + X) / (1 + X ^ 2)`. -/
theorem torusWeightSeries_true_two_mul :
    torusWeightSeries true 2 * (1 + X ^ 2) = 1 + X := by
  simp only [torusWeightSeries, positiveSeries, ite_true]
  rw [mul_assoc, invOfUnit_mul _ 1 (by simp), mul_one]

/-- `f_(+,3) = (1 + X) (1 - X ^ 2) / (1 + X ^ 2)`. -/
theorem torusWeightSeries_true_three_mul :
    torusWeightSeries true 3 * (1 + X ^ 2) = (1 + X) * (1 - X ^ 2) := by
  simp only [torusWeightSeries, positiveSeries, ite_true]
  rw [mul_assoc, invOfUnit_mul _ 1 (by simp), mul_one]

/-- `f_(-,0) = 1 - X`. -/
@[simp]
theorem torusWeightSeries_false_zero : torusWeightSeries false 0 = 1 - X := by
  rw [torusWeightSeries_false_eq_iff, torusWeightSeries_true_zero_mul]

/-- `f_(-,1) = 1 / (1 + X)`. -/
theorem torusWeightSeries_false_one_mul : torusWeightSeries false 1 * (1 + X) = 1 := by
  simpa using torusWeightSeries_false_mul_true 1

/-- `f_(-,2) = (1 + X ^ 2) / (1 + X)`. -/
theorem torusWeightSeries_false_two_mul :
    torusWeightSeries false 2 * (1 + X) = 1 + X ^ 2 := by
  rw [← torusWeightSeries_true_two_mul, ← mul_assoc, mul_comm _ (torusWeightSeries true 2),
    torusWeightSeries_true_mul_false, one_mul]

/-- `f_(-,3) = (1 + X ^ 2) / ((1 + X) (1 - X ^ 2))`. -/
theorem torusWeightSeries_false_three_mul :
    torusWeightSeries false 3 * ((1 + X) * (1 - X ^ 2)) = 1 + X ^ 2 := by
  rw [← torusWeightSeries_true_three_mul, ← mul_assoc, mul_comm _ (torusWeightSeries true 3),
    torusWeightSeries_true_mul_false, one_mul]

/-! ### Closed forms for the multiplicity weights

Each closed form is checked against the coefficient recurrence obtained by multiplying by the
denominator of the corresponding rational function, which is a unit of `ℤ⟦X⟧`. -/

/-- The multiplicity weights of `f_(+,2) = (1 + X) / (1 + X ^ 2)` are
`1, 1, -1, -1, 1, 1, …`. -/
@[simp]
theorem coeff_torusWeightSeries_true_two (m : ℕ) :
    coeff m (torusWeightSeries true 2) = (-1) ^ (m / 2) := by
  suffices torusWeightSeries true 2 = mk fun m ↦ (-1) ^ (m / 2) by simp [this]
  refine (isUnit_iff_constantCoeff.2 (by simp) : IsUnit (1 + X ^ 2 : ℤ⟦X⟧)).mul_right_cancel ?_
  rw [torusWeightSeries_true_two_mul]
  ext (_ | _ | n)
  · simp
  · simp [mul_add, coeff_mul_X_pow']
  · simp only [mul_add, map_add, mul_one]
    rw [coeff_mul_X_pow']
    simp [coeff_X, Nat.add_assoc, Nat.add_div_right, pow_succ]

/-- The multiplicity weights of `f_(+,3) = (1 + X) (1 - X ^ 2) / (1 + X ^ 2)` are
`1, 1, -2, -2, 2, 2, …`. -/
@[simp]
theorem coeff_torusWeightSeries_true_three (m : ℕ) :
    coeff m (torusWeightSeries true 3) = if m ≤ 1 then 1 else 2 * (-1) ^ (m / 2) := by
  suffices torusWeightSeries true 3 =
      mk fun m ↦ if m ≤ 1 then 1 else 2 * (-1) ^ (m / 2) by simp [this]
  refine (isUnit_iff_constantCoeff.2 (by simp) : IsUnit (1 + X ^ 2 : ℤ⟦X⟧)).mul_right_cancel ?_
  rw [torusWeightSeries_true_three_mul]
  ext (_ | _ | _ | _ | n)
  · simp
  · simp [mul_add, mul_sub, coeff_mul_X_pow']
  · simp only [mul_add, map_add, mul_one]
    rw [coeff_mul_X_pow']
    simp [mul_sub, add_mul, coeff_X, pow_succ]
  · simp only [mul_add, map_add, mul_one]
    rw [coeff_mul_X_pow']
    simp [mul_sub, add_mul, coeff_X, pow_succ]
  · simp only [mul_add, map_add, mul_one]
    rw [coeff_mul_X_pow']
    have h : (n + 4) / 2 = n / 2 + 2 := by omega
    simp [mul_sub, add_mul, coeff_X, Nat.add_assoc, h, pow_succ]

/-- The multiplicity weights of `f_(-,1) = 1 / (1 + X)` are `1, -1, 1, -1, …`. -/
@[simp]
theorem coeff_torusWeightSeries_false_one (m : ℕ) :
    coeff m (torusWeightSeries false 1) = (-1) ^ m := by
  suffices torusWeightSeries false 1 = mk fun m ↦ (-1) ^ m by simp [this]
  rw [torusWeightSeries_false_eq_iff, torusWeightSeries_true_one, mul_comm]
  exact mk_neg_one_pow_mul_one_add_eq_one ℤ

/-- The multiplicity weights of `f_(-,2) = (1 + X ^ 2) / (1 + X)` are
`1, -1, 2, -2, 2, -2, …`. -/
@[simp]
theorem coeff_torusWeightSeries_false_two (m : ℕ) :
    coeff m (torusWeightSeries false 2) = if m ≤ 1 then (-1) ^ m else 2 * (-1) ^ m := by
  suffices torusWeightSeries false 2 =
      mk fun m ↦ if m ≤ 1 then (-1) ^ m else 2 * (-1) ^ m by simp [this]
  refine (isUnit_iff_constantCoeff.2 (by simp) : IsUnit (1 + X : ℤ⟦X⟧)).mul_right_cancel ?_
  rw [torusWeightSeries_false_two_mul]
  ext (_ | _ | n)
  · simp
  · simp [mul_add]
  · simp only [mul_add, map_add, mul_one]
    rw [coeff_succ_mul_X]
    rcases n with _ | n <;> simp [coeff_X, pow_succ]

/-- The multiplicity weights of `f_(-,3) = (1 + X ^ 2) / ((1 + X) (1 - X ^ 2))` are
`1, -1, 3, -3, 5, -5, …`. -/
@[simp]
theorem coeff_torusWeightSeries_false_three (m : ℕ) :
    coeff m (torusWeightSeries false 3) = (-1) ^ m * (2 * ((m / 2 : ℕ) : ℤ) + 1) := by
  suffices torusWeightSeries false 3 = mk fun m ↦ (-1) ^ m * (2 * ((m / 2 : ℕ) : ℤ) + 1) by
    simp [this]
  refine (isUnit_iff_constantCoeff.2 (by simp) :
    IsUnit ((1 + X) * (1 - X ^ 2) : ℤ⟦X⟧)).mul_right_cancel ?_
  rw [torusWeightSeries_false_three_mul]
  ext (_ | _ | _ | n)
  · simp
  · simp [mul_add, mul_sub, ← mul_assoc, coeff_mul_X_pow']
  · rw [← mul_assoc]
    simp only [mul_sub, map_sub, mul_one, coeff_mul_X_pow', mul_add, map_add,
      coeff_succ_mul_X]
    simp [coeff_X_pow]
  · rw [← mul_assoc]
    simp only [mul_sub, map_sub, mul_one, coeff_mul_X_pow', mul_add, map_add,
      coeff_succ_mul_X]
    obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
    all_goals
      simp [pow_succ, pow_mul, coeff_X]
      omega

/-! ### Tori on a square-zero homology ray

Let `A₀` be a primitive square-zero class. A torus whose class is `m • A₀` and which appears
with multiplicity `l` contributes the class `(m * l) • A₀`, so its local series enters the count
of configurations on the ray of `A₀` with `t` replaced by `t ^ m`. The coefficient expansion,
the finite cutoff and the infinite product specialise the corresponding results of
`TauCeti.RingTheory.PowerSeries.Expand` for products of expanded power series. -/

section Ray

variable {ι : Type*}

/-- The weight series `∏ c ∈ s, f_(σ c, i c)(t ^ m c)` of a finite family `s` of embedded
square-zero pseudoholomorphic tori on the homology ray of a primitive class `A₀`, the torus `c`
having class `m c • A₀` and label `(σ c, i c)`. Its `n`-th coefficient is the sum, over the
multiplicity assignments of total class `n • A₀`, of the products of the local weights
(`TauCeti.coeff_rayTorusWeightSeries`). -/
noncomputable def rayTorusWeightSeries (s : Finset ι) (m : ι → ℕ+) (σ : ι → Bool)
    (i : ι → Fin 4) : ℤ⟦X⟧ :=
  ∏ c ∈ s, expand (m c) (m c).ne_zero (torusWeightSeries (σ c) (i c))

/-- The ray series is the product of the local series evaluated at `t ^ m c`. -/
theorem rayTorusWeightSeries_def (s : Finset ι) (m : ι → ℕ+) (σ : ι → Bool) (i : ι → Fin 4) :
    rayTorusWeightSeries s m σ i =
      ∏ c ∈ s, expand (m c) (m c).ne_zero (torusWeightSeries (σ c) (i c)) := by
  rw [rayTorusWeightSeries]

/-- The ray series has constant term `1`. -/
@[simp]
theorem constantCoeff_rayTorusWeightSeries (s : Finset ι) (m : ι → ℕ+) (σ : ι → Bool)
    (i : ι → Fin 4) : constantCoeff (rayTorusWeightSeries s m σ i) = 1 := by
  simp [rayTorusWeightSeries_def, map_prod, constantCoeff_expand]

/-- **Independent-component expansion** of the ray series: its `n`-th coefficient is the sum,
over all configurations `l` of total class `n • A₀` (the elements of
`s.weightedFinsuppAntidiag m n`), of the products of the local weights
`w_(σ c, i c)(l c)`. -/
theorem coeff_rayTorusWeightSeries (s : Finset ι) (m : ι → ℕ+) (σ : ι → Bool) (i : ι → Fin 4)
    (n : ℕ) :
    coeff n (rayTorusWeightSeries s m σ i) =
      ∑ l ∈ s.weightedFinsuppAntidiag m n, ∏ c ∈ s, torusWeight (σ c) (i c) (l c) :=
  coeff_prod_expand s m _ n

/-- **Finite cutoff** for the ray series: adjoining tori whose classes are all larger than
`n • A₀` does not change the `n`-th coefficient. -/
theorem coeff_rayTorusWeightSeries_of_subset {s t : Finset ι} (hst : s ⊆ t) {m : ι → ℕ+}
    (σ : ι → Bool) (i : ι → Fin 4) {n : ℕ} (h : ∀ c ∈ t, c ∉ s → n < m c) :
    coeff n (rayTorusWeightSeries t m σ i) = coeff n (rayTorusWeightSeries s m σ i) :=
  coeff_prod_expand_of_subset hst h fun c _ _ ↦ constantCoeff_torusWeightSeries (σ c) (i c)

open scoped PowerSeries.WithPiTopology

/-- The ray factors `f_(σ c, i c)(t ^ m c)` of a family of tori with finitely many tori in each
class `m • A₀` have an infinite product in the coefficientwise topology
(`PowerSeries.WithPiTopology`) on `ℤ⟦X⟧`. -/
theorem multipliable_expand_torusWeightSeries {m : ι → ℕ+}
    (hm : ∀ n : ℕ, {c | (m c : ℕ) ≤ n}.Finite) (σ : ι → Bool) (i : ι → Fin 4) :
    Multipliable fun c ↦ expand (m c) (m c).ne_zero (torusWeightSeries (σ c) (i c)) :=
  multipliable_expand hm fun c ↦ constantCoeff_torusWeightSeries (σ c) (i c)

/-- The `n`-th coefficient of the infinite ray product `∏_c f_(σ c, i c)(t ^ m c)`, over a
family of tori with finitely many tori in each class, is that of the ray series of any finite
subfamily containing every torus of class at most `n • A₀`. -/
theorem coeff_tprod_expand_torusWeightSeries {m : ι → ℕ+}
    (hm : ∀ n : ℕ, {c | (m c : ℕ) ≤ n}.Finite) (σ : ι → Bool) (i : ι → Fin 4) {s : Finset ι}
    {n : ℕ} (hs : ∀ c, (m c : ℕ) ≤ n → c ∈ s) :
    coeff n (∏' c, expand (m c) (m c).ne_zero (torusWeightSeries (σ c) (i c))) =
      coeff n (rayTorusWeightSeries s m σ i) :=
  coeff_tprod_expand hm (fun c ↦ constantCoeff_torusWeightSeries (σ c) (i c)) hs

end Ray

end TauCeti

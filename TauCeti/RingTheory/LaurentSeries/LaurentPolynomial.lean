/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Laurent
public import TauCeti.RingTheory.LaurentSeries.Basic

/-!
# Laurent polynomials as Laurent series

A Laurent polynomial is a Laurent series with finitely many nonzero coefficients. This file
defines the ring homomorphism `LaurentPolynomial.toLaurentSeries : R[T;T⁻¹] →+* R⸨X⸩` sending `T`
to `X`, and shows that it preserves coefficients, so in particular it is injective.

## Main definitions

* `LaurentPolynomial.toLaurentSeries`: the inclusion of Laurent polynomials into Laurent series.

## Main results

* `LaurentPolynomial.toLaurentSeries_T`: `Tⁿ` is sent to `Xⁿ`, for every integer `n`.
* `LaurentPolynomial.coeff_toLaurentSeries`: the inclusion preserves coefficients.
* `LaurentPolynomial.toLaurentSeries_injective`: the inclusion is injective.
* `TauCeti.toLaurentSeriesAlgHom`: the same inclusion as an algebra homomorphism.
* `TauCeti.mem_range_toLaurentSeries_iff`: its image is exactly the series with finite support.
* `TauCeti.tendsto_laurentPolynomialTrunc`: finite Laurent truncations converge in the
  valuation topology, retaining negative exponents as well as nonnegative ones.
* `TauCeti.denseRange_toLaurentSeries`: Laurent polynomials are dense in Laurent series.

Finite truncation uses Mathlib's `HahnSeries.truncLT` and `Finsupp.ofSupportFinite`.

The algebra-homomorphism, support, image, and truncation results below are in `TauCeti`.
Use their qualified names, for example `TauCeti.mem_range_toLaurentSeries_iff f` and
`TauCeti.tendsto_laurentPolynomialTrunc f`.
-/

public section

open scoped LaurentPolynomial LaurentSeries

namespace LaurentPolynomial

variable {R : Type*} [CommSemiring R]

/-- `X` as a unit of `R⸨X⸩`, with inverse `X⁻¹`. -/
private noncomputable def singleOneUnit : (R⸨X⸩)ˣ where
  val := HahnSeries.single 1 1
  inv := HahnSeries.single (-1) 1
  val_inv := by simp
  inv_val := by simp

private theorem val_singleOneUnit_zpow (n : ℤ) :
    ((singleOneUnit (R := R) ^ n : (R⸨X⸩)ˣ) : R⸨X⸩) = HahnSeries.single n 1 := by
  induction n using Int.induction_on with
  | zero => simp
  | succ n ih =>
    rw [zpow_add_one, Units.val_mul, ih]
    simp [singleOneUnit]
  | pred n ih =>
    rw [zpow_sub_one, Units.val_mul, ih]
    simp [singleOneUnit, sub_eq_add_neg]

/-- The inclusion of Laurent polynomials into Laurent series, sending `T` to `X`. -/
noncomputable def toLaurentSeries : R[T;T⁻¹] →+* R⸨X⸩ :=
  eval₂ HahnSeries.C singleOneUnit

/-- `Tⁿ` is sent to `Xⁿ`, for every integer `n`. -/
@[simp]
theorem toLaurentSeries_T (n : ℤ) : toLaurentSeries (T n : R[T;T⁻¹]) = HahnSeries.single n 1 := by
  rw [toLaurentSeries, eval₂_T, val_singleOneUnit_zpow]

/-- Constants are sent to constants. -/
@[simp]
theorem toLaurentSeries_C (r : R) : toLaurentSeries (C r) = HahnSeries.C r := by
  rw [toLaurentSeries, eval₂_C]

/-- The inclusion of Laurent polynomials into Laurent series preserves coefficients. -/
@[simp]
theorem coeff_toLaurentSeries (p : R[T;T⁻¹]) (n : ℤ) :
    (toLaurentSeries p).coeff n = p.coeff n := by
  induction p using LaurentPolynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | C_mul_T m r =>
    rw [map_mul, toLaurentSeries_T, toLaurentSeries_C, ← single_eq_C_mul_T, HahnSeries.C_apply,
      HahnSeries.single_mul_single, zero_add, mul_one, HahnSeries.coeff_single,
      AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
    simp [eq_comm]

/-- The inclusion of Laurent polynomials into Laurent series is injective. -/
theorem toLaurentSeries_injective : Function.Injective (toLaurentSeries (R := R)) :=
  fun p q h ↦ LaurentPolynomial.ext fun n ↦ by
    rw [← coeff_toLaurentSeries, h, coeff_toLaurentSeries]

end LaurentPolynomial

open scoped Topology

namespace TauCeti
open HahnSeries

noncomputable section

variable {R : Type*} [CommSemiring R]

/-- The canonical Laurent-series inclusion, equipped with its coefficient-algebra structure. -/
def toLaurentSeriesAlgHom : R[T;T⁻¹] →ₐ[R] R⸨X⸩ where
  __ := LaurentPolynomial.toLaurentSeries
  commutes' c := by
    change LaurentPolynomial.toLaurentSeries (algebraMap R R[T;T⁻¹] c) =
      algebraMap R R⸨X⸩ c
    rw [← LaurentPolynomial.C_eq_algebraMap, LaurentPolynomial.toLaurentSeries_C]
    simp [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_eq, ofPowerSeries_C]

/-- The Laurent-polynomial and power-series inclusions of a polynomial agree. -/
@[simp]
theorem toLaurentSeries_toLaurent (p : Polynomial R) :
    LaurentPolynomial.toLaurentSeries p.toLaurent = ((p : PowerSeries R) : R⸨X⸩) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n c =>
    ext i
    simp only [Polynomial.toLaurent_C_mul_T, map_mul, LaurentPolynomial.toLaurentSeries_C,
      LaurentPolynomial.toLaurentSeries_T, HahnSeries.C_apply, single_mul_single, zero_add, mul_one,
      coeff_single, PowerSeries.coeff_coe, Polynomial.coe_monomial]
    by_cases hi : i < 0
    · have hne : i ≠ (n : ℤ) := by omega
      simp [hi, hne]
    · have habs : (i.natAbs : ℤ) = i := Int.natAbs_of_nonneg (by omega)
      have hindex : i = (n : ℤ) ↔ i.natAbs = n := by omega
      simp [hi, PowerSeries.coeff_monomial, hindex]

/-- The inclusion preserves support, viewed as a subset of the integers. -/
@[simp]
theorem support_toLaurentSeries (p : R[T;T⁻¹]) :
    (LaurentPolynomial.toLaurentSeries (R := R) p).support = (p.coeff.support : Set ℤ) := by
  ext n
  simp

/-- The image of the inclusion is exactly the Laurent series with finite support. -/
theorem mem_range_toLaurentSeries_iff (f : R⸨X⸩) :
    f ∈ Set.range (LaurentPolynomial.toLaurentSeries (R := R)) ↔ f.support.Finite := by
  constructor
  · rintro ⟨p, rfl⟩
    simpa only [support_toLaurentSeries] using p.coeff.support.finite_toSet
  · intro hf
    refine ⟨AddMonoidAlgebra.ofCoeff (Finsupp.ofSupportFinite f.coeff hf), ?_⟩
    ext n
    rw [LaurentPolynomial.coeff_toLaurentSeries, AddMonoidAlgebra.coeff_ofCoeff]
    exact congrFun Finsupp.ofSupportFinite_coe n

/-- The Laurent polynomial retaining exactly the coefficients strictly below `a`. -/
def laurentPolynomialTrunc {A : Type*} [Semiring A] (a : ℤ) (f : A⸨X⸩) : A[T;T⁻¹] :=
  AddMonoidAlgebra.ofCoeff
    (Finsupp.ofSupportFinite (truncLT a f).coeff (support_truncLT_finite a f))

/-- The coefficient formula for finite Laurent truncation. -/
@[simp]
theorem coeff_laurentPolynomialTrunc {A : Type*} [Semiring A] (a n : ℤ) (f : A⸨X⸩) :
    (laurentPolynomialTrunc a f).coeff n = if n < a then f.coeff n else 0 := by
  rw [laurentPolynomialTrunc, AddMonoidAlgebra.coeff_ofCoeff,
    ← HahnSeries.coeff_truncLT a f n]
  exact congrFun Finsupp.ofSupportFinite_coe n

/-- Finite Laurent truncation agrees with Hahn-series truncation after inclusion. -/
@[simp]
theorem toLaurentSeries_trunc (a : ℤ) (f : R⸨X⸩) :
    LaurentPolynomial.toLaurentSeries (laurentPolynomialTrunc a f) = truncLT a f := by
  ext n
  simp [HahnSeries.coeff_truncLT]

variable {K : Type*} [Field K]

/-- The truncation error has valuation at most `exp (-a)`. -/
theorem valuation_sub_laurentPolynomialTrunc_le (a : ℤ) (f : K⸨X⸩) :
    Valued.v (f - LaurentPolynomial.toLaurentSeries (laurentPolynomialTrunc a f)) ≤
      WithZero.exp (-a) := by
  rw [_root_.LaurentSeries.valuation_le_iff_coeff_lt_eq_zero]
  intro n hn
  simp [hn]

open Filter MonoidWithZeroHom.ValueGroup₀

/-- Finite Laurent truncations converge to the original series in the valuation topology. -/
theorem tendsto_laurentPolynomialTrunc (f : K⸨X⸩) :
    Tendsto (fun a : ℤ ↦ LaurentPolynomial.toLaurentSeries (laurentPolynomialTrunc a f))
      atTop (𝓝 f) := by
  rw [Filter.tendsto_def]
  intro s hs
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds.mp hs
  let v := (Valued.v : Valuation K⸨X⸩ (WithZero (Multiplicative ℤ)))
  let e := embedding (f := v.toMonoidWithZeroHom)
  let δ := e γ.1
  have hδ : δ ≠ 0 := embedding_unit_ne_zero (f := v.toMonoidWithZeroHom) γ
  filter_upwards [eventually_ge_atTop (-WithZero.log δ + 1)] with a ha
  apply hγ
  simp only [Set.mem_ofPred_eq]
  rw [Valuation.restrict_lt_iff_lt_embedding (v := v)]
  apply lt_of_le_of_lt (b := WithZero.exp (-a))
  · rw [Valuation.map_sub_swap]
    exact valuation_sub_laurentPolynomialTrunc_le a f
  · have hbound : WithZero.exp (-a) < δ := by
      rw [← WithZero.exp_log hδ, WithZero.exp_lt_exp]
      omega
    exact hbound

/-- Laurent polynomials are dense in the Laurent field for its valuation topology. -/
theorem denseRange_toLaurentSeries : DenseRange (LaurentPolynomial.toLaurentSeries (R := K)) := by
  intro f
  exact mem_closure_of_tendsto (tendsto_laurentPolynomialTrunc f)
    (Eventually.of_forall fun a ↦ Set.mem_range_self (laurentPolynomialTrunc a f))

end

end TauCeti

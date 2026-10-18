/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Laurent
public import TauCeti.RingTheory.LaurentSeries.Basic
public import TauCeti.RingTheory.LaurentSeries.Convergence

/-!
# Laurent polynomials as Laurent series

A Laurent polynomial is a Laurent series with finitely many nonzero coefficients. This file
defines the ring homomorphism `LaurentPolynomial.toLaurentSeries : R[T;T⁻¹] →+* R⸨X⸩` sending `T`
to `X`, and shows that it preserves coefficients, so in particular it is injective. This map gives
`R⸨X⸩` its canonical `R[T;T⁻¹]`-algebra structure. The resulting algebra towers make the two
routes from polynomials to Laurent series agree: through power series and through Laurent
polynomials. The image of the Laurent-polynomial map is exactly the Laurent series of finite
support, and the order of a nonzero image is the least exponent in the Laurent polynomial's
support.

For a Laurent series `f`, `LaurentSeries.trunc N f` retains the terms of exponent strictly less
than `N`. These Laurent polynomials converge to `f` as `N` tends to infinity. Consequently,
Laurent polynomials are dense in the Laurent-series field for its valuation topology.

## Main definitions

* `LaurentPolynomial.toLaurentSeries`: the inclusion of Laurent polynomials into Laurent series.
* `LaurentSeries.algebraLaurentPolynomial`: the induced Laurent-polynomial algebra structure.

## Main results

* `LaurentPolynomial.toLaurentSeries_T`: `Tⁿ` is sent to `Xⁿ`, for every integer `n`.
* `LaurentPolynomial.coeff_toLaurentSeries`: the inclusion preserves coefficients.
* `LaurentPolynomial.toLaurentSeries_injective`: the inclusion is injective.
* `LaurentPolynomial.toLaurentSeries_toLaurent`: the polynomial embedding commutes with the
  inclusions into Laurent polynomials and power series.
* `LaurentPolynomial.mem_range_toLaurentSeries_iff`: the image consists exactly of the
  finite-support Laurent series.
* `LaurentSeries.trunc`: truncation of a Laurent series above a given integer exponent.
* `LaurentSeries.tendsto_toLaurentSeries_trunc`: the truncations converge to the original series.
* `LaurentPolynomial.denseRange_toLaurentSeries`: Laurent polynomials are dense in Laurent series.
* `TauCeti.valuation_sub_toLaurentSeries_trunc_le`: the valuation bound on truncation errors.
-/

public section

open scoped LaurentPolynomial LaurentSeries Polynomial

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

/-- Laurent series form an algebra over Laurent polynomials through the finite-support
inclusion. -/
noncomputable instance _root_.LaurentSeries.algebraLaurentPolynomial : Algebra R[T;T⁻¹] R⸨X⸩ :=
  toLaurentSeries.toAlgebra

/-- The algebra map from Laurent polynomials to Laurent series is the finite-support
inclusion. -/
@[simp]
theorem algebraMap_eq_toLaurentSeries (p : R[T;T⁻¹]) :
    algebraMap R[T;T⁻¹] R⸨X⸩ p = toLaurentSeries p := (rfl)

/-- The coefficient ring, Laurent-polynomial ring, and Laurent-series ring form an algebra
tower. -/
instance isScalarTower_laurentSeries : IsScalarTower R R[T;T⁻¹] R⸨X⸩ :=
  .of_algebraMap_smul fun r f ↦ by
    simp [Algebra.smul_def]

/-- The inclusion of a polynomial into Laurent series agrees with first viewing it as a Laurent
polynomial. -/
@[simp]
theorem toLaurentSeries_toLaurent (p : R[X]) :
    toLaurentSeries (Polynomial.toLaurent p) =
      ((p : PowerSeries R) : LaurentSeries R) := by
  have h : (toLaurentSeries (R := R)).comp Polynomial.toLaurent =
      (HahnSeries.ofPowerSeries ℤ R).comp Polynomial.coeToPowerSeries.ringHom := by
    apply Polynomial.ringHom_ext
    · intro r
      simp
    · simp
  exact DFunLike.congr_fun h p

/-- The polynomial, Laurent-polynomial, and Laurent-series algebra structures form a tower. -/
instance isScalarTower_polynomial_laurentPolynomial :
    IsScalarTower (Polynomial R) R[T;T⁻¹] (LaurentSeries R) :=
  .of_algebraMap_eq fun p ↦ by simp

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

/-- The support of a Laurent polynomial viewed as a Laurent series is its finite support. -/
@[simp]
theorem support_toLaurentSeries (p : R[T;T⁻¹]) :
    (toLaurentSeries p).support = p.coeff.support := by
  ext n
  simp [HahnSeries.mem_support]

/-- A Laurent series is the image of a Laurent polynomial exactly when it has finite support. -/
theorem mem_range_toLaurentSeries_iff (f : R⸨X⸩) :
    f ∈ Set.range (toLaurentSeries (R := R)) ↔ f.support.Finite := by
  constructor
  · rintro ⟨p, rfl⟩
    rw [support_toLaurentSeries]
    exact p.coeff.support.finite_toSet
  · intro hf
    let p : R[T;T⁻¹] := AddMonoidAlgebra.ofCoeff (Finsupp.ofSupportFinite f.coeff hf)
    refine ⟨p, ?_⟩
    ext n
    rw [coeff_toLaurentSeries]
    exact congrFun Finsupp.ofSupportFinite_coe n

/-- The order of a nonzero Laurent polynomial viewed as a Laurent series is the least exponent in
its support. -/
theorem order_toLaurentSeries (p : R[T;T⁻¹]) (hp : p ≠ 0) :
    (toLaurentSeries p).order = p.coeff.support.min'
      (Finsupp.support_nonempty_iff.mpr (AddMonoidAlgebra.coeff_injective.ne hp)) := by
  apply le_antisymm
  · apply HahnSeries.order_le_of_coeff_ne_zero
    rw [coeff_toLaurentSeries]
    exact Finsupp.mem_support_iff.mp (Finset.min'_mem _ _)
  · apply Finset.min'_le
    rw [Finsupp.mem_support_iff, ← coeff_toLaurentSeries]
    apply HahnSeries.coeff_order_eq_zero.not.mpr
    intro h
    apply hp
    apply toLaurentSeries_injective
    simpa using h

end LaurentPolynomial

namespace LaurentSeries

open Filter Topology

section Semiring

variable {R : Type*} [Semiring R]

/-- The Laurent polynomial obtained from a Laurent series by retaining the coefficients at
exponents strictly less than `N`. The lower bound on a Laurent series makes this a finite sum. -/
noncomputable def trunc (N : ℤ) : R⸨X⸩ →ₗ[R] R[T;T⁻¹] where
  toFun f := AddMonoidAlgebra.ofCoeff <| Finsupp.ofSupportFinite
    (HahnSeries.truncLT N f).coeff (TauCeti.support_truncLT_finite N f)
  map_add' f g := by
    ext n
    change (HahnSeries.truncLT N (f + g)).coeff n =
      (HahnSeries.truncLT N f).coeff n + (HahnSeries.truncLT N g).coeff n
    rw [HahnSeries.truncLT_add, HahnSeries.coeff_add]
  map_smul' r f := by
    ext n
    change (HahnSeries.truncLT N (r • f)).coeff n = r • (HahnSeries.truncLT N f).coeff n
    rw [HahnSeries.truncLT_smul, HahnSeries.coeff_smul]

/-- The coefficient of a truncation agrees with the original series below the cutoff and vanishes
at and above it. -/
@[simp]
theorem coeff_trunc (N n : ℤ) (f : R⸨X⸩) :
    (trunc N f).coeff n = if n < N then f.coeff n else 0 := by
  rw [trunc, AddMonoidAlgebra.coeff_ofCoeff]
  exact congrFun Finsupp.ofSupportFinite_coe n

end Semiring

variable {R : Type*} [CommSemiring R]

/-- Embedding a Laurent-polynomial truncation gives the corresponding strict truncation of the
Hahn series. -/
@[simp]
theorem toLaurentSeries_trunc (N : ℤ) (f : R⸨X⸩) :
    LaurentPolynomial.toLaurentSeries (trunc N f) = HahnSeries.truncLT N f := by
  ext n
  simp only [LaurentPolynomial.coeff_toLaurentSeries, coeff_trunc,
    HahnSeries.coeff_truncLT]

section Ring

variable {A : Type*} [CommRing A]

/-- The difference between a Laurent series and its truncation has order at least the cutoff. -/
theorem le_orderTop_sub_toLaurentSeries_trunc (N : ℤ) (f : A⸨X⸩) :
    (N : WithTop ℤ) ≤
      (LaurentPolynomial.toLaurentSeries (trunc N f) - f).orderTop := by
  rw [HahnSeries.le_orderTop_iff_forall]
  intro n hn
  rw [HahnSeries.coeff_sub, LaurentPolynomial.coeff_toLaurentSeries, coeff_trunc,
    ite_eq_left (WithTop.coe_lt_coe.mp hn), sub_self]

end Ring

variable {K : Type*} [Field K]

/-- The Laurent-polynomial truncations of a Laurent series converge to it in the valuation
topology. -/
theorem tendsto_toLaurentSeries_trunc (f : K⸨X⸩) :
    Tendsto (fun N : ℤ ↦ LaurentPolynomial.toLaurentSeries (trunc N f)) atTop (nhds f) := by
  rw [TauCeti.tendsto_laurentSeries_iff_orderTop_sub]
  intro D
  filter_upwards [eventually_ge_atTop D] with N hN
  exact (WithTop.coe_le_coe.mpr hN).trans (le_orderTop_sub_toLaurentSeries_trunc N f)

end LaurentSeries

namespace LaurentPolynomial

open Topology

variable {K : Type*} [Field K]

/-- Laurent polynomials are dense in the Laurent-series field for the valuation topology. -/
theorem denseRange_toLaurentSeries :
    DenseRange (toLaurentSeries (R := K) : K[T;T⁻¹] → K⸨X⸩) := by
  rw [denseRange_iff_closure_range]
  apply Set.eq_univ_of_forall
  intro f
  exact mem_closure_of_tendsto (LaurentSeries.tendsto_toLaurentSeries_trunc f) <|
    Filter.Eventually.of_forall fun N ↦ Set.mem_range_self (LaurentSeries.trunc N f)

end LaurentPolynomial

namespace TauCeti

variable {K : Type*} [Field K]

/-- The truncation error has valuation at most `exp (-a)`. -/
theorem valuation_sub_toLaurentSeries_trunc_le (a : ℤ) (f : K⸨X⸩) :
    Valued.v (f - LaurentPolynomial.toLaurentSeries (_root_.LaurentSeries.trunc a f)) ≤
      WithZero.exp (-a) := by
  rw [_root_.LaurentSeries.valuation_le_iff_coeff_lt_eq_zero]
  intro n hn
  simp [hn]

end TauCeti

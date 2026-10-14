/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Laurent
public import TauCeti.RingTheory.LaurentSeries.Basic

/-!
# Laurent polynomials inside Laurent series

The coefficient-preserving algebra homomorphism `laurentPolynomialToSeries` embeds Laurent
polynomials into Laurent series. Its image consists exactly of the series with finite support,
and its restriction to polynomials agrees with the inclusion through power series.

The finite Laurent polynomial `laurentPolynomialTrunc a f` retains the coefficients of `f`
strictly below the integer cutoff `a`. These truncations approximate `f` in the valuation
topology, proving density of Laurent polynomials. Negative exponents are retained, so this
approximation applies to series with poles as well as to power series.

The algebra map uses Mathlib's `AddMonoidAlgebra.lift`; truncation uses
`HahnSeries.truncLT` and `Finsupp.ofSupportFinite`.
-/

public section

open scoped LaurentPolynomial LaurentSeries Topology

namespace TauCeti

open HahnSeries

noncomputable section

variable (R : Type*) [CommSemiring R]

/-- The coefficient-preserving inclusion of Laurent polynomials into Laurent series. -/
def laurentPolynomialToSeries : R[T;T⁻¹] →ₐ[R] R⸨X⸩ :=
  AddMonoidAlgebra.lift R R⸨X⸩ ℤ
    { toFun n := single n.toAdd 1
      map_one' := by simp
      map_mul' m n := by simp [single_mul_single] }

variable {R}

/-- The inclusion sends a constant Laurent polynomial to the constant Hahn series. -/
@[simp]
theorem laurentPolynomialToSeries_C (c : R) :
    laurentPolynomialToSeries R (LaurentPolynomial.C c) = single 0 c := by
  rw [LaurentPolynomial.C_eq_algebraMap, AlgHom.commutes]
  simp [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_eq, ofPowerSeries_C, C_apply]

/-- An integral power of the Laurent variable maps to the corresponding singleton series. -/
@[simp]
theorem laurentPolynomialToSeries_T (n : ℤ) :
    laurentPolynomialToSeries R (LaurentPolynomial.T n) = single n 1 := by
  dsimp only [laurentPolynomialToSeries, LaurentPolynomial.T]
  rw [AddMonoidAlgebra.lift_single, Algebra.smul_def, map_one, one_mul]
  -- Evaluate the monoid homomorphism supplied to the monoid-algebra lift.
  rfl

/-- The inclusion preserves every coefficient. -/
@[simp]
theorem coeff_laurentPolynomialToSeries (p : R[T;T⁻¹]) (n : ℤ) :
    (laurentPolynomialToSeries R p).coeff n = p.coeff n := by
  induction p using LaurentPolynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | C_mul_T m c =>
    simp only [map_mul, laurentPolynomialToSeries_C, laurentPolynomialToSeries_T,
      single_mul_single, zero_add, mul_one]
    rw [← LaurentPolynomial.single_eq_C_mul_T]
    simp only [coeff_single, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
    split_ifs <;> simp_all

/-- Distinct Laurent polynomials have distinct Laurent-series images. -/
theorem laurentPolynomialToSeries_injective : Function.Injective (laurentPolynomialToSeries R) := by
  intro p q h
  ext n
  simpa using congrArg (fun f : R⸨X⸩ ↦ f.coeff n) h

/-- The Laurent-polynomial and power-series inclusions of a polynomial agree. -/
@[simp]
theorem laurentPolynomialToSeries_toLaurent (p : Polynomial R) :
    laurentPolynomialToSeries R p.toLaurent = ((p : PowerSeries R) : R⸨X⸩) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n c =>
    ext i
    simp only [Polynomial.toLaurent_C_mul_T, map_mul, laurentPolynomialToSeries_C,
      laurentPolynomialToSeries_T, single_mul_single, zero_add, mul_one,
      coeff_single, PowerSeries.coeff_coe, Polynomial.coe_monomial]
    by_cases hi : i < 0
    · have hne : i ≠ (n : ℤ) := by omega
      simp [hi, hne]
    · have habs : (i.natAbs : ℤ) = i := Int.natAbs_of_nonneg (by omega)
      have hindex : i = (n : ℤ) ↔ i.natAbs = n := by omega
      simp [hi, PowerSeries.coeff_monomial, hindex]

/-- The inclusion preserves support, viewed as a subset of the integers. -/
@[simp]
theorem support_laurentPolynomialToSeries (p : R[T;T⁻¹]) :
    (laurentPolynomialToSeries R p).support = (p.coeff.support : Set ℤ) := by
  ext n
  simp

/-- The image of the inclusion is exactly the Laurent series with finite support. -/
theorem mem_range_laurentPolynomialToSeries_iff (f : R⸨X⸩) :
    f ∈ Set.range (laurentPolynomialToSeries R) ↔ f.support.Finite := by
  constructor
  · rintro ⟨p, rfl⟩
    simpa only [support_laurentPolynomialToSeries] using p.coeff.support.finite_toSet
  · intro hf
    refine ⟨AddMonoidAlgebra.ofCoeff (Finsupp.ofSupportFinite f.coeff hf), ?_⟩
    ext n
    rw [coeff_laurentPolynomialToSeries, AddMonoidAlgebra.coeff_ofCoeff]
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
theorem laurentPolynomialToSeries_trunc (a : ℤ) (f : R⸨X⸩) :
    laurentPolynomialToSeries R (laurentPolynomialTrunc a f) = truncLT a f := by
  ext n
  simp [HahnSeries.coeff_truncLT]

variable {K : Type*} [Field K]

/-- The truncation error has valuation at most `exp (-a)`. -/
theorem valuation_sub_laurentPolynomialTrunc_le (a : ℤ) (f : K⸨X⸩) :
    Valued.v (f - laurentPolynomialToSeries K (laurentPolynomialTrunc a f)) ≤
      WithZero.exp (-a) := by
  rw [_root_.LaurentSeries.valuation_le_iff_coeff_lt_eq_zero]
  intro n hn
  simp [hn]

open Filter MonoidWithZeroHom.ValueGroup₀

/-- Finite Laurent truncations converge to the original series in the valuation topology. -/
theorem tendsto_laurentPolynomialTrunc (f : K⸨X⸩) :
    Tendsto (fun a : ℤ ↦ laurentPolynomialToSeries K (laurentPolynomialTrunc a f))
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
theorem denseRange_laurentPolynomialToSeries : DenseRange (laurentPolynomialToSeries K) := by
  intro f
  exact mem_closure_of_tendsto (tendsto_laurentPolynomialTrunc f)
    (Eventually.of_forall fun a ↦ Set.mem_range_self (laurentPolynomialTrunc a f))

end

end TauCeti

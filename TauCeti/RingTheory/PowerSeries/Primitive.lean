/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Log
public import TauCeti.RingTheory.MvPowerSeries.Primitive.Basic


/-!
# The normalised formal primitive of a power series

Over a `ℚ`-algebra `R`, the normalised formal primitive of `f = ∑ aₙ Xⁿ` is

```text
∫ f dX = ∑ aₙ Xⁿ⁺¹ / (n + 1),
```

the unique power series with derivative `f` and constant coefficient zero. It is the univariate
case of `MvPowerSeries.primitive`, in the same way as `PowerSeries.derivative` is the univariate
case of `MvPowerSeries.pderiv`. Termwise integration of power series is the formal step in
building primitives of analytic functions on p-adic discs, and hence in p-adic (Coleman)
integration and the p-adic polylogarithms.

Rational scalars are needed to divide by `n + 1`: over `ZMod p` the monomial `X ^ (p - 1)` is not
a derivative, since the derivative of `X ^ p` vanishes.

## Main definitions

* `PowerSeries.primitive`: the normalised formal primitive, as an `R`-linear map.

## Main results

* `PowerSeries.coeff_primitive`, `PowerSeries.coeff_succ_primitive`,
  `PowerSeries.constantCoeff_primitive`: its coefficients.
* `PowerSeries.derivative_primitive`: `d/dX (∫ f dX) = f`.
* `PowerSeries.primitive_derivative`, `PowerSeries.coeff_primitive_derivative`:
  `∫ (d/dX f) dX = f - C (constantCoeff f)`.
* `PowerSeries.eq_C_add_primitive_iff`: `g = C c + ∫ f dX` iff `d/dX g = f` and
  `constantCoeff g = c`.
* `PowerSeries.primitive_monomial`, `PowerSeries.primitive_X_pow`,
  `PowerSeries.primitive_X`: `∫ Xⁿ dX = Xⁿ⁺¹ / (n + 1)`.
* `PowerSeries.map_primitive`: the primitive commutes with change of coefficients.
* `PowerSeries.primitive_mk_neg_one_pow`: the primitive of `∑ (-1)ⁿ Xⁿ = 1 / (1 + X)` is the
  formal logarithm `log (1 + X)`.

## References

* J. S. Balakrishnan, R. W. Bradshaw, K. S. Kedlaya, *Explicit Coleman integration for
  hyperelliptic curves*, ANTS IX, LNCS 6197 (2010), §3.2, Algorithm 8: termwise integration of
  local expansions in the computation of Coleman integrals.
* A. Besser, *Heidelberg lectures on Coleman integration*, §1.3.2.
-/

public section

namespace PowerSeries

section Semiring

variable {R : Type*} [Semiring R] [Algebra ℚ R]

/-- The **normalised formal primitive** `∑ aₙ Xⁿ ↦ ∑ aₙ Xⁿ⁺¹ / (n + 1)` of a power series over a
`ℚ`-algebra. Its coefficient at `n` is `aₙ₋₁ / n`, which is zero for `n = 0`. -/
noncomputable def primitive : R⟦X⟧ →ₗ[R] R⟦X⟧ :=
  MvPowerSeries.primitive ()

/-- The coefficient of the primitive at `n` is `aₙ₋₁ / n`. -/
theorem coeff_primitive (f : R⟦X⟧) (n : ℕ) :
    coeff n (primitive f) = (n : ℚ)⁻¹ • coeff (n - 1) f := by
  simp [primitive, coeff, MvPowerSeries.coeff_primitive]

/-- The coefficient of the primitive at `0` vanishes. -/
@[simp]
theorem coeff_zero_primitive (f : R⟦X⟧) : coeff 0 (primitive f) = 0 := by
  simp [coeff_primitive]

/-- The primitive has constant coefficient zero. -/
@[simp]
theorem constantCoeff_primitive (f : R⟦X⟧) : constantCoeff (primitive f) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_zero_primitive]

/-- The coefficient of the primitive at `n + 1` is `aₙ / (n + 1)`. -/
@[simp]
theorem coeff_succ_primitive (f : R⟦X⟧) (n : ℕ) :
    coeff (n + 1) (primitive f) = ((n : ℚ) + 1)⁻¹ • coeff n f := by
  simp [coeff_primitive]

/-- The primitive of a monomial: `∫ a Xⁿ dX = a Xⁿ⁺¹ / (n + 1)`. -/
@[simp]
theorem primitive_monomial (n : ℕ) (a : R) :
    primitive (monomial n a) = monomial (n + 1) (((n : ℚ) + 1)⁻¹ • a) := by
  simp [primitive, monomial, ← Finsupp.single_add]

/-- The primitive of a constant: `∫ a dX = a X`. -/
@[simp]
theorem primitive_C (a : R) : primitive (C a) = monomial 1 a := by
  simpa using primitive_monomial 0 a

/-- The primitive of `1` is `X`. -/
@[simp]
theorem primitive_one : primitive (1 : R⟦X⟧) = X := by
  rw [← map_one C, primitive_C, X_eq]

/-- The primitive of a power of `X`: `∫ Xⁿ dX = Xⁿ⁺¹ / (n + 1)`. -/
@[simp]
theorem primitive_X_pow (n : ℕ) :
    primitive (X ^ n : R⟦X⟧) = ((n : ℚ) + 1)⁻¹ • X ^ (n + 1) := by
  rw [X_pow_eq, primitive_monomial, X_pow_eq, ← LinearMap.map_smul_of_tower]

/-- The primitive of `X` is `X ^ 2 / 2`. -/
@[simp]
theorem primitive_X : primitive (X : R⟦X⟧) = (2 : ℚ)⁻¹ • X ^ 2 := by
  simpa [one_add_one_eq_two] using primitive_X_pow (R := R) 1

/-- The primitive commutes with change of coefficients along a ring homomorphism of
`ℚ`-algebras. -/
@[simp]
theorem map_primitive {S : Type*} [Semiring S] [Algebra ℚ S] (φ : R →+* S) (f : R⟦X⟧) :
    map φ (primitive f) = primitive (map φ f) := by
  ext n
  simp only [coeff_map, coeff_primitive, Algebra.smul_def, map_mul, RingHom.map_rat_algebraMap]

/-- The primitive is injective. -/
theorem primitive_injective : Function.Injective (primitive (R := R)) :=
  MvPowerSeries.primitive_injective ()

end Semiring

section CommSemiring

variable {R : Type*} [CommSemiring R] [Algebra ℚ R]

/-- **The primitive is a right inverse of the derivative**: `d/dX (∫ f dX) = f`. -/
@[simp]
theorem derivative_primitive (f : R⟦X⟧) : d⁄dX (primitive f) = f :=
  MvPowerSeries.pderiv_primitive () f

/-- **The primitive of a derivative**: `∫ (d/dX f) dX` is `f` with its constant term removed. -/
theorem coeff_primitive_derivative (f : R⟦X⟧) (n : ℕ) :
    coeff n (primitive (d⁄dX f)) = if n = 0 then 0 else coeff n f :=
  (MvPowerSeries.coeff_primitive_pderiv () f (Finsupp.single () n)).trans (by simp)

/-- **Characterisation of the primitive**: `g = C c + ∫ f dX` iff `d/dX g = f` and
`constantCoeff g = c`. -/
theorem eq_C_add_primitive_iff {f g : R⟦X⟧} {c : R} :
    g = C c + primitive f ↔ d⁄dX g = f ∧ constantCoeff g = c := by
  constructor
  · rintro rfl
    simp
  · rintro ⟨rfl, rfl⟩
    ext n
    rcases n with _ | n
    · simp
    · simp [coeff_primitive_derivative, -coeff_succ_primitive]

/-- **Characterisation of the primitive**: `g = ∫ f dX` iff `d/dX g = f` and `g` has constant
coefficient zero. -/
theorem eq_primitive_iff {f g : R⟦X⟧} :
    g = primitive f ↔ d⁄dX g = f ∧ constantCoeff g = 0 := by
  simpa using eq_C_add_primitive_iff (f := f) (g := g) (c := 0)

end CommSemiring

section CommRing

variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- **The primitive of a derivative**: `∫ (d/dX f) dX = f - C (constantCoeff f)`. -/
@[simp]
theorem primitive_derivative (f : R⟦X⟧) : primitive (d⁄dX f) = f - C (constantCoeff f) := by
  rw [eq_sub_iff_add_eq, add_comm, eq_comm, eq_C_add_primitive_iff]
  exact ⟨rfl, rfl⟩

/-- The primitive of the geometric series `∑ (-1)ⁿ Xⁿ = 1 / (1 + X)` is the formal logarithm
`log (1 + X) = ∑ (-1)ⁿ⁺¹ Xⁿ / n`. -/
theorem primitive_mk_neg_one_pow : primitive (mk fun n ↦ (-1 : R) ^ n) = log R := by
  rw [← derivative_log, primitive_derivative, constantCoeff_log, map_zero, sub_zero]

end CommRing

end PowerSeries

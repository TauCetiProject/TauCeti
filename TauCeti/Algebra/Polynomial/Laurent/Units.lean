/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Degree.Units
public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.Algebra.Polynomial.RingDivision
public import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.RingTheory.RootsOfUnity.Basic
public import TauCeti.Algebra.MonoidAlgebra.Grading
public import TauCeti.Algebra.Polynomial.Laurent.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Units of Laurent polynomials

A constant Laurent polynomial `C r` is a unit exactly when its coefficient `r` is a unit. The map
`C` is Mathlib's `AddMonoidAlgebra.singleZeroRingHom`, which is a local ring homomorphism. This is
the Laurent counterpart of Mathlib's `Polynomial.isUnit_C`. In particular, a natural number `n` is a
unit in `R[T;T⁻¹]` exactly when it is a unit in `R`, and over a division semiring of exponential
characteristic `p`, every nonzero natural number coprime to `p` is a unit in `K[T;T⁻¹]`.

Over a commutative ring without zero divisors, every unit of `R[T;T⁻¹]` is a unit monomial
`C r * T n`. This is the Laurent counterpart of Mathlib's `Polynomial.isUnit_iff`, where only
the constants survive. Over `ℤ` it says that the units of `ℤ[T;T⁻¹]` are exactly `±Tⁿ`, which is
the form taken by a unimodular determinant over the Laurent ring.

Evaluating at any unit `u` of a coefficient algebra sends the generic unit `genericUnit R` to `u`
(`TauCeti.laurentEval_genericUnit`), and evaluating at any `u ∈ Rˣ` induces a surjective
homomorphism `μ_n(R[T;T⁻¹]) → μ_n(R)` on roots of unity, split by the constant inclusion `C`
(`TauCeti.restrictRootsOfUnity_laurentEval_surjective`).

## Main results

* `LaurentPolynomial.isUnit_C`: `C r` is a unit if and only if `r` is.
* `LaurentPolynomial.isUnit_natCast`: a natural number is a unit in `R[T;T⁻¹]` if and only if it is
  a unit in `R`.
* `LaurentPolynomial.isUnit_natCast_of_coprime`: over a division semiring of exponential
  characteristic `p`, a nonzero natural number coprime to `p` is a unit in `K[T;T⁻¹]`.
* `LaurentPolynomial.isUnit_iff`: over a commutative ring without zero divisors, the units of
  `R[T;T⁻¹]` are the monomials `C r * T n` with `r` a unit.
* `LaurentPolynomial.isUnit_iff_exists_eq_T_or_neg_T`: the units of `ℤ[T;T⁻¹]` are the `±Tⁿ`.
* `TauCeti.laurentEval_genericUnit`: `laurentEval u` maps `LaurentPolynomial.genericUnit R` to `u`.
* `TauCeti.restrictRootsOfUnity_laurentEval_surjective`: evaluation at any unit `u ∈ Rˣ` induces a
  surjective map `μ_n(R[T;T⁻¹]) → μ_n(R)` on roots of unity.
* `TauCeti.shiftClassGroupLaurentPolynomialEquiv`: for `R[T;T⁻¹]` graded with `T` of degree `w`,
  the shift class group `TauCeti.ShiftClassGroup` of homogeneous unit degrees is `ZMod |w|`.
-/

public section

namespace LaurentPolynomial

variable {R : Type*}

section Semiring

variable [Semiring R]

/-- A constant Laurent polynomial is a unit exactly when its coefficient is. -/
@[simp]
theorem isUnit_C {r : R} : IsUnit (C r : R[T;T⁻¹]) ↔ IsUnit r :=
  isUnit_map_iff (AddMonoidAlgebra.singleZeroRingHom (R := R) (M := ℤ)) r

/-- A natural number is a unit in `R[T;T⁻¹]` exactly when it is a unit in `R`. -/
@[simp]
theorem isUnit_natCast {n : ℕ} : IsUnit (n : R[T;T⁻¹]) ↔ IsUnit (n : R) := by
  rw [← map_natCast (C : R →+* R[T;T⁻¹]), isUnit_C]

end Semiring

section DivisionSemiring

variable {K : Type*} [DivisionSemiring K]

/-- Over a division semiring `K` of exponential characteristic `p`, every nonzero natural number
coprime to `p` is invertible in `K[T;T⁻¹]`. -/
theorem isUnit_natCast_of_coprime {p : ℕ} [ExpChar K p] {m : ℕ} (hm₀ : m ≠ 0) (hm : m.Coprime p) :
    IsUnit (m : K[T;T⁻¹]) := by
  rw [isUnit_natCast, isUnit_iff_ne_zero]
  obtain _ | ⟨hq⟩ := ‹ExpChar K p›
  · exact Nat.cast_ne_zero.mpr hm₀
  · rw [ne_eq, CharP.cast_eq_zero_iff K _ m]
    exact hq.coprime_iff_not_dvd.mp hm.symm

end DivisionSemiring

section CommRing

variable [CommRing R] [NoZeroDivisors R]

/-- **Units of a Laurent polynomial ring.** Over a commutative ring without zero divisors, a
Laurent polynomial is a unit exactly when it is a unit monomial `C r * T n`. -/
theorem isUnit_iff {f : R[T;T⁻¹]} : IsUnit f ↔ ∃ r : R, IsUnit r ∧ ∃ n : ℤ, C r * T n = f := by
  refine ⟨fun hf => ?_, fun ⟨r, hr, n, hf⟩ => hf ▸ (isUnit_C.2 hr).mul (isUnit_T n)⟩
  nontriviality R
  have : IsDomain R := NoZeroDivisors.to_isDomain R
  obtain ⟨g, hfg⟩ := hf.exists_right_inv
  obtain ⟨m, f', hf'⟩ := f.exists_T_pow
  obtain ⟨n, g', hg'⟩ := g.exists_T_pow
  -- Clearing denominators turns `f * g = 1` into `f' * g' = X ^ (m + n)` in `R[X]`.
  have hX : f' * g' = Polynomial.X ^ (m + n) := by
    apply Polynomial.toLaurent_injective
    simp only [map_mul, hf', hg', Polynomial.toLaurent_X_pow, Nat.cast_add, T_add]
    linear_combination (T m * T n) * hfg
  -- As `X` is prime in `R[X]`, `f'` is a power of `X` times a unit, and that unit is constant.
  obtain ⟨i, -, u, hu⟩ := (dvd_prime_pow Polynomial.prime_X _).1 (Dvd.intro _ hX)
  obtain ⟨r, hr, hru⟩ := Polynomial.isUnit_iff.1 (u⁻¹).isUnit
  refine ⟨r, hr, i - m, ?_⟩
  have hf'_eq : f' = Polynomial.C r * Polynomial.X ^ i := by
    rw [hru, ← hu, mul_comm, Units.mul_inv_cancel_right]
  have hfT : f * T m = C r * T i := by
    rw [← hf', hf'_eq, map_mul, Polynomial.toLaurent_C, Polynomial.toLaurent_X_pow]
  calc C r * T (i - m) = f * T m * T (-m) := by rw [hfT, mul_T_assoc, sub_eq_add_neg]
    _ = f := by rw [mul_T_assoc, add_neg_cancel, T_zero, mul_one]

end CommRing

/-- **Units of `ℤ[T;T⁻¹]`.** An integral Laurent polynomial is a unit exactly when it is `Tⁿ` or
`-Tⁿ` for some `n : ℤ`. -/
theorem isUnit_iff_exists_eq_T_or_neg_T {f : ℤ[T;T⁻¹]} :
    IsUnit f ↔ ∃ n : ℤ, f = T n ∨ f = -T n := by
  rw [isUnit_iff]
  constructor
  · rintro ⟨r, hr, n, rfl⟩
    rcases Int.isUnit_iff.1 hr with rfl | rfl
    · exact ⟨n, .inl (by simp)⟩
    · exact ⟨n, .inr (by simp)⟩
  · rintro ⟨n, rfl | rfl⟩
    · exact ⟨1, isUnit_one, n, by simp⟩
    · exact ⟨-1, isUnit_one.neg, n, by simp⟩

end LaurentPolynomial

namespace TauCeti

open AddMonoidAlgebra

open scoped LaurentPolynomial

/-- Evaluating a Laurent polynomial at a unit `u` sends the generic unit `T` to `u`.

Not tagged `@[simp]`: `LaurentPolynomial.genericUnit_val` simplifies `(genericUnit R : R[T;T⁻¹])`
to `T 1`, after which `laurentEval_T` and `zpow_one` reduce the left-hand side to `u`. -/
theorem laurentEval_genericUnit {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    (u : Aˣ) :
    laurentEval (R := R) u (LaurentPolynomial.genericUnit R : R[T;T⁻¹]) = u := by
  rw [LaurentPolynomial.genericUnit_val, laurentEval_T_one]

/-- Evaluation at any unit `u ∈ Rˣ` induces a surjective homomorphism `μ_n(R[T;T⁻¹]) → μ_n(R)` on
roots of unity, split by the constant inclusion `LaurentPolynomial.C : R →+* R[T;T⁻¹]`. -/
theorem restrictRootsOfUnity_laurentEval_surjective {R : Type*} [CommSemiring R]
    (u : Rˣ) (n : ℕ) :
    Function.Surjective (restrictRootsOfUnity (laurentEval (R := R) u) n) := fun ζ ↦
  ⟨restrictRootsOfUnity (LaurentPolynomial.C : R →+* R[T;T⁻¹]) n ζ, by
    ext
    simp [restrictRootsOfUnity]⟩

/-- For the Laurent ring `R[T;T⁻¹]` over a nontrivial commutative semiring, graded with `T` of
degree `w`, the degrees of the homogeneous units are the multiples of `w` (by
`homogeneousUnitDegrees_gradeBy`), so the shift class group is `ZMod |w|`. This is the graded ring
of `𝔾_m` acting on itself by `s • x = s ^ w * x`. -/
noncomputable def shiftClassGroupLaurentPolynomialEquiv (R : Type*) [CommSemiring R]
    [Nontrivial R] (w : ℤ) :
    ShiftClassGroup (gradeBy R (zmultiplesHom ℤ w) : ℤ → Submodule R R[T;T⁻¹]) ≃+
      ZMod w.natAbs :=
  (QuotientAddGroup.quotientAddEquivOfEq (by simp)).trans
    (Int.quotientZMultiplesEquivZMod w)

/-- The identification of the shift classes of `R[T;T⁻¹]` with `ZMod |w|` sends the class of a
shift `d` to `d mod |w|`. -/
@[simp]
theorem shiftClassGroupLaurentPolynomialEquiv_mk (R : Type*) [CommSemiring R] [Nontrivial R]
    (w d : ℤ) : shiftClassGroupLaurentPolynomialEquiv R w d = d := by
  -- Both quotient equivalences are induced by maps on representatives, and the last one is the
  -- cast `ℤ → ZMod |w|`; Mathlib states no lemma evaluating them on a class.
  rfl

end TauCeti

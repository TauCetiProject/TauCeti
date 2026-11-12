/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Minpoly.Field
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import TauCeti.NumberTheory.NumberField.ComplexConjugation.MaximalRealSubfield

/-!
# Real elements of an imaginary quadratic field

Let `K` be an imaginary quadratic field: a quadratic extension of `ℚ` with no real embedding. Then
`K / ℚ` is a CM extension, so its maximal real subfield is `ℚ`
(`NumberField.CMExtension.maximalRealSubfield_eq_fieldRange ℚ K`), and under any complex embedding
`φ : K →+* ℂ`, `φ(K) ∩ ℝ = φ(ℚ)`: an element of `K` with a real image is rational
(`NumberField.CMExtension.mem_range_algebraMap_iff_star_eq ℚ`). This file adds the integral
version: an algebraic integer of `K` with a real image is a rational integer.

The same holds one level up. If `K ⊆ ℂ` and `x` is a real algebraic number, the minimal polynomial
of `x` over `K` is the minimal polynomial of `x` over `ℚ`
(`NumberField.CMExtension.minpoly_eq_map_minpoly_of_star_eq` with `F = ℚ`); if `x` is moreover an
algebraic integer, it is the minimal polynomial of `x` over `ℤ`. In Heegner's and Stark's proof of
the class number one theorem, this is the step that turns the minimal polynomial over an imaginary
quadratic field `K` of class number one of a real algebraic integer generating a cubic extension of
`K` into a monic cubic `X³ + a X² + b X + c` with `a, b, c ∈ ℤ`, the input of
`TauCeti.tschirnhausPolynomial_X_pow_four_eq_iff`.

## Main results

* `NumberField.RingOfIntegers.mem_range_algebraMap_iff_star_eq_of_isTotallyComplex`: an algebraic
  integer of `K` is a rational integer exactly when its image under a given complex embedding is
  real.
* `NumberField.minpoly_eq_map_minpoly_int_of_star_eq_of_isTotallyComplex`: over an imaginary
  quadratic subfield of `ℂ`, the minimal polynomial of a real algebraic integer is its minimal
  polynomial over `ℤ`.

## References

* H. M. Stark, *On the “gap” in a theorem of Heegner*, J. Number Theory 1 (1969), 16–27.
* D. H. Shin, *Generation of class fields by Siegel–Ramachandra invariants*, §5.
-/

public section

open Polynomial

namespace NumberField

variable {K : Type*} [Field K] [NumberField K] [Algebra.IsQuadraticExtension ℚ K]
  [IsTotallyComplex K]

/-- **Real algebraic integers of an imaginary quadratic field are rational integers.** Under any
complex embedding, an algebraic integer of an imaginary quadratic field has a real image exactly
when it is a rational integer. -/
theorem RingOfIntegers.mem_range_algebraMap_iff_star_eq_of_isTotallyComplex (φ : K →+* ℂ)
    (x : 𝓞 K) : x ∈ Set.range (algebraMap ℤ (𝓞 K)) ↔ star (φ x) = φ x := by
  rw [← CMExtension.mem_range_algebraMap_iff_star_eq ℚ,
    IsIntegralClosure.mem_range_algebraMap ℤ (B := ℚ) x.isIntegral_coe]
  exact ⟨fun ⟨n, hn⟩ ↦ ⟨n, by simp [← hn]⟩,
    fun ⟨n, hn⟩ ↦ ⟨n, RingOfIntegers.ext (by simpa using hn)⟩⟩

/-- **Minimal polynomials of real algebraic integers over an imaginary quadratic field.** For an
imaginary quadratic field `K ⊆ ℂ` and a real algebraic integer `x`, the minimal polynomial of `x`
over `K` has rational integer coefficients: it is the minimal polynomial of `x` over `ℤ`. -/
theorem minpoly_eq_map_minpoly_int_of_star_eq_of_isTotallyComplex [Algebra K ℂ] {x : ℂ}
    (hx : star x = x) (hint : IsIntegral ℤ x) :
    minpoly K x = (minpoly ℤ x).map (algebraMap ℤ K) := by
  rw [CMExtension.minpoly_eq_map_minpoly_of_star_eq (F := ℚ) hx,
    minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hint, Polynomial.map_map,
    ← IsScalarTower.algebraMap_eq]

end NumberField

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
import TauCeti.FieldTheory.Galois.Abelian.Basic
import TauCeti.NumberTheory.NumberField.ComplexConjugation.MaximalRealSubfield

/-!
# Real elements of an imaginary quadratic field

Let `K` be an imaginary quadratic field: a quadratic extension of `ℚ` with no real embedding. It is
a CM field (its Galois group over `ℚ` is abelian), and its maximal real subfield is a proper
subfield of a field of degree two over `ℚ`, hence `ℚ` itself. So under any complex embedding
`φ : K →+* ℂ`, `φ(K) ∩ ℝ = φ(ℚ)`: an element of `K` with a real image is rational, and an algebraic
integer of `K` with a real image is a rational integer.

The same holds one level up. If `K ⊆ ℂ` and `x` is a real algebraic number, the minimal polynomial
of `x` over `K` is the minimal polynomial of `x` over `ℚ`; if `x` is moreover an algebraic integer,
it is the minimal polynomial of `x` over `ℤ`. In Heegner's and Stark's proof of the class number
one theorem, this is the step that turns the minimal polynomial over an imaginary quadratic field
`K` of class number one of a real algebraic integer generating a cubic extension of `K` into a
monic cubic `X³ + a X² + b X + c` with `a, b, c ∈ ℤ`, the input of
`TauCeti.tschirnhausPolynomial_X_pow_four_eq_iff`.

## Main results

* `NumberField.maximalRealSubfield_eq_fieldRange`: the maximal real subfield of an imaginary
  quadratic field is `ℚ`.
* `NumberField.mem_range_algebraMap_iff_star_eq`: an element of `K` is rational exactly when its
  image under a given complex embedding is real.
* `NumberField.RingOfIntegers.mem_range_algebraMap_iff_star_eq`: an algebraic integer of `K` is a
  rational integer exactly when its image under a given complex embedding is real.
* `NumberField.minpoly_eq_map_minpoly_rat_of_star_eq`,
  `NumberField.minpoly_eq_map_minpoly_int_of_star_eq`: over an imaginary quadratic subfield of `ℂ`,
  the minimal polynomial of a real algebraic number is its minimal polynomial over `ℚ`, and that
  of a real algebraic integer is its minimal polynomial over `ℤ`.

## References

* H. M. Stark, *On the “gap” in a theorem of Heegner*, J. Number Theory 1 (1969), 16–27.
* D. H. Shin, *Generation of class fields by Siegel–Ramachandra invariants*, §5.
-/

public section

open Polynomial

namespace NumberField

variable {K : Type*} [Field K] [NumberField K] [Algebra.IsQuadraticExtension ℚ K]
  [IsTotallyComplex K]

variable (K) in
/-- **The maximal real subfield of an imaginary quadratic field is `ℚ`.** It is a subfield over
which `K` is quadratic, and `K` is already quadratic over `ℚ`. -/
@[simp]
theorem maximalRealSubfield_eq_fieldRange :
    maximalRealSubfield K = (algebraMap ℚ K).fieldRange := by
  have h := Module.finrank_mul_finrank ℚ (maximalRealSubfield K) K
  rw [Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield K) K,
    Algebra.IsQuadraticExtension.finrank_eq_two ℚ K] at h
  have h1 : Module.finrank ℚ (maximalRealSubfield K) = 1 := by omega
  refine le_antisymm (fun x hx ↦ ?_) ?_
  · obtain ⟨q, hq⟩ := (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp h1).2 ⟨x, hx⟩
    exact ⟨q, congrArg Subtype.val hq⟩
  · rintro _ ⟨q, rfl⟩
    simp

/-- **Real elements of an imaginary quadratic field are rational.** Under any complex embedding,
an element of an imaginary quadratic field has a real image exactly when it is rational. -/
theorem mem_range_algebraMap_iff_star_eq (φ : K →+* ℂ) (x : K) :
    x ∈ Set.range (algebraMap ℚ K) ↔ star (φ x) = φ x := by
  rw [← IsCMField.mem_maximalRealSubfield_iff_star_eq, maximalRealSubfield_eq_fieldRange,
    RingHom.mem_fieldRange, Set.mem_range]

/-- **Real algebraic integers of an imaginary quadratic field are rational integers.** Under any
complex embedding, an algebraic integer of an imaginary quadratic field has a real image exactly
when it is a rational integer. -/
theorem RingOfIntegers.mem_range_algebraMap_iff_star_eq (φ : K →+* ℂ) (x : 𝓞 K) :
    x ∈ Set.range (algebraMap ℤ (𝓞 K)) ↔ star (φ x) = φ x := by
  rw [← NumberField.mem_range_algebraMap_iff_star_eq]
  refine ⟨fun ⟨n, hn⟩ ↦ ⟨n, by simp [← hn]⟩, fun ⟨q, hq⟩ ↦ ?_⟩
  -- A rational number that is an algebraic integer is an integer.
  have hq' : IsIntegral ℤ q := by
    rw [← isIntegral_algebraMap_iff (B := K), hq]
    exact x.isIntegral_coe
  obtain ⟨n, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.mp hq'
  exact ⟨n, RingOfIntegers.ext (by simp [← hq])⟩

/-- **Minimal polynomials of real numbers over an imaginary quadratic field.** For an imaginary
quadratic field `K ⊆ ℂ` and a real complex number `x`, the minimal polynomial of `x` over `K` is
its minimal polynomial over `ℚ`. -/
theorem minpoly_eq_map_minpoly_rat_of_star_eq [Algebra K ℂ] {x : ℂ} (hx : star x = x) :
    minpoly K x = (minpoly ℚ x).map (algebraMap ℚ K) := by
  by_cases hint : IsIntegral ℚ x
  · refine (minpoly.map_algebraMap hint ((lifts_iff_coeff_lifts _).mpr fun n ↦ ?_)).symm
    have := IsCMField.coeff_minpoly_mem_maximalRealSubfield (K := K) hx n
    rwa [maximalRealSubfield_eq_fieldRange, RingHom.mem_fieldRange, ← Set.mem_range] at this
  · rw [minpoly.eq_zero hint, Polynomial.map_zero,
      minpoly.eq_zero fun h ↦ hint (isIntegral_trans (R := ℚ) x h)]

/-- **Minimal polynomials of real algebraic integers over an imaginary quadratic field.** For an
imaginary quadratic field `K ⊆ ℂ` and a real algebraic integer `x`, the minimal polynomial of `x`
over `K` has rational integer coefficients: it is the minimal polynomial of `x` over `ℤ`. -/
theorem minpoly_eq_map_minpoly_int_of_star_eq [Algebra K ℂ] {x : ℂ} (hx : star x = x)
    (hint : IsIntegral ℤ x) : minpoly K x = (minpoly ℤ x).map (algebraMap ℤ K) := by
  rw [minpoly_eq_map_minpoly_rat_of_star_eq hx,
    minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hint, Polynomial.map_map,
    ← IsScalarTower.algebraMap_eq]

end NumberField

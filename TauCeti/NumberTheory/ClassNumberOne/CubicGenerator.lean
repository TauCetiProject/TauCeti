/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassNumberOne.HeegnerQuartic
public import TauCeti.NumberTheory.ClassNumberOne.SingularValue
public import TauCeti.NumberTheory.ModularForms.SiegelFunction.GammaTwo
public import TauCeti.NumberTheory.NumberField.Quadratic.MaximalRealSubfield
import TauCeti.Algebra.Polynomial.Cubic.Basic

/-!
# Real cubic generators over an imaginary quadratic field

In Heegner's and Stark's proof of the class number one theorem, for an imaginary quadratic field
`K ⊆ ℂ` of class number one in which `2` is inert, the CM theory of the level-two Siegel functions
produces a real algebraic integer `x` of degree `3` over `K` such that the conjugates of `x⁴` over
`K` are the roots of `X³ - γ₂(τ_D) X - 16`, where `γ₂` is the cube root of `j` and `τ_D` the CM
point of `K`. This file turns that data into the integer equation solved in
`TauCeti.NumberTheory.ClassNumberOne.HeegnerQuartic`, and so into the six possible values
`γ₂(τ_D) ∈ {0, -32, -96, -960, -5280, -640320}`.

The comparison has two steps. Since `x` is real and `K` is imaginary quadratic, the minimal
polynomial of `x` over `K` is the image of its minimal polynomial over `ℤ`, a monic integer cubic
`X³ + a X² + b X + c` (`NumberField.minpoly_eq_map_minpoly_int_of_star_eq_of_isTotallyComplex`).
The Tschirnhaus transform by `X⁴` of this cubic, whose roots are the fourth powers of the
conjugates of `x`, is then the minimal polynomial of `x⁴` over `K` as soon as `x⁴` also has degree
`3` (`Polynomial.minpoly_aeval_eq_tschirnhausPolynomial_iff`). Neither step uses the class number.

Finally, `j = γ₂³` and the singular-value enclosure of
`TauCeti.NumberTheory.ClassNumberOne.SingularValue` recover the discriminant from `γ₂(τ_D)`.

## Main results

* `TauCeti.mem_image_intCast_of_map_tschirnhausPolynomial_minpoly_X_pow_four_eq`: if the
  fourth-power cubic of the minimal polynomial over `K` of a real algebraic integer `x` is
  `X³ - γ X - 16` in `ℂ[X]`, then `γ ∈ {0, -32, -96, -960, -5280, -640320}`.
* `TauCeti.mem_image_intCast_of_map_minpoly_pow_four_eq`: the same conclusion when `x` has degree
  `3` over `K` and the minimal polynomial of `x⁴` over `K` is `X³ - γ X - 16` in `ℂ[X]`.
* `TauCeti.ModularForm.mem_of_map_minpoly_pow_four_eq_gammaTwo`: if moreover `γ = γ₂(τ)` with
  `Im τ = √n / 2` and `n ≥ 3`, then `n ∈ {3, 11, 19, 43, 67, 163}`.

## References

* H. M. Stark, *On the “gap” in a theorem of Heegner*, J. Number Theory 1 (1969), 16–27.
* D. H. Shin, *Generation of class fields by Siegel–Ramachandra invariants*, §5.
* D. A. Cox, *Primes of the Form x² + ny²*, §12.
-/

public section

open Polynomial

namespace TauCeti

variable {K : Type*} [Field K] [NumberField K] [Algebra.IsQuadraticExtension ℚ K]
  [NumberField.IsTotallyComplex K] [Algebra K ℂ]

/-- **The six values of `γ` from a real algebraic integer.** Let `K ⊆ ℂ` be an imaginary
quadratic field and `x` a real algebraic integer. If the Tschirnhaus transform by `X⁴` of the
minimal polynomial of `x` over `K`, whose roots are the fourth powers of the conjugates of `x`
over `K`, is `X³ - γ X - 16` in `ℂ[X]`, then `γ` is one of `0, -32, -96, -960, -5280, -640320`. -/
theorem mem_image_intCast_of_map_tschirnhausPolynomial_minpoly_X_pow_four_eq {x γ : ℂ}
    (hx : star x = x) (hint : IsIntegral ℤ x)
    (h : (tschirnhausPolynomial (minpoly K x) (X ^ 4)).map (algebraMap K ℂ) =
      X ^ 3 - C γ * X - 16) :
    γ ∈ (Int.cast '' {0, -32, -96, -960, -5280, -640320} : Set ℂ) := by
  have hp := minpoly.monic hint
  have hφ : (algebraMap K ℂ).comp (algebraMap ℤ K) = Int.castRingHom ℂ := RingHom.ext_int _ _
  rw [NumberField.minpoly_eq_map_minpoly_int_of_star_eq_of_isTotallyComplex hx hint,
    map_tschirnhausPolynomial (hp.map _), Polynomial.map_map, hφ, Polynomial.map_pow,
    map_X] at h
  have h3 : (minpoly ℤ x).natDegree = 3 := by
    have hd := congrArg natDegree h
    rw [natDegree_tschirnhausPolynomial (hp.map _), hp.natDegree_map] at hd
    rw [hd]
    compute_degree!
  have hmap : (minpoly ℤ x).map (Int.castRingHom ℂ) = X ^ 3 +
      C (((minpoly ℤ x).coeff 2 : ℤ) : ℂ) * X ^ 2 + C (((minpoly ℤ x).coeff 1 : ℤ) : ℂ) * X +
        C (((minpoly ℤ x).coeff 0 : ℤ) : ℂ) := by
    conv_lhs => rw [hp.eq_X_pow_three_add h3]
    simp
  rw [hmap] at h
  exact mem_image_intCast_of_tschirnhausPolynomial_X_pow_four_eq h

/-- **The six values of `γ` from a real cubic generator.** Let `K ⊆ ℂ` be an imaginary quadratic
field and `x` a real algebraic integer of degree `3` over `K`. If the minimal polynomial of `x⁴`
over `K` is `X³ - γ X - 16` in `ℂ[X]`, then `γ` is one of `0, -32, -96, -960, -5280, -640320`. -/
theorem mem_image_intCast_of_map_minpoly_pow_four_eq {x γ : ℂ} (hx : star x = x)
    (hint : IsIntegral ℤ x) (hdeg : (minpoly K x).natDegree = 3)
    (h : (minpoly K (x ^ 4)).map (algebraMap K ℂ) = X ^ 3 - C γ * X - 16) :
    γ ∈ (Int.cast '' {0, -32, -96, -960, -5280, -640320} : Set ℂ) := by
  have hpow : x ^ 4 = aeval x (X ^ 4 : K[X]) := by simp
  have h4 : (minpoly K (x ^ 4)).natDegree = 3 := by
    have hd := congrArg natDegree h
    rw [natDegree_map] at hd
    rw [hd]
    compute_degree!
  rw [hpow, (minpoly_aeval_eq_tschirnhausPolynomial_iff hint.tower_top _).2
    (by rw [← hpow, h4, hdeg])] at h
  exact mem_image_intCast_of_map_tschirnhausPolynomial_minpoly_X_pow_four_eq hx hint h

/-- **Recovering the discriminant from a real cubic generator.** Let `K ⊆ ℂ` be an imaginary
quadratic field, `x` a real algebraic integer of degree `3` over `K`, and `τ` a point of the upper
half-plane with `Im τ = √n / 2` for some `n ≥ 3`. If the minimal polynomial of `x⁴` over `K` is
`X³ - γ₂(τ) X - 16` in `ℂ[X]`, then `n` is one of `3, 11, 19, 43, 67, 163`. -/
theorem ModularForm.mem_of_map_minpoly_pow_four_eq_gammaTwo {τ : UpperHalfPlane} {n : ℕ}
    (hn : 3 ≤ n) (hτ : τ.im = √n / 2) {x : ℂ} (hx : star x = x) (hint : IsIntegral ℤ x)
    (hdeg : (minpoly K x).natDegree = 3)
    (h : (minpoly K (x ^ 4)).map (algebraMap K ℂ) = X ^ 3 - C (ModularForm.gammaTwo τ) * X - 16) :
    n ∈ ({3, 11, 19, 43, 67, 163} : Finset ℕ) := by
  obtain ⟨v, hv, hγ⟩ := mem_image_intCast_of_map_minpoly_pow_four_eq hx hint hdeg h
  refine ModularForm.mem_of_j_eq_intCast_pow_three hn hτ (v := v) (by simpa using hv) ?_
  rw [← ModularForm.gammaTwo_pow_three, ← hγ]

end TauCeti

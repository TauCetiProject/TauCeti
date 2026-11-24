/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.FieldTheory.Minpoly.Field

/-!
# Evaluating cyclotomic polynomials at primitive roots

A primitive `e`-th root of unity in a domain is a root of the cyclotomic polynomial `Φ_e` over any
ring, once its coefficients are mapped into the domain along a ring homomorphism. If a rational
polynomial vanishes at one primitive `h`-th root of unity in a `ℚ`-algebra domain, it vanishes at
every primitive `h`-th root of unity in any `ℚ`-algebra domain. Consequently, two polynomials over
`ℚ[X]` whose coefficients evaluate identically at one primitive `h`-th root of unity also become
equal at any primitive `h`-th root of unity in any `ℚ`-algebra domain.

## Main results

* `IsPrimitiveRoot.eval₂_cyclotomic`: a primitive `e`-th root of unity is a root of `Φ_e` mapped
  along any ring homomorphism.
* `IsPrimitiveRoot.aeval_eq_zero_of_aeval_eq_zero`: if `p : ℚ[X]` vanishes at a primitive `h`-th
  root of unity `ζ₀`, it vanishes at any primitive `h`-th root of unity `ζ`.
* `IsPrimitiveRoot.isRoot_map_of_isRoot_map`: root transfer across primitive `h`-th roots of unity
  for rational polynomials.
* `Polynomial.map_aeval_map_C`: mapping `p.map C` by coefficientwise `aeval r` yields
  `p.map (algebraMap R A)`.
* `Polynomial.map_aeval_eq_of_isPrimitiveRoot`: equality of `(ℚ[X])[X]` polynomials after
  coefficientwise evaluation at one primitive `h`-th root transfers to any primitive `h`-th root.
-/

public section

open Polynomial

namespace IsPrimitiveRoot

/-- A primitive `e`-th root of unity `r` in a domain `R` is a root of the cyclotomic polynomial
`Φ_e` over any ring, mapped to `R` along any ring homomorphism `f`. Mathlib's
`IsPrimitiveRoot.isRoot_cyclotomic` is the case of `Φ_e` taken over `R` itself. -/
theorem eval₂_cyclotomic {e : ℕ} {S R : Type*} [Ring S] [CommRing R] [IsDomain R] [NeZero e]
    (f : S →+* R) {r : R} (hr : IsPrimitiveRoot r e) : (cyclotomic e S).eval₂ f r = 0 := by
  rw [← eval_map, map_cyclotomic]
  exact hr.isRoot_cyclotomic (NeZero.pos e)

/-- **Rational cyclotomic evaluation transfer.** If a polynomial over `ℚ` evaluates to zero at one
primitive `h`-th root of unity in a `ℚ`-algebra domain, then it evaluates to zero at any primitive
`h`-th root of unity in any `ℚ`-algebra domain. -/
theorem aeval_eq_zero_of_aeval_eq_zero {K A : Type*} [CommRing K] [IsDomain K] [Algebra ℚ K]
    [CommRing A] [IsDomain A] [Algebra ℚ A] {h : ℕ} (hh : 0 < h) {ζ₀ : K}
    (hζ₀ : IsPrimitiveRoot ζ₀ h) {ζ : A} (hζ : IsPrimitiveRoot ζ h) {p : ℚ[X]}
    (hp : aeval ζ₀ p = 0) : aeval ζ p = 0 := by
  have : NeZero h := ⟨hh.ne'⟩
  have : NeZero (h : ℚ) := ⟨Nat.cast_ne_zero.mpr hh.ne'⟩
  have hdvd : cyclotomic h ℚ ∣ p := by
    rw [hζ₀.minpoly_eq_cyclotomic_of_irreducible (cyclotomic.irreducible_rat hh)]
    exact minpoly.dvd ℚ ζ₀ hp
  obtain ⟨q, rfl⟩ := hdvd
  rw [map_mul, aeval_def, hζ.eval₂_cyclotomic (algebraMap ℚ A), zero_mul]

/-- **Root transfer for rational polynomials.** If a primitive `h`-th root of unity `ζ₀` in a
`ℚ`-algebra domain is a root of a rational polynomial `p`, then any primitive `h`-th root of unity
`ζ` in any `ℚ`-algebra domain is also a root of `p`. -/
theorem isRoot_map_of_isRoot_map {K A : Type*} [CommRing K] [IsDomain K] [Algebra ℚ K]
    [CommRing A] [IsDomain A] [Algebra ℚ A] {h : ℕ} (hh : 0 < h) {ζ₀ : K}
    (hζ₀ : IsPrimitiveRoot ζ₀ h) {ζ : A} (hζ : IsPrimitiveRoot ζ h) {p : ℚ[X]}
    (hp : (p.map (algebraMap ℚ K)).IsRoot ζ₀) : (p.map (algebraMap ℚ A)).IsRoot ζ := by
  rw [IsRoot.def, ← eval₂_eq_eval_map, ← aeval_def] at hp ⊢
  exact hζ₀.aeval_eq_zero_of_aeval_eq_zero hh hζ hp

end IsPrimitiveRoot

namespace Polynomial

/-- Coefficientwise evaluation of `p.map C` at `r` recovers `p.map (algebraMap R A)`. -/
@[simp]
theorem map_aeval_map_C {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
    (p : R[X]) (r : A) :
    (p.map Polynomial.C).map (↑(aeval r : R[X] →ₐ[R] A) : R[X] →+* A) =
      p.map (algebraMap R A) := by
  rw [Polynomial.map_map]
  congr 1
  ext x
  simp

/-- **Cyclotomic transfer for `(ℚ[X])[X]` polynomials.** If two polynomials over `ℚ[X]` have equal
images under coefficientwise evaluation at a primitive `h`-th root of unity `ζ₀` in a `ℚ`-algebra
domain, then they have equal images under coefficientwise evaluation at any primitive `h`-th root
of unity `ζ` in any `ℚ`-algebra domain. -/
theorem map_aeval_eq_of_isPrimitiveRoot (F₁ F₂ : (ℚ[X])[X]) {K A : Type*}
    [CommRing K] [IsDomain K] [Algebra ℚ K] [CommRing A] [IsDomain A] [Algebra ℚ A]
    {h : ℕ} (hh : 0 < h) {ζ₀ : K} (hζ₀ : IsPrimitiveRoot ζ₀ h) {ζ : A} (hζ : IsPrimitiveRoot ζ h)
    (heq : F₁.map (aeval ζ₀).toRingHom = F₂.map (aeval ζ₀).toRingHom) :
    F₁.map (aeval ζ).toRingHom = F₂.map (aeval ζ).toRingHom := by
  ext k
  have hk₀ : aeval ζ₀ (F₁.coeff k - F₂.coeff k) = 0 := by
    have hcoeff := congrArg (fun p : K[X] ↦ p.coeff k) heq
    simp only [coeff_map, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at hcoeff
    rw [map_sub, hcoeff, sub_self]
  have hk : aeval ζ (F₁.coeff k - F₂.coeff k) = 0 :=
    hζ₀.aeval_eq_zero_of_aeval_eq_zero hh hζ hk₀
  rw [map_sub, sub_eq_zero] at hk
  simpa only [coeff_map, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] using hk

end Polynomial

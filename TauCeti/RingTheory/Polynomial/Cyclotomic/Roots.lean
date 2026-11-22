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
ring, once its coefficients are mapped into the domain along a ring homomorphism. Moreover, two
polynomials over `ℚ[X]` whose coefficients evaluate identically at one primitive `h`-th root of
unity in a characteristic-zero field also become equal at any primitive `h`-th root of unity in a
`ℚ`-algebra domain.

## Main results

* `IsPrimitiveRoot.eval₂_cyclotomic`: a primitive `e`-th root of unity is a root of `Φ_e` mapped
  along any ring homomorphism.
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

end IsPrimitiveRoot

namespace Polynomial

/-- **Cyclotomic transfer for `(ℚ[X])[X]` polynomials.** If two polynomials over `ℚ[X]` have equal
images under coefficientwise evaluation at a primitive `h`-th root of unity `ζ₀` in a
characteristic-zero field, then they have equal images under coefficientwise evaluation at any
primitive `h`-th root of unity `ζ` in any `ℚ`-algebra domain. -/
theorem map_aeval_eq_of_isPrimitiveRoot {K A : Type*} [Field K] [CharZero K]
    [CommRing A] [IsDomain A] [Algebra ℚ A] {h : ℕ} (hh : 0 < h) {ζ₀ : K}
    (hζ₀ : IsPrimitiveRoot ζ₀ h) {ζ : A} (hζ : IsPrimitiveRoot ζ h)
    {F₁ F₂ : (ℚ[X])[X]}
    (heq : F₁.map (aeval ζ₀).toRingHom = F₂.map (aeval ζ₀).toRingHom) :
    F₁.map (aeval ζ).toRingHom = F₂.map (aeval ζ).toRingHom := by
  have : NeZero h := ⟨hh.ne'⟩
  ext k
  have hk₀ : aeval ζ₀ (F₁.coeff k - F₂.coeff k) = 0 := by
    have hcoeff := congrArg (fun p : K[X] ↦ p.coeff k) heq
    simp only [coeff_map, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at hcoeff
    rw [map_sub, hcoeff, sub_self]
  have hdvd : cyclotomic h ℚ ∣ F₁.coeff k - F₂.coeff k := by
    rw [cyclotomic_eq_minpoly_rat hζ₀ hh]
    exact minpoly.dvd ℚ ζ₀ hk₀
  have hk : aeval ζ (F₁.coeff k - F₂.coeff k) = 0 := by
    obtain ⟨q, hq⟩ := hdvd
    rw [hq, map_mul, aeval_def, hζ.eval₂_cyclotomic (algebraMap ℚ A), zero_mul]
  rw [map_sub, sub_eq_zero] at hk
  simpa only [coeff_map, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] using hk

end Polynomial

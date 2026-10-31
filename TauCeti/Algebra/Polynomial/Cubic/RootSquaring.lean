/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Polynomial.Tschirnhaus
import Mathlib.Algebra.CubicDiscriminant
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Polynomial.Basic

/-!
# Root squaring for monic cubics

If the monic cubic `X³ + a X² + b X + c` has roots `x, y, z`, then the monic cubic with roots
`x², y², z²` is

  `X³ + (2b - a²) X² + (b² - 2ac) X - c²`.

This is one step of the Dandelin–Graeffe root-squaring method. Iterating it once more gives the
cubic whose roots are the fourth powers `x⁴, y⁴, z⁴`.

The statements are made for the Tschirnhaus transform `tschirnhausPolynomial f (X ^ n)`, the
coefficient-side construction of the polynomial whose roots are the `n`-th powers of the roots
of `f`. They hold over every commutative ring: no roots of `f` need to exist in the ring itself.
The proof computes over an algebraic closure for domains and reduces the general case to the
universal monic cubic over `ℤ[a, b, c]`.

## Main results

* `Polynomial.prod_X_sub_C_sq_eq`: the root-squaring identity for a cubic given as a product of
  three linear factors.
* `Polynomial.tschirnhausPolynomial_cubic_X_sq`: the Tschirnhaus transform of a monic cubic by
  `X²`.
* `Polynomial.tschirnhausPolynomial_cubic_X_pow_four`: the Tschirnhaus transform of a monic cubic
  by `X⁴`, obtained by squaring the roots twice.

## References

* A. S. Householder, *Dandelin, Lobačevskii, or Graeffe?*, Amer. Math. Monthly 66 (1959),
  464–466, for the history of the root-squaring method.
-/

public section

open Polynomial

namespace Polynomial

variable {R : Type*} [CommRing R]

/-- **Root squaring for a split cubic.** If `(X - x)(X - y)(X - z) = X³ + a X² + b X + c`, then
`(X - x²)(X - y²)(X - z²) = X³ + (2b - a²) X² + (b² - 2ac) X - c²`. -/
theorem prod_X_sub_C_sq_eq {a b c x y z : R}
    (h : (X - C x) * (X - C y) * (X - C z) = X ^ 3 + C a * X ^ 2 + C b * X + C c) :
    (X - C (x ^ 2)) * (X - C (y ^ 2)) * (X - C (z ^ 2)) =
      X ^ 3 + C (2 * b - a ^ 2) * X ^ 2 + C (b ^ 2 - 2 * a * c) * X - C (c ^ 2) := by
  have hcubic (a b c : R) :
      X ^ 3 + C a * X ^ 2 + C b * X + C c = (⟨1, a, b, c⟩ : Cubic R).toPoly := by
    simp [Cubic.toPoly]
  rw [Cubic.prod_X_sub_C_eq, hcubic, Cubic.toPoly_injective] at h
  simp only [Cubic.mk.injEq, true_and] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  rw [Cubic.prod_X_sub_C_eq, sub_eq_add_neg, ← C_neg, hcubic, Cubic.toPoly_injective]
  simp only [Cubic.mk.injEq, true_and]
  refine ⟨?_, ?_, ?_⟩ <;> ring

/-- Over a domain `R`, a monic cubic splits into three linear factors in an algebraic closure of
the fraction field of `R`, and its Tschirnhaus transforms are computed from those roots. -/
private theorem exists_map_tschirnhausPolynomial_cubic [IsDomain R] (a b c : R) :
    ∃ (φ : R →+* AlgebraicClosure (FractionRing R)) (x y z : AlgebraicClosure (FractionRing R)),
      Function.Injective φ ∧
      (X - C x) * (X - C y) * (X - C z) = X ^ 3 + C (φ a) * X ^ 2 + C (φ b) * X + C (φ c) ∧
      ∀ T : R[X], (tschirnhausPolynomial (X ^ 3 + C a * X ^ 2 + C b * X + C c) T).map φ =
        (X - C ((T.map φ).eval x)) * (X - C ((T.map φ).eval y)) * (X - C ((T.map φ).eval z)) := by
  let K := AlgebraicClosure (FractionRing R)
  let φ : R →+* K := (algebraMap (FractionRing R) K).comp (algebraMap R (FractionRing R))
  have hφ : Function.Injective φ :=
    (algebraMap (FractionRing R) K).injective.comp (IsFractionRing.injective R (FractionRing R))
  set f : R[X] := X ^ 3 + C a * X ^ 2 + C b * X + C c with hf_def
  have hdeg : f.natDegree = 3 := by rw [hf_def]; compute_degree!
  have hmonic : f.Monic := by rw [hf_def]; monicity!
  have hmap : f.map φ = X ^ 3 + C (φ a) * X ^ 2 + C (φ b) * X + C (φ c) := by simp [hf_def]
  have hs : (f.map φ).Splits := IsAlgClosed.splits _
  have hcard : Multiset.card (f.map φ).roots = 3 := by
    rw [← hs.natDegree_eq_card_roots, hmonic.natDegree_map, hdeg]
  obtain ⟨x, y, z, hroots⟩ := Multiset.card_eq_three.mp hcard
  refine ⟨φ, x, y, z, hφ, ?_, fun T ↦ ?_⟩
  · rw [← hmap, hs.eq_prod_roots_of_monic (hmonic.map φ), hroots]
    simp [mul_assoc]
  · rw [map_tschirnhausPolynomial hmonic, tschirnhausPolynomial_eq_prod_roots (hmonic.map φ) hs,
      hroots]
    simp [mul_assoc]

/-- The universal monic cubic `X³ + a X² + b X + c` over `ℤ[a, b, c]` specializes to any monic
cubic over any commutative ring. -/
private theorem cubic_eq_map_universal (a b c : R) :
    X ^ 3 + C a * X ^ 2 + C b * X + C c =
      (X ^ 3 + C (MvPolynomial.X 0) * X ^ 2 + C (MvPolynomial.X 1) * X +
          C (MvPolynomial.X 2) : (MvPolynomial (Fin 3) ℤ)[X]).map
        (MvPolynomial.eval₂Hom (Int.castRingHom R) ![a, b, c]) := by
  simp

private theorem monic_universal_cubic :
    (X ^ 3 + C (MvPolynomial.X 0) * X ^ 2 + C (MvPolynomial.X 1) * X +
      C (MvPolynomial.X 2) : (MvPolynomial (Fin 3) ℤ)[X]).Monic := by
  monicity!

/-- **Root squaring for a monic cubic.** The Tschirnhaus transform of `X³ + a X² + b X + c` by
`X²`, whose roots are the squares of the roots of the cubic, is
`X³ + (2b - a²) X² + (b² - 2ac) X - c²`. -/
theorem tschirnhausPolynomial_cubic_X_sq (a b c : R) :
    tschirnhausPolynomial (X ^ 3 + C a * X ^ 2 + C b * X + C c) (X ^ 2) =
      X ^ 3 + C (2 * b - a ^ 2) * X ^ 2 + C (b ^ 2 - 2 * a * c) * X - C (c ^ 2) := by
  have hdom {S : Type} [CommRing S] [IsDomain S] (a b c : S) :
      tschirnhausPolynomial (X ^ 3 + C a * X ^ 2 + C b * X + C c) (X ^ 2) =
        X ^ 3 + C (2 * b - a ^ 2) * X ^ 2 + C (b ^ 2 - 2 * a * c) * X - C (c ^ 2) := by
    obtain ⟨φ, x, y, z, hφ, hxyz, hT⟩ := exists_map_tschirnhausPolynomial_cubic a b c
    apply map_injective φ hφ
    rw [hT]
    simp only [Polynomial.map_pow, map_X, eval_pow, eval_X]
    rw [prod_X_sub_C_sq_eq hxyz]
    simp only [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
      map_X, map_C, map_sub, map_mul, map_pow, map_ofNat, Polynomial.map_ofNat]
  have key := map_tschirnhausPolynomial monic_universal_cubic (X ^ 2)
    (MvPolynomial.eval₂Hom (Int.castRingHom R) ![a, b, c])
  rw [hdom, ← cubic_eq_map_universal] at key
  simpa using key.symm

/-- **Root squaring twice for a monic cubic.** The Tschirnhaus transform of `X³ + a X² + b X + c`
by `X⁴`, whose roots are the fourth powers of the roots of the cubic, is
`X³ + a' X² + b' X - c⁴` with `a' = 2(b² - 2ac) - (2b - a²)²` and
`b' = (b² - 2ac)² + 2(2b - a²)c²`. -/
theorem tschirnhausPolynomial_cubic_X_pow_four (a b c : R) :
    tschirnhausPolynomial (X ^ 3 + C a * X ^ 2 + C b * X + C c) (X ^ 4) =
      X ^ 3 + C (2 * (b ^ 2 - 2 * a * c) - (2 * b - a ^ 2) ^ 2) * X ^ 2 +
        C ((b ^ 2 - 2 * a * c) ^ 2 + 2 * (2 * b - a ^ 2) * c ^ 2) * X - C (c ^ 4) := by
  have hdom {S : Type} [CommRing S] [IsDomain S] (a b c : S) :
      tschirnhausPolynomial (X ^ 3 + C a * X ^ 2 + C b * X + C c) (X ^ 4) =
        X ^ 3 + C (2 * (b ^ 2 - 2 * a * c) - (2 * b - a ^ 2) ^ 2) * X ^ 2 +
          C ((b ^ 2 - 2 * a * c) ^ 2 + 2 * (2 * b - a ^ 2) * c ^ 2) * X - C (c ^ 4) := by
    obtain ⟨φ, x, y, z, hφ, hxyz, hT⟩ := exists_map_tschirnhausPolynomial_cubic a b c
    apply map_injective φ hφ
    have h2 := prod_X_sub_C_sq_eq hxyz
    rw [sub_eq_add_neg (_ + _), ← C_neg] at h2
    rw [hT]
    have hpow (t : AlgebraicClosure (FractionRing S)) : t ^ 4 = (t ^ 2) ^ 2 := by ring
    simp only [Polynomial.map_pow, map_X, eval_pow, eval_X, hpow]
    rw [prod_X_sub_C_sq_eq h2]
    simp only [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
      map_X, map_C, map_sub, map_add, map_mul, map_pow, map_neg, map_ofNat, Polynomial.map_ofNat]
    ring
  have key := map_tschirnhausPolynomial monic_universal_cubic (X ^ 4)
    (MvPolynomial.eval₂Hom (Int.castRingHom R) ![a, b, c])
  rw [hdom, ← cubic_eq_map_universal] at key
  simpa using key.symm

end Polynomial

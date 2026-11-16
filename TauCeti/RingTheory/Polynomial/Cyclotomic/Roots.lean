/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import TauCeti.Algebra.Polynomial.Reverse

/-!
# Evaluating cyclotomic polynomials and reciprocal root-of-unity factorizations

A primitive `e`-th root of unity in a domain is a root of the cyclotomic polynomial `Φ_e` over any
ring, once its coefficients are mapped into the domain along a ring homomorphism.

When a domain contains a primitive `n`-th root of unity (`n > 0`), reversing Mathlib's factorization
`X ^ n - 1 = ∏ μ ∈ nthRootsFinset n 1, (X - C μ)` yields the reciprocal factorization
`∏ μ ∈ nthRootsFinset n 1, (1 - C μ * X) = 1 - X ^ n`, and the same product indexed by the group
`rootsOfUnity n R`.

## Main results

* `IsPrimitiveRoot.eval₂_cyclotomic`: a primitive `e`-th root of unity in a domain is a root of
  `Φ_e` mapped along any ring homomorphism.
* `Polynomial.prod_one_sub_C_mul_X_nthRootsFinset`:
  `∏ μ ∈ nthRootsFinset n (1 : R), (1 - C μ * X) = 1 - X ^ n`.
* `Polynomial.finprod_one_sub_C_mul_X_rootsOfUnity`:
  `∏ᶠ μ : rootsOfUnity n R, (1 - C ((μ : Rˣ) : R) * X) = 1 - X ^ n`.
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

/-- **Reciprocal factorization of `1 - X ^ n` over `nthRootsFinset`.** If a domain `R` contains a
primitive `n`-th root of unity (`0 < n`), then
`∏ μ ∈ nthRootsFinset n 1, (1 - C μ * X) = 1 - X ^ n`. This is the reversal of Mathlib's
`Polynomial.X_pow_sub_one_eq_prod`. -/
theorem prod_one_sub_C_mul_X_nthRootsFinset {R : Type*} [CommRing R] [IsDomain R] {ζ : R} {n : ℕ}
    (hpos : 0 < n) (hζ : IsPrimitiveRoot ζ n) :
    ∏ μ ∈ nthRootsFinset n (1 : R), (1 - C μ * X) = 1 - X ^ n := by
  have hrev := congrArg Polynomial.reverse (X_pow_sub_one_eq_prod hpos hζ)
  have hlhs : (X ^ n - 1 : R[X]).reverse = 1 - X ^ n := by
    simpa using reverse_X_pow_sub_C n (1 : R)
  have hrhs : (∏ μ ∈ nthRootsFinset n (1 : R), (X - C μ)).reverse =
      ∏ μ ∈ nthRootsFinset n (1 : R), (1 - C μ * X) := by
    have h := reverse_multiset_prod_of_monic
      (s := (nthRootsFinset n (1 : R)).val.map fun μ ↦ X - C μ) (by simp [monic_X_sub_C])
    rw [Finset.prod, Finset.prod, h, Multiset.map_map]
    refine congrArg Multiset.prod (Multiset.map_congr rfl fun μ _ ↦ ?_)
    simpa using reverse_X_pow_sub_C 1 μ
  rw [hlhs, hrhs] at hrev
  exact hrev.symm

/-- **Reciprocal factorization of `1 - X ^ n` over `rootsOfUnity`.** If a domain `R` contains a
primitive `n`-th root of unity (`0 < n`), then
`∏ᶠ μ : rootsOfUnity n R, (1 - C μ * X) = 1 - X ^ n`. -/
theorem finprod_one_sub_C_mul_X_rootsOfUnity {R : Type*} [CommRing R] [IsDomain R] {ζ : R} {n : ℕ}
    (hpos : 0 < n) (hζ : IsPrimitiveRoot ζ n) :
    ∏ᶠ μ : rootsOfUnity n R, (1 - C ((μ : Rˣ) : R) * X) = 1 - X ^ n := by
  have : NeZero n := ⟨hpos.ne'⟩
  let e : rootsOfUnity n R ≃ nthRootsFinset n (1 : R) :=
    { toFun μ := ⟨((μ : Rˣ) : R), (mem_nthRootsFinset hpos (1 : R)).mpr
        ((mem_rootsOfUnity' n (μ : Rˣ)).mp μ.prop)⟩
      invFun μ := rootsOfUnity.mkOfPowEq μ.1 ((mem_nthRootsFinset hpos (1 : R)).mp μ.2)
      left_inv μ := by
        apply Subtype.ext; apply Units.ext
        exact rootsOfUnity.coe_mkOfPowEq (n := n) ((mem_rootsOfUnity' n (μ : Rˣ)).mp μ.prop)
      right_inv μ := Subtype.ext (rootsOfUnity.coe_mkOfPowEq (n := n)
        ((mem_nthRootsFinset hpos (1 : R)).mp μ.2)) }
  have := Fintype.ofEquiv _ e.symm
  rw [finprod_eq_prod_of_fintype,
    Fintype.prod_equiv e (fun μ : rootsOfUnity n R ↦ 1 - C ((μ : Rˣ) : R) * X)
      (fun μ : nthRootsFinset n (1 : R) ↦ 1 - C μ.1 * X) (fun _ ↦ rfl),
    Finset.prod_coe_sort (nthRootsFinset n (1 : R)) (fun μ ↦ 1 - C μ * X)]
  exact prod_one_sub_C_mul_X_nthRootsFinset hpos hζ

end Polynomial

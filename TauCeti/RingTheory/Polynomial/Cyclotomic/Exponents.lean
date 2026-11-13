/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

/-!
# Coprime exponents in rational polynomial factorizations

Suppose a rational polynomial splits as a product of linear factors with roots `ζ ^ e i`,
where `ζ` is a primitive `h`-th root of unity and `e i < h`. If the polynomial has any
primitive `h`-th root, then every residue coprime to `h` occurs among the `e i`.

The rationality hypothesis matters: a polynomial over a larger field can have just one
primitive root without having its cyclotomic conjugates. No simplicity of the roots is
assumed, so repeated exponents are permitted. This is the arithmetic step that turns
integral characteristic polynomials into constraints on their lists of eigenvalue exponents.

The ambient ring can be any domain that is a rational algebra. The proof uses Mathlib's
`IsPrimitiveRoot.minpoly_eq_cyclotomic_of_irreducible` and irreducibility of cyclotomic
polynomials over the rationals.
-/

public section

open Polynomial

namespace IsPrimitiveRoot

variable {K ι : Type*} [CommRing K] [IsDomain K] [Algebra ℚ K] [Fintype ι]

/-- If a rational polynomial factors with roots `ζ ^ e i`, with all `e i < h`, and has a
primitive `h`-th root, every residue less than `h` and coprime to `h` occurs in `e`.
The primitive root already known to be a root need not be `ζ` itself. -/
theorem exists_eq_of_isRoot_of_map_eq_prod {h : ℕ} {ζ ξ : K}
    (hζ : IsPrimitiveRoot ζ h) (hξ : IsPrimitiveRoot ξ h) {p : ℚ[X]}
    (hp : (p.map (algebraMap ℚ K)).IsRoot ξ) {e : ι → ℕ}
    (he : ∀ i, e i < h)
    (hprod : p.map (algebraMap ℚ K) = ∏ i, (X - C (ζ ^ e i)))
    {a : ℕ} (ha : a < h) (hcop : a.Coprime h) : ∃ i, e i = a := by
  classical
  have hh : 0 < h := Nat.zero_lt_of_lt ha
  have : NeZero (h : ℚ) := ⟨Nat.cast_ne_zero.mpr hh.ne'⟩
  have hdiv : cyclotomic h ℚ ∣ p := by
    rw [hξ.minpoly_eq_cyclotomic_of_irreducible (cyclotomic.irreducible_rat hh)]
    exact minpoly.dvd ℚ ξ (by simpa only [aeval_def, eval₂_eq_eval_map, IsRoot.def] using hp)
  have hroot : (p.map (algebraMap ℚ K)).IsRoot (ζ ^ a) := by
    obtain ⟨q, rfl⟩ := hdiv
    rw [Polynomial.map_mul, map_cyclotomic]
    have hcy : (cyclotomic h K).IsRoot (ζ ^ a) :=
      (hζ.pow_of_coprime a hcop).isRoot_cyclotomic hh
    rw [IsRoot.def, eval_mul, hcy.eq_zero, zero_mul]
  rw [hprod, IsRoot.def, eval_prod] at hroot
  obtain ⟨i, -, hi⟩ := Finset.prod_eq_zero_iff.mp hroot
  have hi' : ζ ^ a = ζ ^ e i := sub_eq_zero.mp (by simpa using hi)
  exact ⟨i, (hζ.pow_inj ha (he i) hi').symm⟩

end IsPrimitiveRoot

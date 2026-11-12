/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Multiquadratic.Galois.Group
public import TauCeti.NumberTheory.Multiquadratic.CMField.Basic

/-!
# The Galois group of a multiquadratic CM field is `(ℤ/2)^{n+1}`

The multiquadratic CM field `ℚ(i, √p₁, …, √pₙ)` has degree `2^{n+1}` over `ℚ`
(`TauCeti.Multiquadratic.finrank_adjoin_I_sqrt_primes`). This file supplies its Galois group:
adjoining `i = √(-1)` together with the real square roots of a finite family of distinct primes
gives a field whose Galois group over `ℚ` is elementary abelian of exponent `2` and rank `n + 1`.

The single new ingredient over the prime-radicand theory
(`TauCeti.Multiquadratic.galoisGroupEquivSqrtPrimes`) is the extra radicand `-1`. Indexing the
combined radicand family by `Option ι` — `none ↦ -1`, `some i ↦ p i` — the negative-radicand
square-class combinator `TauCeti.Multiquadratic.not_isSquare_prod_optionNeg` shows this family is
still square-class independent, so the field-generic isomorphism
`TauCeti.Multiquadratic.galoisGroupEquiv` applies verbatim. This gives the explicit isomorphism,
its cardinality reading, and the worked examples `|Gal(ℚ(i, √2)/ℚ)| = 4` and
`|Gal(ℚ(i, √5)/ℚ)| = 4`.

## Main results

* `TauCeti.Multiquadratic.galoisGroupEquivISqrtPrimes`: for a finite family of distinct primes
  `p : ι → ℕ`, the explicit isomorphism
  `Gal(ℚ(i, √p₁, …, √pₙ)/ℚ) ≃ Multiplicative (Option ι → ℤ/2)`.
* `TauCeti.Multiquadratic.card_aut_adjoin_I_sqrt_primes`: `|Gal(ℚ(i, √p₁, …, √pₙ)/ℚ)| = 2^{|ι|+1}`.
* `TauCeti.Multiquadratic.card_aut_adjoin_I_sqrt_prime`: `|Gal(ℚ(i, √p)/ℚ)| = 4` for a prime
  `p` — the one-prime case of the multiquadratic CM Galois group.
* `TauCeti.Multiquadratic.card_aut_adjoin_I_sqrt_two`: `|Gal(ℚ(i, √2)/ℚ)| = 4`.
* `TauCeti.Multiquadratic.card_aut_adjoin_I_sqrt_five`: `|Gal(ℚ(i, √5)/ℚ)| = 4`, the
  genus-field-generator example for the prime discriminants `-4` and `5`.

## Provenance

Like the CM degree it accompanies, this parallels the analysis of one concrete CM field in
[kim-em/erdos-unit-distance](https://github.com/kim-em/erdos-unit-distance), the formalization of
L. Alpöge's disproof of the uniform-constant Erdős unit-distance conjecture. The `Option`-indexed
route — treating `i = √(-1)` as one more radicand rather than a separate quadratic step — matches
the CM degree file `TauCeti.NumberTheory.Multiquadratic.CMField.Basic` and reuses its square-class
combinator.
-/

public section

open IntermediateField

namespace TauCeti.Multiquadratic

variable {ι : Type*} (p : ι → ℕ)

variable [Finite ι] (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)

include hp hinj

/-- **The Galois group of a multiquadratic CM field is `(ℤ/2)^{n+1}`.** For a finite family of
distinct primes `p : ι → ℕ`, the field `ℚ(i, √p₁, …, √pₙ)` generated over `ℚ` by `i` and the real
square roots of the `p i` has Galois group isomorphic to `Multiplicative (Option ι → ℤ/2)`. This
is the `Option`-indexed corollary of the field-generic isomorphism `galoisGroupEquiv`. -/
noncomputable def galoisGroupEquivISqrtPrimes :
    (adjoin ℚ (Set.range (cmRoot p)) ≃ₐ[ℚ] adjoin ℚ (Set.range (cmRoot p))) ≃*
      Multiplicative (Option ι → ZMod 2) :=
  galoisGroupEquiv (cmRoot_sq p) (not_isSquare_prod_cmRadicand p hp hinj)

/-- The CM Galois equivalence sends an automorphism to its sign pattern on the generators
`i, √(p i)`. -/
@[simp] theorem galoisGroupEquivISqrtPrimes_apply
    (σ : adjoin ℚ (Set.range (cmRoot p)) ≃ₐ[ℚ] adjoin ℚ (Set.range (cmRoot p))) :
    galoisGroupEquivISqrtPrimes p hp hinj σ =
      Multiplicative.ofAdd (signPattern (cmRoot p) σ) :=
  galoisGroupEquiv_apply (cmRoot_sq p) (not_isSquare_prod_cmRadicand p hp hinj) σ

/-- The inverse CM Galois equivalence realizes a sign pattern by sending each generator to
`(-1)^(ε x)` times itself: `i ↦ ±i` and `√(p i) ↦ ±√(p i)`. -/
@[simp] theorem galoisGroupEquivISqrtPrimes_symm_apply_gen (ε : Option ι → ZMod 2) (x : Option ι) :
    ((galoisGroupEquivISqrtPrimes p hp hinj).symm (Multiplicative.ofAdd ε)) (gen (cmRoot p) x)
      = (-1) ^ (ε x).val * gen (cmRoot p) x :=
  galoisGroupEquiv_symm_apply_gen (cmRoot_sq p) (not_isSquare_prod_cmRadicand p hp hinj) ε x

/-- **Cardinality of the Galois group of a multiquadratic CM field.** For a finite family of
distinct primes `p : ι → ℕ`, `|Gal(ℚ(i, √p₁, …, √pₙ)/ℚ)| = 2^{|ι|+1}`. This is the cardinality
reading of `galoisGroupEquivISqrtPrimes`, matching the CM degree `finrank_adjoin_I_sqrt_primes`. -/
theorem card_aut_adjoin_I_sqrt_primes :
    Nat.card
        ((adjoin ℚ (insert Complex.I (Set.range fun i => ((Real.sqrt (p i) : ℝ) : ℂ))) :
            IntermediateField ℚ ℂ) ≃ₐ[ℚ]
          (adjoin ℚ (insert Complex.I (Set.range fun i => ((Real.sqrt (p i) : ℝ) : ℂ))) :
            IntermediateField ℚ ℂ))
      = 2 ^ (Nat.card ι + 1) := by
  have hcard : Nat.card (Option ι) = Nat.card ι + 1 := by
    let := Fintype.ofFinite ι
    simp [Nat.card_eq_fintype_card, Fintype.card_option]
  have hkey := card_aut_adjoin_range (cmRoot_sq p) (not_isSquare_prod_cmRadicand p hp hinj)
  rw [range_cmRoot p, hcard] at hkey
  exact hkey

end TauCeti.Multiquadratic

namespace TauCeti.Multiquadratic

/-- **Cardinality of the Galois group of a single-prime multiquadratic CM field.** For a prime
`p`, `|Gal(ℚ(i, √p)/ℚ)| = 4`, the one-prime case of `card_aut_adjoin_I_sqrt_primes`. -/
theorem card_aut_adjoin_I_sqrt_prime (p : ℕ) (hp : p.Prime) :
    Nat.card
        ((adjoin ℚ ({Complex.I, ((Real.sqrt p : ℝ) : ℂ)} : Set ℂ) : IntermediateField ℚ ℂ)
          ≃ₐ[ℚ]
           (adjoin ℚ ({Complex.I, ((Real.sqrt p : ℝ) : ℂ)} : Set ℂ) : IntermediateField ℚ ℂ))
      = 4 := by
  have h := card_aut_adjoin_I_sqrt_primes (ι := Unit) (fun _ => p) (fun _ => hp)
    (fun _ _ _ => Subsingleton.elim _ _)
  rw [Set.range_const] at h
  exact h.trans (by simp)

/-- **Worked example: `|Gal(ℚ(i, √2)/ℚ)| = 4`.** The one-real-prime worked example,
obtained from `card_aut_adjoin_I_sqrt_prime` with the single prime `2`. -/
theorem card_aut_adjoin_I_sqrt_two :
    Nat.card
        ((adjoin ℚ ({Complex.I, ((Real.sqrt 2 : ℝ) : ℂ)} : Set ℂ) : IntermediateField ℚ ℂ) ≃ₐ[ℚ]
          (adjoin ℚ ({Complex.I, ((Real.sqrt 2 : ℝ) : ℂ)} : Set ℂ) : IntermediateField ℚ ℂ))
      = 4 := by
  simpa using card_aut_adjoin_I_sqrt_prime 2 Nat.prime_two

/-- **Worked example: `|Gal(ℚ(i, √5)/ℚ)| = 4`.** This is the Galois group of the
multiquadratic field generated by the radicands attached to the prime discriminants `-4` and
`5`, the genus-field generators for `ℚ(√-5)`, obtained from the single-prime CM field lemma
`card_aut_adjoin_I_sqrt_prime` with the prime `5`. -/
theorem card_aut_adjoin_I_sqrt_five :
    Nat.card
      ((adjoin ℚ ({Complex.I, ((Real.sqrt 5 : ℝ) : ℂ)} : Set ℂ) :
          IntermediateField ℚ ℂ)
          ≃ₐ[ℚ]
        (adjoin ℚ ({Complex.I, ((Real.sqrt 5 : ℝ) : ℂ)} : Set ℂ) :
          IntermediateField ℚ ℂ))
      = 4 := by
  simpa using card_aut_adjoin_I_sqrt_prime 5 (by decide)

end TauCeti.Multiquadratic

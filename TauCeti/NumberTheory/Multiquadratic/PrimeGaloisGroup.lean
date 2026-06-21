/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TauCeti.NumberTheory.Multiquadratic.GaloisGroup
import TauCeti.NumberTheory.Multiquadratic.PrimeRadicands

/-!
# The Galois group of a prime-radicand multiquadratic field

The field-generic isomorphism `TauCeti.Multiquadratic.galoisGroupEquiv` identifies the Galois
group of a multiquadratic field `M = K(rootᵢ : i)` with `(ℤ/2)ⁿ` once the radicands are
**square-class independent**: no nonempty subset product of them is a square. This file derives
the cardinality of that Galois group, `|Gal(M/K)| = 2^|ι|`, and supplies the
square-class-independence hypothesis for the most common concrete source of independent
radicands — a family of **distinct primes** — to obtain the prime-indexed corollary
`Gal(ℚ(√p₁, …, √pₙ)/ℚ) ≃ (ℤ/2)ⁿ` (a genus-theory input) and the smallest non-vacuity example
`|Gal(ℚ(√2, √3)/ℚ)| = 4`.

The prime case reuses `TauCeti.Multiquadratic.not_isSquare_prod_primes`: a nonempty subset
product of distinct primes is squarefree and not a unit, hence not a square.

## Main results

* `TauCeti.Multiquadratic.card_aut_adjoin_range`: for square-class independent radicands over a
  field with `2 ≠ 0`, `|Gal(M/K)| = 2^|ι|`, the field-generic Galois-group cardinality.
* `TauCeti.Multiquadratic.galoisGroupEquivSqrtPrimes`: for a finite family of distinct primes
  `p : ι → ℕ`, the explicit isomorphism `Gal(ℚ(√p₁, …, √pₙ)/ℚ) ≃ Multiplicative (ι → ℤ/2)`.
* `TauCeti.Multiquadratic.card_aut_adjoin_sqrt_primes`: `|Gal(ℚ(√p₁, …, √pₙ)/ℚ)| = 2^|ι|`.
* `TauCeti.Multiquadratic.card_aut_adjoin_sqrt_two_three`: `|Gal(ℚ(√2, √3)/ℚ)| = 4`.
-/

open IntermediateField

namespace TauCeti.Multiquadratic

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {ι : Type*}

/-- **Cardinality of the Galois group of a multiquadratic field.** If no nonempty subset product
of the radicands `d i` is a square in `K` (and `2 ≠ 0` in `K`), then the multiquadratic field
`M = K(rootᵢ : i)` has `|Gal(M/K)| = 2^|ι|`. This is the cardinality reading of the explicit
isomorphism `galoisGroupEquiv`. -/
theorem card_aut_adjoin_range [Finite ι] {d : ι → K} {root : ι → L} [NeZero (2 : K)]
    (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i))
    (hindep : ∀ S : Finset ι, S.Nonempty → ¬ IsSquare (∏ i ∈ S, d i)) :
    Nat.card (adjoin K (Set.range root) ≃ₐ[K] adjoin K (Set.range root)) = 2 ^ Nat.card ι := by
  classical
  letI := Fintype.ofFinite ι
  rw [Nat.card_congr (galoisGroupEquiv hroot hindep).toEquiv,
    Nat.card_congr (Multiplicative.ofAdd (α := ι → ZMod 2)).symm,
    Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_pi]
  simp [ZMod.card]

/-- **The Galois group of a prime-radicand multiquadratic field is `(ℤ/2)ⁿ`.** For a finite family
of distinct primes `p : ι → ℕ`, the field generated over `ℚ` by their real square roots has Galois
group isomorphic to `Multiplicative (ι → ℤ/2)`. This is the prime-indexed corollary of the
field-generic isomorphism `galoisGroupEquiv`. -/
noncomputable def galoisGroupEquivSqrtPrimes [Finite ι] (p : ι → ℕ)
    (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p) :
    (adjoin ℚ (Set.range fun i => (Real.sqrt (p i) : ℝ)) ≃ₐ[ℚ]
        adjoin ℚ (Set.range fun i => (Real.sqrt (p i) : ℝ))) ≃*
      Multiplicative (ι → ZMod 2) :=
  galoisGroupEquiv (d := fun i => (p i : ℚ)) (root := fun i => Real.sqrt (p i))
    (fun i => by rw [Real.sq_sqrt (Nat.cast_nonneg _), map_natCast])
    (fun S hS => not_isSquare_prod_primes p (fun i _ => hp i)
      (fun i _ j _ hij h => hij (hinj h)) hS)

/-- **Cardinality of the Galois group of a prime-radicand multiquadratic field.** For a finite
family of distinct primes `p : ι → ℕ`, `|Gal(ℚ(√p₁, …, √pₙ)/ℚ)| = 2^|ι|`. -/
theorem card_aut_adjoin_sqrt_primes [Finite ι] (p : ι → ℕ)
    (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p) :
    Nat.card (adjoin ℚ (Set.range fun i => (Real.sqrt (p i) : ℝ)) ≃ₐ[ℚ]
        adjoin ℚ (Set.range fun i => (Real.sqrt (p i) : ℝ))) = 2 ^ Nat.card ι :=
  card_aut_adjoin_range (d := fun i => (p i : ℚ)) (root := fun i => Real.sqrt (p i))
    (fun i => by rw [Real.sq_sqrt (Nat.cast_nonneg _), map_natCast])
    (fun S hS => not_isSquare_prod_primes p (fun i _ => hp i)
      (fun i _ j _ hij h => hij (hinj h)) hS)

/-- **Worked example: `|Gal(ℚ(√2, √3)/ℚ)| = 4`.** The Galois group of the smallest nontrivial
multiquadratic field, obtained from `card_aut_adjoin_sqrt_primes` with the primes `2` and `3`. -/
theorem card_aut_adjoin_sqrt_two_three :
    Nat.card ((adjoin ℚ {Real.sqrt 2, Real.sqrt 3} : IntermediateField ℚ ℝ) ≃ₐ[ℚ]
        (adjoin ℚ {Real.sqrt 2, Real.sqrt 3} : IntermediateField ℚ ℝ)) = 4 := by
  have h := card_aut_adjoin_sqrt_primes ![2, 3] (by decide) (by decide)
  have hset : (Set.range fun i : Fin 2 => Real.sqrt ((![2, 3] : Fin 2 → ℕ) i))
      = {Real.sqrt 2, Real.sqrt 3} := by
    ext x
    simp [Fin.exists_fin_two, eq_comm]
  rw [hset] at h
  rw [h, Nat.card_eq_fintype_card, Fintype.card_fin]
  norm_num

end TauCeti.Multiquadratic

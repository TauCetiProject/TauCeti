/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Defs
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
import Mathlib.Algebra.Field.ZMod
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.ZMod.Basic
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.ZMod.SignedQuotient

/-!
# Prime-field orders and non-isomorphism of `PSL₂(𝔽_p)`

This file establishes the exact orders of `PSL₂(𝔽_p)` for primes `p` and deduces that distinct
primes give non-isomorphic groups `PSL₂(𝔽_p)`:

* `Matrix.ProjectiveSpecialLinearGroup.card_fin_two_zmod_two`: `|PSL₂(𝔽₂)| = 6`.
* `Matrix.ProjectiveSpecialLinearGroup.two_mul_card_fin_two_zmod_prime`: for an odd prime `p`,
  `2 · |PSL₂(𝔽_p)| = p(p² - 1)`.
* `Matrix.ProjectiveSpecialLinearGroup.eq_of_fin_two_zmod_mulEquiv`: `PSL₂(𝔽_p) ≃* PSL₂(𝔽_q)`
  implies `p = q` for primes `p, q`.

## References

* G. Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, Princeton University
  Press, 1971, §1.6.
-/

public section

open scoped MatrixGroups

namespace Matrix.ProjectiveSpecialLinearGroup

open Matrix.SpecialLinearGroup

/-- Over `𝔽₂`, the center of `SL₂(𝔽₂)` is trivial, so `|PSL₂(𝔽₂)| = |SL₂(𝔽₂)| = 6`. -/
theorem card_fin_two_zmod_two : Nat.card PSL(2, ZMod 2) = 6 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← Nat.card_congr (TauCeti.Matrix.SignedQuotient.equivPSL (ZMod 2)).toEquiv,
    TauCeti.Matrix.SignedQuotient.card_fin_two_zmod_two]

/-- For an odd prime `p`, `2 · |PSL₂(𝔽_p)| = p(p² - 1)`. -/
theorem two_mul_card_fin_two_zmod_prime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    2 * Nat.card PSL(2, ZMod p) = p * (p ^ 2 - 1) := by
  have : Fact p.Prime := ⟨hp⟩
  rw [← Nat.card_congr (TauCeti.Matrix.SignedQuotient.equivPSL (ZMod p)).toEquiv,
    TauCeti.Matrix.SignedQuotient.two_mul_card_fin_two_zmod (by have := hp.two_le; omega),
    card_fin_two_zmod_prime hp]

/-- **Distinct primes have non-isomorphic projective special linear groups `PSL₂(𝔽_p)`:** if
`PSL₂(𝔽_p) ≃* PSL₂(𝔽_q)` with `p, q` prime, then `p = q`. -/
theorem eq_of_fin_two_zmod_mulEquiv {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (e : PSL(2, ZMod p) ≃* PSL(2, ZMod q)) : p = q := by
  wlog hpq : p ≤ q generalizing p q
  · exact (this hq hp e.symm (by omega)).symm
  rcases hpq.eq_or_lt with rfl | hlt
  · rfl
  · exfalso
    have hcard : Nat.card PSL(2, ZMod p) = Nat.card PSL(2, ZMod q) := Nat.card_congr e.toEquiv
    have hq2 : q ≠ 2 := by have := hp.two_le; omega
    have hq_eq := two_mul_card_fin_two_zmod_prime hq hq2
    by_cases hp2 : p = 2
    · subst hp2
      rw [← hcard, card_fin_two_zmod_two] at hq_eq
      have : 3 * (3 ^ 2 - 1) ≤ q * (q ^ 2 - 1) :=
        Nat.mul_le_mul (by omega) (Nat.sub_le_sub_right (Nat.pow_le_pow_left (by omega) 2) 1)
      omega
    · have hp_eq := two_mul_card_fin_two_zmod_prime hp hp2
      have h1 : 1 < p ^ 2 := by nlinarith [hp.two_le]
      have h2 : p ^ 2 < q ^ 2 := by nlinarith [hp.two_le]
      have : p * (p ^ 2 - 1) < q * (q ^ 2 - 1) :=
        (Nat.mul_lt_mul_of_pos_right hlt (by omega)).trans
          (Nat.mul_lt_mul_of_pos_left (by omega) hq.pos)
      omega

end Matrix.ProjectiveSpecialLinearGroup

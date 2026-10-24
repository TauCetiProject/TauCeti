/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `GL` occurs in the statements below.
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
-- Non-public: `Matrix.card_GL_field` is what the two factorizations below are read off, in the
-- proofs only.
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
-- Non-public: the determinant surjection transfers vanishing cardinality for infinite fields.
import Mathlib.SetTheory.Cardinal.NatCard

/-!
# The order of `GL₂` over a field

Mathlib's `Matrix.card_GL_field` gives `|GL n 𝔽_q| = ∏ i, (qⁿ - qⁱ)`, which in size two reads
`(q² - 1)(q² - q)`. That form is a product of differences, and every index computation in `GL₂`
divides it by the order of a subgroup, so what is wanted is the factored form
`(q - 1)² · q · (q + 1)`, where the natural subtraction has already been carried out. It is
recorded here in the two associations the two maximal tori call for: the split torus has order
`(q - 1)²` and the non-split one `q² - 1`.

The formulas use `q = Nat.card F` and require no chosen enumeration or finiteness assumption.
For an infinite field, both the field and its general linear group have `Nat.card` equal to zero,
so the same identities hold.

## Main results

* `TauCeti.natCard_GL_fin_two`: `|GL₂(𝔽_q)| = (q - 1)² · q(q + 1)`.
* `TauCeti.natCard_GL_fin_two_eq_sq_sub_one_mul`: `|GL₂(𝔽_q)| = (q² - 1) · q(q - 1)`.
* `TauCeti.natCard_GL_fin_two_of_card_eq_two`: `|GL₂(𝔽₂)| = 6`.
-/

public section

namespace TauCeti

variable (F : Type*) [Field F]

/-- **The order of `GL₂` over a field**, in the factored form `(q - 1)² · q(q + 1)`: the
first factor is the order of the split torus and the second its index. -/
theorem natCard_GL_fin_two :
    Nat.card (GL (Fin 2) F) =
      (Nat.card F - 1) ^ 2 * (Nat.card F * (Nat.card F + 1)) := by
  rcases finite_or_infinite F with hF | hF
  · let := Fintype.ofFinite F
    rw [Matrix.card_GL_field, Fin.prod_univ_two]
    simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, ← Nat.card_eq_fintype_card]
    simp_rw [pow_two, mul_self_tsub_one]
    rw [← Nat.mul_sub_one]
    ring
  · have hcard : Nat.card (GL (Fin 2) F) = 0 :=
      Finite.card_eq_zero_of_surjective Matrix.GeneralLinearGroup.det_surjective
        (by simp [Nat.card_units])
    simp [hcard]

/-- **The order of `GL₂` over a field**, in the factored form `(q² - 1) · q(q - 1)`: the
first factor is the order of the non-split torus and the second its index. -/
theorem natCard_GL_fin_two_eq_sq_sub_one_mul :
    Nat.card (GL (Fin 2) F) =
      (Nat.card F ^ 2 - 1) * (Nat.card F * (Nat.card F - 1)) := by
  rw [natCard_GL_fin_two F]
  simp_rw [pow_two, mul_self_tsub_one]
  ring

variable {F} in
/-- **`GL₂` over a field with two elements has order `6`.** This is `(q - 1)² · q(q + 1)` at
`q = 2`. -/
theorem natCard_GL_fin_two_of_card_eq_two (hF : Nat.card F = 2) :
    Nat.card (GL (Fin 2) F) = 6 := by
  rw [natCard_GL_fin_two F, hF]
  norm_num

end TauCeti

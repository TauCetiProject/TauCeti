/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.NumberTheory.GaloisRepresentation.TateTwist

/-!
# Examples: Tate twists

* `M(0) = M`.
* `ℤ_ℓ(1)` is the first Tate twist of the trivial line, and twisting it once more gives
  determinant `χ_ℓ²`.
-/

open TauCeti ContinuousRep

variable (ℓ : ℕ) [Fact ℓ.Prime] (F : Type*) [Field F]

-- The zeroth Tate twist changes nothing.
example {M : Type*} [AddCommMonoid M] [Module ℤ_[ℓ] M] [TopologicalSpace M]
    [ContinuousSMul ℤ_[ℓ] M] (ρ : ContinuousRep (Field.absoluteGaloisGroup F) ℤ_[ℓ] M) :
    ρ.tateTwist ℓ 0 = ρ :=
  tateTwist_zero ρ

-- `ℤ_ℓ(1)` is the Tate twist of the trivial line.
example : (trivial (Field.absoluteGaloisGroup F) ℤ_[ℓ] ℤ_[ℓ]).tateTwist ℓ 1 = cyclotomicLine ℓ F :=
  tateTwist_trivial_one

-- `ℤ_ℓ(1)(1) = ℤ_ℓ(2)` has determinant `χ_ℓ²`, not `χ_ℓ`.
example : ((cyclotomicLine ℓ F).tateTwist ℓ 1).det =
    (cyclotomicPow ℓ F ℤ_[ℓ] 2 : Field.absoluteGaloisGroup F →* ℤ_[ℓ]ˣ) := by
  rw [← tateTwist_trivial_one, tateTwist_tateTwist, tateTwist_trivial, det_ofCharacter,
    one_add_one_eq_two]

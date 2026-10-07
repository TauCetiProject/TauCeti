/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.RingTheory.SimpleRing.Pi
public import Mathlib.RingTheory.SimpleRing.Matrix

/-!
# Invariance of the number of matrix blocks

Artin--Wedderburn presents a semisimple ring `R` as a finite product of positive-size matrix
algebras over division rings. `RingEquiv.card_blocks_eq` compares any two such presentations:
the number of blocks is an invariant of the ring.

Simplicity of the coefficient rings is all the argument uses. Positivity of the matrix sizes is
essential: a zero-size matrix algebra is trivial, so any presentation could be padded with such
blocks. These are the same `NeZero` hypotheses produced by
`IsSemisimpleRing.exists_ringEquiv_pi_matrix_divisionRing`. Semisimplicity of `R` guarantees a
Wedderburn presentation exists, but is not needed to compare presentations.

The underlying factor matching and cardinality invariance for arbitrary products of simple rings
are `RingEquiv.exists_equiv_factors` and `RingEquiv.card_eq_of_pi_of_isSimpleRing` in
`TauCeti/RingTheory/SimpleRing/Pi.lean`. The finer uniqueness of the matrix sizes and division
rings is `TauCeti.wedderburn_blocks_unique` in
`TauCeti/RingTheory/Semisimple/Wedderburn/Uniqueness.lean`, which applies
`TauCeti.wedderburn_data_unique` to the matched matrix blocks.

## Main results

* `RingEquiv.card_blocks_eq`: two presentations as finite products of positive-size matrix
  algebras over simple rings have the same number of blocks.

## References

T. Y. Lam, *A First Course in Noncommutative Rings*, §3, or C. W. Curtis and I. Reiner,
*Representation Theory of Finite Groups and Associative Algebras*, §25.
-/

public section

namespace RingEquiv

/-- **Invariance of the block count.** Two presentations of the same ring as finite products of
positive-size matrix algebras over simple rings have the same number of blocks.

This applies in particular to two Wedderburn presentations. The `NeZero` hypotheses are essential:
a zero-size matrix algebra is trivial, so any presentation could be padded with empty blocks.
Semisimplicity of `R` guarantees a Wedderburn presentation exists, but is not needed here. -/
theorem card_blocks_eq {R : Type*} [Ring R] {m n : ℕ} {D : Fin m → Type*} {D' : Fin n → Type*}
    [∀ i, Ring (D i)] [∀ i, IsSimpleRing (D i)] [∀ i, Ring (D' i)] [∀ i, IsSimpleRing (D' i)]
    {d : Fin m → ℕ} {d' : Fin n → ℕ} [∀ i, NeZero (d i)] [∀ i, NeZero (d' i)]
    (f : R ≃+* ∀ i, Matrix (Fin (d i)) (Fin (d i)) (D i))
    (g : R ≃+* ∀ i, Matrix (Fin (d' i)) (Fin (d' i)) (D' i)) : m = n := by
  have : ∀ i, Nonempty (Fin (d i)) := fun i ↦ ⟨⟨0, NeZero.pos (d i)⟩⟩
  have : ∀ i, Nonempty (Fin (d' i)) := fun i ↦ ⟨⟨0, NeZero.pos (d' i)⟩⟩
  simpa using f.card_eq_of_pi_of_isSimpleRing g

end RingEquiv

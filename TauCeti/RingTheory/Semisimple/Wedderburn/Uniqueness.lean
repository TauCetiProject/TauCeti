/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Semisimple.MatrixDivisionRing
import Mathlib.RingTheory.SimpleRing.Matrix
import TauCeti.RingTheory.SimpleRing.Pi

/-!
# Uniqueness of Wedderburn blocks

Artin--Wedderburn presents a semisimple ring as a finite product of matrix rings over division
rings. `RingEquiv.wedderburn_blocks_unique` proves that two such presentations have the same
matrix sizes and division rings after one permutation of the blocks. More generally, it compares
products over arbitrary index sets, with each matrix block indexed by any finite nonempty type;
the products themselves need not be semisimple.

The generic factor matching in `RingEquiv.exists_equiv_factors` permutes the factors of the two
products. The single-block classification `TauCeti.nonempty_ringEquiv_matrix_iff` then identifies
the matrix size and coefficient division ring of each matched pair.

## Main results

* `RingEquiv.wedderburn_blocks_unique`: two products of matrix rings over division rings with
  finite nonempty row indices have matching degrees and coefficients after a permutation of blocks.

## References

See T. Y. Lam, *A First Course in Noncommutative Rings*, GTM 131, section 3, or C. W. Curtis and
I. Reiner, *Representation Theory of Finite Groups and Associative Algebras*, section 26.
-/

public section

namespace RingEquiv

/-- **Uniqueness of every block in a product of matrix rings over division rings.** Two such
presentations differ only by a permutation of the blocks: corresponding matrix sizes agree and
their coefficient division rings are isomorphic. The block index sets are arbitrary; each matrix
index type is finite and nonempty.

The nonemptiness hypotheses are essential. A zero-size matrix ring is trivial and can be inserted
with arbitrary coefficients without changing the product. -/
theorem wedderburn_blocks_unique {R : Type*} [Ring R]
    {ι κ : Type*} {D : ι → Type*} {E : κ → Type*}
    [∀ i, DivisionRing (D i)] [∀ j, DivisionRing (E j)]
    {m : ι → Type*} {n : κ → Type*} [∀ i, Fintype (m i)] [∀ j, Fintype (n j)]
    [∀ i, Nonempty (m i)] [∀ j, Nonempty (n j)]
    (f : R ≃+* ∀ i, Matrix (m i) (m i) (D i))
    (g : R ≃+* ∀ j, Matrix (n j) (n j) (E j)) :
    ∃ σ : ι ≃ κ, ∀ i, Fintype.card (m i) = Fintype.card (n (σ i)) ∧
      Nonempty (D i ≃+* E (σ i)) := by
  classical
  obtain ⟨σ, hσ⟩ := (f.symm.trans g).exists_equiv_factors
  refine ⟨σ, fun i ↦ ?_⟩
  obtain ⟨hblock, -⟩ := hσ i
  exact TauCeti.nonempty_ringEquiv_matrix_iff.mp ⟨hblock⟩

end RingEquiv

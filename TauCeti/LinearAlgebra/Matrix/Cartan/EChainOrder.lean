/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Cartan.Basic

/-!
# The type `E` Cartan matrix in chain order

Mathlib's `CartanMatrix.E n` numbers the nodes of the `Eₙ` diagram as Bourbaki does: the nodes
`1, 3, 4, …, n` form a chain and node `2` is attached to node `4`. A common alternative numbers the
long chain first: nodes `1, 2, …, n - 1` form a chain and the extra node `n` is attached to node
`3`. This file defines the Cartan matrix `CartanMatrix.eChain n` in this chain order and the
relabelling `CartanMatrix.eChainEquiv n` that sends a chain label to its Bourbaki label,
`(1, 2, 3, …, n - 1, n) ↦ (1, 3, 4, …, n, 2)`, and proves that the relabelling carries one
Cartan matrix to the other. Indices are `0`-based, so in `Fin n` the relabelling fixes `0`, sends
`k` to `k + 1` for `1 ≤ k ≤ n - 2`, and sends `n - 1` to `1`.

As for `CartanMatrix.E`, the definition and the comparison are uniform in `n`; the values
`n = 6, 7, 8` are the finite types `E₆`, `E₇`, `E₈`. The comparison lets coefficient vectors
computed in one numbering be read in the other: a vector `c` indexed by Bourbaki labels is listed
in chain order as `c ∘ CartanMatrix.eChainEquiv n`, so that the `E₈` marks
`(2, 3, 4, 6, 5, 4, 3, 2)` become `(2, 4, 6, 5, 4, 3, 2, 3)`.

## Main definitions

* `CartanMatrix.eChain`: the Cartan matrix of the `Eₙ` diagram in chain order.
* `CartanMatrix.eChainEquiv`: the relabelling of the nodes from chain order to Bourbaki order.

## Main results

* `CartanMatrix.E_eChainEquiv_apply` and `CartanMatrix.E_submatrix_eChainEquiv`: relabelling the
  Bourbaki-numbered matrix `CartanMatrix.E n` by `CartanMatrix.eChainEquiv n` gives
  `CartanMatrix.eChain n`.
* `CartanMatrix.eChain_six_eq`, `CartanMatrix.eChain_seven_eq`, `CartanMatrix.eChain_eight_eq`:
  the three finite-type matrices, written out.

## References

Bourbaki, *Lie Groups and Lie Algebras, Chapters 4–6*, Chapter VI §4, Plates V–VII.
-/

public section

open Matrix

namespace CartanMatrix

/-- The Cartan matrix of the `Eₙ` diagram in **chain order**: the nodes `0, 1, …, n - 2` form a
chain and the last node `n - 1` is attached to node `2`. With `1`-based labels this is the chain
`1 — 2 — ⋯ — (n - 1)` with the extra node `n` attached to `3`. It agrees with the
Bourbaki-numbered `CartanMatrix.E n` after the relabelling `CartanMatrix.eChainEquiv n`; see
`CartanMatrix.E_submatrix_eChainEquiv`. -/
def eChain (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  .of fun i j =>
    if i = j then 2
    else if (i.val + 1 = j.val ∧ j.val + 1 < n) ∨ (j.val + 1 = i.val ∧ i.val + 1 < n) ∨
      (i.val = 2 ∧ j.val + 1 = n) ∨ (j.val = 2 ∧ i.val + 1 = n)
    then -1 else 0

-- `(rfl)`, not `rfl`: the body of `CartanMatrix.eChain` is not exposed, and the parenthesised form
-- keeps this equation out of the exported definitional-equality check.
/-- The entries of `CartanMatrix.eChain n`, spelled out. -/
lemma eChain_apply (n : ℕ) (i j : Fin n) :
    eChain n i j =
      if i = j then 2
      else if (i.val + 1 = j.val ∧ j.val + 1 < n) ∨ (j.val + 1 = i.val ∧ i.val + 1 < n) ∨
        (i.val = 2 ∧ j.val + 1 = n) ∨ (j.val = 2 ∧ i.val + 1 = n)
      then -1 else 0 := (rfl)

/-- The diagonal entries of the chain-order Cartan matrix are `2`. -/
@[simp]
theorem eChain_apply_same (n : ℕ) (i : Fin n) : eChain n i i = 2 := by
  simp [eChain_apply]

/-- The chain-order Cartan matrix is symmetric: the `Eₙ` diagram is simply laced. -/
theorem eChain_transpose (n : ℕ) : (eChain n)ᵀ = eChain n := by
  ext i j
  simp only [transpose_apply, eChain_apply, eq_comm (a := j)]
  split_ifs <;> omega

/-- The relabelling of the `Eₙ` nodes **from chain order to Bourbaki order**. It fixes `0`, sends
the last node `n - 1` to `1`, and sends every other node `k` to `k + 1`; with `1`-based labels it
is `(1, 2, 3, …, n - 1, n) ↦ (1, 3, 4, …, n, 2)`. -/
def eChainEquiv (n : ℕ) : Fin n ≃ Fin n where
  toFun c := ⟨if c.val = 0 then 0 else if c.val + 1 = n then 1 else c.val + 1, by
    split_ifs <;> omega⟩
  invFun b := ⟨if b.val = 0 then 0 else if b.val = 1 then n - 1 else b.val - 1, by
    split_ifs <;> omega⟩
  left_inv c := Fin.ext <| by grind
  right_inv b := Fin.ext <| by grind

/-- The value of `CartanMatrix.eChainEquiv`: the Bourbaki label of a chain label. -/
lemma eChainEquiv_apply_val {n : ℕ} (c : Fin n) :
    (eChainEquiv n c : ℕ) = if c.val = 0 then 0 else if c.val + 1 = n then 1 else c.val + 1 :=
  (rfl)

/-- The value of the inverse of `CartanMatrix.eChainEquiv`: the chain label of a Bourbaki
label. -/
lemma eChainEquiv_symm_apply_val {n : ℕ} (b : Fin n) :
    ((eChainEquiv n).symm b : ℕ) =
      if b.val = 0 then 0 else if b.val = 1 then n - 1 else b.val - 1 :=
  (rfl)

/-- **Relabelling the Bourbaki-numbered `Eₙ` Cartan matrix into chain order**, entrywise: the
Cartan integer of two chain labels is the Bourbaki Cartan integer of their Bourbaki labels. -/
@[simp]
theorem E_eChainEquiv_apply (n : ℕ) (i j : Fin n) :
    E n (eChainEquiv n i) (eChainEquiv n j) = eChain n i j := by
  have hi := eChainEquiv_apply_val i
  have hj := eChainEquiv_apply_val j
  simp only [E, of_apply, eChain_apply, Fin.ext_iff]
  generalize eChainEquiv n i = x at hi ⊢
  generalize eChainEquiv n j = y at hj ⊢
  have := i.isLt
  have := j.isLt
  split_ifs at hi hj ⊢ <;> omega

/-- **Relabelling the Bourbaki-numbered `Eₙ` Cartan matrix into chain order** gives the chain-order
Cartan matrix. -/
@[simp]
theorem E_submatrix_eChainEquiv (n : ℕ) :
    (E n).submatrix (eChainEquiv n) (eChainEquiv n) = eChain n := by
  ext i j
  exact E_eChainEquiv_apply n i j

/-- The Cartan matrix of type `E₆` in chain order: the chain `0 — 1 — 2 — 3 — 4` with node `5`
attached to node `2`. -/
lemma eChain_six_eq :
    eChain 6 = !![ 2, -1,  0,  0,  0,  0;
                  -1,  2, -1,  0,  0,  0;
                   0, -1,  2, -1,  0, -1;
                   0,  0, -1,  2, -1,  0;
                   0,  0,  0, -1,  2,  0;
                   0,  0, -1,  0,  0,  2] := by decide

/-- The Cartan matrix of type `E₇` in chain order: the chain `0 — 1 — ⋯ — 5` with node `6`
attached to node `2`. -/
lemma eChain_seven_eq :
    eChain 7 = !![ 2, -1,  0,  0,  0,  0,  0;
                  -1,  2, -1,  0,  0,  0,  0;
                   0, -1,  2, -1,  0,  0, -1;
                   0,  0, -1,  2, -1,  0,  0;
                   0,  0,  0, -1,  2, -1,  0;
                   0,  0,  0,  0, -1,  2,  0;
                   0,  0, -1,  0,  0,  0,  2] := by decide

/-- The Cartan matrix of type `E₈` in chain order: the chain `0 — 1 — ⋯ — 6` with node `7`
attached to node `2`. -/
lemma eChain_eight_eq :
    eChain 8 = !![ 2, -1,  0,  0,  0,  0,  0,  0;
                  -1,  2, -1,  0,  0,  0,  0,  0;
                   0, -1,  2, -1,  0,  0,  0, -1;
                   0,  0, -1,  2, -1,  0,  0,  0;
                   0,  0,  0, -1,  2, -1,  0,  0;
                   0,  0,  0,  0, -1,  2, -1,  0;
                   0,  0,  0,  0,  0, -1,  2,  0;
                   0,  0, -1,  0,  0,  0,  0,  2] := by decide

end CartanMatrix

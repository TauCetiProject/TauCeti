/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Block.Congruence

/-!
# Checks: two-block congruence subgroups

For two blocks, ranked by `Sum.isRight`, `P(J, K)` consists of the `(A B; C D)` with `C ≡ 0`
modulo `K` and `A ≡ 1`, `D ≡ 1` modulo `J`. With `J = ⊤` the diagonal blocks and the upper-right
block are arbitrary. For `GL₂` over `ZMod 9` and the ideal `(3)`, whose residue field is `𝔽₃`, the
level `P((3), (3))` contains the upper unipotent `(1 1; 0 1)` but not the lower unipotent
`(1 0; 1 1)`, and the diagonal matrix `diag(2, 1)` lies in `P(⊤, (3))` but not in `P((3), (3))`,
since `2 ≢ 1` modulo `3`.
-/

public section

open Matrix

namespace TauCeti.Examples.BlockCongruenceSubgroup

/-- With `J = ⊤`, every invertible block upper triangular matrix lies in `P(⊤, K)`: its diagonal
blocks and its upper-right block are arbitrary. -/
example {R : Type*} [CommRing R] {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n]
    [DecidableEq n] (K : Ideal R) (g : GL (m ⊕ n) R)
    (h : (g : Matrix (m ⊕ n) (m ⊕ n) R).toBlocks₂₁ = 0) :
    g ∈ blockCongruenceSubgroup Sum.isRight ⊤ K := by
  rw [mem_blockCongruenceSubgroup_isRight_iff le_top]
  simp [h]

/-- The upper unipotent `(1 1; 0 1)` lies in `P((3), (3))` over `ZMod 9`. -/
example : GeneralLinearGroup.mk'' (fromBlocks 1 1 0 1 : Matrix (Unit ⊕ Unit) (Unit ⊕ Unit) (ZMod 9))
    (by simp) ∈
      blockCongruenceSubgroup Sum.isRight (Ideal.span {3}) (Ideal.span {3}) := by
  rw [mem_blockCongruenceSubgroup_isRight_iff le_rfl]
  simp

/-- The lower unipotent `(1 0; 1 1)` does not lie in `P((3), (3))` over `ZMod 9`. -/
example : GeneralLinearGroup.mk'' (fromBlocks 1 0 1 1 : Matrix (Unit ⊕ Unit) (Unit ⊕ Unit) (ZMod 9))
    (by simp) ∉
      blockCongruenceSubgroup Sum.isRight (Ideal.span {3}) (Ideal.span {3}) := by
  rw [mem_blockCongruenceSubgroup_isRight_iff le_rfl]
  simpa [Ideal.mem_span_singleton'] using (by decide : ¬ ∃ a : ZMod 9, a * 3 = 1)

/-- `diag(2, 1)` lies in the Siegel parahoric `P(⊤, (3))` over `ZMod 9`. -/
example : GeneralLinearGroup.mk''
    (fromBlocks (diagonal fun _ ↦ 2) 0 0 1 : Matrix (Unit ⊕ Unit) (Unit ⊕ Unit) (ZMod 9))
    (by simpa using (Units.mk (2 : ZMod 9) 5 (by decide) (by decide)).isUnit) ∈
      blockCongruenceSubgroup Sum.isRight ⊤ (Ideal.span {3}) := by
  rw [mem_blockCongruenceSubgroup_isRight_iff le_top]
  simp

/-- `diag(2, 1)` does not lie in `P((3), (3))` over `ZMod 9`, since `2 - 1 = 1 ∉ (3)`. -/
example : GeneralLinearGroup.mk''
    (fromBlocks (diagonal fun _ ↦ 2) 0 0 1 : Matrix (Unit ⊕ Unit) (Unit ⊕ Unit) (ZMod 9))
    (by simpa using (Units.mk (2 : ZMod 9) 5 (by decide) (by decide)).isUnit) ∉
      blockCongruenceSubgroup Sum.isRight (Ideal.span {3}) (Ideal.span {3}) := by
  rw [mem_blockCongruenceSubgroup_isRight_iff le_rfl]
  simpa [Ideal.mem_span_singleton'] using (by decide : ¬ ∃ a : ZMod 9, a * 3 = 2 - 1)

end TauCeti.Examples.BlockCongruenceSubgroup

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Intertwining
public import TauCeti.GroupTheory.Perm.Coxeter
public import Mathlib.LinearAlgebra.Matrix.Permutation

/-!
# Words in the adjacent transpositions, as permutation matrices

The product `(0 1) (1 2) ⋯ (n-1 n)` of the adjacent transpositions of `Fin (n + 1)` is the rotation
`finRotate (n + 1)` (`TauCeti.permCoxeterSystem_wordProd_finRange`). Hence a (possibly rectangular)
matrix `E` that intertwines each letter `f i` of a word with the permutation matrix of `(i i+1)`
intertwines the product of the word with the permutation matrix of `finRotate (n + 1)`:

* `Matrix.mul_prod_map_finRange_eq_permMatrixHom_finRotate_mul`: the word `f 0 * ⋯ * f (n - 1)`.
* `Matrix.mul_prod_map_finRange_succ_eq_permMatrixHom_finRotate_mul_mul`: the word
  `f 0 * ⋯ * f n` whose last letter `f n` is intertwined with an arbitrary matrix `L`. This is the
  shape of the Coxeter elements of types `Bₙ` and `Dₙ` in their `ε`-models.
-/

public section

namespace Matrix

variable {n : ℕ} {k R : Type*} [Fintype k] [DecidableEq k] [Semiring R]

/-- If `E` intertwines each `f i` with the permutation matrix of the adjacent transposition
`(i i+1)`, then it intertwines the product `f 0 * f 1 * ⋯ * f (n - 1)` with the permutation matrix
of their product, the rotation `finRotate (n + 1)` (`TauCeti.permCoxeterSystem_wordProd_finRange`).
-/
theorem mul_prod_map_finRange_eq_permMatrixHom_finRotate_mul {E : Matrix (Fin (n + 1)) k R}
    {f : Fin n → Matrix k k R}
    (h : ∀ i,
      E * f i = permMatrixHom (R := R) (TauCeti.BraidGroup.transposition (n := n + 1) i) * E) :
    E * ((List.finRange n).map f).prod = permMatrixHom (R := R) (finRotate (n + 1)) * E := by
  rw [mul_prod_map_eq_prod_map_mul h]
  refine congrArg (· * E) ?_
  rw [← TauCeti.permCoxeterSystem_wordProd_finRange, TauCeti.permCoxeterSystem_wordProd,
    map_list_prod, List.map_map, Function.comp_def]
  -- the two sides differ only in the index type `Fin (n + 1 - 1)`, which reduces to `Fin n`
  rfl

/-- If `E` intertwines `f i` with the permutation matrix of the transposition `(i i+1)` for every
`i < n`, and the last letter `f n` with `L`, then it intertwines the product `f 0 * ⋯ * f n` with
the rotation `finRotate (n + 1)` followed by `L`. -/
theorem mul_prod_map_finRange_succ_eq_permMatrixHom_finRotate_mul_mul
    {E : Matrix (Fin (n + 1)) k R} {f : Fin (n + 1) → Matrix k k R}
    {L : Matrix (Fin (n + 1)) (Fin (n + 1)) R}
    (h : ∀ (i : Fin (n + 1)) (hi : i.val + 1 < n + 1),
      E * f i = permMatrixHom (R := R) (Equiv.swap i ⟨i.val + 1, hi⟩) * E)
    (hlast : E * f (Fin.last n) = L * E) :
    E * ((List.finRange (n + 1)).map f).prod =
      (permMatrixHom (R := R) (finRotate (n + 1)) * L) * E := by
  have hswap : ∀ i : Fin n, E * f i.castSucc =
      permMatrixHom (R := R) (TauCeti.BraidGroup.transposition (n := n + 1) i) * E := fun i => by
    rw [h i.castSucc (by simp), TauCeti.BraidGroup.transposition_eq_swap_castSucc_succ,
      show (⟨i.castSucc.val + 1, by simp⟩ : Fin (n + 1)) = i.succ from Fin.ext (by simp)]
  rw [List.finRange_succ_last]
  simp only [List.map_append, List.prod_append, List.map_map, Function.comp_def, List.map_cons,
    List.map_nil, List.prod_cons, List.prod_nil, Matrix.mul_one, ← Matrix.mul_assoc,
    mul_prod_map_finRange_eq_permMatrixHom_finRotate_mul hswap]
  simp only [Matrix.mul_assoc, hlast]

end Matrix

end

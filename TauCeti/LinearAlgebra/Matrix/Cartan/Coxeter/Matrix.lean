/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Coxeter.Matrix

/-!
# The Coxeter matrix of an integral Cartan matrix

Given any integral square matrix `A : Matrix I I ℤ`, `TauCeti.cartanCoxeterMatrix A` constructs a
`CoxeterMatrix I` without requiring finiteness of `I`, diagonal entries equal to `2`, or any
upper bound on the off-diagonal Cartan products `aᵢⱼ aⱼᵢ`:

* on the diagonal, `mᵢᵢ = 1`;
* off the diagonal, `mᵢⱼ = 2, 3, 4, 6` when `aᵢⱼ aⱼᵢ = 0, 1, 2, 3` respectively (via
  `TauCeti.coxeterOrder`), and `mᵢⱼ = 0` (Mathlib's encoding of `∞`) otherwise — in particular
  when `aᵢⱼ aⱼᵢ ≥ 4`, as for affine `A₁⁽¹⁾` and indefinite generalized Cartan matrices.

This generalizes `TauCeti.coxeterMatrixOfCartanMatrix` from finite crystallographic matrices
(whose off-diagonal products lie in `{0, 1, 2, 3}`) to arbitrary integral matrices, agreeing with
it whenever those hypotheses hold (`TauCeti.cartanCoxeterMatrix_eq_coxeterMatrixOfCartanMatrix`).
It supplies the Coxeter matrix for the Weyl group presentation of a Cartan realization.

## Main definitions

* `TauCeti.cartanCoxeterMatrix`: the Kac–Moody Coxeter matrix attached to an integral matrix `A`.

## Main results

* `TauCeti.cartanCoxeterMatrix_apply`, `TauCeti.cartanCoxeterMatrix_self`,
  `TauCeti.cartanCoxeterMatrix_of_ne`, `TauCeti.cartanCoxeterMatrix_of_ne_of_le`,
  `TauCeti.cartanCoxeterMatrix_of_ne_of_lt`: entry formulas for `cartanCoxeterMatrix`.
* `TauCeti.cartanCoxeterMatrix_eq_coxeterMatrixOfCartanMatrix`: agreement with
  `TauCeti.coxeterMatrixOfCartanMatrix` when `A` has diagonal `2` and off-diagonal products in
  `{0, 1, 2, 3}`.
* `TauCeti.cartanCoxeterMatrix_B_two` and `TauCeti.cartanCoxeterMatrix_affine_A_one`: evaluations
  on the `B₂` Cartan matrix (`m₀₁ = 4`) and the affine `A₁⁽¹⁾` Cartan matrix (`m₀₁ = 0`).

## References

* V. G. Kac, *Infinite-dimensional Lie algebras*, third edition, Cambridge University Press, 1990,
  §§3.7 and 3.13.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4–6*, Ch. VI, §1.3.
-/

public section

namespace TauCeti

/-- **The Coxeter matrix attached to an integral Cartan matrix.** On the diagonal the entry is `1`.
Off the diagonal it translates the Cartan product `aᵢⱼ aⱼᵢ` into `2, 3, 4, 6` when
`aᵢⱼ aⱼᵢ = 0, 1, 2, 3` (`TauCeti.coxeterOrder`), and into `0` (Mathlib's encoding of an infinite
order) otherwise — in particular when `aᵢⱼ aⱼᵢ = 4` at two distinct nodes, as in affine `A₁⁽¹⁾`. -/
noncomputable def cartanCoxeterMatrix {I : Type*} (A : Matrix I I ℤ) : CoxeterMatrix I := by
  classical
  exact
    { M := Matrix.of fun i j ↦
        if i = j then 1
        else if A i j * A j i ≤ 3 then coxeterOrder (A i j * A j i) else 0
      isSymm := Matrix.IsSymm.ext fun i j ↦ by
        simp only [Matrix.of_apply, eq_comm (a := i), mul_comm (A i j)]
      diagonal i := by simp
      off_diagonal i j hij := by
        simp only [Matrix.of_apply, hij, ↓reduceIte]
        split_ifs with hle
        · rcases lt_or_ge (A i j * A j i) 0 with hlt | hge
          · have h0 : coxeterOrder (A i j * A j i) = 0 := coxeterOrder_eq_zero_iff.mpr <| by
              simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; omega
            omega
          · have hmem : A i j * A j i ∈ ({0, 1, 2, 3} : Set ℤ) := by
              simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; omega
            have := two_le_coxeterOrder hmem
            omega
        · decide }

/-- Unfolded entry formula for `TauCeti.cartanCoxeterMatrix`. -/
theorem cartanCoxeterMatrix_apply {I : Type*} [DecidableEq I] (A : Matrix I I ℤ) (i j : I) :
    cartanCoxeterMatrix A i j =
      if i = j then 1
      else if A i j * A j i ≤ 3 then coxeterOrder (A i j * A j i) else 0 := by
  -- Reconcile the classical `DecidableEq` inside `cartanCoxeterMatrix` with the caller's instance.
  change (letI := Classical.decEq I;
    if i = j then 1 else if A i j * A j i ≤ 3 then coxeterOrder (A i j * A j i) else 0) = _
  congr 1

/-- Every diagonal entry of `cartanCoxeterMatrix A` is `1`. -/
theorem cartanCoxeterMatrix_self {I : Type*} (A : Matrix I I ℤ) (i : I) :
    cartanCoxeterMatrix A i i = 1 :=
  (cartanCoxeterMatrix A).diagonal i

/-- Off-diagonal entry formula for `cartanCoxeterMatrix`. -/
theorem cartanCoxeterMatrix_of_ne {I : Type*} (A : Matrix I I ℤ) {i j : I} (hij : i ≠ j) :
    cartanCoxeterMatrix A i j =
      if A i j * A j i ≤ 3 then coxeterOrder (A i j * A j i) else 0 := by
  classical simp [cartanCoxeterMatrix_apply, hij]

/-- Off-diagonal entry of `cartanCoxeterMatrix` when `aᵢⱼ aⱼᵢ ≤ 3`. -/
@[simp]
theorem cartanCoxeterMatrix_of_ne_of_le {I : Type*} (A : Matrix I I ℤ) {i j : I} (hij : i ≠ j)
    (h : A i j * A j i ≤ 3) : cartanCoxeterMatrix A i j = coxeterOrder (A i j * A j i) := by
  simp [cartanCoxeterMatrix_of_ne A hij, h]

/-- Off-diagonal entry of `cartanCoxeterMatrix` when `aᵢⱼ aⱼᵢ > 3` (`0`, encoding `∞`). -/
@[simp]
theorem cartanCoxeterMatrix_of_ne_of_lt {I : Type*} (A : Matrix I I ℤ) {i j : I} (hij : i ≠ j)
    (h : 3 < A i j * A j i) : cartanCoxeterMatrix A i j = 0 := by
  simp [cartanCoxeterMatrix_of_ne A hij, not_le.mpr h]

/-- When all off-diagonal Cartan products lie in `{0, 1, 2, 3}`, `cartanCoxeterMatrix` agrees with
`coxeterMatrixOfCartanMatrix`. -/
theorem cartanCoxeterMatrix_eq_coxeterMatrixOfCartanMatrix {I : Type*} (A : Matrix I I ℤ)
    (hdiag : ∀ i, A i i = 2)
    (hmem : ∀ i j, i ≠ j → A i j * A j i ∈ ({0, 1, 2, 3} : Set ℤ)) :
    cartanCoxeterMatrix A = coxeterMatrixOfCartanMatrix A hdiag hmem := by
  ext i j
  rcases eq_or_ne i j with rfl | hij
  · simp
  · have hle : A i j * A j i ≤ 3 := by
      have := hmem i j hij
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this; omega
    rw [cartanCoxeterMatrix_of_ne_of_le A hij hle, coxeterMatrixOfCartanMatrix_apply]

/-- **Type `B₂` Coxeter entry**: `a₀₁ a₁₀ = (-2)(-1) = 2`, so `m₀₁ = 4` (not `3`). -/
@[simp]
theorem cartanCoxeterMatrix_B_two : cartanCoxeterMatrix (CartanMatrix.B 2) 0 1 = 4 := by
  have hprod : CartanMatrix.B 2 0 1 * CartanMatrix.B 2 1 0 = 2 := by
    rw [CartanMatrix.B_two]; decide
  rw [cartanCoxeterMatrix_of_ne_of_le (CartanMatrix.B 2) (by decide) (by omega), hprod,
    coxeterOrder_two]

/-- **Affine `A₁⁽¹⁾` Coxeter entry**: for `A = !![2, -2; -2, 2]`, `a₀₁ a₁₀ = 4`, so `m₀₁ = 0`
(encoding `∞`). -/
@[simp]
theorem cartanCoxeterMatrix_affine_A_one :
    cartanCoxeterMatrix !![(2 : ℤ), -2; -2, 2] 0 1 = 0 :=
  cartanCoxeterMatrix_of_ne_of_lt !![(2 : ℤ), -2; -2, 2] (by decide) (by decide)

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Perm.Cycle.Factors
public import TauCeti.LinearAlgebra.Matrix.NormTwoShell.Basic
import TauCeti.GroupTheory.Perm.Basic
import TauCeti.LinearAlgebra.Matrix.Submatrix
import TauCeti.LinearAlgebra.Matrix.Symmetric

/-!
# The folded Cartan matrix of a diagram automorphism

Let `B : Matrix I I ℤ` be positive definite with diagonal entries `2` and nonpositive off-diagonal
entries, the Cartan matrix of a simply laced Dynkin diagram, possibly disconnected, and let
`σ : Equiv.Perm I` be a diagram automorphism, `B.reindex σ σ = B`. For a `σ`-orbit `O` of
vertices, an element of `Quotient (Equiv.Perm.SameCycle.setoid σ)`, put

`d_O = ∑_{i ∈ O} B i i₀`  for `i₀ ∈ O`,  and  `c_O = 2 / d_O`.

The column sum `d_O` does not depend on `i₀ ∈ O`. The induced graph on `O` is regular of degree
`2 - d_O`, and positive definiteness of `B` at the orbit sum `∑_{i ∈ O} αᵢ` forces
`d_O ∈ {1, 2}`, so `c_O ∈ {2, 1}` is an integer with `c_O d_O = 2`. The folded Cartan matrix,
with rows `O` and columns `P`, is

`C_{O,P} = c_O ∑_{i ∈ O} B i j`  for `j ∈ P`,

which does not depend on the choice of `j ∈ P`. It has diagonal entries `2` and nonpositive
off-diagonal entries.

The file also proves the orbit string bound behind the higher Serre relations of the folded
frame: if `α_j + ∑_{i ∈ O} sᵢ αᵢ` has norm two for some `s ≥ 0` and `j ∉ O`, then
`∑_{i ∈ O} sᵢ ≤ -c_O ∑_{i ∈ O} B i j`. The Laplacian bound `Matrix.IsSymm.mul_sum_sq_le` turns
the norm-two condition into `∑ sᵢ² ≤ c_O ∑ sᵢ (-B i j)`, and an elementary termwise inequality
gives the claim.

## Main definitions

* `Matrix.foldingScale B σ O`: the scale `c_O = 2 / d_O`.
* `Matrix.foldedCartanMatrix B σ`: the folded Cartan matrix `C`.

## Main results

* `Matrix.sum_apply_eq_of_sameCycle`: column sums over an orbit are constant along `σ`-cycles.
* `Matrix.sum_eq_one_or_eq_two`: `d_O ∈ {1, 2}`.
* `Matrix.foldingScale_mul_sum`, `Matrix.foldingScale_pos`,
  `Matrix.foldingScale_eq_one_or_eq_two`: `c_O d_O = 2`, `c_O > 0` and `c_O ∈ {1, 2}`.
* `Matrix.foldingScale_eq_of_sameCycle`: `c_O` may be computed at any `i₀ ∈ O`.
* `Matrix.foldedCartanMatrix_apply_of_sameCycle`: `C_{O,P}` may be computed at any `j ∈ P`.
* `Matrix.foldedCartanMatrix_apply_self`, `Matrix.foldedCartanMatrix_nonpos`: `C` has diagonal
  entries `2` and nonpositive off-diagonal entries.
* `Matrix.IsSymm.sum_le_of_mem_normTwoShell`: the orbit string bound.

## References

* V. G. Kac, *Infinite dimensional Lie algebras*, third edition, Cambridge University Press (1990),
  §7.9, for the fixed points of a diagram automorphism and the folded generators.
-/

public section

open Finset

namespace Matrix

/-! ### The folded Cartan matrix -/

section CartanMatrix

variable {I : Type*} [Fintype I] [DecidableEq I] (B : Matrix I I ℤ) (σ : Equiv.Perm I)

/-- The folding scale `c_O = 2 / d_O` of a `σ`-orbit `O` of vertices, where
`d_O = ∑_{i ∈ O} B i i₀` is computed at the representative `i₀ = O.out`. When `B` is positive
definite with diagonal entries `2`, nonpositive off-diagonal entries, and invariant under `σ`, the
column sum `d_O` is `1` or `2` (`Matrix.sum_eq_one_or_eq_two`) and any `i₀ ∈ O` gives the same
value (`Matrix.foldingScale_eq_of_sameCycle`). -/
noncomputable def foldingScale (O : Quotient (Equiv.Perm.SameCycle.setoid σ)) : ℤ :=
  2 / ∑ i with σ.SameCycle i O.out, B i O.out

theorem foldingScale_def (O : Quotient (Equiv.Perm.SameCycle.setoid σ)) :
    B.foldingScale σ O = 2 / ∑ i with σ.SameCycle i O.out, B i O.out :=
  (rfl)

/-- The folded Cartan matrix of a diagram automorphism `σ` of `B`, indexed by the `σ`-orbits of
vertices, with `H` rows and `E` columns: `C_{O,P} = c_O ∑_{i ∈ O} B i j`, computed at the
representative `j = P.out`. For a `σ`-invariant `B`, any `j ∈ P` gives the same value
(`Matrix.foldedCartanMatrix_apply_of_sameCycle`). -/
noncomputable def foldedCartanMatrix :
    Matrix (Quotient (Equiv.Perm.SameCycle.setoid σ)) (Quotient (Equiv.Perm.SameCycle.setoid σ))
      ℤ :=
  fun O P ↦ B.foldingScale σ O * ∑ i with σ.SameCycle i O.out, B i P.out

theorem foldedCartanMatrix_apply (O P : Quotient (Equiv.Perm.SameCycle.setoid σ)) :
    B.foldedCartanMatrix σ O P = B.foldingScale σ O * ∑ i with σ.SameCycle i O.out, B i P.out :=
  (rfl)

variable {B σ}

/-- For a `σ`-invariant `B`, the column sums over an orbit are constant along `σ`-cycles. -/
theorem sum_apply_eq_of_sameCycle (hσ : B.reindex σ σ = B)
    (O : Quotient (Equiv.Perm.SameCycle.setoid σ)) {j j' : I} (h : σ.SameCycle j j') :
    ∑ i with σ.SameCycle i O.out, B i j = ∑ i with σ.SameCycle i O.out, B i j' := by
  obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
  clear h
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ih, pow_succ', Equiv.Perm.mul_apply]
    exact (sum_congr rfl fun i _ ↦ (apply_apply_of_reindex_eq hσ i _).symm).trans
      (σ.sum_filter_sameCycle_comp O.out (B · (σ ((σ ^ n) j))))

/-- The folded Cartan matrix may be computed at any vertex `j` of the column orbit `P`. -/
theorem foldedCartanMatrix_apply_of_sameCycle (hσ : B.reindex σ σ = B)
    (O : Quotient (Equiv.Perm.SameCycle.setoid σ)) {P : Quotient (Equiv.Perm.SameCycle.setoid σ)}
    {j : I} (hj : σ.SameCycle j P.out) :
    B.foldedCartanMatrix σ O P = B.foldingScale σ O * ∑ i with σ.SameCycle i O.out, B i j := by
  rw [foldedCartanMatrix_apply, sum_apply_eq_of_sameCycle hσ O hj]

/-- The folding scale may be computed at any vertex `i₀` of the orbit `O`. -/
theorem foldingScale_eq_of_sameCycle (hσ : B.reindex σ σ = B)
    {O : Quotient (Equiv.Perm.SameCycle.setoid σ)} {i₀ : I} (hi₀ : σ.SameCycle i₀ O.out) :
    B.foldingScale σ O = 2 / ∑ i with σ.SameCycle i O.out, B i i₀ := by
  rw [foldingScale_def, sum_apply_eq_of_sameCycle hσ O hi₀]

/-- For a symmetric `σ`-invariant `B`, the row sums over an orbit `O` at a vertex of `O` are
`d_O`. -/
theorem sum_apply_eq_of_sameCycle_out (hB : B.IsSymm) (hσ : B.reindex σ σ = B)
    {O : Quotient (Equiv.Perm.SameCycle.setoid σ)} {i : I} (hi : σ.SameCycle i O.out) :
    ∑ i' with σ.SameCycle i' O.out, B i i' = ∑ i' with σ.SameCycle i' O.out, B i' O.out := by
  rw [← sum_apply_eq_of_sameCycle hσ O hi]
  exact sum_congr rfl fun i' _ ↦ hB.apply i' i

/-- For positive definite `σ`-invariant `B` with diagonal entries `2` and nonpositive
off-diagonal entries, the orbit column sum `d_O` is `1` or `2`. The induced graph on `O` is regular
of degree `2 - d_O`, and positive definiteness at the orbit sum `∑_{i ∈ O} αᵢ` gives `d_O > 0`. -/
theorem sum_eq_one_or_eq_two (hB : B.PosDef) (hdiag : ∀ i, B i i = 2)
    (hoff : ∀ i j, i ≠ j → B i j ≤ 0) (hσ : B.reindex σ σ = B)
    (O : Quotient (Equiv.Perm.SameCycle.setoid σ)) :
    ∑ i with σ.SameCycle i O.out, B i O.out = 1 ∨ ∑ i with σ.SameCycle i O.out, B i O.out = 2 := by
  set s : Finset I := {i | σ.SameCycle i O.out}
  have hmem : O.out ∈ s := by simpa [s] using Equiv.Perm.SameCycle.refl σ O.out
  -- `d_O ≤ 2`: only the diagonal entry of the column is positive.
  have hle : ∑ i ∈ s, B i O.out ≤ 2 := by
    rw [← add_sum_erase s _ hmem, hdiag]
    have : ∑ i ∈ s.erase O.out, B i O.out ≤ 0 :=
      sum_nonpos fun i hi ↦ hoff i _ (ne_of_mem_erase hi)
    omega
  -- `0 < d_O`: the norm of the orbit sum is `|O| d_O`.
  have hpos : 0 < ∑ i ∈ s, B i O.out := by
    have hne : (∑ i ∈ s, Pi.single i 1 : I → ℤ) ≠ 0 := fun h ↦ by
      simpa [Finset.sum_apply, Pi.single_apply, hmem] using congr_fun h O.out
    have hnorm := hB.dotProduct_mulVec_pos hne
    simp only [star_trivial, sum_dotProduct, dotProduct_sum, mulVec_sum] at hnorm
    have hcol : ∀ i' ∈ s, ∑ i ∈ s, (Pi.single i 1 ⬝ᵥ B *ᵥ Pi.single i' 1 : ℤ) =
        ∑ i ∈ s, B i O.out := fun i' hi' ↦ by
      simpa using sum_apply_eq_of_sameCycle hσ O (by simpa [s] using hi')
    rw [sum_congr rfl hcol, sum_const, nsmul_eq_mul] at hnorm
    exact pos_of_mul_pos_right hnorm (Nat.cast_nonneg _)
  omega

/-- **The folding scale `c_O = 2 / d_O` satisfies `c_O d_O = 2`**, for positive definite
`σ`-invariant `B` with diagonal entries `2` and nonpositive off-diagonal entries: the orbit column
sum `d_O` is `1` or `2`. -/
theorem foldingScale_mul_sum (hB : B.PosDef) (hdiag : ∀ i, B i i = 2)
    (hoff : ∀ i j, i ≠ j → B i j ≤ 0) (hσ : B.reindex σ σ = B)
    (O : Quotient (Equiv.Perm.SameCycle.setoid σ)) :
    B.foldingScale σ O * ∑ i with σ.SameCycle i O.out, B i O.out = 2 := by
  rw [foldingScale_def]
  rcases sum_eq_one_or_eq_two hB hdiag hoff hσ O with h | h <;> rw [h] <;> norm_num

/-- The folding scale `c_O` is `1` or `2`. -/
theorem foldingScale_eq_one_or_eq_two (hB : B.PosDef) (hdiag : ∀ i, B i i = 2)
    (hoff : ∀ i j, i ≠ j → B i j ≤ 0) (hσ : B.reindex σ σ = B)
    (O : Quotient (Equiv.Perm.SameCycle.setoid σ)) :
    B.foldingScale σ O = 1 ∨ B.foldingScale σ O = 2 := by
  rw [foldingScale_def]
  rcases sum_eq_one_or_eq_two hB hdiag hoff hσ O with h | h <;> rw [h] <;> norm_num

/-- The folding scale `c_O` is positive. -/
theorem foldingScale_pos (hB : B.PosDef) (hdiag : ∀ i, B i i = 2)
    (hoff : ∀ i j, i ≠ j → B i j ≤ 0) (hσ : B.reindex σ σ = B)
    (O : Quotient (Equiv.Perm.SameCycle.setoid σ)) : 0 < B.foldingScale σ O := by
  rcases foldingScale_eq_one_or_eq_two hB hdiag hoff hσ O with h | h <;> rw [h] <;> norm_num

/-- **The diagonal entries of the folded Cartan matrix are `2`.** -/
theorem foldedCartanMatrix_apply_self (hB : B.PosDef) (hdiag : ∀ i, B i i = 2)
    (hoff : ∀ i j, i ≠ j → B i j ≤ 0) (hσ : B.reindex σ σ = B)
    (O : Quotient (Equiv.Perm.SameCycle.setoid σ)) : B.foldedCartanMatrix σ O O = 2 :=
  foldingScale_mul_sum hB hdiag hoff hσ O

/-- **The off-diagonal entries of the folded Cartan matrix are nonpositive.** -/
theorem foldedCartanMatrix_nonpos (hB : B.PosDef) (hdiag : ∀ i, B i i = 2)
    (hoff : ∀ i j, i ≠ j → B i j ≤ 0) (hσ : B.reindex σ σ = B)
    {O P : Quotient (Equiv.Perm.SameCycle.setoid σ)} (hOP : O ≠ P) :
    B.foldedCartanMatrix σ O P ≤ 0 :=
  mul_nonpos_of_nonneg_of_nonpos (foldingScale_pos hB hdiag hoff hσ O).le <|
    sum_nonpos fun i hi ↦ hoff i _ <|
      Equiv.Perm.ne_of_sameCycle_out (by simpa using hi) (Equiv.Perm.SameCycle.refl σ P.out) hOP

end CartanMatrix

/-! ### The orbit string bound -/

variable {I : Type*} [Fintype I] [DecidableEq I] {B : Matrix I I ℤ}

/-- **The orbit string bound.** Let `O` be a set of vertices on which the row sums of a symmetric
`B` with nonpositive off-diagonal entries are a constant `d` with `c d = 2` for some `c > 0`, and
let `j ∉ O` be a vertex with `B j j = 2` and `B i j ≥ -1` for `i ∈ O`. If `α_j + ∑_{i ∈ O} sᵢ αᵢ`
has norm two for some `s ≥ 0`, then `∑_{i ∈ O} sᵢ ≤ -c ∑_{i ∈ O} B i j`. -/
theorem IsSymm.sum_le_of_mem_normTwoShell (hB : B.IsSymm) (hoff : ∀ i j, i ≠ j → B i j ≤ 0)
    {O : Finset I} {j : I} (hj : j ∉ O) (hjj : B j j = 2) {c d : ℤ} (hcd : c * d = 2)
    (hc : 0 < c) (hrow : ∀ i ∈ O, ∑ i' ∈ O, B i i' = d) (hcol : ∀ i ∈ O, -1 ≤ B i j)
    {s : I → ℤ} (hs : ∀ i ∈ O, 0 ≤ s i)
    (hmem : Pi.single j 1 + ∑ i ∈ O, s i • Pi.single i 1 ∈ B.normTwoShell) :
    ∑ i ∈ O, s i ≤ c * -∑ i ∈ O, B i j := by
  rw [mem_normTwoShell, IsSymm.add_dotProduct_mulVec_add hB] at hmem
  have e1 : (Pi.single j 1 : I → ℤ) ⬝ᵥ B *ᵥ Pi.single j 1 = 2 := by simp [hjj]
  have e2 : (Pi.single j 1 : I → ℤ) ⬝ᵥ B *ᵥ ∑ i ∈ O, s i • Pi.single i 1 =
      ∑ i ∈ O, s i * B i j := by
    simp only [mulVec_sum, mulVec_smul, dotProduct_sum, dotProduct_smul, smul_eq_mul]
    exact sum_congr rfl fun i _ ↦ by simp [hB.apply i j]
  have e3 : (∑ i ∈ O, s i • Pi.single i 1 : I → ℤ) ⬝ᵥ B *ᵥ ∑ i ∈ O, s i • Pi.single i 1 =
      ∑ i ∈ O, ∑ i' ∈ O, s i * B i i' * s i' := by
    simp only [mulVec_sum, mulVec_smul, dotProduct_sum, sum_dotProduct, dotProduct_smul,
      smul_dotProduct, smul_eq_mul, mul_sum]
    refine sum_comm.trans (sum_congr rfl fun i _ ↦ sum_congr rfl fun i' _ ↦ ?_)
    simp only [mulVec_single, MulOpposite.op_one, one_smul, single_dotProduct, col_apply, one_mul]
    ring
  rw [e1, e2, e3] at hmem
  have hquad := mul_le_mul_of_nonneg_left (hB.mul_sum_sq_le hoff hrow s) hc.le
  rw [← mul_assoc, hcd] at hquad
  have hc12 : c = 1 ∨ c = 2 := by
    have : 0 < d := by nlinarith
    have : c ≤ 2 := by nlinarith
    omega
  -- Termwise, `sᵢ ≤ sᵢ² + c wᵢ - c wᵢ sᵢ` for `wᵢ = -B i j ∈ {0, 1}`.
  have hterm : ∑ i ∈ O, s i ≤ ∑ i ∈ O, (s i ^ 2 + c * -B i j + c * (s i * B i j)) :=
    sum_le_sum fun i hi ↦ by
      have h1 := hcol i hi
      have h2 := hoff i j (ne_of_mem_of_not_mem hi hj)
      have h3 := hs i hi
      rcases (by omega : B i j = 0 ∨ B i j = -1) with h | h <;> rw [h] <;>
        rcases (by omega : s i = 0 ∨ s i = 1 ∨ 2 ≤ s i) with h' | h' | h' <;>
        rcases hc12 with rfl | rfl <;> nlinarith
  simp only [sum_add_distrib, ← mul_sum, sum_neg_distrib] at hterm
  nlinarith

end Matrix

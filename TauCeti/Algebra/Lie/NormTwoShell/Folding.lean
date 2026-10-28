/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Perm.Cycle.Factors
public import TauCeti.Algebra.Lie.NormTwoShell.Reindex
public import TauCeti.Algebra.Lie.NormTwoShell.Serre
import TauCeti.LinearAlgebra.Matrix.Symmetric

/-!
# The folded Chevalley frame of a diagram automorphism

Let `B : Matrix I I ℤ` be positive definite with diagonal entries `2` and nonpositive off-diagonal
entries, the Cartan matrix of a simply laced Dynkin diagram, possibly disconnected, and let
`σ : Equiv.Perm I` be a diagram automorphism, `B.reindex σ σ = B`. For a `σ`-orbit `O` of
vertices, an element of `Quotient (Equiv.Perm.SameCycle.setoid σ)`, put

`d_O = ∑_{i ∈ O} B i i₀`  for `i₀ ∈ O`,  and  `c_O = 2 / d_O`.

The induced graph on `O` is regular of degree `2 - d_O`, and positive definiteness of `B` at the
orbit sum `∑_{i ∈ O} αᵢ` forces `d_O ∈ {1, 2}`, so `c_O ∈ {2, 1}` is an integer
(`Matrix.foldingScale_mul_sum`). In the signed shell Lie algebra `Matrix.ShellLieAlgebra B`, with
Chevalley generators `Hᵢ`, `Eᵢ`, `Fᵢ`, the folded frame is

`H'_O = c_O ∑_{i ∈ O} Hᵢ`,  `E'_O = ∑_{i ∈ O} Eᵢ`,  `F'_O = c_O ∑_{i ∈ O} Fᵢ`,

and the folded Cartan matrix, with `H` rows and `E` columns, is

`C_{O,P} = c_O ∑_{i ∈ O} B i j`  for `j ∈ P`,

which does not depend on the choice of `j ∈ P`. It has diagonal entries `2` and nonpositive
off-diagonal entries. The main result (`Matrix.ShellLieAlgebra.isSerreSystem_folded`) is that the
folded frame is a Serre system for `C`, so that `TauCeti.serreLift` maps the Serre presentation of
`C` over `ℤ` to `Matrix.ShellLieAlgebra B`. The frame is fixed by the pinned action
`Matrix.ShellLieAlgebra.reindex σ` of the diagram automorphism, hence so is the image of that map
(`Matrix.ShellLieAlgebra.reindex_serreLift_folded`).

All relations except the higher Serre relations follow from those of the Chevalley generators
by bilinearity. For the higher relations between distinct orbits `O ≠ P`, every term of
`(ad E'_O) ^ (1 - C_{O,P}) E'_P` lies in the root space of a vector
`α_j + ∑_{i ∈ O} sᵢ αᵢ` with `j ∈ P`, `sᵢ ≥ 0` and `∑ sᵢ = 1 - C_{O,P}`. Such a vector is never a
root: by the Laplacian identity `∑_{i, i' ∈ O} B i i' (sᵢ - sᵢ')² = 2 (d_O ∑ sᵢ² - s ⬝ B s)`,
the norm-two condition forces `∑ sᵢ² ≤ c_O ∑ sᵢ (-B i j)`, and hence `∑ sᵢ ≤ -c_O ∑ B i j`,
which is `-C_{O,P}`. No division by `2` or `3` occurs, and the argument does not distinguish the
cases of orbits of size one, two or three.

## Main definitions

* `Matrix.foldingScale B σ O`: the scale `c_O = 2 / d_O`.
* `Matrix.foldedCartanMatrix B σ`: the folded Cartan matrix `C`.
* `Matrix.ShellLieAlgebra.foldedH`, `Matrix.ShellLieAlgebra.foldedE`,
  `Matrix.ShellLieAlgebra.foldedF`: the folded frame `H'_O`, `E'_O`, `F'_O`.

## Main results

* `Matrix.foldingScale_mul_sum`: `c_O d_O = 2`.
* `Matrix.foldedCartanMatrix_apply_of_sameCycle`: `C_{O,P}` may be computed at any `j ∈ P`.
* `Matrix.foldedCartanMatrix_apply_self`, `Matrix.foldedCartanMatrix_nonpos`: `C` has diagonal
  entries `2` and nonpositive off-diagonal entries.
* `Matrix.ShellLieAlgebra.isSerreSystem_folded`: the folded frame is a Serre system for `C`.
* `Matrix.ShellLieAlgebra.reindex_foldedH`, `Matrix.ShellLieAlgebra.reindex_foldedE`,
  `Matrix.ShellLieAlgebra.reindex_foldedF`: the folded frame is fixed by the pinned action of `σ`.
* `Matrix.ShellLieAlgebra.reindex_serreLift_folded`: so is the image of the Serre presentation.

## References

* V. G. Kac, *Infinite dimensional Lie algebras*, third edition, Cambridge University Press (1990),
  §7.9, for the fixed points of a diagram automorphism and the folded generators.
-/

public section

open Finset LieAlgebra TauCeti

namespace Matrix

/-! ### The folded Cartan matrix -/

section CartanMatrix

variable {I : Type*} [Fintype I] [DecidableEq I] (B : Matrix I I ℤ) (σ : Equiv.Perm I)

/-- The folding scale `c_O = 2 / d_O` of a `σ`-orbit `O` of vertices, where
`d_O = ∑_{i ∈ O} B i i₀` is computed at the representative `i₀ = O.out`. When `B` is positive
definite with diagonal entries `2`, nonpositive off-diagonal entries, and invariant under `σ`, the
column sum `d_O` is `1` or `2` (`Matrix.foldingScale_mul_sum`). -/
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

omit [Fintype I] [DecidableEq I] in
/-- A `σ`-invariant matrix has the same entries at `(σ a, σ b)` and at `(a, b)`. -/
private theorem apply_apply_of_reindex_eq (hσ : B.reindex σ σ = B) (a b : I) :
    B (σ a) (σ b) = B a b := by
  simpa using (congrFun₂ hσ (σ a) (σ b)).symm

omit [Fintype I] [DecidableEq I] in
/-- Points of distinct orbits are distinct. -/
private theorem ne_of_sameCycle_out {i i' : I} {O P : Quotient (Equiv.Perm.SameCycle.setoid σ)}
    (hi : σ.SameCycle i O.out) (hi' : σ.SameCycle i' P.out) (hOP : O ≠ P) : i ≠ i' := by
  rintro rfl
  have h (P : Quotient (Equiv.Perm.SameCycle.setoid σ)) (hP : σ.SameCycle i P.out) :
      Quotient.mk _ i = P :=
    Quotient.mk_eq_iff_out.mpr hP
  exact hOP ((h O hi).symm.trans (h P hi'))

/-- For a `σ`-invariant `B`, the column sums over an orbit are constant along `σ`-cycles. -/
private theorem sum_apply_eq_of_sameCycle (hσ : B.reindex σ σ = B)
    (O : Quotient (Equiv.Perm.SameCycle.setoid σ)) {j j' : I} (h : σ.SameCycle j j') :
    ∑ i with σ.SameCycle i O.out, B i j = ∑ i with σ.SameCycle i O.out, B i j' := by
  obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
  clear h
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ih, pow_succ', Equiv.Perm.mul_apply]
    exact sum_equiv σ (fun i ↦ by simp [Equiv.Perm.sameCycle_apply_left])
      fun i _ ↦ (apply_apply_of_reindex_eq hσ i _).symm

/-- The folded Cartan matrix may be computed at any vertex `j` of the column orbit `P`. -/
theorem foldedCartanMatrix_apply_of_sameCycle (hσ : B.reindex σ σ = B)
    (O : Quotient (Equiv.Perm.SameCycle.setoid σ)) {P : Quotient (Equiv.Perm.SameCycle.setoid σ)}
    {j : I} (hj : σ.SameCycle j P.out) :
    B.foldedCartanMatrix σ O P = B.foldingScale σ O * ∑ i with σ.SameCycle i O.out, B i j := by
  rw [foldedCartanMatrix_apply, sum_apply_eq_of_sameCycle hσ O hj]

/-- For a `σ`-invariant `B`, the row sums over an orbit `O` at a vertex of `O` are `d_O`. -/
private theorem sum_apply_eq_of_sameCycle_out (hB : B.IsSymm) (hσ : B.reindex σ σ = B)
    {O : Quotient (Equiv.Perm.SameCycle.setoid σ)} {i : I} (hi : σ.SameCycle i O.out) :
    ∑ i' with σ.SameCycle i' O.out, B i i' = ∑ i' with σ.SameCycle i' O.out, B i' O.out := by
  rw [← sum_apply_eq_of_sameCycle hσ O hi]
  exact sum_congr rfl fun i' _ ↦ hB.apply i' i

/-- For positive definite `σ`-invariant `B` with diagonal entries `2` and nonpositive
off-diagonal entries, the orbit column sum `d_O` is `1` or `2`. The induced graph on `O` is regular
of degree `2 - d_O`, and positive definiteness at the orbit sum `∑_{i ∈ O} αᵢ` gives `d_O > 0`. -/
private theorem sum_eq_one_or_eq_two (hB : B.PosDef) (hdiag : ∀ i, B i i = 2)
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

/-- The folding scale `c_O` is positive. -/
private theorem foldingScale_pos (hB : B.PosDef) (hdiag : ∀ i, B i i = 2)
    (hoff : ∀ i j, i ≠ j → B i j ≤ 0) (hσ : B.reindex σ σ = B)
    (O : Quotient (Equiv.Perm.SameCycle.setoid σ)) : 0 < B.foldingScale σ O := by
  rw [foldingScale_def]
  rcases sum_eq_one_or_eq_two hB hdiag hoff hσ O with h | h <;> rw [h] <;> norm_num

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
      ne_of_sameCycle_out (by simpa using hi) (Equiv.Perm.SameCycle.refl σ P.out) hOP

end CartanMatrix

/-! ### Orbit strings are not roots -/

section Strings

variable {I : Type*} [Fintype I] [DecidableEq I] {B : Matrix I I ℤ}

omit [DecidableEq I] in
/-- `ζ` times a root, for a sign `ζ`, is a root. -/
private theorem smul_mem_normTwoShell {ζ : ℤ} (hζ : ζ * ζ = 1) {a : I → ℤ}
    (ha : a ∈ B.normTwoShell) : ζ • a ∈ B.normTwoShell := by
  rw [mem_normTwoShell] at ha ⊢
  simp only [mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, ← mul_assoc, hζ, one_mul,
    ha]

omit [Fintype I] [DecidableEq I] in
/-- With constant row sums `d` on `O` and nonpositive off-diagonal entries, a symmetric `B`
satisfies `d ∑_{i ∈ O} sᵢ² ≤ ∑_{i, i' ∈ O} sᵢ B i i' sᵢ'`. The difference is half of
`-∑_{i, i' ∈ O} B i i' (sᵢ - sᵢ')²`. -/
private theorem mul_sum_sq_le (hB : B.IsSymm) (hoff : ∀ i j, i ≠ j → B i j ≤ 0) {O : Finset I}
    {d : ℤ} (hrow : ∀ i ∈ O, ∑ i' ∈ O, B i i' = d) (s : I → ℤ) :
    d * ∑ i ∈ O, s i ^ 2 ≤ ∑ i ∈ O, ∑ i' ∈ O, s i * B i i' * s i' := by
  have h1 : ∑ i ∈ O, ∑ i' ∈ O, B i i' * s i ^ 2 = d * ∑ i ∈ O, s i ^ 2 := by
    rw [mul_sum]
    exact sum_congr rfl fun i hi ↦ by rw [← sum_mul, hrow i hi]
  have h2 : ∑ i ∈ O, ∑ i' ∈ O, B i i' * s i' ^ 2 = d * ∑ i ∈ O, s i ^ 2 := by
    rw [sum_comm, mul_sum]
    refine sum_congr rfl fun i' hi' ↦ ?_
    rw [← sum_mul, ← hrow i' hi']
    exact congrArg (· * _) (sum_congr rfl fun i _ ↦ hB.apply i' i)
  have hexp : ∑ i ∈ O, ∑ i' ∈ O, B i i' * (s i - s i') ^ 2 =
      2 * (d * ∑ i ∈ O, s i ^ 2) - 2 * ∑ i ∈ O, ∑ i' ∈ O, s i * B i i' * s i' := by
    calc _ = ∑ i ∈ O, ∑ i' ∈ O,
          (B i i' * s i ^ 2 + B i i' * s i' ^ 2 - 2 * (s i * B i i' * s i')) :=
          sum_congr rfl fun i _ ↦ sum_congr rfl fun i' _ ↦ by ring
      _ = _ := by simp only [sum_sub_distrib, sum_add_distrib, ← mul_sum, h1, h2]; ring
  have hnonpos : ∑ i ∈ O, ∑ i' ∈ O, B i i' * (s i - s i') ^ 2 ≤ 0 :=
    sum_nonpos fun i _ ↦ sum_nonpos fun i' _ ↦ by
      rcases eq_or_ne i i' with rfl | h
      · simp
      · exact mul_nonpos_of_nonpos_of_nonneg (hoff i i' h) (sq_nonneg _)
  linarith

/-- **The orbit string bound.** Let `O` be a set of vertices on which the row sums of `B` are
a constant `d` with `c d = 2` for some `c > 0`, and let `j ∉ O` be a vertex with `B j j = 2` and
`B i j ≥ -1` for `i ∈ O`. If `α_j + ∑_{i ∈ O} sᵢ αᵢ` has norm two for some `s ≥ 0`, then
`∑_{i ∈ O} sᵢ ≤ -c ∑_{i ∈ O} B i j`. -/
private theorem sum_le_of_mem_normTwoShell (hB : B.IsSymm) (hoff : ∀ i j, i ≠ j → B i j ≤ 0)
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
    simp
    ring
  rw [e1, e2, e3] at hmem
  have hquad := mul_le_mul_of_nonneg_left (mul_sum_sq_le hB hoff hrow s) hc.le
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

/-- An orbit string of `O` at `j` of length `n`: the vector `α_j + ∑_{i ∈ O} sᵢ αᵢ` for some
`s ≥ 0` with `∑_{i ∈ O} sᵢ = n`. -/
private def IsString (O : Finset I) (j : I) (n : ℤ) (v : I → ℤ) : Prop :=
  ∃ s : I → ℤ, (∀ i ∈ O, 0 ≤ s i) ∧ ∑ i ∈ O, s i = n ∧
    v = Pi.single j 1 + ∑ i ∈ O, s i • Pi.single i 1

omit [Fintype I] in
private theorem isString_single (O : Finset I) (j : I) : IsString O j 0 (Pi.single j 1) :=
  ⟨0, by simp, by simp, by simp⟩

omit [Fintype I] in
private theorem IsString.single_add {O : Finset I} {j : I} {n : ℤ} {v : I → ℤ}
    (h : IsString O j n v) {i : I} (hi : i ∈ O) : IsString O j (n + 1) (Pi.single i 1 + v) := by
  obtain ⟨s, hs, hsum, rfl⟩ := h
  refine ⟨s + Pi.single i 1, fun i' hi' ↦ ?_, ?_, ?_⟩
  · have := hs i' hi'
    rcases eq_or_ne i' i with rfl | h
    · simp only [Pi.add_apply, Pi.single_eq_same]
      omega
    · simpa [h] using this
  · simp [sum_add_distrib, hsum, Pi.single_apply, hi]
  · have hsingle : ∑ i' ∈ O, (Pi.single i 1 : I → ℤ) i' • (Pi.single i' 1 : I → ℤ) =
        Pi.single i 1 := by
      rw [sum_eq_single i (fun i' _ h ↦ by simp [h]) (fun h ↦ (h hi).elim)]
      simp
    simp only [Pi.add_apply, add_smul, sum_add_distrib, hsingle]
    abel

omit [Fintype I] in
private theorem IsString.apply_self {O : Finset I} {j : I} {n : ℤ} {v : I → ℤ}
    (h : IsString O j n v) (hj : j ∉ O) : v j = 1 := by
  obtain ⟨s, -, -, rfl⟩ := h
  simp only [Pi.add_apply, Pi.single_eq_same, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    add_eq_left]
  exact sum_eq_zero fun i hi ↦ by simp [ne_of_mem_of_not_mem hi hj]

/-- An orbit string of length `1 - c ∑_{i ∈ O} B i j` is not a root. -/
private theorem IsString.notMem_normTwoShell (hB : B.IsSymm) (hoff : ∀ i j, i ≠ j → B i j ≤ 0)
    {O : Finset I} {j : I} (hj : j ∉ O) (hjj : B j j = 2) {c d : ℤ} (hcd : c * d = 2)
    (hc : 0 < c) (hrow : ∀ i ∈ O, ∑ i' ∈ O, B i i' = d) (hcol : ∀ i ∈ O, -1 ≤ B i j)
    {v : I → ℤ} (h : IsString O j (c * -∑ i ∈ O, B i j + 1) v) : v ∉ B.normTwoShell := by
  obtain ⟨s, hs, hsum, rfl⟩ := h
  intro hmem
  have := sum_le_of_mem_normTwoShell hB hoff hj hjj hcd hc hrow hcol hs hmem
  omega

end Strings

/-! ### The folded frame -/

namespace ShellLieAlgebra

variable {I : Type*} [Fintype I] [LinearOrder I] {B : Matrix I I ℤ}

variable (B) in
/-- The folded Cartan vector `H'_O = c_O ∑_{i ∈ O} H_(αᵢ)` of a `σ`-orbit `O` of vertices, with
the folding scale `c_O = Matrix.foldingScale B σ O`. -/
noncomputable def foldedH (σ : Equiv.Perm I) (O : Quotient (Equiv.Perm.SameCycle.setoid σ)) :
    ShellLieAlgebra B :=
  B.foldingScale σ O • ∑ i with σ.SameCycle i O.out, cartan B (Pi.single i 1)

variable (B) in
theorem foldedH_def (σ : Equiv.Perm I) (O : Quotient (Equiv.Perm.SameCycle.setoid σ)) :
    foldedH B σ O = B.foldingScale σ O • ∑ i with σ.SameCycle i O.out, cartan B (Pi.single i 1) :=
  (rfl)

/-- The folded raising generator `E'_O = ∑_{i ∈ O} Eᵢ` of a `σ`-orbit `O` of vertices. -/
noncomputable def foldedE (hdiag : ∀ i, B i i = 2) (σ : Equiv.Perm I)
    (O : Quotient (Equiv.Perm.SameCycle.setoid σ)) : ShellLieAlgebra B :=
  ∑ i with σ.SameCycle i O.out, chevalleyE B hdiag i

theorem foldedE_def (hdiag : ∀ i, B i i = 2) (σ : Equiv.Perm I)
    (O : Quotient (Equiv.Perm.SameCycle.setoid σ)) :
    foldedE hdiag σ O = ∑ i with σ.SameCycle i O.out, chevalleyE B hdiag i :=
  (rfl)

/-- The folded lowering generator `F'_O = c_O ∑_{i ∈ O} Fᵢ` of a `σ`-orbit `O` of vertices, with
the folding scale `c_O = Matrix.foldingScale B σ O`. -/
noncomputable def foldedF (hdiag : ∀ i, B i i = 2) (σ : Equiv.Perm I)
    (O : Quotient (Equiv.Perm.SameCycle.setoid σ)) : ShellLieAlgebra B :=
  B.foldingScale σ O • ∑ i with σ.SameCycle i O.out, chevalleyF B hdiag i

theorem foldedF_def (hdiag : ∀ i, B i i = 2) (σ : Equiv.Perm I)
    (O : Quotient (Equiv.Perm.SameCycle.setoid σ)) :
    foldedF hdiag σ O = B.foldingScale σ O • ∑ i with σ.SameCycle i O.out, chevalleyF B hdiag i :=
  (rfl)

/-- **Root-space grading of iterated brackets.** For a sign `ζ` and roots `rᵢ = ζ αᵢ`, with
`X = ∑_{i ∈ O} x_(rᵢ)` and `j ∉ O`, the vector `(ad X) ^ n x_(r_j)` is a combination of root
vectors `x_c` with `ζ c` an orbit string of `O` at `j` of length `n`. -/
private theorem ad_pow_root_mem_span (hB : B.PosDef) (hdiag : ∀ i, B i i = 2) {ζ : ℤ}
    (hζ : ζ * ζ = 1) {r : I → B.normTwoShell} (hr : ∀ i, (r i : I → ℤ) = ζ • Pi.single i 1)
    {O : Finset I} {j : I} (hj : j ∉ O) (n : ℕ) :
    letI := lieRing hB fun i ↦ hdiag i ▸ even_two
    (ad ℤ (ShellLieAlgebra B) (∑ i ∈ O, root B (r i)) ^ n) (root B (r j)) ∈
      Submodule.span ℤ (root B '' {c | IsString O j n (ζ • (c : I → ℤ))}) := by
  let _ := lieRing hB fun i ↦ hdiag i ▸ even_two
  have hsmul (i : I) (c : I → ℤ) : ζ • ((r i : I → ℤ) + c) = Pi.single i 1 + ζ • c := by
    rw [hr, smul_add, smul_smul, hζ, one_smul]
  -- One bracket with `X` raises the length of the strings by one.
  have step (m : ℤ) : Submodule.span ℤ (root B '' {c | IsString O j m (ζ • (c : I → ℤ))}) ≤
      (Submodule.span ℤ (root B '' {c | IsString O j (m + 1) (ζ • (c : I → ℤ))})).comap
        (ad ℤ (ShellLieAlgebra B) (∑ i ∈ O, root B (r i))) := by
    rw [Submodule.span_le]
    rintro _ ⟨c, hc, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap, ad_apply, sum_lie, root_lie_root]
    refine Submodule.sum_mem _ fun i hi ↦ ?_
    have hc' : IsString O j (m + 1) (ζ • ((r i : I → ℤ) + c)) := by
      rw [hsmul]
      exact hc.single_add hi
    by_cases h1 : (r i : I → ℤ) + c ∈ B.normTwoShell
    · rw [rootBracket_of_mem h1]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨_, h1⟩, hc', rfl⟩)
    · have h2 : (r i : I → ℤ) + c ≠ 0 := fun h ↦ by
        simpa [h] using hc'.apply_self hj
      rw [rootBracket_of_notMem_of_add_ne_zero h1 h2]
      exact zero_mem _
  induction n with
  | zero =>
    refine Submodule.subset_span ⟨r j, ?_, by simp⟩
    rw [Set.mem_ofPred_eq, Nat.cast_zero, hr, smul_smul, hζ, one_smul]
    exact isString_single O j
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, Nat.cast_succ]
    exact step n ih

/-- **The folded higher Serre relation.** For a sign `ζ` and roots `rᵢ = ζ αᵢ`, with
`X = ∑_{i ∈ O} x_(rᵢ)` and `j ∉ O`, if the row sums of `B` on `O` are a constant `d` with `c d = 2`
for some `c > 0`, then `(ad X) ^ (1 - c ∑_{i ∈ O} B i j) x_(r_j) = 0`. -/
private theorem ad_pow_root_eq_zero (hB : B.PosDef) (hdiag : ∀ i, B i i = 2)
    (hoff : ∀ i j, i ≠ j → B i j ≤ 0) {ζ : ℤ} (hζ : ζ * ζ = 1) {r : I → B.normTwoShell}
    (hr : ∀ i, (r i : I → ℤ) = ζ • Pi.single i 1) {O : Finset I} {j : I} (hj : j ∉ O)
    {c d : ℤ} (hcd : c * d = 2) (hc : 0 < c) (hrow : ∀ i ∈ O, ∑ i' ∈ O, B i i' = d) {n : ℕ}
    (hn : (n : ℤ) = c * -∑ i ∈ O, B i j + 1) :
    letI := lieRing hB fun i ↦ hdiag i ▸ even_two
    (ad ℤ (ShellLieAlgebra B) (∑ i ∈ O, root B (r i)) ^ n) (root B (r j)) = 0 := by
  have h := ad_pow_root_mem_span hB hdiag hζ hr hj n
  have hempty : {c : B.normTwoShell | IsString O j n (ζ • (c : I → ℤ))} = ∅ := by
    -- Distinct simple roots pair to at least `-1`.
    have hcol (i : I) (hi : i ∈ O) : -1 ≤ B i j := by
      have hij : i ≠ j := ne_of_mem_of_not_mem hi hj
      simpa using hB.neg_one_le_dotProduct_mulVec (fun i ↦ hdiag i ▸ even_two)
        (single_mem_normTwoShell (hdiag i)) (single_mem_normTwoShell (hdiag j))
        fun h ↦ by simpa [hij] using congr_fun h i
    refine Set.eq_empty_of_forall_notMem fun x hx ↦ ?_
    rw [Set.mem_ofPred_eq, hn] at hx
    exact hx.notMem_normTwoShell hB.isHermitian.isSymm hoff hj (hdiag j) hcd hc hrow hcol
      (smul_mem_normTwoShell hζ x.2)
  rwa [hempty, Set.image_empty, Submodule.span_empty, Submodule.mem_bot] at h

/-- The higher Serre relation between distinct orbits `O ≠ P`, for the folded sums of the roots
`rᵢ = ζ αᵢ` attached to a sign `ζ`. -/
private theorem ad_pow_lie_sum_root_eq_zero {σ : Equiv.Perm I} (hB : B.PosDef)
    (hdiag : ∀ i, B i i = 2) (hoff : ∀ i j, i ≠ j → B i j ≤ 0) (hσ : B.reindex σ σ = B)
    {ζ : ℤ} (hζ : ζ * ζ = 1) {r : I → B.normTwoShell} (hr : ∀ i, (r i : I → ℤ) = ζ • Pi.single i 1)
    {O P : Quotient (Equiv.Perm.SameCycle.setoid σ)} (hOP : O ≠ P) :
    letI := lieRing hB fun i ↦ hdiag i ▸ even_two
    (ad ℤ (ShellLieAlgebra B) (∑ i with σ.SameCycle i O.out, root B (r i)) ^
        (-B.foldedCartanMatrix σ O P).toNat)
      ⁅∑ i with σ.SameCycle i O.out, root B (r i), ∑ j with σ.SameCycle j P.out, root B (r j)⁆ =
      0 := by
  let _ := lieRing hB fun i ↦ hdiag i ▸ even_two
  have hm : 0 ≤ -B.foldedCartanMatrix σ O P :=
    neg_nonneg.mpr (foldedCartanMatrix_nonpos hB hdiag hoff hσ hOP)
  rw [← ad_apply ℤ, ← Module.End.mul_apply, ← pow_succ, map_sum]
  refine sum_eq_zero fun j hj ↦ ?_
  have hj' : σ.SameCycle j P.out := by simpa using hj
  refine ad_pow_root_eq_zero hB hdiag hoff hζ hr
    (fun hjO ↦ ne_of_sameCycle_out (by simpa using hjO) hj' hOP rfl)
    (foldingScale_mul_sum hB hdiag hoff hσ O) (foldingScale_pos hB hdiag hoff hσ O)
    (fun i hi ↦ sum_apply_eq_of_sameCycle_out hB.isHermitian.isSymm hσ (by simpa using hi)) ?_
  rw [Nat.cast_succ, Int.toNat_of_nonneg hm, foldedCartanMatrix_apply_of_sameCycle hσ O hj']
  ring

/-- **The folded frame is a Serre system for the folded Cartan matrix.** For a positive definite
`B` with diagonal entries `2` and nonpositive off-diagonal entries, and a diagram automorphism `σ`
of `B`, the vectors `H'_O = c_O ∑_{i ∈ O} Hᵢ`, `E'_O = ∑_{i ∈ O} Eᵢ` and `F'_O = c_O ∑_{i ∈ O} Fᵢ`
of `Matrix.ShellLieAlgebra B`, indexed by the `σ`-orbits `O`, satisfy Serre's relations for
`Matrix.foldedCartanMatrix B σ`. -/
theorem isSerreSystem_folded (σ : Equiv.Perm I) (hB : B.PosDef)
    (hdiag : ∀ i, B i i = 2) (hoff : ∀ i j, i ≠ j → B i j ≤ 0) (hσ : B.reindex σ σ = B) :
    letI := lieRing hB fun i ↦ hdiag i ▸ even_two
    IsSerreSystem ℤ (B.foldedCartanMatrix σ) (foldedH B σ) (foldedE hdiag σ) (foldedF hdiag σ) := by
  let _ := lieRing hB fun i ↦ hdiag i ▸ even_two
  have h := isSerreSystem hB hdiag hoff
  have hHE : ∀ i j, ⁅cartan B (Pi.single i 1), chevalleyE B hdiag j⁆ =
      (1 * B i j) • chevalleyE B hdiag j := fun i j ↦ by rw [one_mul]; exact h.lie_H_E i j
  have hHF : ∀ i j, ⁅cartan B (Pi.single i 1), chevalleyF B hdiag j⁆ =
      (-1 * B i j) • chevalleyF B hdiag j := fun i j ↦ by
    rw [neg_one_mul, neg_smul]; exact h.lie_H_F i j
  have hEF : ∀ i, ⁅chevalleyE B hdiag i, chevalleyF B hdiag i⁆ = cartan B (Pi.single i 1) :=
    h.lie_E_F_self
  have hEF' : ∀ i j, i ≠ j → ⁅chevalleyE B hdiag i, chevalleyF B hdiag j⁆ = 0 :=
    h.lie_E_F_of_ne
  -- The Cartan sum of `O` acts on a folded sum over `P` by the folded column sum.
  have hcartan (O P : Quotient (Equiv.Perm.SameCycle.setoid σ)) (G : I → ShellLieAlgebra B)
      (ε : ℤ) (hG : ∀ i j, ⁅cartan B (Pi.single i 1), G j⁆ = (ε * B i j) • G j) :
      ⁅∑ i with σ.SameCycle i O.out, cartan B (Pi.single i 1), ∑ j with σ.SameCycle j P.out, G j⁆ =
        (ε * ∑ i with σ.SameCycle i O.out, B i P.out) • ∑ j with σ.SameCycle j P.out, G j := by
    calc _ = ∑ i with σ.SameCycle i O.out, ∑ j with σ.SameCycle j P.out, (ε * B i j) • G j := by
          rw [sum_lie]
          simp only [lie_sum, hG]
      _ = ∑ j with σ.SameCycle j P.out, ∑ i with σ.SameCycle i O.out, (ε * B i j) • G j :=
          sum_comm
      _ = ∑ j with σ.SameCycle j P.out, (ε * ∑ i with σ.SameCycle i O.out, B i P.out) • G j :=
          sum_congr rfl fun j hj ↦ by
            rw [← sum_smul, ← mul_sum, sum_apply_eq_of_sameCycle hσ O (by simpa using hj)]
      _ = _ := (smul_sum ..).symm
  refine
    { lie_H_H := fun O P ↦ ?_
      lie_E_F_self := fun O ↦ ?_
      lie_E_F_of_ne := fun O P hOP ↦ ?_
      lie_H_E := fun O P ↦ ?_
      lie_H_F := fun O P ↦ ?_
      ad_pow_lie_E_E := fun O P ↦ ?_
      ad_pow_lie_F_F := fun O P ↦ ?_ }
  · simp [foldedH_def, sum_lie, lie_sum]
  · rw [foldedE_def, foldedF_def, foldedH_def, lie_smul, sum_lie]
    refine congrArg _ (sum_congr rfl fun i hi ↦ ?_)
    rw [lie_sum, sum_eq_single i (fun i' _ hne ↦ hEF' i i' hne.symm) (fun h ↦ (h hi).elim), hEF]
  · rw [foldedE_def, foldedF_def, lie_smul, sum_lie, sum_eq_zero, smul_zero]
    refine fun i hi ↦ (lie_sum ..).trans (sum_eq_zero fun i' hi' ↦ hEF' i i' ?_)
    exact ne_of_sameCycle_out (by simpa using hi) (by simpa using hi') hOP
  · rw [foldedH_def, foldedE_def, smul_lie, hcartan O P _ 1 hHE, foldedCartanMatrix_apply]
    module
  · rw [foldedH_def, foldedF_def, smul_lie, lie_smul, hcartan O P _ (-1) hHF,
      foldedCartanMatrix_apply]
    module
  · rcases eq_or_ne O P with rfl | hOP
    · rw [foldedCartanMatrix_apply_self hB hdiag hoff hσ]
      simp
    · simpa only [foldedE_def, chevalleyE_def] using
        ad_pow_lie_sum_root_eq_zero hB hdiag hoff hσ (ζ := 1) (by norm_num)
          (r := fun i ↦ ⟨Pi.single i 1, single_mem_normTwoShell (hdiag i)⟩) (fun i ↦ by simp) hOP
  · rcases eq_or_ne O P with rfl | hOP
    · rw [foldedCartanMatrix_apply_self hB hdiag hoff hσ]
      simp
    · have key := ad_pow_lie_sum_root_eq_zero hB hdiag hoff hσ (ζ := -1) (by norm_num)
        (r := fun i ↦
          ⟨-Pi.single i 1, neg_mem_normTwoShell.mpr (single_mem_normTwoShell (hdiag i))⟩)
        (fun i ↦ by simp) hOP
      simp only [← chevalleyF_def B hdiag] at key
      simp only [foldedF_def, map_zsmul, smul_pow, LinearMap.smul_apply, smul_lie, lie_smul, key,
        smul_zero]

/-! ### Fixedness under the pinned action -/

/-- The pinned action `Matrix.ShellLieAlgebra.reindex σ` of a diagram automorphism `σ` fixes the
folded Cartan vectors `H'_O`. -/
@[simp]
theorem reindex_foldedH (σ : Equiv.Perm I) (hσ : B.reindex σ σ = B)
    (O : Quotient (Equiv.Perm.SameCycle.setoid σ)) :
    reindex σ hσ (foldedH B σ O) = foldedH B σ O := by
  rw [foldedH_def, map_zsmul, map_sum]
  refine congrArg _ (sum_equiv σ (fun i ↦ by simp [Equiv.Perm.sameCycle_apply_left])
    fun i _ ↦ ?_)
  rw [reindex_cartan, Pi.single_comp_equiv, Equiv.symm_symm]

/-- The pinned action `Matrix.ShellLieAlgebra.reindex σ` of a diagram automorphism `σ` fixes the
folded raising generators `E'_O`. -/
@[simp]
theorem reindex_foldedE (hdiag : ∀ i, B i i = 2) (σ : Equiv.Perm I) (hσ : B.reindex σ σ = B)
    (O : Quotient (Equiv.Perm.SameCycle.setoid σ)) :
    reindex σ hσ (foldedE hdiag σ O) = foldedE hdiag σ O := by
  rw [foldedE_def, map_sum]
  exact sum_equiv σ (fun i ↦ by simp [Equiv.Perm.sameCycle_apply_left])
    fun i _ ↦ by rw [chevalleyE_def, chevalleyE_def]; exact reindex_root_single σ hσ i _ _

/-- The pinned action `Matrix.ShellLieAlgebra.reindex σ` of a diagram automorphism `σ` fixes the
folded lowering generators `F'_O`. -/
@[simp]
theorem reindex_foldedF (hdiag : ∀ i, B i i = 2) (σ : Equiv.Perm I) (hσ : B.reindex σ σ = B)
    (O : Quotient (Equiv.Perm.SameCycle.setoid σ)) :
    reindex σ hσ (foldedF hdiag σ O) = foldedF hdiag σ O := by
  rw [foldedF_def, map_zsmul, map_sum]
  exact congrArg _ (sum_equiv σ (fun i ↦ by simp [Equiv.Perm.sameCycle_apply_left])
    fun i _ ↦ by
      rw [chevalleyF_def, chevalleyF_def]; exact reindex_root_neg_single σ hσ i _ _)

/-- **The image of the folded Serre presentation is fixed by the diagram automorphism.** The
homomorphism `TauCeti.serreLift` from the Serre presentation of `Matrix.foldedCartanMatrix B σ` to
`Matrix.ShellLieAlgebra B` determined by the folded frame lands in the fixed points of the pinned
action `Matrix.ShellLieAlgebra.reindex σ`. -/
theorem reindex_serreLift_folded (σ : Equiv.Perm I)
    [DecidableEq (Quotient (Equiv.Perm.SameCycle.setoid σ))] (hB : B.PosDef)
    (hdiag : ∀ i, B i i = 2) (hoff : ∀ i j, i ≠ j → B i j ≤ 0) (hσ : B.reindex σ σ = B)
    (x : ToLieAlgebra ℤ (B.foldedCartanMatrix σ)) :
    letI := lieRing hB fun i ↦ hdiag i ▸ even_two
    reindex σ hσ (serreLift (isSerreSystem_folded σ hB hdiag hoff hσ) x) =
      serreLift (isSerreSystem_folded σ hB hdiag hoff hσ) x := by
  let _ := lieRing hB fun i ↦ hdiag i ▸ even_two
  have h := isSerreSystem_folded σ hB hdiag hoff hσ
  have hext : (reindexLieEquiv σ hσ hB fun i ↦ hdiag i ▸ even_two).toLieHom.comp (serreLift h) =
      serreLift h :=
    serre_hom_ext (fun O ↦ by simp) (fun O ↦ by simp) fun O ↦ by simp
  simpa using DFunLike.congr_fun hext x

end ShellLieAlgebra

end Matrix

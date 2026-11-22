/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.RingTheory.Polynomial.Chebyshev
public import TauCeti.RingTheory.Polynomial.Hermite.Derivative
import TauCeti.LinearAlgebra.Matrix.CornerMinor

/-!
# Polynomials of a three-term recurrence

Given sequences `α β : ℕ → R` in a commutative ring, the *monic recurrence polynomials* are

  `p₀ = 1`, `p₁ = X - α₀`, `p_{n+2} = (X - α_{n+1}) p_{n+1} - β_{n+1} p_n`,

and the *corecursive polynomials* `p_n^{(0)}` satisfy the same recurrence with the initial values
`p₀^{(0)} = 0`, `p₁^{(0)} = 1`. Every family of monic orthogonal polynomials on the real line is of
the first kind (Favard's theorem is the converse), the corecursive polynomials are the numerators
of the approximants of the associated J-fraction, and the characteristic polynomials of truncated
tridiagonal (Jacobi) matrices are recurrence polynomials. This file develops this algebra over an
arbitrary commutative ring, with no measure in sight; it is the common starting point of the
theory of orthogonal polynomials, of Jacobi matrices and of J-fractions.

## Main definitions

* `Polynomial.monicThreeTerm α β`: the monic polynomials of the three-term recurrence.
* `Polynomial.corecursive α β`: the corecursive polynomials, with `p₀ = 0` and `p₁ = 1`.
* `TauCeti.jacobiMatrix a b c n`: the `n × n` tridiagonal matrix with diagonal `b`, entries `a`
  above the diagonal and `c` below it.

## Main results

* `Polynomial.monic_monicThreeTerm`, `Polynomial.natDegree_monicThreeTerm`: `p_n` is monic of
  degree `n` (the degree statement over a nontrivial ring).
* `Polynomial.map_monicThreeTerm`: the recurrence polynomials commute with ring homomorphisms
  applied to the coefficients.
* `Polynomial.eval_monicThreeTerm_add_two`, `Polynomial.aeval_monicThreeTerm_add_two`: the scalar
  recurrence satisfied by the values `p_n(x)`.
* `Polynomial.corecursive_succ_eq_monicThreeTerm`: the corecursive polynomials are the shifted
  *first associated polynomials*, `p_{n+1}^{(0)} = p_n^{(1)}`, where `p^{(1)}` is the recurrence
  with coefficients `α_{k+1}`, `β_{k+1}`.
* `Polynomial.monicThreeTerm_mul_corecursive_sub_mul_corecursive` and
  `Polynomial.monicThreeTerm_mul_monicThreeTerm_sub_mul_monicThreeTerm`: the Casoratian identity
  `p_n p_{n+1}^{(0)} - p_{n+1} p_n^{(0)} = β₁ ⋯ β_n`, and its form
  `p_{n+1} p_{n+1}^{(1)} - p_{n+2} p_n^{(1)} = β₁ ⋯ β_{n+1}` for the associated polynomials.
* `TauCeti.det_jacobiMatrix_add_two`: the continuant recurrence
  `det J_{n+2} = b_{n+1} det J_{n+1} - a_n c_{n+1} det J_n` of tridiagonal determinants.
* `TauCeti.charpoly_jacobiMatrix`: the characteristic polynomial of `J_n` is the recurrence
  polynomial `p_n` with `α_k = b_k` and `β_k = a_{k-1} c_k`.
* `TauCeti.isSymm_jacobiMatrix_iff`: `J_n` is symmetric iff `c_k = a_{k-1}` for `1 ≤ k < n`.
* `Polynomial.C_two_pow_mul_monicThreeTerm_eq_chebyshev_U` and
  `Polynomial.monicThreeTerm_natCast_eq_map_hermite`: the constant recurrence `α = 0`,
  `β = 1/4` gives the rescaled Chebyshev polynomials of the second kind `2^{-n} U_n`, and `α = 0`,
  `β_k = k` gives the probabilists' Hermite polynomials `He_n`.

## References

* T. S. Chihara, *An Introduction to Orthogonal Polynomials*, Gordon and Breach, 1978, Ch. I, §4
  and Ch. III, §4.
* W. Gautschi, *Orthogonal Polynomials: Computation and Approximation*, Oxford University Press,
  2004, §1.3.
* M. E. H. Ismail, *Classical and Quantum Orthogonal Polynomials in One Variable*, Cambridge
  University Press, 2005, §2.2.
* *NIST Digital Library of Mathematical Functions*, §18.2, equations 18.2.11_5, 18.2.18 and
  18.2.31–18.2.32.
-/

public section

open Finset

namespace Polynomial

variable {R S : Type*} [CommRing R] [CommRing S]

/-! ## The monic recurrence polynomials -/

/-- The monic polynomials of the three-term recurrence with coefficients `α β : ℕ → R`:
`p₀ = 1`, `p₁ = X - α₀` and `p_{n+2} = (X - α_{n+1}) p_{n+1} - β_{n+1} p_n` (DLMF 18.2.11_5).
The coefficient `β₀` is never used. -/
noncomputable def monicThreeTerm (α β : ℕ → R) : ℕ → R[X]
  | 0 => 1
  | 1 => X - C (α 0)
  | n + 2 => (X - C (α (n + 1))) * monicThreeTerm α β (n + 1) - C (β (n + 1)) * monicThreeTerm α β n

variable (α β : ℕ → R)

@[simp]
theorem monicThreeTerm_zero : monicThreeTerm α β 0 = 1 := by
  simp [monicThreeTerm]

@[simp]
theorem monicThreeTerm_one : monicThreeTerm α β 1 = X - C (α 0) := by
  simp [monicThreeTerm]

@[simp]
theorem monicThreeTerm_add_two (n : ℕ) :
    monicThreeTerm α β (n + 2) =
      (X - C (α (n + 1))) * monicThreeTerm α β (n + 1) - C (β (n + 1)) * monicThreeTerm α β n := by
  simp [monicThreeTerm]

theorem monicThreeTerm_two :
    monicThreeTerm α β 2 = (X - C (α 1)) * (X - C (α 0)) - C (β 1) := by
  simp

private theorem monic_monicThreeTerm_and_natDegree [Nontrivial R] (n : ℕ) :
    (monicThreeTerm α β n).Monic ∧ (monicThreeTerm α β n).natDegree = n := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => exact ⟨by simpa using monic_X_sub_C (α 0), by simp⟩
  | more n ih₀ ih₁ =>
    have hm : ((X - C (α (n + 1))) * monicThreeTerm α β (n + 1)).Monic :=
      (monic_X_sub_C _).mul ih₁.1
    have hd : ((X - C (α (n + 1))) * monicThreeTerm α β (n + 1)).natDegree = n + 2 := by
      rw [(monic_X_sub_C _).natDegree_mul ih₁.1, natDegree_X_sub_C, ih₁.2, add_comm]
    have hlt : (C (β (n + 1)) * monicThreeTerm α β n).natDegree <
        ((X - C (α (n + 1))) * monicThreeTerm α β (n + 1)).natDegree := by
      rw [hd]
      exact (natDegree_C_mul_le _ _).trans_lt (by omega)
    rw [monicThreeTerm_add_two]
    exact ⟨hm.sub_of_left (degree_lt_degree hlt),
      (natDegree_sub_eq_left_of_natDegree_lt hlt).trans hd⟩

/-- The recurrence polynomials are monic. Over the zero ring every polynomial is monic, so no
nontriviality assumption is needed. -/
theorem monic_monicThreeTerm (n : ℕ) : (monicThreeTerm α β n).Monic := by
  nontriviality R
  exact (monic_monicThreeTerm_and_natDegree α β n).1

@[simp]
theorem natDegree_monicThreeTerm [Nontrivial R] (n : ℕ) : (monicThreeTerm α β n).natDegree = n :=
  (monic_monicThreeTerm_and_natDegree α β n).2

@[simp]
theorem degree_monicThreeTerm [Nontrivial R] (n : ℕ) : (monicThreeTerm α β n).degree = n := by
  rw [degree_eq_natDegree (monic_monicThreeTerm α β n).ne_zero, natDegree_monicThreeTerm]

@[simp]
theorem leadingCoeff_monicThreeTerm (n : ℕ) : (monicThreeTerm α β n).leadingCoeff = 1 :=
  monic_monicThreeTerm α β n

/-- The recurrence polynomials commute with ring homomorphisms applied to the coefficients. -/
@[simp]
theorem map_monicThreeTerm (f : R →+* S) (n : ℕ) :
    (monicThreeTerm α β n).map f = monicThreeTerm (f ∘ α) (f ∘ β) n := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n ih₀ ih₁ => simp [ih₀, ih₁]

/-- The values of the recurrence polynomials at a point `x` of an `R`-algebra satisfy the scalar
three-term recurrence. -/
theorem aeval_monicThreeTerm_add_two {A : Type*} [Ring A] [Algebra R A] (x : A) (n : ℕ) :
    aeval x (monicThreeTerm α β (n + 2)) =
      (x - algebraMap R A (α (n + 1))) * aeval x (monicThreeTerm α β (n + 1)) -
        algebraMap R A (β (n + 1)) * aeval x (monicThreeTerm α β n) := by
  simp

/-- The values `p_n(x)` of the recurrence polynomials satisfy the scalar three-term recurrence
`p_{n+2}(x) = (x - α_{n+1}) p_{n+1}(x) - β_{n+1} p_n(x)` (DLMF 18.2.11_5). -/
theorem eval_monicThreeTerm_add_two (x : R) (n : ℕ) :
    (monicThreeTerm α β (n + 2)).eval x =
      (x - α (n + 1)) * (monicThreeTerm α β (n + 1)).eval x -
        β (n + 1) * (monicThreeTerm α β n).eval x := by
  simp

/-! ## Corecursive and associated polynomials -/

/-- The corecursive polynomials `p_n^{(0)}` of the three-term recurrence with coefficients
`α β : ℕ → R`: the same recurrence as `Polynomial.monicThreeTerm α β`, with the initial values
`p₀^{(0)} = 0` and `p₁^{(0)} = 1` (DLMF 18.2.32). -/
noncomputable def corecursive (α β : ℕ → R) : ℕ → R[X]
  | 0 => 0
  | 1 => 1
  | n + 2 => (X - C (α (n + 1))) * corecursive α β (n + 1) - C (β (n + 1)) * corecursive α β n

@[simp]
theorem corecursive_zero : corecursive α β 0 = 0 := by
  simp [corecursive]

@[simp]
theorem corecursive_one : corecursive α β 1 = 1 := by
  simp [corecursive]

@[simp]
theorem corecursive_add_two (n : ℕ) :
    corecursive α β (n + 2) =
      (X - C (α (n + 1))) * corecursive α β (n + 1) - C (β (n + 1)) * corecursive α β n := by
  simp [corecursive]

theorem corecursive_two : corecursive α β 2 = X - C (α 1) := by
  simp

/-- The corecursive polynomials commute with ring homomorphisms applied to the coefficients. -/
@[simp]
theorem map_corecursive (f : R →+* S) (n : ℕ) :
    (corecursive α β n).map f = corecursive (f ∘ α) (f ∘ β) n := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n ih₀ ih₁ => simp [ih₀, ih₁]

/-- The corecursive polynomials are the first associated polynomials shifted by one:
`p_{n+1}^{(0)} = p_n^{(1)}`, where `p_n^{(1)} = monicThreeTerm (α ∘ succ) (β ∘ succ) n` is the
recurrence with the coefficients shifted by one (Chihara, Ch. III, (4.3); DLMF 18.2.31–18.2.32). -/
theorem corecursive_succ_eq_monicThreeTerm (n : ℕ) :
    corecursive α β (n + 1) = monicThreeTerm (fun k ↦ α (k + 1)) (fun k ↦ β (k + 1)) n := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n ih₀ ih₁ => rw [corecursive_add_two, ih₀, ih₁, monicThreeTerm_add_two]

/-- **The Casoratian of the recurrence and corecursive polynomials**:
`p_n p_{n+1}^{(0)} - p_{n+1} p_n^{(0)} = β₁ ⋯ β_n` (Chihara, Ch. III, (4.4)). -/
theorem monicThreeTerm_mul_corecursive_sub_mul_corecursive (n : ℕ) :
    monicThreeTerm α β n * corecursive α β (n + 1) -
        monicThreeTerm α β (n + 1) * corecursive α β n =
      C (∏ k ∈ range n, β (k + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [prod_range_succ, C_mul, ← ih, corecursive_add_two, monicThreeTerm_add_two]
    ring

/-- **The Casoratian of the recurrence and first associated polynomials**:
`p_{n+1} p_{n+1}^{(1)} - p_{n+2} p_n^{(1)} = β₁ ⋯ β_{n+1}`, where
`p_n^{(1)} = monicThreeTerm (α ∘ succ) (β ∘ succ) n` (Chihara, Ch. III, (4.4)). -/
theorem monicThreeTerm_mul_monicThreeTerm_sub_mul_monicThreeTerm (n : ℕ) :
    monicThreeTerm α β (n + 1) * monicThreeTerm (fun k ↦ α (k + 1)) (fun k ↦ β (k + 1)) (n + 1) -
        monicThreeTerm α β (n + 2) * monicThreeTerm (fun k ↦ α (k + 1)) (fun k ↦ β (k + 1)) n =
      C (∏ k ∈ range (n + 1), β (k + 1)) := by
  rw [← corecursive_succ_eq_monicThreeTerm, ← corecursive_succ_eq_monicThreeTerm]
  exact monicThreeTerm_mul_corecursive_sub_mul_corecursive α β (n + 1)

/-! ## Chebyshev and Hermite polynomials -/

/-- The constant recurrence `α = 0`, `β = 1/4` gives the Chebyshev polynomials of the second kind,
rescaled to be monic: `2ⁿ p_n = U_n`. -/
theorem C_two_pow_mul_monicThreeTerm_eq_chebyshev_U {b : R} (hb : 4 * b = 1) (n : ℕ) :
    C (2 ^ n : R) * monicThreeTerm 0 (fun _ ↦ b) n = Chebyshev.U R n := by
  have hb' : 4 * C b = 1 := by simpa [C_ofNat] using congrArg C hb
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp [C_ofNat]
  | more n ih₀ ih₁ =>
    push_cast at ih₁ ⊢
    rw [Chebyshev.U_add_two, ← ih₀, ← ih₁, monicThreeTerm_add_two]
    simp only [map_pow, Pi.zero_apply, map_zero, sub_zero, C_ofNat]
    linear_combination (-(2 : R[X]) ^ n * monicThreeTerm 0 (fun _ ↦ b) n) * hb'

/-- The recurrence `α = 0`, `β_k = k` gives the probabilists' Hermite polynomials `He_n`, Mathlib's
`Polynomial.hermite`, mapped to `R`. -/
theorem monicThreeTerm_natCast_eq_map_hermite (n : ℕ) :
    monicThreeTerm 0 Nat.cast n = (hermite n).map (Int.castRingHom R) := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n ih₀ ih₁ =>
    rw [monicThreeTerm_add_two, ih₀, ih₁, hermite_add_two]
    simp [nsmul_eq_mul]

end Polynomial

/-! ## Jacobi matrices -/

namespace TauCeti

open Polynomial

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The truncated Jacobi (tridiagonal) matrix `J_n` with diagonal `b₀, …, b_{n-1}`, entries `a_i`
at `(i, i + 1)` above the diagonal and `c_i` at `(i, i - 1)` below it (DLMF 18.2.18). -/
noncomputable def jacobiMatrix (a b c : ℕ → R) (n : ℕ) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j ↦
    if (j : ℕ) = i then b i else if (j : ℕ) = i + 1 then a i else if (i : ℕ) = j + 1 then c i
    else 0

variable (a b c : ℕ → R)

theorem jacobiMatrix_apply {n : ℕ} (i j : Fin n) :
    jacobiMatrix a b c n i j =
      if (j : ℕ) = i then b i else if (j : ℕ) = i + 1 then a i else if (i : ℕ) = j + 1 then c i
      else 0 :=
  (rfl)

@[simp]
theorem jacobiMatrix_apply_self {n : ℕ} (i : Fin n) : jacobiMatrix a b c n i i = b i := by
  simp [jacobiMatrix_apply]

/-- The entries `a_i` above the diagonal of a Jacobi matrix. -/
theorem jacobiMatrix_apply_superdiag {n : ℕ} {i j : Fin n} (h : (j : ℕ) = i + 1) :
    jacobiMatrix a b c n i j = a i := by
  simp [jacobiMatrix_apply, h]

/-- The entries `c_i` below the diagonal of a Jacobi matrix. -/
theorem jacobiMatrix_apply_subdiag {n : ℕ} {i j : Fin n} (h : (i : ℕ) = j + 1) :
    jacobiMatrix a b c n i j = c i := by
  rw [jacobiMatrix_apply, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left h]

/-- A Jacobi matrix vanishes off the three central diagonals. -/
theorem jacobiMatrix_apply_eq_zero {n : ℕ} {i j : Fin n} (h : (i : ℕ) + 1 < j ∨ (j : ℕ) + 1 < i) :
    jacobiMatrix a b c n i j = 0 := by
  rw [jacobiMatrix_apply, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]

/-- Jacobi matrices commute with ring homomorphisms applied to their entries. -/
@[simp]
theorem jacobiMatrix_map (f : R →+* S) (n : ℕ) :
    (jacobiMatrix a b c n).map f = jacobiMatrix (f ∘ a) (f ∘ b) (f ∘ c) n := by
  ext i j
  simp only [Matrix.map_apply, jacobiMatrix_apply]
  split_ifs <;> simp

/-- A Jacobi matrix `J_n` is symmetric exactly when `c_k = a_{k-1}` for `1 ≤ k < n`. -/
theorem isSymm_jacobiMatrix_iff {n : ℕ} :
    (jacobiMatrix a b c n).IsSymm ↔ ∀ k, 0 < k → k < n → c k = a (k - 1) := by
  refine ⟨fun h k hk hkn ↦ ?_, fun h ↦ Matrix.IsSymm.ext fun i j ↦ ?_⟩
  · have := h.apply (⟨k - 1, by omega⟩ : Fin n) ⟨k, hkn⟩
    rwa [jacobiMatrix_apply_subdiag _ _ _ (by simp only; omega),
      jacobiMatrix_apply_superdiag _ _ _ (by simp only; omega)] at this
  · obtain h₁ | h₁ | h₁ | h₁ : (i : ℕ) = j ∨ (j : ℕ) = i + 1 ∨ (i : ℕ) = j + 1 ∨
        ((i : ℕ) + 1 < j ∨ (j : ℕ) + 1 < i) := by omega
    · rw [Fin.ext h₁]
    · rw [jacobiMatrix_apply_subdiag _ _ _ h₁, jacobiMatrix_apply_superdiag _ _ _ h₁,
        h _ (by omega) j.isLt, h₁, Nat.add_sub_cancel]
    · rw [jacobiMatrix_apply_superdiag _ _ _ h₁, jacobiMatrix_apply_subdiag _ _ _ h₁,
        h _ (by omega) i.isLt, h₁, Nat.add_sub_cancel]
    · rw [jacobiMatrix_apply_eq_zero _ _ _ h₁.symm, jacobiMatrix_apply_eq_zero _ _ _ h₁]

/-- The leading principal `n × n` submatrix of `J_{n+1}` is `J_n`. -/
@[simp]
theorem submatrix_castSucc_jacobiMatrix (n : ℕ) :
    (jacobiMatrix a b c (n + 1)).submatrix Fin.castSucc Fin.castSucc = jacobiMatrix a b c n := by
  ext i j
  simp [jacobiMatrix_apply]

/-- The minor of `J_{n+2}` obtained by deleting the last row and the column `n` is
`a_n det J_n`: expand it along its last column, whose only nonzero entry is `a_n`. -/
private theorem det_submatrix_jacobiMatrix (n : ℕ) :
    ((jacobiMatrix a b c (n + 2)).submatrix Fin.castSucc
      (Fin.last n).castSucc.succAbove).det = a n * (jacobiMatrix a b c n).det := by
  have hcol : (Fin.last n).castSucc.succAbove (Fin.last n) = Fin.last (n + 1) := by
    rw [Fin.succAbove_castSucc_self, Fin.succ_last]
  have hminor : (Fin.last n).castSucc.succAbove ∘ Fin.castSucc = Fin.castSucc ∘ Fin.castSucc :=
    funext fun k ↦ Fin.succAbove_castSucc_of_lt _ _ (Fin.castSucc_lt_last k)
  -- The entries of the last column above the corner `a_n` vanish, and the corner minor is the
  -- leading principal submatrix `J_n`.
  rw [Matrix.det_eq_mul_det_submatrix_castSucc_of_col _ fun i hi ↦ by
      rw [Matrix.submatrix_apply, hcol, jacobiMatrix_apply_eq_zero _ _ _ (Or.inl (by
        simp only [Fin.val_castSucc, Fin.val_last]; exact Nat.succ_lt_succ (Fin.val_lt_last hi)))],
    Matrix.submatrix_apply, hcol, jacobiMatrix_apply_superdiag _ _ _ (by simp),
    Matrix.submatrix_submatrix, hminor, ← Matrix.submatrix_submatrix,
    submatrix_castSucc_jacobiMatrix, submatrix_castSucc_jacobiMatrix, Fin.val_castSucc,
    Fin.val_last]

/-- **The continuant recurrence of tridiagonal determinants**: expanding along the last row,
`det J_{n+2} = b_{n+1} det J_{n+1} - a_n c_{n+1} det J_n`. -/
theorem det_jacobiMatrix_add_two (n : ℕ) :
    (jacobiMatrix a b c (n + 2)).det =
      b (n + 1) * (jacobiMatrix a b c (n + 1)).det -
        a n * c (n + 1) * (jacobiMatrix a b c n).det := by
  have hrow (j : Fin n) : jacobiMatrix a b c (n + 2) (Fin.last (n + 1)) j.castSucc.castSucc = 0 :=
    jacobiMatrix_apply_eq_zero _ _ _ (Or.inr (by simp only [Fin.val_castSucc, Fin.val_last]; omega))
  -- Expand along the last row: only the entries `c_{n+1}` and `b_{n+1}` survive, with the minors
  -- computed by `det_submatrix_jacobiMatrix` and `submatrix_castSucc_jacobiMatrix`.
  rw [Matrix.det_succ_row _ (Fin.last (n + 1)), Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  simp only [hrow, mul_zero, zero_mul, sum_const_zero, zero_add]
  rw [jacobiMatrix_apply_subdiag _ _ _ (by simp), jacobiMatrix_apply_self, Fin.succAbove_last,
    det_submatrix_jacobiMatrix, submatrix_castSucc_jacobiMatrix, Fin.val_last, Fin.val_castSucc,
    Fin.val_last, Odd.neg_one_pow ⟨n, by ring⟩, Even.neg_one_pow ⟨n + 1, rfl⟩]
  ring

/-- The characteristic matrix of a Jacobi matrix is the Jacobi matrix over `R[X]` with diagonal
`X - b_i` and off-diagonal entries `-a_i`, `-c_i`. -/
theorem charmatrix_jacobiMatrix (n : ℕ) :
    (jacobiMatrix a b c n).charmatrix =
      jacobiMatrix (fun k ↦ -C (a k)) (fun k ↦ X - C (b k)) (fun k ↦ -C (c k)) n := by
  ext i j
  by_cases h : i = j
  · subst h
    simp
  · have h' : (j : ℕ) ≠ i := fun h'' ↦ h (Fin.ext h''.symm)
    simp only [Matrix.charmatrix_apply_ne _ _ _ h, jacobiMatrix_apply, h', ↓reduceIte]
    split_ifs <;> simp

/-- **The characteristic polynomial of a Jacobi matrix** is the monic recurrence polynomial with
coefficients `α_k = b_k` and `β_k = a_{k-1} c_k`:
`charpoly J_n = monicThreeTerm b (k ↦ a_{k-1} c_k) n` (Ismail, Theorem 2.2.4; DLMF 18.2.18). -/
theorem charpoly_jacobiMatrix (n : ℕ) :
    (jacobiMatrix a b c n).charpoly = monicThreeTerm b (fun k ↦ a (k - 1) * c k) n := by
  rw [Matrix.charpoly, charmatrix_jacobiMatrix]
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp [Matrix.det_unique]
  | more n ih₀ ih₁ =>
    rw [det_jacobiMatrix_add_two, ih₀, ih₁, monicThreeTerm_add_two]
    simp

end TauCeti

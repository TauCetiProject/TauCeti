/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
public import Mathlib.NumberTheory.LegendreSymbol.ZModChar
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import TauCeti.NumberTheory.DirichletCharacter.Dyadic.Orthogonality
import TauCeti.NumberTheory.DirichletCharacter.Basic
import TauCeti.NumberTheory.DirichletCharacter.Dyadic.Classification

/-!
# The quadratic reciprocity matrix of the characters modulo eight

For positive odd integers `n` and `d` and complex Dirichlet characters `ψ`, `ψ'` of level eight,
consider the coefficient `ψ n * ψ' d * (d / n)` with the Jacobi symbol `(d / n)`. These are the
coefficients of the quadratic double Dirichlet series
`∑_d ψ'(d) d⁻ʷ ∑_n ψ(n) (d / n) n⁻ˢ` over odd `n` and `d`. Interchanging the roles of `n` and `d`
uses quadratic reciprocity `(d / n) = (-1) ^ (((d - 1) / 2) * ((n - 1) / 2)) * (n / d)`. The sign
depends only on the residues of `n` and `d` modulo four, so it can be expanded in the characters
of level eight. The result is the identity

`ψ n * ψ' d * (d / n) = ∑_(ρ, ρ') A (ψ, ψ') (ρ, ρ') * ρ d * ρ' n * (n / d)`,

for the `16 × 16` matrix `A` indexed by pairs of characters of level eight, with entries

`A (ψ, ψ') (ρ, ρ') = 1/16 ∑_(η, ν) ψ ν * ψ' η * ρ η * ρ' ν * ε (η, ν)`,

with the sign `ε (η, ν) = (-1) ^ (((η - 1) / 2) * ((ν - 1) / 2))`, the sum running over the odd
residues `η, ν` modulo eight. Here these residues are written `2 * a + 1` for `a : Fin 4`, so the
sign is `(-1) ^ (a * b)`. The matrix is symmetric and is its own inverse: applying the reciprocity
twice returns the original coefficient.

These are the matrix and the swap identity of Blomer's proof of the meromorphic continuation of
the quadratic double Dirichlet series, where the swap `(s, w) ↦ (w, s)` acts on the vector of
the sixteen series through `A`.

## Main results

* `TauCeti.quadraticReciprocityMatrix`: the matrix `A`.
* `TauCeti.quadraticReciprocityMatrix_transpose`: `Aᵀ = A`.
* `TauCeti.sum_quadraticReciprocityMatrix_mul_apply_mul_apply`: the reciprocity identity on the
  odd residues modulo eight.
* `TauCeti.apply_mul_apply_mul_jacobiSym_eq_sum`: the twisted reciprocity law for the
  coefficients `ψ n * ψ' d * (d / n)` displayed above.
* `TauCeti.quadraticReciprocityMatrix_mul_self`: `A * A = 1`.
* `TauCeti.quadraticReciprocityMatrix_apply_one_one`,
  `TauCeti.quadraticReciprocityMatrix_apply_one_χ₄`: the entries `1/2` and `-1/2` of the row of
  the principal pair, at the principal pair and at the pair of lifts of `ZMod.χ₄`.

## References

V. Blomer, *Subconvexity for a double Dirichlet series*, Compositio Mathematica 147 (2011),
355–374, §2.1, (7)–(11), and §3, (31)–(35).
-/

public section

open Finset DirichletCharacter

namespace TauCeti

/-- The quadratic reciprocity matrix of the characters modulo eight, indexed by pairs of complex
Dirichlet characters of level eight. Its entry at `((ψ, ψ'), (ρ, ρ'))` is
`1/16 ∑_(η, ν) ψ ν * ψ' η * ρ η * ρ' ν * (-1) ^ (((η - 1) / 2) * ((ν - 1) / 2))`, the sum running
over the odd residues `η = 2 * a + 1` and `ν = 2 * b + 1` modulo eight, for `a b : Fin 4`, so that
the sign is `(-1) ^ (a * b)`. -/
noncomputable def quadraticReciprocityMatrix :
    Matrix (DirichletCharacter ℂ 8 × DirichletCharacter ℂ 8)
      (DirichletCharacter ℂ 8 × DirichletCharacter ℂ 8) ℂ :=
  Matrix.of fun p q ↦ 1 / 16 * ∑ a : Fin 4, ∑ b : Fin 4,
    p.1 (2 * (b : ℕ) + 1) * p.2 (2 * (a : ℕ) + 1) * q.1 (2 * (a : ℕ) + 1) *
      q.2 (2 * (b : ℕ) + 1) * (-1) ^ ((a : ℕ) * b)

/-- The entries of the quadratic reciprocity matrix. -/
theorem quadraticReciprocityMatrix_apply (p q : DirichletCharacter ℂ 8 × DirichletCharacter ℂ 8) :
    quadraticReciprocityMatrix p q = 1 / 16 * ∑ a : Fin 4, ∑ b : Fin 4,
      p.1 (2 * (b : ℕ) + 1) * p.2 (2 * (a : ℕ) + 1) * q.1 (2 * (a : ℕ) + 1) *
        q.2 (2 * (b : ℕ) + 1) * (-1) ^ ((a : ℕ) * b) :=
  (rfl)

/-- The quadratic reciprocity matrix is symmetric. -/
@[simp]
theorem quadraticReciprocityMatrix_transpose :
    quadraticReciprocityMatrix.transpose = quadraticReciprocityMatrix := by
  ext p q
  rw [Matrix.transpose_apply, quadraticReciprocityMatrix_apply, quadraticReciprocityMatrix_apply,
    sum_comm]
  congr 1
  refine sum_congr rfl fun a _ ↦ sum_congr rfl fun b _ ↦ ?_
  rw [mul_comm (a : ℕ)]
  ring

/-- **Reciprocity on the odd residues modulo eight.** Summing the reciprocity matrix against the
values `ρ (2 * a + 1) * ρ' (2 * b + 1)` recovers the sign `(-1) ^ (a * b)` times the values of
`ψ` and `ψ'` with the residues interchanged. -/
theorem sum_quadraticReciprocityMatrix_mul_apply_mul_apply
    (ψ ψ' : DirichletCharacter ℂ 8) (a b : Fin 4) :
    ∑ q : DirichletCharacter ℂ 8 × DirichletCharacter ℂ 8,
        quadraticReciprocityMatrix (ψ, ψ') q * (q.1 (2 * (a : ℕ) + 1) * q.2 (2 * (b : ℕ) + 1)) =
      (-1) ^ ((a : ℕ) * b) * ψ (2 * (b : ℕ) + 1) * ψ' (2 * (a : ℕ) + 1) := by
  simp_rw [quadraticReciprocityMatrix_apply, mul_sum, sum_mul]
  rw [sum_comm]
  -- Move the sum over the pair of characters inside, where orthogonality evaluates it.
  rw [Finset.sum_congr rfl fun c _ ↦ sum_comm]
  have key (c e : Fin 4) :
      ∑ q : DirichletCharacter ℂ 8 × DirichletCharacter ℂ 8,
        1 / 16 * (ψ (2 * (e : ℕ) + 1) * ψ' (2 * (c : ℕ) + 1) * q.1 (2 * (c : ℕ) + 1) *
          q.2 (2 * (e : ℕ) + 1) * (-1) ^ ((c : ℕ) * e)) *
          (q.1 (2 * (a : ℕ) + 1) * q.2 (2 * (b : ℕ) + 1)) =
      if c = a then if e = b then
        ψ (2 * (e : ℕ) + 1) * ψ' (2 * (c : ℕ) + 1) * (-1) ^ ((c : ℕ) * e) else 0 else 0 := by
    have horth := congrArg₂ (· * ·) (sum_apply_fin_four_mul_apply_fin_four ℂ c a)
      (sum_apply_fin_four_mul_apply_fin_four ℂ e b)
    rw [sum_mul_sum] at horth
    calc _ = 1 / 16 * (ψ (2 * (e : ℕ) + 1) * ψ' (2 * (c : ℕ) + 1) * (-1) ^ ((c : ℕ) * e)) *
          ∑ ρ : DirichletCharacter ℂ 8, ∑ ρ' : DirichletCharacter ℂ 8,
            ρ (2 * (c : ℕ) + 1) * ρ (2 * (a : ℕ) + 1) *
              (ρ' (2 * (e : ℕ) + 1) * ρ' (2 * (b : ℕ) + 1)) := by
          rw [← Finset.univ_product_univ, sum_product, mul_sum]
          refine sum_congr rfl fun ρ _ ↦ by
            rw [mul_sum]; exact sum_congr rfl fun ρ' _ ↦ by ring
      _ = _ := by
          rw [horth]
          split_ifs <;> ring
  simp_rw [key]
  rw [Fintype.sum_eq_single a fun c hc ↦ by simp [hc],
    Fintype.sum_eq_single b fun e he ↦ by simp [he]]
  simp only [↓reduceIte]
  ring

/-- **The twisted reciprocity law of the quadratic reciprocity matrix.** For positive odd
integers `n` and `d` and characters `ψ`, `ψ'` of level eight, the coefficient
`ψ n * ψ' d * (d / n)` is the combination, with the entries of the row `(ψ, ψ')` of the
quadratic reciprocity matrix, of the coefficients `ρ d * ρ' n * (n / d)` with `n` and `d`
interchanged. -/
theorem apply_mul_apply_mul_jacobiSym_eq_sum {n d : ℕ} (hn : Odd n) (hd : Odd d)
    (ψ ψ' : DirichletCharacter ℂ 8) :
    ψ n * ψ' d * (jacobiSym d n : ℂ) =
      ∑ q : DirichletCharacter ℂ 8 × DirichletCharacter ℂ 8,
        quadraticReciprocityMatrix (ψ, ψ') q * (q.1 d * q.2 n * (jacobiSym n d : ℂ)) := by
  -- The residues of `d` and `n` modulo eight, as odd residues `2 * a + 1`.
  set a : Fin 4 := ⟨d % 8 / 2, by omega⟩
  set b : Fin 4 := ⟨n % 8 / 2, by omega⟩
  have hres {m : ℕ} (hm : Odd m) : (m : ZMod 8) = 2 * ((m % 8 / 2 : ℕ) : ZMod 8) + 1 := by
    rw [← ZMod.natCast_mod m 8]
    have hm8 : m % 8 = 2 * (m % 8 / 2) + 1 := by
      have := Nat.odd_iff.mp hm
      omega
    conv_lhs => rw [hm8]
    push_cast
    ring
  have hda : (d : ZMod 8) = 2 * (a : ℕ) + 1 := hres hd
  have hnb : (n : ZMod 8) = 2 * (b : ℕ) + 1 := hres hn
  -- The reciprocity sign only depends on the parities of `(d - 1) / 2` and `(n - 1) / 2`.
  have hsign : (((-1) ^ (d / 2 * (n / 2)) : ℤ) : ℂ) = (-1) ^ ((a : ℕ) * b) := by
    push_cast
    rw [neg_one_pow_eq_pow_mod_two (R := ℂ), neg_one_pow_eq_pow_mod_two (R := ℂ) (n := _ * _),
      Nat.mul_mod, Nat.mul_mod (a : ℕ)]
    congr 3 <;> simp only [a, b] <;> omega
  have hJ : ∑ q : DirichletCharacter ℂ 8 × DirichletCharacter ℂ 8,
        quadraticReciprocityMatrix (ψ, ψ') q * (q.1 d * q.2 n * (jacobiSym n d : ℂ)) =
      (∑ q : DirichletCharacter ℂ 8 × DirichletCharacter ℂ 8,
        quadraticReciprocityMatrix (ψ, ψ') q * (q.1 d * q.2 n)) * (jacobiSym n d : ℂ) := by
    rw [sum_mul]
    exact sum_congr rfl fun _ _ ↦ by ring
  rw [hJ, hda, hnb, sum_quadraticReciprocityMatrix_mul_apply_mul_apply,
    jacobiSym.quadratic_reciprocity hd hn, Int.cast_mul, hsign]
  ring

/-- **The quadratic reciprocity matrix is an involution**: `A * A = 1`. -/
theorem quadraticReciprocityMatrix_mul_self [DecidableEq (DirichletCharacter ℂ 8)] :
    quadraticReciprocityMatrix * quadraticReciprocityMatrix = 1 := by
  ext p r
  obtain ⟨ψ, ψ'⟩ := p
  obtain ⟨σ, σ'⟩ := r
  rw [Matrix.mul_apply]
  -- Expand the right factor and evaluate the sum over the middle index by
  -- `sum_quadraticReciprocityMatrix_mul_apply_mul_apply`.
  have hexp (q : DirichletCharacter ℂ 8 × DirichletCharacter ℂ 8) :
      quadraticReciprocityMatrix (ψ, ψ') q * quadraticReciprocityMatrix q (σ, σ') =
        1 / 16 * ∑ a : Fin 4, ∑ b : Fin 4, σ (2 * (a : ℕ) + 1) * σ' (2 * (b : ℕ) + 1) *
          (-1) ^ ((a : ℕ) * b) * (quadraticReciprocityMatrix (ψ, ψ') q *
            (q.1 (2 * (b : ℕ) + 1) * q.2 (2 * (a : ℕ) + 1))) := by
    rw [quadraticReciprocityMatrix_apply q, mul_left_comm, mul_sum]
    refine congrArg _ (sum_congr rfl fun a _ ↦ ?_)
    rw [mul_sum]
    exact sum_congr rfl fun b _ ↦ by ring
  have hswap : ∑ q : DirichletCharacter ℂ 8 × DirichletCharacter ℂ 8, ∑ a : Fin 4, ∑ b : Fin 4,
      σ (2 * (a : ℕ) + 1) * σ' (2 * (b : ℕ) + 1) * (-1) ^ ((a : ℕ) * b) *
        (quadraticReciprocityMatrix (ψ, ψ') q * (q.1 (2 * (b : ℕ) + 1) * q.2 (2 * (a : ℕ) + 1))) =
      ∑ a : Fin 4, ∑ b : Fin 4, σ (2 * (a : ℕ) + 1) * σ' (2 * (b : ℕ) + 1) *
        (-1) ^ ((a : ℕ) * b) * ∑ q : DirichletCharacter ℂ 8 × DirichletCharacter ℂ 8,
          quadraticReciprocityMatrix (ψ, ψ') q *
            (q.1 (2 * (b : ℕ) + 1) * q.2 (2 * (a : ℕ) + 1)) := by
    rw [sum_comm]
    refine sum_congr rfl fun a _ ↦ ?_
    rw [sum_comm]
    simp_rw [mul_sum]
  simp_rw [hexp]
  rw [← mul_sum, hswap]
  simp_rw [sum_quadraticReciprocityMatrix_mul_apply_mul_apply]
  -- The two reciprocity signs cancel, leaving two orthogonality sums over the odd residues.
  have hsq (a b : Fin 4) : ((-1 : ℂ) ^ ((a : ℕ) * b)) * (-1) ^ ((b : ℕ) * a) = 1 := by
    rw [mul_comm (b : ℕ), ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
  have hfac : ∑ a : Fin 4, ∑ b : Fin 4, σ (2 * (a : ℕ) + 1) * σ' (2 * (b : ℕ) + 1) *
      (-1) ^ ((a : ℕ) * b) * ((-1) ^ ((b : ℕ) * a) * ψ (2 * (a : ℕ) + 1) *
        ψ' (2 * (b : ℕ) + 1)) =
      (∑ a : Fin 4, ψ (2 * (a : ℕ) + 1) * σ (2 * (a : ℕ) + 1)) *
        ∑ b : Fin 4, ψ' (2 * (b : ℕ) + 1) * σ' (2 * (b : ℕ) + 1) := by
    rw [sum_mul_sum]
    refine sum_congr rfl fun a _ ↦ sum_congr rfl fun b _ ↦ ?_
    linear_combination (σ (2 * (a : ℕ) + 1) * σ' (2 * (b : ℕ) + 1) * ψ (2 * (a : ℕ) + 1) *
      ψ' (2 * (b : ℕ) + 1)) * hsq a b
  rw [hfac, sum_fin_four_apply_mul_apply, sum_fin_four_apply_mul_apply, Matrix.one_apply]
  by_cases h : ψ = σ <;> by_cases h' : ψ' = σ' <;> norm_num [h, h']

/-! ### Two entries -/

/-- The diagonal entry of the quadratic reciprocity matrix at the pair of principal characters
is `1/2`. -/
theorem quadraticReciprocityMatrix_apply_one_one :
    quadraticReciprocityMatrix (1, 1) (1, 1) = 1 / 2 := by
  rw [quadraticReciprocityMatrix_apply]
  simp only [MulChar.one_apply (isUnit_two_mul_add_one_fin_four _), one_mul]
  simp [Fin.sum_univ_four]
  norm_num

/-- The entry of the quadratic reciprocity matrix in the row of the pair of principal characters
and the column of the pair of lifts of `ZMod.χ₄` is `-1/2`. -/
theorem quadraticReciprocityMatrix_apply_one_χ₄ :
    quadraticReciprocityMatrix (1, 1)
      (changeLevel (by norm_num : 4 ∣ 8) (ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)),
        changeLevel (by norm_num : 4 ∣ 8) (ZMod.χ₄.ringHomComp (Int.castRingHom ℂ))) =
      -1 / 2 := by
  rw [quadraticReciprocityMatrix_apply]
  simp only [MulChar.one_apply (isUnit_two_mul_add_one_fin_four _), one_mul,
    changeLevel_χ₄_apply_fin_four]
  simp [Fin.sum_univ_four]
  norm_num

end TauCeti
